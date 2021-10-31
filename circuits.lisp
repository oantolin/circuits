(defun sum-to (s n k)
  "Return all K-tuples of integers between 0 and N that sum to S."
  (if (zerop k)
      (if (zerop s) '(()) nil)
      (let (results) 
        (dotimes (i (1+ (min n s)))
          (dolist (x (sum-to (- s i) n (1- k)))
            (push (cons i x) results)))
        results)))

(defun mapcart (fn lists)
  "Apply FN to all elements of the cartesion product of LISTS."
  (if (null lists)
      (funcall fn nil)
      (mapc (lambda (x)
              (mapcart (lambda (y) (funcall fn (cons x y)))
                       (cdr lists)))
            (car lists))))

(defun minexprs (ops atoms &key goal complexity)
  "Find minimal expressions for given values in terms of OPS and ATOMS.

OPS should be a list of 3-element lists of the form (name func arity).
If func returns nil for some arguments, that means the operation is
not applicable to those arguments and should be skipped. For example
one might use (lambda (x y) (unless (zerop y) (/ x y))) to avoid
division by 0.

ATOMS should be a list of 2-element lists of the form (name value).

The COMPLEXITY keyword parameter is the maximum expression complexity
to explore. The complexity of an expression is the total number of
operations and atoms that it comprises.

The GOAL parameter is a target number of values for which to find a
minimal expression. If the goal is met, computation stops even before
the maximum COMPLEXITY is reached.

At least one of GOAL and COMPLEXITY should be given.

The return value is a hash-table mapping values to a minimal
complexity expression that produces the value."
  (let ((values (make-array 2 :initial-element nil
                              :fill-pointer 2 :adjustable t))
        ;; values[i] holds an alist of (value . expr) pairs of complexity i
        (found 0)
        (minexpr (make-hash-table)))
    (dolist (nv atoms) ; nv is a (name value) list
      (incf found)
      (push (cons (cadr nv) (car nv)) (aref values 1))
      (setf (gethash (cadr nv) minexpr) (cons 1 (car nv))))
    (do ((cx 2 (1+ cx)))
        ((or (and goal (>= found goal))
             (and complexity (> cx complexity)))
         minexpr)
      (vector-push-extend nil values)
      (dolist (op ops)
        (destructuring-bind (name func arity) op
          (dolist (ix (sum-to (1- cx) (1- cx) arity))
            (mapcart (lambda (args)
                       (let ((val (apply func (mapcar #'car args))))
                         (unless (gethash val minexpr)
                           (let ((expr (cons name (mapcar #'cdr args))))
                             (incf found)
                             (setf (gethash val minexpr) (cons cx expr))
                             (push (cons val expr) (aref values cx))))))
                     (mapcar (lambda (i) (aref values i)) ix))))))))

(defun mincircuits (n &key complexity)
  "Find minimal circuits for all N variable boolean functions.

The optional COMPLEXITY keyword argument specifies a maximum
complexity for the search."
  (flet ((pp (k) (ash 1 (ash 1 k))))
    (let* ((mask (1- (pp n)))
           (variable-names
             (subseq '(p q r s t u v w x y z) 0 n)) ; even n=5 is too high :)
           (projections
             (loop for k below n
                   collect (/ (* (1- (pp n)) (pp k)) (1+ (pp k))))))
      (minexprs
       `((and ,#'logand 2)
         (or ,#'logior 2)
         (not ,(lambda (x) (logand mask (lognot x))) 1))
       (mapcar #'list variable-names projections)
       :complexity complexity
       :goal (ash 1 (ash 1 n))))))

(defun save-mincircuits (n &key (file "mincircuits~d.txt") complexity verbose)
  "Save minimal circuits for boolean functions of N variables to FILE.

The FILE can contain a '~d' which will be replaced by N.

The optional COMPLEXITY specifies a maximum complexity for the search.

If VERBOSE is true, then a message is printed for functions for which
no circuit was found. By default, these functions are silently omitted."
  (with-open-file (out (format nil file n) :direction :output
                                           :if-exists :supersede)
    (let ((circuits (mincircuits n :complexity complexity)))
      (dotimes (k (ash 1 (ash 1 n)))
        (let ((me (gethash k circuits)))
          (if (null me)
              (when verbose
                (format out "~%~v,'0b no circuit found" (ash 1 n) k))
              (format out "~%~v,'0b [~2d] ~a"
                      (ash 1 n) k (car me) (cdr me))))))))

(defun empty-stats (n circuits)
  "Compare circuits for boolean functions that differ only on 00...0.

N is the number of variables of the boolean functions.

CIRCUITS is hash-table mapping functions to pairs whose cdr is an
optimal circuit for the function and whose car is the complexity of
said function."
  (loop with total = (ash 1 (1- (ash 1 n)))
        for e below total
        for c0 = (car (gethash (* 2 e) circuits))
        for c1 = (car (gethash (1+ (* 2 e)) circuits))
        count (< c0 c1) into win0
        count (= c0 c1) into ties
        count (> c0 c1) into win1
        if (< c0 c1)
          sum (- c1 c0) into diff0
        else
          sum (- c0 c1) into diff1
        finally
           (format t "Which value of f(00...0) gives simpler circuits?
0 is simpler: ~,2f% (~d)~%1 is simpler: ~,2f% (~d)
No difference: ~,2f% (~d)~%
Average complexity savings:
When 0 is simpler: ~,2f~%When 1 is simpler: ~,2f
Total (includes ties): ~,2f"
                   (* 100 (/ win0 total)) win0
                   (* 100 (/ win1 total)) win1
                   (* 100 (/ ties total)) ties
                   (/ diff0 win0)
                   (/ diff1 win1)
                   (/ (+ diff0 diff1) total))))

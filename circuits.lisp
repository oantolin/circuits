(defun partitions (n k m)
  "Return all partitions of N into K parts, each at most m.
Each partition is represented as an alist of parts and multiplicities.
For example ((3 . 2) (2 . 1)) represents the partition 3+3+2 of 8."
  (cond
    ((= n k 0) '(()))
    ((or (= n 0) (= k 0) (= m 0)) nil)
    (t (let ((results (partitions n k (1- m))))
         (dotimes (i (min k (floor n m)))
           (dolist (p (partitions (- n (* (1+ i) m)) (- k i 1) (1- m)))
             (push (cons (cons m (1+ i)) p) results)))
         results))))

(defun subsets (k list)
  "Return all susbets of K elements taken from LIST.
The order of the elements in each subset is the same as in LIST."
  (cond
    ((= k 0) '(()))
    ((= k 1) (mapcar #'list list))
    ((null list) nil)
    (t (destructuring-bind (x . rest) list
         (append (mapcar (lambda (s) (cons x s)) (subsets (1- k) rest))
                 (subsets k rest))))))

(defun mapcart (fn lists)
  "Apply FN to all elements of the cartesion product of LISTS."
  (if (null lists)
      (funcall fn nil)
      (mapc (lambda (x)
              (mapcart (lambda (y) (funcall fn (cons x y)))
                       (cdr lists)))
            (car lists))))

(defun minexprs (ops atoms &key goal complexity)
  "Find all minimal expressions for given values in terms of OPS and ATOMS.

OPS should be a list of 4-element lists of the following form:
(name func min-arity max-arity). The max-arity can be the symbol
:infinity. The operations are assumed to be commutative and
idempotent, and thus to reduce repetitions of the expression an
arbitrary total order is imposed on the expressions and operations are
only constructed with arguments in increasing order.

ATOMS should be a list of 2-element lists of the form (name value).

The COMPLEXITY keyword parameter is the maximum expression complexity
to explore. The complexity of an expression is the total number of
operations and atoms that it comprises.

The GOAL parameter is a target number of values for which to find a
minimal expression. If the goal is met, computation stops even before
the maximum COMPLEXITY is reached.

At least one of GOAL and COMPLEXITY should be given.

The return value is a hash-table mapping values to a list whose first
element is the minimal complexity of expression that produces the
value, and whose tail is the list of all expressions of that minimum
complexity."
  (let ((values (make-array 2 :initial-element nil
                              :fill-pointer 2 :adjustable t))
        ;; values[i] holds an alist of (value . expr) pairs of complexity i
        (found 0)
        (minexpr (make-hash-table)))
    (dolist (nv atoms) ; nv is a (name value) list
      (incf found)
      (push (cons (cadr nv) (car nv)) (aref values 1))
      (setf (gethash (cadr nv) minexpr) (list 1 (car nv))))
    (do ((cx 2 (1+ cx)))
        ((or (and goal (>= found goal))
             (and complexity (> cx complexity)))
         minexpr)
      (vector-push-extend nil values)
      (dolist (op ops)
        (destructuring-bind (name func min-arity max-arity) op
          (dotimes (i (1+ (- (if (eq max-arity :infinity) (1- cx) max-arity)
                             min-arity)))
            (let ((arity (+ i min-arity)))
              (dolist (part (partitions (1- cx) arity (1- cx)))
                (mapcart (lambda (args)
                           (setf args (reduce #'append args :from-end t))
                           (let* ((val (apply func (mapcar #'car args)))
                                  (seen (gethash val minexpr)))
                             (when (or (not seen) (= (car seen) cx))
                               (let ((expr (cons name (mapcar #'cdr args))))
                                 (unless seen
                                   (incf found)
                                   (push cx (gethash val minexpr)))
                                 (push expr (cdr (gethash val minexpr)))
                                 (push (cons val expr) (aref values cx))))))
                         (mapcar (lambda (p)
                                   (subsets (cdr p) (aref values (car p))))
                                 part))))))))))

(defun mincircuits (n &key complexity max-arity)
  "Find minimal circuits for all N variable boolean functions.

The optional COMPLEXITY argument specifies a maximum complexity for
the search.

The optional MAX-ARITY argument specifies a maximum arity for the AND
and OR gates. If absent it defaults to N. You can also use the symbol
:infinity."
  (unless max-arity (setf max-arity n))
  (flet ((pp (k) (ash 1 (ash 1 k))))
    (let* ((mask (1- (pp n)))
           (variable-names
             (subseq '(p q r s t u v w x y z) 0 n)) ; even n=5 is too high :)
           (projections
             (loop for k below n
                   collect (/ (* (1- (pp n)) (pp k)) (1+ (pp k))))))
      (minexprs
       `((and ,#'logand 2 ,max-arity)
         (or ,#'logior 2 ,max-arity)
         (not ,(lambda (x) (logand mask (lognot x))) 1 1))
       (mapcar #'list variable-names projections)
       :complexity complexity
       :goal (ash 1 (ash 1 n))))))

(defun save-mincircuits (n &key (file "mincircuits~d.txt")
                             complexity max-arity verbose)
  "Save minimal circuits for boolean functions of N variables to FILE.

The FILE can contain a '~d' which will be replaced by N.

The optional COMPLEXITY specifies a maximum complexity for the search.

The optional MAX-ARITY argument specifies a maximum arity for the AND
and OR gates. If absent it defaults to N. You can also use the symbol
:infinity.
  
If VERBOSE is true, then a message is printed for functions for which
no circuit was found. By default, these functions are silently omitted."
  (with-open-file (out (format nil file n) :direction :output
                                           :if-exists :supersede)
    (let ((circuits (mincircuits n :complexity complexity
                                   :max-arity max-arity)))
      (dotimes (k (ash 1 (ash 1 n)))
        (let ((me (gethash k circuits)))
          (if (null me)
              (when verbose
                (format out "~%~v,'0b no circuit found" (ash 1 n) k))
              (format out "~%~v,'0b [~2d] ~a"
                      (ash 1 n) k (car me) (cdr me))))))))

;;; auxiliary functions for collecting statistics on circuits

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

(defun max-arity (expr)
  "Return maximum arity of any operation in EXPR."
  (if (atom expr)
      0
      (apply #'max (1- (length expr)) (mapcar #'max-arity (cdr expr)))))

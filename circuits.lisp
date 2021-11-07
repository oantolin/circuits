(defmacro dorange ((var from to) &body body)
  `(loop for ,var from ,from to ,to do ,@body))

(defun partitions (n k l m)
  "Return all partitions of N into between K and L parts, each at most M.
Each partition is represented as an alist of parts and multiplicities.
For example ((3 . 2) (2 . 1)) represents the partition 3+3+2 of 8."
  (cond
    ((= n k 0) '(()))
    ((or (= n 0) (= l 0) (= m 0)) nil)
    (t (let ((results (partitions n k l (1- m))))
         (dorange (i 1 (min l (floor n m)))
           (dolist (p (partitions (- n (* i m)) (max 0 (- k i)) (- l i) (1- m)))
             (push (cons (cons m i) p) results)))
         results))))

(defun subsets (k list)
  "Return all susbets of K elements taken from LIST.
The order of the elements in each subset is the same as in LIST."
  (cond
    ((= k 0) '(()))
    ((= k 1) (mapcar #'list list))
    ((= k 2) (loop for (x . rest) on list
                   nconc (loop for y in rest collect (list x y))))
    ((null list) nil)
    (t (destructuring-bind (x . rest) list
         (nconc (mapcar (lambda (s) (cons x s)) (subsets (1- k) rest))
                (subsets k rest))))))

(defun mapcart (fn lists)
  "Apply FN to all elements of the cartesion product of LISTS."
  (if (null lists)
      (funcall fn nil)
      (mapc (lambda (x)
              (mapcart (lambda (y) (funcall fn (cons x y)))
                       (cdr lists)))
            (car lists))))

(defun mincircuits (n &key complexity max-arity)
  "Find minimal circuits for all boolean functions of N variables.

The circuits use NOT, AND & OR gates. The AND & OR gates used are
allowed to have arity between 2 and MAX-ARITY, which, if omitted
defaults to N. One can also use the symbol :infinity, to specify there
is no upper bound on arity.

The return value is an array of length 2^2^n associating to each
boolean function a list of minimal circuits for it. The circuits are
specified by a list whose first element is the type of gate, and whose
remaining elements are other boolean functions.

The optional argument COMPLEXITY specifies a maximum complexity to
bound the search."
  (unless max-arity (setf max-arity n))
  (flet ((pp (k) (ash 1 (ash 1 k))))
    (let* ((mask (1- (pp n)))
           (atoms
             (append
              `((0 . 0) (1 . ,mask))
              (loop for var in '(p q r s t u v w x y z) and k below n
                    collect (cons var (/ (* (1- (pp n)) (pp k)) (1+ (pp k)))))))
           (total 0)
           (minexpr (make-array (pp n) :initial-element nil))
           (fns-w/cx (make-array 2 :initial-element nil
                                   :fill-pointer 2 :adjustable t)))
      (flet ((found (cx fn expr) 
               (let ((seen (aref minexpr fn)))
                 (when (or (not seen) (= cx (car seen)))
                   (unless seen
                     (incf total)
                     (push cx (aref minexpr fn))
                     (push fn (aref fns-w/cx cx)))
                   (push expr (cdr (aref minexpr fn)))))))
        ;; complexity 1: constants 0, 1 & variables
        (dolist (name-func atoms)
          (destructuring-bind (name . func) name-func
            (found 1 func name)))
        ;; higher complexities
        (do ((cx 2 (1+ cx)))
            ((or (= total (pp n)) (and complexity (> cx complexity)))
             minexpr)
          (vector-push-extend nil fns-w/cx)
          ;; NOT gates
          (dolist (fn (aref fns-w/cx (1- cx)))
            (found cx (logand mask (lognot fn)) (list 'not fn)))
          ;; AND & OR gates
          (let ((max-parts (if (eq max-arity :infinity) (1- cx) max-arity)))
            (dolist (part (partitions (1- cx) 2 max-parts (1- cx)))
              (mapcart
               (lambda (args)
                 (setf args (reduce #'append args :from-end t))
                 (found cx (apply #'logior args) (cons 'or args))
                 (found cx (apply #'logand args) (cons 'and args)))
               (mapcar (lambda (p) (subsets (cdr p) (aref fns-w/cx (car p))))
                       part)))))))))

(defun expand-circuits (fn table)
  "Return all circuits for FN implicitly in TABLE."
  (labels ((rec (fn)
             (mapcan (lambda (circuit)
                       (if (atom circuit)
                           (list circuit)
                           (let (all)
                             (mapcart
                              (lambda (args)
                                (push (cons (car circuit) args) all))
                              (mapcar #'rec (cdr circuit)))
                             (nreverse all))))
                     (cdr (aref table fn)))))
    (rec fn)))

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
        (let ((cx (car (aref circuits k))))
          (if (null cx)
              (when verbose
                (format out "~%~v,'0b no circuit found" (ash 1 n) k))
              (format out "~%~v,'0b [~2d] ~a"
                      (ash 1 n) k cx (expand-circuits k circuits))))))))

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

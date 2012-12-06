 (defun variable-p (exp)
  (member exp '(x y n u v))) ; considers these symbols as variables 
  
  
;;code that checks for pattern matching  
;;Match pattern against an input.
  
(defun pat-match (pattern input &optional (pairings '((t . t))))
  (cond ((eq pairings nil) nil)  ; if matching has failed already then no need to check further
        ((variable-p pattern)    ; if it's a variable, add this to pairings
         (match-variable pattern input pairings))
        ((eql pattern input) pairings) ; written pairings
        ((segment-pattern-p pattern)   ; does greddy matching for a variable    
         (segment-match+ pattern input pairings)) 
        ((single-pattern-p pattern)         
         (match-is (rest pattern) input pairings))		 
        ((and (consp pattern) (consp input)) 
         (pat-match (cdr pattern) (cdr input)
                    (pat-match (car pattern) (car input) 
                               pairings)))
        (t nil)))

;;code that checks for matching variables 
(defun match-variable (var input pairings)
  (let ((binding (assoc var pairings)))       ; if var is not already present in pairings add to pairings
    (cond ((not binding) (cons (cons var input) ; else check wheter input is equal to already present value of var in pairing
        (if (eq pairings '((t . t)))
            nil
            pairings)))
          ((equal input (cdr binding)) pairings)
          (t nil))))                       ; if not equal return null
		  
(defun match-is (var-and-pred input pairings)
    (if (or (eq (pat-match (first var-and-pred) input pairings) nil)  ; checks whether input satisfies the predicate 
            (not (funcall (second var-and-pred) input)))
        nil                                               
        (pat-match (first var-and-pred) input pairings))) ; if satisfies assign var to input and add to pairing

;;single pattern match check
(defun single-pattern-p (pattern)
  (and (consp pattern)
       (equal (first pattern) '?is)))  ; checks whether pattern is of the form (?is n predicate)
	
;;segment pattern match check		
(defun segment-pattern-p (pattern)
  (and (consp pattern) (consp (car pattern)) ; checks whether pattern is of the form (?+ var)
       (symbolp (car (car pattern)))
       (equal (car (car pattern)) '?+)))

(defun segment-match+ (pattern input pairings &optional (start 1))
  (let ((var (second (car pattern)))   ; does a greedy matching of pattern over input
        (pat (cdr pattern)))           ; and assign to var
    (if (null pat)
        (match-variable var input pairings)
        (let ((pos (car-match-pos (car pat) input start)))  ; checks the position of the symbol after segment variable 
          (if (null pos)                                    ; in the rest of the input from 'start' position
              nil
              (let ((b2 (pat-match
                          pat (subseq input pos)
                          (match-variable var (subseq input 0 pos)
                                          pairings))))
                (if (eq b2 nil)                            ; if it fails it checks for the next occurence of the (symbol after segment variable)
                    (segment-match+ pattern input pairings (+ pos 1))
                    b2)))))))


;;function that converts an expression from infix->prefix based on the infix->prefix rules!
(defun infix->prefix (exp)
  (cond ((atom exp) exp)
        ((and (consp exp) (null (rest exp))) (infix->prefix (car exp)))
        ((rule-based-translator exp *infix->prefix-rules*  ; applies set of rules to convert from infix to prefix
           :rule-if #'rule-pattern :rule-then #'rule-response
           :action
           #'(lambda (pairings response)
               (sublis (mapcar
                         #'(lambda (pair)
                             (cons (first pair)
                                   (infix->prefix (cdr pair))))
                         pairings)
                       response))))
        ((symbolp (first exp))
         (list (car exp) (infix->prefix (cdr exp))))
        (t (error "Invalid input"))))

(defun car-match-pos (pat1 input start)
  (cond ((not (or (not (atom pat1)) (variable-p pat1))) ; checks where the pattern occurs in input from 'start' position
         (position pat1 input :start start :test #'equal))
        ((<= start (length input)) start) 
        (t nil)))

;;Apply a set of rules.
(defun rule-based-translator 
       (input rules &key (matcher 'pat-match) 
        (rule-if #'car) (rule-then #'cdr) (action #'sublis))
  (some 
    #'(lambda (rule)
        (let ((result (funcall matcher (funcall rule-if rule)  ; checks whether input matches the rule
                               input)))
          (if (not (eq result nil))
              (funcall action result (funcall rule-then rule))))) ; applies the corresponding option
    rules))


(defstruct (rule (:type list)) pattern response)  ; data structure for storing rules
(defstruct (expr (:type list)
                (:constructor mkexp (lhs op rhs))) ; data structure for storing expressions, they are stored in prefix form internally
  op lhs rhs)


(defun prefix->infix (exp)
  (if (not (atom exp)) 
      (mapcar #'prefix->infix        ; applies this function recursively to internal sublists
              (if (and (consp exp) (= (length (cdr exp)) 2)) ; checks whether it is binary expression or not
                  (list (expr-lhs exp) (expr-op exp) (expr-rhs exp)) ; returns the expression in infix form in a list
                  exp))
				  exp))

;;define all the rules for infix->prefix conversion in the order of precedence
(defparameter *infix->prefix-rules*
  '((((?+ u) = (?+ v)) (= u v)) ((- (?+ u)) (- u)) ((+ (?+ v)) (+ v))
 (((?+ v) + (?+ u)) (+ v u)) (((?+ u) - (?+ v)) (- u v))
 ((D (?+ u) / D v) (D u v)) ((INT (?+ u) D v) (INT u v))
 (((?+ u) * (?+ v)) (* u v)) (((?+ u) / (?+ v)) (/ u v))
 (((?+ X) ^ (?+ Y)) (^ X Y)))
)

		
(defun integration (inf x) (prefix->infix (simplify (infix->prefix (list 'int (list inf) 'd x)))))

;;function that takes an expression as input and simplifies it by applying the various simplification rules!
(defun simplify (exp) 
  (if (not (atom exp)) 
      (simplify-exp (mapcar #'simplify exp)) ; applies simplify-exp to all members of a list
	  exp))

(defvar *simplification-rules* nil) 

(defun ^ (x y)  (expt x y))

;;Decide if an expression can be numerically evaluated.
(defun evaluable (exp)
  (and (every #'numberp (cdr exp))
       (or (and (eq (expr-op exp) '^)
                (integerp (second (cdr exp))))
				(member (expr-op exp) '(+ - * /))
           )))
		   
;;Divide a list of factors by another, producing a third. 

(defun divide-factors (numer denom)
  (let ((result (mapcar #'copy-list numer)))
    (dolist (d denom)      
        (if (find (expr-lhs d) result :key #'expr-lhs 
                          :test #'equal)
            (decf (expr-rhs (find (expr-lhs d) result :key #'expr-lhs ; checks wether a factor or denominator is found in numberator or not
                          :test #'equal)) (expr-rhs d))
            (push `(^ ,(expr-lhs d) ,(- (expr-rhs d))) result)))
    (delete 0 result :key #'expr-rhs)))

;;Simplify a non-atomic prefix expression.
(defun simplify-exp (exp)
  (cond ((equal (expr-op exp) 'int) (simplify (unfactorize  ; if exp starts with 'int' do integration 
		       (factorize
			(integrate (expr-lhs exp) (expr-rhs exp))))))                             
        ((rule-based-translator exp *simplification-rules*  ; else use simplification rules
           :rule-if #'expr-lhs :rule-then #'expr-rhs
           :action #'(lambda (pairings response)
                       (simplify (sublis pairings response)))))
        ((evaluable exp) (eval exp))
        (t exp)))

;;function which takes the expression and factorizes it into sub exprsns
(defun factorize (exp)
  (let ((factors nil)
        (constant 1))
    (labels
      ((fac (x n)
         (cond
           ((numberp x) ; if x is a constant, multiply the factor by x
            (setf constant (* constant (expt x n))))
           ((and (consp x) (eql (car x) '*)) ;if expression stars with * apply recursively on both parts
            (fac (expr-lhs x) n)
            (fac (expr-rhs x) n))
           ((and (consp x) (eql (car x) '/)) ; starts with /
            (fac (expr-lhs x) n)
            (fac (expr-rhs x) (- n)))         ; denominator all powers of x are converted to negative
           ((and (and (consp x) (eql (car x) '-)) (and (consp (cdr x)) (null (cdr (cdr x)))))
            (setf constant (- constant))
            (fac (expr-lhs x) n))
           ((and (and (consp x) (eql (car x) '^)) (numberp (expr-rhs x)))
            (fac (expr-lhs x) (* n (expr-rhs x))))
           (t (let ((factor (find x factors :key #'expr-lhs
                                  :test #'equal)))
                (if factor
                    (incf (expr-rhs factor) n)
                    (push `(^ ,x ,n) factors)))))))
      (fac exp 1)
      (case constant
        (0 '((^ 0 1)))
        (1 factors)
        (t `((^ ,constant 1) .,factors))))))


;;function to unfactorize
;;Convert a list of factors back into prefix form

(defun unfactorize (factors) 
  (cond ((null factors) 1)
        ((and (consp factors) (null (cdr factors))) (car factors)) ; checks whether length of factors is 1
        (t `(* ,(car factors) ,(unfactorize (cdr factors)))))) 

;;Checks if item occurs anywhere in tree? If so, return it 
(defun find-anywhere (item tree)
  (cond ((eql item tree) tree)
        ((atom tree) nil)
        ((find-anywhere item (car tree)))
        ((find-anywhere item (cdr tree)))))

;;function integrate which takes the expression to be integrated as input! 
(defun integrate (exp x)
  (cond
    ((not (find-anywhere x exp)) `(* ,exp x))          ; if thers is no x in expression, then ans is constant * x
    ((and (consp exp) (eql (car exp) '+))               ; if expression begins with + , apply integration to both sides
     `(+ ,(integrate (expr-lhs exp) x)     
         ,(integrate (expr-rhs exp) x)))
    ((and (consp exp) (eql (car exp) '-))             ; checks whether expression begins with - or not 
     (ecase (length (cdr exp))        
       (1 (integrate (expr-lhs exp) x))                ; '-' here is a unary operator
       (2 `(- ,(integrate (expr-lhs exp) x) 
              ,(integrate (expr-rhs exp) x)))))  
    ((multiple-value-bind (const-factors x-factors)
         (partition-if #'(lambda (factor) (not (find-anywhere x factor)))
                       (factorize exp))
       (identity 
         `(* ,(unfactorize const-factors)
             ,(cond ((null x-factors) x)
                    ((some #'(lambda (factor)
                               (deriv-divides factor x-factors x))
                           x-factors)) ; substitutionn method
					((equal (expr-op exp) '*)  (mkexp (mkexp (expr-lhs exp) '* (integrate (expr-rhs exp) x)) '- 
					(integrate (mkexp (deriv (expr-lhs exp) x) '* (expr-rhs exp)) x)))	; u v rule
                     ((equal (expr-op exp) '^) (mkexp 'e '^ (integrate (list '* (expr-rhs exp) (list 'log (expr-lhs exp))) x)))		; x ^ f(x) form			
                    (t (error "cannot integrate")))))))))

;;partition if required
(defun partition-if (pred list)
  (let ((yes-list nil)
        (no-list nil))
    (dolist (item list)
      (if (not (funcall pred item)) ; divides the list into two parts absed on predicate
	  (push item no-list)
          (push item yes-list)
          ))
    (values (nreverse yes-list) (nreverse no-list))))

(defun deriv-divides (factor factors x)
  (assert (and (consp factor) (eql (car factor) '^))) ; checks wheter factor list begins with '^'
  (let* ((u (expr-lhs factor))            
         (n (expr-rhs factor))
         (k (divide-factors 
              factors (factorize `(* ,factor ,(deriv u x))))))
    (cond ((not (find-anywhere x k))  ; applies substitution method
           (if (= n -1)
               `(* ,(unfactorize k) (log ,u))
               `(/ (* ,(unfactorize k) (^ ,u ,(+ n 1)))
                   ,(+ n 1))))
          ((and (= n 1) (in-integral-table? u))
           (let ((k2 (divide-factors
                       factors
                       (factorize `(* ,u ,(deriv (expr-lhs u) x))))))
             (if (not (find-anywhere x k2))
                 `(* ,(integrate-from-table (expr-op u) (expr-lhs u))
                     ,(unfactorize k2))))))))



(defun deriv (y x) (simplify `(d ,y ,x))) ;;get derivative of y wrt x

(defun integration-table (rules)
  (dolist (i-rule rules)
      (setf (get (expr-op (expr-lhs (expr-lhs i-rule))) 'int) ;; sets up integration table from the rules
            i-rule)))

(defun in-integral-table? (exp)
  (and (consp exp) (get (expr-op exp) 'int))) ;first check if integral is in the predefined integral-table 

(defun integrate-from-table (op arg)
    (subst arg (expr-lhs (expr-lhs (expr-lhs (get op 'int)))) (expr-rhs (get op 'int)))) ; gets the value of integral from table


;;Rules to simplify an expression.
;;Store all the simplification rules! 
(setf *simplification-rules* '((= (+ X 0) X) (= (+ 0 X) X) (= (+ X X) (* 2 X)) (= (- X 0) X)
 (= (- 0 X) (- X)) (= (- X X) 0) (= (- (- X)) X) (= (* X 1) X) (= (* 1 X) X)
 (= (* X 0) 0) (= (* 0 X) 0) (= (* X X) (^ X 2)) (= (/ X 0) UNDEFINED)
 (= (/ 0 X) 0) (= (/ X 1) X) (= (/ X X) 1) (= (^ 0 0) UNDEFINED) (= (^ X 0) 1)
 (= (^ 0 X) 0) (= (^ 1 X) 1) (= (^ X 1) X) (= (^ X -1) (/ 1 X))
 (= (* X (/ Y X)) Y) (= (* (/ Y X) X) Y) (= (/ (* Y X) X) Y)
 (= (/ (* X Y) X) Y) (= (+ X (- X)) 0) (= (+ (- X) X) 0) (= (+ X (- Y X)) Y)))


(setf *simplification-rules* 
 (append *simplification-rules* '((= (D X X) 1) 
  (= (D (/ U V) X) (/ (- (* V (D U X)) (* U (D V X))) (^ V 2)))
 (= (D (- U) X) (- (D U X)))
  (= (D (- U V) X) (- (D U X) (D V X))) 
 (= (D (^ U N) X) (* N (* (^ U (- N 1)) (D U X))))
  (= (D (+ U V) X) (+ (D U X) (D V X)))
 (= (D (* U V) X) (+ (* U (D V X)) (* V (D U X))))
 (= (D (LOG U) X) (/ (D U X) U)) (= (D (SIN U) X) (* (COS U) (D U X)))
 (= (D (COS U) X) (- (* (SIN U) (D U X))))
 (= (D (^ U V) X)
  (+ (* V (* (^ U (- V 1)) (D U X))) (* (^ U V) (* (LOG U) (D V X)))))

 (= (D (^ E U) X) (* (^ E U) (D U X))) (= (D U X) 0))
))

;;Integration Look up table with predefined values of certain integrals! 
;; need to add some more functions here      
(integration-table
  '((= (INT (E X) X) (E X))
  (= (INT (LOG X) X) (- (* X (LOG X)) X)) 
  (= (INT (TAN X) X) (- (LOG (COS X))))
  (= (INT (COS X) X) (SIN X))
 (= (INT (SIN X) X) (- (COS X))) 
  (= (INT (SINH X) X) (COSH X))
  (= (INT (TANH X) X) (LOG (COSH X)))
 (= (INT (COSH X) X) (SINH X)) )
 )
 
 ; Reference from the book Paradigms of AI programming

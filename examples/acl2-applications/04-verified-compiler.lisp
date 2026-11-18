; 04  A verified compiler and optimizer for a small expression language
;
; Industry context: ACL2 has been used to model real instruction sets and
; virtual machines, including Rockwell Collins' AAMP7G microprocessor, the
; Java Virtual Machine (the M1-M6 models) and the x86 ISA (Shilpi Goel's
; x86isa model, used at Centaur and Intel).  Verifying code generators
; and optimization passes against such models is the step that rules out
; miscompilation bugs.  (CompCert in Coq is the best-known full compiler
; done this way.)
;
; The source language has variables, constants, + - * and an
; if-nonzero-then-else.  The target is a stack machine with conditional
; and unconditional relative jumps, so control flow is included.  Proved:
;
;   * the compiler is correct for every program, every variable
;     environment and every starting stack (not just the empty one, which
;     is the generalization the induction needs);
;   * a constant-folding / algebraic-simplification pass preserves
;     meaning, so it can be added to the pipeline without re-proving the
;     back end.

(in-package "ACL2")

;; ---------------------------------------------------------------------
;; Source language
;;   e ::= n | x | (+ e e) | (- e e) | (* e e) | (if e e e)

(defun lookup (x env) (ifix (cdr (assoc-equal x env))))

(defun eval-expr (e env)
  (cond ((integerp e) e)
        ((atom e) (lookup e env))
        ((eq (car e) '+) (+ (eval-expr (cadr e) env) (eval-expr (caddr e) env)))
        ((eq (car e) '-) (- (eval-expr (cadr e) env) (eval-expr (caddr e) env)))
        ((eq (car e) '*) (* (eval-expr (cadr e) env) (eval-expr (caddr e) env)))
        ((eq (car e) 'if) (if (equal (eval-expr (cadr e) env) 0)
                              (eval-expr (cadddr e) env)
                            (eval-expr (caddr e) env)))
        (t 0)))

;; ---------------------------------------------------------------------
;; Target machine.  A program is a list of instructions run from the
;; front; jumps are relative and only go forward (enough for
;; expressions), so plain structural recursion terminates.
;;   (PUSH n) (LOAD x) (ADD) (SUB) (MUL)
;;   (JZ k)    pop; if the value is 0, skip the next k instructions
;;   (JMP k)   skip the next k instructions

(defthm len-nthcdr-bound                  ; needed for termination
  (<= (len (nthcdr n x)) (len x))
  :rule-classes :linear)

(defun exec (prog env stk)
  (declare (xargs :measure (len prog)))
  (if (endp prog)
      stk
    (let ((ins (car prog)) (rest (cdr prog)))
      (case (car ins)
        (push (exec rest env (cons (ifix (cadr ins)) stk)))
        (load (exec rest env (cons (lookup (cadr ins) env) stk)))
        (add  (exec rest env (cons (+ (ifix (cadr stk)) (ifix (car stk))) (cddr stk))))
        (sub  (exec rest env (cons (- (ifix (cadr stk)) (ifix (car stk))) (cddr stk))))
        (mul  (exec rest env (cons (* (ifix (cadr stk)) (ifix (car stk))) (cddr stk))))
        (jz   (if (equal (ifix (car stk)) 0)
                  (exec (nthcdr (nfix (cadr ins)) rest) env (cdr stk))
                (exec rest env (cdr stk))))
        (jmp  (exec (nthcdr (nfix (cadr ins)) rest) env stk))
        (otherwise stk)))))

;; ---------------------------------------------------------------------
;; Compiler

(defun compile-expr (e)
  (cond ((integerp e) (list (list 'push e)))
        ((atom e) (list (list 'load e)))
        ((member-eq (car e) '(+ - *))
         (append (compile-expr (cadr e))
                 (compile-expr (caddr e))
                 (list (list (case (car e) (+ 'add) (- 'sub) (t 'mul))))))
        ((eq (car e) 'if)
         (let ((c (compile-expr (cadr e)))
               (a (compile-expr (caddr e)))
               (b (compile-expr (cadddr e))))
           (append c
                   (list (list 'jz (+ 1 (len a))))
                   a
                   (list (list 'jmp (len b)))
                   b)))
        (t (list (list 'push 0)))))

;; Key lemma: running compiled code followed by more code is running the
;; compiled code and then the rest, with the value pushed on the stack.
;; The induction has to let the continuation code MORE and the stack
;; vary: when compiling (+ a b), the code for b runs with a's value
;; already on the stack.  The function below exists only to tell ACL2
;; that induction scheme; it is never run.

(defun op-ins (op) (case op (+ 'add) (- 'sub) (t 'mul)))

(defun comp-induct (e env more stk)
  (cond ((atom e) (list env more stk))
        ((member-eq (car e) '(+ - *))
         (list (comp-induct (cadr e) env
                            (append (compile-expr (caddr e))
                                    (cons (list (op-ins (car e))) more))
                            stk)
               (comp-induct (caddr e) env
                            (cons (list (op-ins (car e))) more)
                            (cons (eval-expr (cadr e) env) stk))))
        ((eq (car e) 'if)
         (let ((a (compile-expr (caddr e)))
               (b (compile-expr (cadddr e))))
           (list (comp-induct (cadr e) env
                              (cons (list 'jz (+ 1 (len a)))
                                    (append a (cons (list 'jmp (len b))
                                                    (append b more))))
                              stk)
                 (comp-induct (caddr e) env
                              (cons (list 'jmp (len b)) (append b more))
                              stk)
                 (comp-induct (cadddr e) env more stk))))
        (t nil)))

(defthm append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm nthcdr-len-append
  (implies (equal n (len a))
           (equal (nthcdr n (append a b)) b)))

(defthm nthcdr-len-append-cons          ; skipping a, then one more
  (implies (equal n (+ 1 (len a)))
           (equal (nthcdr n (append a (cons x b))) b)))

(defthm integerp-eval-expr
  (integerp (eval-expr e env))
  :rule-classes :type-prescription)

(defthm run-append-comp
  (equal (exec (append (compile-expr e) more) env stk)
         (exec more env (cons (eval-expr e env) stk)))
  :hints (("Goal" :induct (comp-induct e env more stk))))

(defthm compiler-correct
  (equal (exec (compile-expr e) env stk)
         (cons (eval-expr e env) stk))
  :hints (("Goal" :use (:instance run-append-comp (more nil))
                  :in-theory (disable run-append-comp))))

;; ---------------------------------------------------------------------
;; Optimizer: constant folding plus the identities x+0, x*1, x*0, x-x
;; and folding of a constant if-test.

(defun mk-op (op a b)
  (cond ((and (integerp a) (integerp b))
         (case op (+ (+ a b)) (- (- a b)) (t (* a b))))
        ((and (eq op '+) (equal a 0)) b)
        ((and (member-eq op '(+ -)) (equal b 0)) a)
        ((and (eq op '*) (or (equal a 0) (equal b 0))) 0)
        ((and (eq op '*) (equal a 1)) b)
        ((and (eq op '*) (equal b 1)) a)
        ((and (eq op '-) (equal a b) (atom a)) 0)   ; x - x, for a variable x
        (t (list op a b))))

(defun opt (e)
  (cond ((atom e) e)
        ((member-eq (car e) '(+ - *))
         (mk-op (car e) (opt (cadr e)) (opt (caddr e))))
        ((eq (car e) 'if)
         (let ((c (opt (cadr e))))
           (cond ((equal c 0) (opt (cadddr e)))
                 ((integerp c) (opt (caddr e)))
                 (t (list 'if c (opt (caddr e)) (opt (cadddr e)))))))
        (t 0)))

(defthm opt-correct
  (equal (eval-expr (opt e) env) (eval-expr e env)))

;; The whole pipeline, source -> optimizer -> code generator -> machine:
(defthm pipeline-correct
  (equal (exec (compile-expr (opt e)) env stk)
         (cons (eval-expr e env) stk)))

;; Concrete check: the optimizer removes dead code and folds constants.
(defthm opt-example
  (and (equal (opt '(+ (* x 1) (if (- 3 3) y (* 2 5)))) '(+ x 10))
       (equal (exec (compile-expr '(if (- a b) (* a a) 7)) '((a . 4) (b . 4)) nil)
              '(7)))
  :rule-classes nil)

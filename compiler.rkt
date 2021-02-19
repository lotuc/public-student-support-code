#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Rint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Rint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniquify-symbol-count 0)
(define next-uniquify-symbol
  (lambda ()
    (set! uniquify-symbol-count (+ uniquify-symbol-count 1))
    (string->symbol (string-append "x." (number->string uniquify-symbol-count)))))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (if (dict-has-key? env x)
           (Var (dict-ref env x))
           (Var x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define e1 ((uniquify-exp env) e))
       (define x1 (next-uniquify-symbol))
       (define body1 ((uniquify-exp (dict-set env x x1)) body))
       (Let x1 e1 body1)]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define rco-symbol-count 0)
(define next-rco-symbol
  (lambda ()
    (set! rco-symbol-count (+ rco-symbol-count 1))
    (string->symbol (string-append "tmp." (number->string rco-symbol-count)))))

(define (map-to-lets maps e)
  (if (null? maps)
      e
      (let ([m (car maps)])
        (if (null? m)
            (map-to-lets (cdr maps) e)
            (Let (car (car m)) (cdr (car m))
              (map-to-lets (cons (cdr m) (cdr maps)) e))))))

(define (rco-exp e)
  (match e
    [(Int i) (Int i)]
    [(Var v) (Var v)]
    [(Prim op es)
     (define-values (atoms maps)
       (for/lists (atoms maps) ([e es])
         (rco-atom e)))
     (map-to-lets maps (Prim op atoms))]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]))

(define (rco-atom e)
  (match e
    [(Var v) (values (Var v) '())]
    [(Int i) (values (Int i) '())]
    [(Prim op es)
     (define s (next-rco-symbol))
     (values (Var s)
       (list (cons s (Prim op (map rco-exp es)))))]
    [(Let x e body)
     (define s (next-rco-symbol))
     (values (Var s)
       (list (cons s (Let x (rco-exp e) (rco-exp body)))))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))

;; C0 tail & variables
(define (explicate-assign exp var tail)
  (match exp
    [(Var v)
     (values
       (Seq (Assign var exp) tail)
       '())]
    [(Int i)
     (values
       (Seq (Assign var exp) tail)
       '())]
    [(Prim op es)
     ;; pass remove-complex-opera* 之后，es 都是 atom
     (values
       (Seq (Assign var exp) tail)
       '())]
    [(Let var1 exp1 body)
     ;; (let var exp tail)
     ;; (let var (let var1 exp1 body) tail)
     ;;   tail1 -> var=body; tail
     ;;   (let var1 exp1 tail1)
     (define-values (tail1 vars1) (explicate-assign body var tail))
     (define-values (tail2 vars2) (explicate-assign exp1 (Var var1) tail1))
     (values tail2 (cons var1 (append vars1 vars2)))]))

;; C0 tail & let-bound variables
(define (explicate-tail e)
  (match e
    [(Var v) (values (Return (Var v)) '())]
    [(Int i) (values (Return (Int i)) '())]
    [(Prim op es) (values (Return (Prim op es)) '())]
    [(Let x e body)
     (define-values (body-tail body-vars) (explicate-tail body))
     (define-values (assign-tail assign-vars) (explicate-assign e (Var x) body-tail))
     (values assign-tail (cons x (append body-vars assign-vars)))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info e)
     (define-values (tail vars) (explicate-tail e))
     (CProgram (append info vars) `((start . ,tail)))]))

(define (atm e)
  (match e
    [(Int i) (Imm i)]
    [else e]))

(define (stmt e)
  (match e
    ;; exp ::= atm
    [(Assign v (Int i))
     `(,(Instr 'movq `(,(atm (Int i)) ,v)))]
    [(Assign (Var x) (Var x1))
     (if (eq? x x1) '()
         `(,(Instr 'movq `(,(Var x1) ,(Var x)))))]
    ;; exp ::= (Prim 'read ()
    [(Assign v (Prim 'read '()))
     `(,(Callq 'read_int 0)
       ,(Instr 'movq `(,(Reg 'rax) ,v)))]
    ;; -
    [(Assign v (Prim '- (list (Int i))))
     `(,(Instr 'movq `(,(atm (Int i)) ,v))
       ,(Instr 'negq `(,v)))]
    [(Assign (Var x) (Prim '- (list (Var x1))))
     (if (eq? x x1)
         `(,(Instr 'negq `(,(Var x))))
         `(,(Instr 'movq `(,(Var x1) ,(Var x)))
           ,(Instr 'negq `(,(Var x)))))]
    ;; +
    [(Assign v (Prim '+ (list (Int i1) (Int i2))))
     `(,(Instr 'movq `(,(atm (Int i1)) ,v))
       ,(Instr 'addq `(,(atm (Int i2)) ,v)))]
    [(Assign (Var x) (Prim '+ (list (Var x1) (Var x2))))
     (if (eq? x x1)
         (if (eq? x x2)
             `(,(Instr 'addq `(,(Var x) ,(Var x))))
             `(,(Instr 'addq `(,(Var x2) ,(Var x)))))
         (if (eq? x x2)
             `(,(Instr 'addq `(,(Var x1) ,(Var x))))
             `(,(Instr 'movq `(,(Var x1) ,(Var x)))
               ,(Instr 'addq `(,(Var x2) ,(Var x))))))]
    [(Assign (Var x) (Prim '+ (list (Int i1) (Var x1))))
     (if (eq? x x1)
         `(,(Instr 'addq `(,(Var x) ,(atm (Int i1)))))
         `(,(Instr 'movq `(,(Var x1) ,(Var x)))
           ,(Instr 'addq `(,(Var x) ,(atm (Int i1))))))]
    [(Assign (Var x) (Prim '+ (list (Var x1) (Int i1))))
     (if (eq? x x1)
         `(,(Instr 'addq `(,(Var x) ,(atm (Int i1)))))
         `(,(Instr 'movq `(,(Var x1) ,(Var x)))
           ,(Instr 'addq `(,(Var x) ,(atm (Int i1))))))]))

(define (tail e)
  (match e
    [(Return r)
     (append
       (match r
         [(Int i)
          `(,(Instr 'movq `(,(atm (Int i)) ,(Reg 'rax))))]
         [(Var x)
          `(,(Instr 'movq `(,(Var x) ,(Reg 'rax))))]
         [(Prim 'read '())
          `(,(Callq 'read_int 0))]
         [(Prim '- (list (Int i)))
          `(,(Instr 'movq `(,(atm (Int i)) ,(Reg 'rax)))
            ,(Instr 'negq `(,(Reg 'rax))))]
         [(Prim '- (list (Var x)))
          `(,(Instr 'movq `(,(Var x) ,(Reg 'rax)))
            ,(Instr 'negq `(,(Reg 'rax))))]
         [(Prim '+ (list (Int i1) (Int i2)))
          `(,(Instr 'movq `(,(atm (Int i1)) ,(Reg 'rax)))
            ,(Instr 'addq `(,(atm (Int i2)) ,(Reg 'rax))))]
         [(Prim '+ (list (Var x1) (Var x2)))
          `(,(Instr 'movq `(,(Var x1) ,(Reg 'rax)))
            ,(Instr 'addq `(,(Var x2) ,(Reg 'rax))))]
         [(Prim '+ (list (Var v) (Int i)))
          `(,(Instr 'movq `(,(Var v) ,(Reg 'rax)))
            ,(Instr 'addq `(,(atm (Int i)) ,(Reg 'rax))))]
         [(Prim '+ (list (Int i) (Var v)))
          `(,(Instr 'movq `(,(Var v) ,(Reg 'rax)))
            ,(Instr 'addq `(,(atm (Int i)) ,(Reg 'rax))))])
       `(,(Jmp 'conclusion)))]
    [(Seq s t)
     (append (stmt s) (tail t))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info `((start . ,t)))
     (X86Program info
       `((start . ,(Block '() (tail t)))))]))


(define (align-stack-size stack-size)
  (+ stack-size (remainder stack-size 16)))

(define (allocate-homes vars next-var-pos)
  (if (null? vars)
      '()
      (dict-set
        (allocate-homes (cdr vars) (- next-var-pos 8))
        (car vars)
        (Deref 'rbp next-var-pos))))

(define (assign-homes-instr instr homes)
  (match instr
    [(Imm i) (Imm i)]
    [(Reg r) (Reg r)]
    [(Deref r i) (Deref r i)]
    [(Var v) (dict-ref homes v)]
    [(Instr op es)
     (Instr op (map (lambda (e) (assign-homes-instr e homes)) es))]
    [else instr]))

(define (assign-homes-instrs instrs homes)
  (if (null? instrs)
      '()
      (cons
        (assign-homes-instr (car instrs) homes)
        (assign-homes-instrs (cdr instrs) homes))))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info `((start . ,(Block bi instrs))))
     (X86Program
       `(,(align-stack-size (* (length info) 8)))
       `((start . ,(Block bi (assign-homes-instrs instrs (allocate-homes info -8))))))]))

(define (patch-x86_0-bin-instr op arg1 arg2)
  (match arg1
    [(Deref r1 i1)
     (match arg2
       [(Deref r2 i2)
        `(,(Instr 'movq `(,(Deref r1 i1) ,(Reg 'rax)))
          ,(Instr op `(,(Reg 'rax) ,(Deref r2 i2))))]
       [else `(,(Instr op `(,arg1 ,arg2)))])]
    [else `(,(Instr op `(,arg1 ,arg2)))]))

(define (patch-x86_0-instr instr)
  (match instr
    [(Instr 'addq args)
     (patch-x86_0-bin-instr 'addq (car args) (cadr args))]
    [(Instr 'subq args)
     (patch-x86_0-bin-instr 'subq (car args) (cadr args))]
    [(Instr 'movq args)
     (patch-x86_0-bin-instr 'movq (car args) (cadr args))]
    [else `(,instr)]))

(define (patch-x86_0-instrs instrs)
  (if (null? instrs)
      '()
      (append
        (patch-x86_0-instr (car instrs))
        (patch-x86_0-instrs (cdr instrs)))))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info `((start . ,(Block bi instrs))))
     (X86Program info
       `((start . ,(Block bi (patch-x86_0-instrs instrs)))))]))

(define (print-arg arg)
  (match arg
    [(Imm i) (format "$~s" i)]
    [(Reg r) (format "%~s" r)]
    [(Deref r i) (format "~s(%~s)" i r)]))

(define (print-instr instr)
  (match instr
    [(Instr op args)
     (string-append
       (symbol->string op)
       " "
       (string-join (map print-arg args) ", "))]
    [(Callq label arity) (format "callq ~s" (if (eq? label 'read_int) '_read_int label))]
    [(Retq) "retq"]
    [(Jmp label) (format "jmp ~s" label)]))

(define (print-instrs instrs)
  (string-append "  " (string-join (map print-instr instrs) "\n  ")))

;; print-x86 : x86 -> string
(define (print-x86 p)
  (match p
    [(X86Program info `((start . ,(Block bi instrs))))
     (string-join
       `("start:"
         ,(print-instrs instrs)
         "\n"
         "  .global _main"
         "_main:\n"
         "  pushq %rbp"
         "  movq  %rsp, %rbp"
         "  subq  $16, %rsp"
         "  jmp   start"
         "conclusion:"
         "  addq  $16, %rsp"
         "  popq  %rbp"
         "  retq"
         "")
       "\n")]))

;; (printf
;;   (print-x86
;;     (patch-instructions
;;       (assign-homes
;;         (select-instructions
;;           (explicate-control
;;             (remove-complex-opera*
;;               (uniquify
;;                 (parse-program
;;                   '(program ()
;;                      (let ([x (read)])
;;                        (let ([y (read)])
;;                          (let ([z (read)])
;;                            (+ (+ x y) (- z)))))))))))))))

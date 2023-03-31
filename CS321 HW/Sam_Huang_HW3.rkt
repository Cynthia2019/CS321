#lang plai

(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))

(print-only-errors)

(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (name symbol?)
        (bound-expr FnWAE?)
        (body-expr FnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg-expr (listof FnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body FnWAE?)])

#|
<FunDef> = {deffun {<id> <id>*} <FnWAE>}
<FnWAE> = <num>
        | {+ <FnWAE> <FnWAE>}
        | {- <FnWAE> <FnWAE>}
        | {with {<id> <FnWAE>} <FnWAE>}
        | <id>
        | {<id> <FnWAE>*}
|#

;; parse-defn : s-expression -> FunDef?
(define (parse-defn s-exp)
  (case (first s-exp)
    [(deffun)
     (if (check-duplicates (rest (second s-exp)))
         (error 'parse-defn "bad syntax: ~a" s-exp)
         (fundef (first (second s-exp)) (rest (second s-exp)) (parse (third s-exp))))]
    [else
     (error 'parse-defn "not a valid deffun: ~a" s-exp)]))

;; parse : s-expression -> FnWAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "empty list is not a valid FnWAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got ~a" (first (second s-exp))))
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [else
            (unless (symbol? (first s-exp))
              (error 'parse "not a function name: ~a" (first s-exp)))
            (app (first s-exp) (map (lambda (x) (parse x)) (rest s-exp)))])]
        [else
         (error 'parse "not a valid FnWAE program: ~a" s-exp)]))

(define (check-pieces s-exp n-pieces who)
  (unless (= n-pieces (length s-exp))
    (error 'parse "expected ~a, got ~a" who s-exp)))


(test (parse `1)
      (num 1))
(test (parse `x)
      (id 'x))
(test (parse `{+ 1 2})
      (add (num 1) (num 2)))
(test (parse `{- 1 2})
      (sub (num 1) (num 2)))
(test (parse `{+ 1 {+ 2 3}})
      (add (num 1) (add (num 2) (num 3))))
(test (parse `{with {x 3} {+ x 2}})
      (with 'x (num 3) (add (id 'x) (num 2))))
(test (parse `{f 10 10})
      (app 'f (list (num 10) (num 10))))
(test (parse `{f 10 x})
      (app 'f (list (num 10) (id 'x))))
(test (parse `{f})
      (app 'f (list)))
(test (parse '{+ {f} {f}})
      (add (app 'f '()) (app 'f '())))
(test/exn (parse `{+ 1 2 3})
          "expected addition")
(test/exn (parse `{})
          "empty list")
(test (parse `{+ + +})
      (add (id '+) (id '+)))

(test (parse-defn '{deffun {g a b c} c})
      (fundef 'g (list 'a 'b 'c) (parse 'c)))
(test (parse-defn '{deffun {f x y} {+ x y}})
      (fundef 'f (list 'x 'y) (parse '{+ x y})))
(test (parse-defn '{deffun {f} 5})
      (fundef 'f '() (parse 5)))



;; ----------------------------------------------------------------------

;; interp : FnWAE? (listof FunDef?) -> number?
(define (interp an-fnwae fundefs)
  (type-case FnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs)
            (interp rhs fundefs))]
    [sub (lhs rhs)
         (- (interp lhs fundefs)
            (interp rhs fundefs))]
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr
                                 fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (interp (interp-subst (fundef-body the-fundef)
                               (fundef-param-name the-fundef)
                               (map (lambda(x) (interp x fundefs)) arg-expr)
                               )
                 fundefs)]))

(define (interp-subst body param-name arg-expr)
  (if (empty? arg-expr)
      (if (empty? param-name)
          body
          (error 'interp "wrong arity: ~a" body))
      (if (empty? param-name)
          (error 'interp "wrong arity: ~a" body)
          (interp-subst
           (subst body (first param-name) (first arg-expr))
           (rest param-name)
           (rest arg-expr)
           ))
      ))

(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? fun-name (fundef-fun-name (first fundefs)))
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))

;; subst : symbol? number? FnWAE? -> FnWAE?
(define (subst a-fnwae name value)
  (type-case FnWAE a-fnwae
    [num (n)
         a-fnwae]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnwae)]
    [app (fun-name arg-expr)
         (app fun-name (map (lambda(x) (subst x name value)) arg-expr))]))


(test (interp (parse `{f 10})
              (list (parse-defn '{deffun {f x} {- 20 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}})))
      -20)
(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)
(test (interp (parse '{f {g 3} 2})
              (list (parse-defn '{deffun {f a b} {+ a b}})
                    (parse-defn '{deffun {g a} 4})))
      6)
(test/exn (interp (parse '{f {g x}})
                  (list (parse-defn '{deffun {f a b} a})
                        (parse-defn '{deffun {g} c})))
          "free identifier")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b} a})
                        ))
          "free identifier")


#|
substitute 10 for x in {+ 1 x}
|#
(test (subst (add (num 1) (id 'x))
             'x
             10)
      (add (num 1) (num 10)))

(test/exn (interp (parse '{with {x y} 1})
                  (list))
          "free identifier")
(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")
(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp (parse '{f 1 11 12})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")
(test/exn (interp (parse '{f x y})
                  (list (parse-defn '{deffun {f a} c})))
          "free identifier")
(test/exn (interp (parse '{f 1 2 3})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")




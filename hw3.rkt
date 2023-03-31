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
;; parse-defn : s-exp -> FunDef
(define (parse-defn s-exp)
  (case (first s-exp)
    [(deffun)
     (if (check-duplicates (rest (second s-exp)))
         (error 'parse-defn "bad syntax: ~a" s-exp)
     (fundef (first (second s-exp)) (rest (second s-exp)) (parse (third s-exp))))
     ]
    [else
     (error "expected deffun, got ~a" (first s-exp))]))

;; parse : s-expression -> FnWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (num s-expr)]
        [(symbol? s-expr)
         (id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid F1WAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (add (parse (second s-expr))
                 (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (sub (parse (second s-expr))
                 (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (unless (symbol? (first (second s-expr)))
              (error 'parse "expected variable name, got ~a" (first (second s-expr))))
            (with (first (second s-expr))
                  (parse (second (second s-expr)))
                  (parse (third s-expr)))]
           [else
            (unless (symbol? (first s-expr))
              (error 'parse "expected function name, got ~a" (first s-expr)))
            (app (first s-expr)
                 (map (λ (exp) (parse exp)) (rest s-expr)))])]
        [else (error 'parse "expected FnWAE, got ~a" s-expr)]))

(define (check-pieces s-expr n-pieces who)
  (unless (= n-pieces (length s-expr))
    (error 'parse "expected ~a, got ~a" who s-expr)))

;test
(test (parse-defn '{deffun {f x y} {+ x y}}) (fundef 'f (list 'x 'y) (parse '{+ x y})))
(test (parse-defn '{deffun {g a b c} c})
      (fundef 'g (list 'a 'b 'c) (parse 'c)))
(test (parse-defn '{deffun {f} 5}) (fundef 'f '() (parse 5)))
(test (parse-defn '{deffun {twice y} {+ y y}}) (fundef 'twice (list 'y) (parse '(+ y y))))
(test (parse 5) (num 5))
(test (parse 'x) (id 'x))
(test (parse '{f 1 2}) (app 'f (list (num 1) (num 2))))
(test (parse '{with {a 4} {+ a a}}) (with 'a (num 4) (add (id 'a) (id 'a))))

(test/exn (parse-defn '(deffun (f x z y y z) x)) "bad syntax")


;; interp : FnWAE? (listof FunDef?) -> number?
(define (interp a-fnwae fundefs)
  (type-case FnWAE a-fnwae
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
                         (interp named-expr fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define body (fundef-body the-fundef))
         (define params (fundef-param-name the-fundef))
         (interp
          (subst-helper body params
                        (map (λ(exp) (interp exp fundefs))
                             arg-expr))
          fundefs)
         ]))
(define (subst-helper body param-names args)
  (if(empty? args)
     (if(empty? param-names)
        body
        (error 'interp "wrong arity: ~a" body))
     (if(empty? param-names)
        (error 'interp "wrong arity: ~a" body)
        (subst-helper (subst body (first param-names) (first args))
                      (rest param-names)
                      (rest args)))))
(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? name (fundef-fun-name (first fundefs)))
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))

;; subst : FnWAE? symbol? number? -> FnWAE?
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
         (app fun-name (map (λ(exp) (subst exp name value)) arg-expr))]))

;test interp
;; {+ 1 2} -> 3
(test (interp (parse `{+ 1 2}) '())
      3)
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (parse `{+ {+ 1 2} {- 3 4}}) '())
      2)
;; {f 1 2} -> 3
(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
;; {+ {f} {f}} -> 10
(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)
;; {f {twice {twice x}}} -> -140
(test (interp (parse `{f 10})
              (list (parse-defn '{deffun {f x} {+ 100 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}})))
      140)
;; {f {g 3} 2} -> 12
(test (interp (parse '{f {g 3} 2})
              (list (parse-defn '{deffun {f a b} {+ a b}})
                    (parse-defn '{deffun {g a} 10})))
      12)
;; {f 1 2 3 4 5 6}
(test (interp (parse '{f 1 2 3 4 5 6})
              (list (parse-defn '{deffun {f a b c d e f}
                                   {+ a {- b {+ c {- d e}}}}})))
      1)
;;test exceptions
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
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")
(test/exn (interp (parse '{f 3 4})
                  (list (parse-defn '{deffun {f a} 5}) (parse-defn '{deffun {f a b} {+ a b}})))
          "wrong arity")
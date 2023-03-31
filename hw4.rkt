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
       (arg-expr (listof FnWAE?))]
  [if0 (first-exp FnWAE?)
       (second-exp FnWAE?)
       (third-exp FnWAE?)])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body FnWAE?)])

(define (mtSub) (hash))
(define (aSub n v rest) (hash-set rest n v))

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
           (error 'parse "the empty list is not a valid FnWAE"))
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
           [(if0)
            (check-pieces s-expr 4 "if0")
            (if0 (parse (second s-expr))
                 (parse (third s-expr))
                 (parse (fourth s-expr)))]
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

(test (parse '{if0 0 1 2}) (if0 (num 0) (num 1) (num 2)))
(test (parse '{if0 {+ -1 1} 1 2}) (if0 (add (num -1) (num 1)) (num 1) (num 2)))

(test/exn (parse-defn '(deffun (f x z y y z) x)) "bad syntax")

;;interp-expr : FnWAE? (listof FunDef) -> number?
(define (interp-expr an-FnWAE fundefs)
  (interp an-FnWAE fundefs (mtSub)))

;; interp : FnWAE? (listof FunDef?) DefSub? -> number?
(define (interp an-FnWAE fundefs ds)
  (type-case FnWAE an-FnWAE
    [num (n) n]
    [add (l r) (+ (interp l fundefs ds) (interp r fundefs ds))]
    [sub (l r) (- (interp l fundefs ds) (interp r fundefs ds))]
    [id (name) (lookup name ds)]
    [with (name named-expr body)
          (interp body
                  fundefs
                  (aSub name
                        (interp named-expr fundefs ds)
                        ds))]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define param-name (fundef-param-name the-fundef))
         (define new-ds (aSub-helper param-name (map(λ(exp) (interp exp fundefs ds)) arg-expr)))
         (interp (fundef-body the-fundef)
                 fundefs
                 new-ds)]
    [if0 (first-exp second-exp third-exp)
         (if (equal? 0 (interp first-exp fundefs ds))
             (interp second-exp fundefs ds)
             (interp third-exp fundefs ds))]
    
    ))

(define (aSub-helper param-names args)
  (if(and (empty? args)
          (empty? param-names))
     (mtSub)
     (if(and (not (empty? args))
             (not (empty? param-names)))
        (aSub (first param-names)
              (first args)
              (aSub-helper (rest param-names) (rest args)))
        (error 'aSub-helper "wrong arity: ~a"
               param-names))))

;; lookup : symbol? DefSub? -> number?
(define (lookup name ds)
  (hash-ref ds name
            (lambda _
              (error 'interp "free identifier: ~a"
                     name))))

;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))


(define initial-def-sub (mtSub))


(define mult-and-neg-deffuns
  (list `{deffun {neg? x} {neg-helper x x}}
        `{deffun {neg-helper a b} {if0 a 1 {if0 b 0 {neg-helper (- a 1) (+ b 1)}}}}
        `{deffun {mult x y} {if0 {neg? x} {mult-neg x y 0} {mult-pos x y 0}}}
        `{deffun {mult-neg x y m} {if0 x m {if0 y m {mult-neg (+ x 1) y (- m y)}}}}
        `{deffun {mult-pos x y m} {if0 x m {if0 y m {mult-pos (- x 1) y (+ m y)}}}}
        ))


;;tests

;;

(test (interp-expr (parse '{mult -1 4}) (map parse-defn mult-and-neg-deffuns))
      -4)
(test (interp-expr (parse '{neg? 0})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      1)

(test (interp-expr (parse '{neg? -4})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      0)

(test (interp-expr (parse '{neg? -1})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      0)

(test (interp-expr (parse '{neg? 1})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      1)
(test (interp-expr (parse '{mult {- 0 1} {- 0 1}})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      1)
(test (interp-expr (parse '{mult -1 0})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      0)
(test (interp-expr (parse '{mult 100 20})
                   (map (λ(x) (parse-defn x)) mult-and-neg-deffuns))
      2000)
(test (interp-expr (parse '(mult -1 1))
                   (map parse-defn mult-and-neg-deffuns))
      -1)
(test (interp-expr (parse `(mult -1 1)) (map parse-defn mult-and-neg-deffuns))
      -1)
(test (interp-expr (parse `(mult -1 -1)) (map parse-defn mult-and-neg-deffuns))
      1)
(test (interp-expr (parse `(mult -1 2)) (map parse-defn mult-and-neg-deffuns))
      -2)
(test (interp-expr (parse `(mult -1 -2)) (map parse-defn mult-and-neg-deffuns))
      2)
(test (interp-expr (parse `(mult -2 1)) (map parse-defn mult-and-neg-deffuns))
      -2)
(test (interp-expr (parse `(mult -2 -1)) (map parse-defn mult-and-neg-deffuns))
      2)
(test (interp-expr (parse `(mult -2 2)) (map parse-defn mult-and-neg-deffuns))
      -4)
(test (interp-expr (parse `(mult -2 -2)) (map parse-defn mult-and-neg-deffuns))
      4)
;; 5 -> 5
(test (interp (parse `5) '() initial-def-sub)
      5)
;; {+ 1 2} -> 3
(test (interp (parse `{+ 1 2}) '() initial-def-sub)
      3)
;; {- 3 4} -> -1
(test (interp (parse `{- 3 4}) '() initial-def-sub)
      -1)
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (parse `{+ {+ 1 2} {- 3 4}}) '() initial-def-sub)
      2)
;; {f 1 2} -> 3
(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}}))
              initial-def-sub)
      3)

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp-expr (parse `{with {x {+ 1 2}}
                                 {+ x x}})
                   '())
      6)

#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {y {- 4 3}}
         {+ y y}}}
|#
(test (interp-expr (parse `{+ {with {x {+ 1 2}}
                                    {+ x x}}
                              {with {y {- 4 3}}
                                    {+ y y}}})
                   '())
      8)

;; {+ {f} {f}} -> 10
(test (interp-expr (parse '{+ {f} {f}})
                   (list (parse-defn '{deffun {f} 5})))
      10)

;; {f {twice {twice x}}} -> -140
(test (interp-expr (parse `{f 10})
                   (list (parse-defn '{deffun {f x} {+ 100 {twice {twice x}}}})
                         (parse-defn '{deffun {twice y} {+ y y}})))
      140)
;; {f {g 3} 2} -> 12
(test (interp-expr (parse '{f {g 3} 2})
                   (list (parse-defn '{deffun {f a b} {+ a b}})
                         (parse-defn '{deffun {g a} 10})))
      12)
;; {f 1 2 3 4 5 6}
(test (interp-expr (parse '{f 1 2 3 4 5 6})
                   (list (parse-defn '{deffun {f a b c d e f}
                                        {+ a {- b {+ c {- d e}}}}})))
      1)

(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)

;;test exceptions
(test/exn (interp (parse '{with {x y} 1})
                  (list)
                  initial-def-sub)
          "free identifier")
(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}}))
                  initial-def-sub)
          "bad syntax")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c}))
                  initial-def-sub)
          "undefined function")
(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}}))
                  initial-def-sub)
          "wrong arity")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c}))
                  initial-def-sub)
          "free identifier")
(test/exn (interp (parse '{f 3 4})
                  (list (parse-defn '{deffun {f a} 5}) (parse-defn '{deffun {f a b} {+ a b}}))
                  initial-def-sub)
          "wrong arity")
(test/exn (parse-defn '(deffun (f x z y y z) x)) "bad syntax")


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

#|
<FunDef> = {deffun {<id> <id>*} <FnWAE>}
<FnWAE> = <num>
        | {+ <FnWAE> <FnWAE>}
        | {- <FnWAE> <FnWAE>}
        | {with {<id> <FnWAE>} <FnWAE>}
        | <id>
        | {<id> <FnWAE>*}
        | {if0 <FnWAE> <FnWAE> <FnWAE>}
|#

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
  [if0 (condition FnWAE?)
       (ifcase FnWAE?)
       (elsecase FnWAE?)])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body FnWAE?)])

(define (mtSub) (hash))
(define (aSub name val rest) (hash-set rest name val))
(define (lookup name ds)
  (hash-ref ds name
            (lambda () (error 'interp "free identifier: ~a" name))))

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
           [(if0)
            (check-pieces s-exp 4 "if0")
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [else
            (unless (symbol? (first s-exp))
              (error 'parse "not a function name: ~a" (first s-exp)))
            (app (first s-exp) (map (lambda (x) (parse x)) (rest s-exp)))])]
        [else
         (error 'parse "not a valid FnWAE program: ~a" s-exp)]))

(define (check-pieces s-exp n-pieces who)
  (unless (= n-pieces (length s-exp))
    (error 'parse "expected ~a, got ~a" who s-exp)))

;; ----------------------------------------------------------------------

;; interp : FnWAE? (listof FunDef?) DefSub? -> number?
(define (interp an-fnwae fundefs ds)
  (type-case FnWAE an-fnwae
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
         (type-case FunDef the-fundef
           [fundef (fun-name param-name body)
                   (interp body
                           fundefs
                           (fundef-aSub-helper param-name
                                               (map (lambda(x) (interp x fundefs ds)) arg-expr)))])]
    [if0 (condition ifcase elcase)
         (if (equal? 0 (interp condition fundefs ds))
             (interp ifcase fundefs ds)
             (interp elcase fundefs ds))]))

(define (fundef-aSub-helper param-name arg-lst)
  (cond [(and (empty? param-name) (empty? arg-lst))
         (mtSub)]
        [(and (not (empty? param-name)) (not (empty? arg-lst)))
         (aSub (first param-name)
               (first arg-lst)
               (fundef-aSub-helper (rest param-name) (rest arg-lst)))]
        [else (error 'interp "wrong arity: ~a, ~a" param-name arg-lst)]))


;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))

;; interp-expr : FnWAE? (listof FunDef?) -> number?
(define (interp-expr an-fnwae fundefs)
  (interp an-fnwae fundefs (mtSub)))


;; ----------------------------------------------------------------------
;; tests from last time, updated


(define mult-and-neg-deffuns
    (list `{deffun {neg? x} {neg-helper x x}}
          `{deffun {mult x y} {if0 {neg? x} {mult-helper-neg x y 0} {mult-helper-pos x y 0}}}
          `{deffun {neg-helper a b} {if0 a 1 {if0 b 0 {neg-helper {- a 1} {+ b 1}}}}}
          `{deffun {mult-helper-pos x y m} {if0 x m {if0 y m {mult-helper-pos {- x 1} y {+ m y}}}}}
          `{deffun {mult-helper-neg x y m} {if0 x m {if0 y m {mult-helper-neg {+ x 1} y {- m y}}}}}
          ; other deffuns okay, too, for your helpers
))


;; ----------------------------------------------------------------------
;; tests from last time, updated

(define initial-def-sub (mtSub))

(test (interp-expr (parse '{neg? 0})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      1)
(test (interp-expr (parse '{neg? {- 0 0}})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      1)
(test (interp-expr (parse '{neg? {- 1 3}})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      0)
(test (interp-expr (parse '{neg? {- 1 {- 0 3}}})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      1)
(test (interp-expr (parse '{mult 2 3})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      6)
(test (interp-expr (parse '{mult 0 3})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      0)
(test (interp-expr (parse '{mult 2 0})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      0)
(test (interp-expr (parse '{mult {- 0 2} 3})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      (- 0 6))
(test (interp-expr (parse '{mult {- 0 2} {- 0 3}})
                   (map (lambda(x) (parse-defn x)) mult-and-neg-deffuns))
      6)

(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)

(test/exn (interp (parse `{with {y 2} {f 10}})
                  (list (parse-defn '{deffun {f x} {+ x y}}))
                  initial-def-sub)
          "free identifier")
(test/exn (interp (parse `{f 10})
                  (list (parse-defn '{deffun {f x} {+ x y}}))
                  initial-def-sub)
          "free identifier")
(test/exn (interp (parse `{with {y 2} {f y}})
                  (list (parse-defn '{deffun {f x} {+ x y}}))
                  initial-def-sub)
          "free identifier")

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

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {+ x x}})
              '()
              initial-def-sub)
      6)
#|
x
|#
(test/exn (interp (parse `x) '() initial-def-sub)
          "free identifier")
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {x {- 4 3}}
         {+ x x}}}
|#
(test (interp (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {x {- 4 3}}
                               {+ x x}}})
              '()
              initial-def-sub)
      8)
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {y {- 4 3}}
         {+ y y}}}
|#
(test (interp (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {y {- 4 3}}
                               {+ y y}}})
              '()
              initial-def-sub)
      8)
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}})
              '()
              initial-def-sub)
      2)
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}})
              '()
              initial-def-sub)
      6)

(test/exn (interp (parse `{f 10})
                  (list)
                  initial-def-sub)
          "undefined function")
(test (interp (parse `{f 10})
              (list (parse-defn '{deffun {f x} {- 20 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}}))
              initial-def-sub)
      -20)
(test (interp (parse `{f 10})
              (list (parse-defn '{deffun {f x} {- 10 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}}))
              initial-def-sub)
      -30)



(test (interp-expr (parse `{f 10})
              (list (parse-defn '{deffun {f x} {- 20 {twice {twice x}}}})
                    (parse-defn '{deffun {twice y} {+ y y}})))
      -20)
(test (interp-expr (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test (interp-expr (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)
(test (interp-expr (parse '{f {g 3} 2})
                  (list (parse-defn '{deffun {f a b} {+ a b}})
                        (parse-defn '{deffun {g a} 4})))
          6)
(test/exn (interp-expr (parse '{f {g x}})
                  (list (parse-defn '{deffun {f a b} a})
                        (parse-defn '{deffun {g} c})))
          "free identifier")
(test/exn (interp-expr (parse '{f x})
                  (list (parse-defn '{deffun {f a b} a})
                        ))
          "free identifier")


(test/exn (interp-expr (parse '{with {x y} 1})
                  (list))
          "free identifier")
(test/exn (interp-expr (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")
(test/exn (interp-expr (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")
(test/exn (interp-expr (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp-expr (parse '{f 1 11 12})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp-expr (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")
(test/exn (interp-expr (parse '{f x y})
                  (list (parse-defn '{deffun {f a} c})))
          "free identifier")









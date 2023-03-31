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
FAE ::= {+ <FAE> <FAE>}
      | {- FAE FAE}
      | <num>
      | <id>
      | {if0 <FAE> <FAE> <FAE>}
      | {fun {<id>} <FAE>}
      | {<FAE> <FAE>} ;; application expressions
|#
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])
#|
FWAE ::= {+ <FWAE> <FWAE>}
       | {- <FWAE> <FWAE>}
       | <num>
       | {with {<id> <FWAE>} <FWAE>}
       | <id>
       | {if0 <FWAE> <FWAE> <FWAE>}
       | {fun {<id>*} <FWAE>}
       | {<FWAE> <FWAE>*} ;; application expressions
|#
(define-type FWAE
  [W-num (n number?)]
  [W-add (lhs FWAE?)
         (rhs FWAE?)]
  [W-sub (lhs FWAE?)
         (rhs FWAE?)]
  [W-with (name symbol?)
          (named-expr FWAE?)
          (body FWAE?)]
  [W-id (name symbol?)]
  [W-if0 (tst FWAE?)
         (thn FWAE?)
         (els FWAE?)]
  [W-fun (params (listof symbol?))
         (body FWAE?)]
  [W-app (fun-expr FWAE?)
         (arg-exprs (listof FWAE?))])

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub (name  symbol?)
        (value FAE-Value?)
        (rest  DefSub?)])

;; ----------------------------------------------------------------------

;; parse : s-expr -> FWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (W-num s-expr)]
        [(symbol? s-expr)
         (W-id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid FWAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "+")
            (W-add (parse (second s-expr))
                   (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "-")
            (W-sub (parse (second s-expr))
                   (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (W-with (first (second s-expr))
                    (parse (second (second s-expr)))
                    (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "if0")
            (W-if0 (parse (second s-expr))
                   (parse (third s-expr))
                   (parse (fourth s-expr)))]
           [(fun)
            (check-pieces s-expr 3 "fun")
            (W-fun (second s-expr)
                   (parse (third s-expr)))]
           [else
            (W-app (parse (first s-expr)) (map (λ (x) (parse x)) (rest s-expr)))])]
        [else
         (error 'parse "expected FWAE, got ~a" s-expr)]))

(define (check-pieces s-expr n who)
  (unless (and (list? s-expr) (= (length s-expr) n))
    (error 'parse "expected ~a, got ~a" who s-expr)))

;;test check parse 
(test (parse `{fun {a b} {+ a b}})
      (W-fun '(a b) (W-add (W-id 'a) (W-id 'b))))
(test (parse 5)
      (W-num 5))
(test (parse `{if0 {+ -1 1} 1 2})
      (W-if0 (W-add (W-num -1) (W-num 1)) (W-num 1) (W-num 2)))
;; ----------------------------------------------------------------------------

;; compile : FWAE? -> FAE?
(define (compile an-fwae)
  (type-case FWAE an-fwae
    [W-num (n) (num n)]
    [W-id (name) (id name)]
    [W-add (l r) (try-constant-fold (add (compile l) (compile r)))]
    [W-sub (l r) (try-constant-fold (sub (compile l) (compile r)))]
    [W-fun (param-name-lst body)
           (unless (not (empty? param-name-lst))
             (error 'compile "nullary function ~a ~a" param-name-lst body))
           (fun (first param-name-lst)
                (if (empty? (rest param-name-lst))
                    (compile body)
                    (compile (W-fun (rest param-name-lst) body))))]
    [W-if0 (condition if_true els)
           (if0 (compile condition) (compile if_true) (compile els))]
    [W-with (name named-expr body)
            (app (fun name (compile body))
                 (compile named-expr))]
    [W-app (fun-expr arg-expr)
           (unless (not (empty? arg-expr))
             (error 'compile "nullary application ~a ~a" fun-expr arg-expr))
           (app-compile-helper fun-expr (reverse arg-expr))]))

(define (app-compile-helper fun-expr arg-expr)
  (if (empty? (rest arg-expr))
      (app (compile fun-expr) (compile (first arg-expr)))
      (app (app-compile-helper fun-expr (rest arg-expr)) (compile (first arg-expr)))))

;; try-constant-fold : FAE? -> FAE?
(define (try-constant-fold an-fae)
  (type-case FAE an-fae
    [add (l r) (if (and (num? l) (num? r))
                   (num (+ (num-n l) (num-n r)))
                   an-fae)]
    [sub (l r) (if (and (num? l) (num? r))
                   (num (- (num-n l) (num-n r)))
                   an-fae)]
    [else an-fae]))

;;test check compile
(test (compile (parse `{if0 {+ -1 1} 1 2}))
      (if0 (num 0) (num 1) (num 2)))
(test (compile (parse `{{fun {a b} {+ a b}} 1 2}))
      (app (app (fun 'a (fun 'b (add (id 'a) (id 'b)))) (num 1)) (num 2)))
(test (compile (parse `{+ 1 2}))
      (num 3))
(test (compile (parse `{with {x 3} {+ x 2}}))
      (app (fun 'x (add (id 'x) (num 2)))
           (num 3)))
;; ----------------------------------------------------------------------------

;; interp : FAE? DefSub? -> FWAE-Value?
(define (interp an-fae ds) ; NEW
  (type-case FAE an-fae
    [num (n)   (numV n)]
    [add (l r) (numop + l r ds)]
    [sub (l r) (numop - l r ds)]
    [id (name)
        (lookup name ds)]
    [fun (param-name body)
         (closureV param-name
                   body
                   ds)]
    [if0 (con then else)
         (define fae-val (interp con ds))
         (type-case FAE-Value fae-val
           [numV (n) (if(equal? 0 n)
                        (interp then ds)
                        (interp else ds))]
           [closureV (param-name body if0-ds)
                     (interp else ds)])]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (define arg-val (interp arg-expr ds))
         (unless (closureV? fun-val)
           (error 'interp "expected function, got ~a" fun-val))
         (define body (closureV-body fun-val))
         (interp body (aSub (closureV-param-name fun-val)
                            arg-val
                            (closureV-ds fun-val)))]))

(define (numop op l r ds)
  (define l-val (interp l ds))
  (define r-val (interp r ds))
  (unless (numV? l-val)
    (error 'interp "expected number, got ~a" l-val))
  (unless (numV? r-val)
    (error 'interp "expected number, got ~a" r-val))
  (numV (op (numV-n l-val) (numV-n r-val))))

;; lookup : symbol? DefSub? -> FAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; interp-expr : FAE -> number or ’function
(define (interp-expr an-fnwae)
  (define output (interp an-fnwae (mtSub)))
  (type-case FAE-Value output
    [numV (n) n]
    [closureV (param-name body local-ds) 'function]))

;; ----------------------------------------------------------------------

(define factorial `{with {mk-rec {fun {body-proc}
                                      {with {fX {fun {fX}
                                                       {with {f {fun {x} {{fX fX} x}}}
                                                             {body-proc f}}}}
                                            {fX fX}}}}
                         {with {neg-helper {mk-rec {fun {neg-helper} {fun {a b} {if0 a 1 {if0 b 0 {neg-helper {- a 1} {+ b 1}}}}}}}}
                               {with {neg? {fun {x} {neg-helper x x}}}
                                     {with {mult-helper-pos {mk-rec {fun {mult-helper-pos} {fun {x y m} {if0 x m {if0 y m {mult-helper-pos {- x 1} y {+ m y}}}}}}}}
                                           {with {mult-helper-neg {mk-rec {fun {mult-helper-neg} {fun {x y m} {if0 x m {if0 y m {mult-helper-neg {+ x 1} y {- m y}}}}}}}}
                                                 {with {mult {fun {x y} {if0 {neg? x} {mult-helper-neg x y 0} {mult-helper-pos x y 0}}}}
                                                       {fun {n}
                                                            {with {fac {mk-rec
                                                                        {fun {fac}
                                                                             {fun {z}
                                                                                  {if0 z 1 {mult z {fac {- z 1}}}}}}}}
                                                                  {fac n}}}}}}}}})

(define prime? `{with {mk-rec {fun {to-make-recursive}
                                   {with {facX {fun {facX}
                                                    {with {fac {fun {n} {{facX facX} n}}}
                                                          {to-make-recursive fac}}}}
                                         {facX facX}}}}
                      {with {neg-helper {mk-rec {fun {neg-helper} {fun {a b} {if0 a 1 {if0 b 0 {neg-helper {- a 1} {+ b 1}}}}}}}}
                            {with {neg? {fun {x} {neg-helper x x}}}
                                  {with {mult-helper-pos {mk-rec {fun {mult-helper-pos} {fun {x y m} {if0 x m {if0 y m {mult-helper-pos {- x 1} y {+ m y}}}}}}}}
                                        {with {mult-helper-neg {mk-rec {fun {mult-helper-neg} {fun {x y m} {if0 x m {if0 y m {mult-helper-neg {+ x 1} y {- m y}}}}}}}}
                                              {with {mult {fun {x y} {if0 {neg? x} {mult-helper-neg x y 0} {mult-helper-pos x y 0}}}}
                                                    {fun {n}
                                                         {with {check {mk-rec
                                                                       {fun {check}
                                                                            {fun {n i j}
                                                                                 {if0 {neg? {- n {mult i j}}}
                                                                                      {if0 {neg? {- n {mult i i}}}
                                                                                           0
                                                                                           {check n {+ i 1} 2}}
                                                                                      {if0 {- n {mult i j}}
                                                                                           1
                                                                                           {check n i {+ j 1}}}}}}}}
                                                               {check n 2 2}}}}}}}}})

;; ----------------------------------------------------------------------

(test (interp-expr (compile (parse `{,factorial 5})))
      120)
(test (interp-expr (compile (parse `{,factorial 0})))
      1)
(test (interp-expr (compile (parse `{,prime? 5})))
      0)
(test (interp-expr (compile (parse `{,prime? 20})))
      1)
;; ----------------------------------------------------------------------
     
(test/exn (compile (parse `{fun {} 10}))
          "nullary function")
(test/exn (compile (parse '{f}))
          "nullary application")

;; ----------------------------------------------------------------------------

(define initial-def-sub (mtSub))

(test/exn (interp-expr (compile (parse `{+ {fun {x} x}
                                           {1 2}})))
          "expected function")

(test (interp-expr (num 10)) 10)

(test (interp-expr (fun 'x (id 'x))) 'function)

(test (interp-expr (compile (parse `{if0 {fun {x} x} 10 20})))
      20)

(test (interp (compile (parse `{fun {x} {+ x 1}}))
              initial-def-sub)
      (closureV 'x (add (id 'x) (num 1))
                (mtSub)))

(test (interp (compile (parse `{with {y 10}
                                     {fun {x} {+ y x}}}))
              initial-def-sub)
      (closureV 'x (add (id 'y) (id 'x))
                (aSub 'y (numV 10) (mtSub))))

(test (interp (compile (parse `{{with {y 10}
                                      {fun {x} {+ y x}}}
                                5}))
              initial-def-sub)
      (numV 15))

(test/exn (interp (compile (parse `{with {z {fun {x} {+ x y}}}
                                         {with {y 10}
                                               {z y}}}))
                  initial-def-sub)
          "free identifier")

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {+ x x}}))
              initial-def-sub)
      (numV 6))
#|
x
|#
(test/exn (interp (compile (parse `x))
                  initial-def-sub)
          "free identifier")
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {x {- 4 3}}
         {+ x x}}}
|#
(test (interp (compile (parse `{+ {with {x {+ 1 2}}
                                        {+ x x}}
                                  {with {x {- 4 3}}
                                        {+ x x}}}))
              initial-def-sub)
      (numV 8))
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {with {x {- 4 3}}
                                           {+ x x}}}))
              initial-def-sub)
      (numV 2))

;; ----------

(test (interp (compile (parse `{with {f {fun {x} {+ x 1}}}
                                     {f 13}}))
              initial-def-sub)
      (numV 14))
(test (interp (compile (parse `{{fun {x} {+ x 1}} 13}))
              initial-def-sub)
      (numV 14))
(test (interp (compile (parse `{fun {x} {+ x 1}}))
              initial-def-sub)
      (closureV 'x (compile (parse `{+ x 1})) (mtSub)))
(test/exn (interp (compile (parse `{1 2}))
                  initial-def-sub)
          "expected function")
(test/exn (interp (compile (parse `{+ 1 {fun {n} n}}))
                  initial-def-sub)
          "expected number")














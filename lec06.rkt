#lang plai

(print-only-errors)

(define-type FWAE ; ugh, name clashes
  [W-num  (n number?)]
  [W-add  (lhs FWAE?)
          (rhs FWAE?)]
  [W-sub  (lhs FWAE?)
          (rhs FWAE?)]
  [W-with (name symbol?)
          (named-expr FWAE?)
          (body FWAE?)]
  [W-id   (name symbol?)]
  [W-fun  (param-name symbol?)
          (body FWAE?)]
  [W-app  (fun-expr FWAE?)
          (arg-expr FWAE?)])

(define-type FAE
  [num  (n number?)]
  [add  (lhs FAE?)
        (rhs FAE?)]
  [sub  (lhs FAE?)
        (rhs FAE?)]
  [id   (name symbol?)]
  [fun  (param-name symbol?)
        (body FAE?)]
  [app  (fun-expr FAE?)
        (arg-expr FAE?)])

(define-type FAE-Value
  [numV (n number?)]
  [funV (param-name symbol?)
        (body FAE?)])

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
           [(fun)
            (check-pieces s-expr 3 "fun")
            (check-pieces (second s-expr) 1 "parameter list")
            (W-fun (first (second s-expr))
                   (parse (third s-expr)))]
           [else
            (check-pieces s-expr 2 "app")
            (W-app (parse (first s-expr)) (parse (second s-expr)))])]
        [else
         (error 'parse "expected FWAE, got ~a" s-expr)]))

(define (check-pieces s-expr n who)
  (unless (and (list? s-expr) (= (length s-expr) n))
    (error 'parse "expected ~a, got ~a" who s-expr)))

;; ----------------------------------------------------------------------------

;; compile : FWAE? -> FAE?
(define (compile an-fwae)
  (type-case FWAE an-fwae
    [W-num (n) (num n)]
    [W-add (l r) (try-constant-fold
                  (add (compile l) (compile r)))]
    [W-sub (l r) (try-constant-fold
                  (sub (compile l) (compile r)))]
    [W-id (name) (id name)]
    [W-with (name named-expr body)
            (app (fun name (compile body))
                 (compile named-expr))]
    [W-fun (param-name body)
           (fun param-name (compile body))]
    [W-app (fun-expr arg-expr)
           (app (compile fun-expr) (compile arg-expr))]))

;; try-constant-fold : FAE? -> FAE?
(define (try-constant-fold e)
  (type-case FAE e
    [add (l r) (do-constant-fold + l r e)]
    [sub (l r) (do-constant-fold - l r e)]
    [else
     (error 'compile
            "internal error: cannot constant fold this")]))

(define (do-constant-fold op l r e)
  (if (and (num? l)
           (num? r))
      (num (op (num-n l)
               (num-n r)))
      e))

(test (compile (W-add (W-num 1) (W-num 2)))
      (num 3))
(test (compile (parse `{+ 1 2}))
      (num 3))
(test (compile (parse `{with {x 3} {+ x 2}}))
      (app (fun 'x (add (id 'x) (num 2)))
           (num 3)))
(test (compile (parse `{+ 2 {with {x 3} {+ x 2}}}))
      (add (num 2)
           (app (fun 'x (add (id 'x) (num 2)))
                (num 3))))
(test (compile (parse `{with {x 3} {with {y 2} {+ x y}}}))
      (app (fun 'x (app (fun 'y (add (id 'x) (id 'y)))
                        (num 2)))
           (num 3)))
(test (compile
        (parse `{with {f {fun {x} {+ x 1}}}
                      {f 3}}))
      (app (fun 'f (app (id 'f) (num 3)))
           (fun 'x (add (id 'x) (num 1)))))

;; for later
(test (compile (parse `{+ 2 2}))
      (num 4))
(test (compile (parse `{+ 2 {- 3 4}}))
      (num 1))
(test (compile (parse `{+ 2 {+ 3 x}}))
      (add (num 2) (add (num 3) (id 'x))))
(test (compile (parse `{+ x {+ 2 3}}))
      (add (id 'x) (num 5)))
(test (compile (parse `{f {+ 2 3}}))
      (app (id 'f) (num 5)))

;; interp : FAE? -> FAE-Value?
(define (interp an-fae)
  (type-case FAE an-fae
    [num (n) (numV n)]
    [id (name) (error 'interp "free identifier")]
    [fun (param-name body) (funV param-name body)]
    [add (l r) (numop + l r)]
    [sub (l r) (numop - l r)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr))
         (unless (funV? fun-val)
           (error 'interp "expected function, got ~a" fun-val))
         (define body (funV-body fun-val))
         (define param-name (funV-param-name fun-val))
         (interp (subst body
                        param-name
                        (interp arg-expr)))]))

(define (numop op l r)
  (define l-val (interp l))
  (unless (numV? l-val)
    (error 'interp "expected number, got ~a" l-val))
  (define r-val (interp r))
  (unless (numV? r-val)
    (error 'interp "expected number, got ~a" r-val))
  (numV (op (numV-n l-val) (numV-n r-val))))

;; subst : FAE? symbol? FAE-Value? -> FAE?
(define (subst expr name value)
  (type-case FAE expr
    [num (n) expr]
    [add (l r) (add (subst l name value)
                    (subst r name value))]
    [sub (l r) (sub (subst l name value)
                    (subst r name value))]
    [id (name2)
        ;; getting an FAE-Value, need to produce an FAE...
        (if (equal? name name2)
            (type-case FAE-Value value
              [numV (n) (num n)]
              [funV (p b) (fun p b)])
            expr)]
    [app (fun-expr arg-expr)
         (app (subst fun-expr name value)
              (subst arg-expr name value))]
    [fun (param-name body)
         (fun param-name
              (if (equal? name param-name)
                  body
                  (subst body name value)))]))

;; ----------------------------------------------------------------------------

;; 5 -> 5
(test (interp (compile (parse `5)))
      (numV 5))
;; {+ 1 2} -> 3
(test (interp (compile (parse `{+ 1 2})))
      (numV 3))
;; {- 3 4} -> -1
(test (interp (compile (parse `{- 3 4})))
      (numV -1))
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (compile (parse `{+ {+ 1 2} {- 3 4}})))
      (numV 2))

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {+ x x}})))
      (numV 6))

(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {- x x}})))
      (numV 0))

#|
x
|#
(test/exn (interp (compile (parse `x)))
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
                                        {+ x x}}})))
      (numV 8))
#|
{+ {with {x {+ 1 2}}
         {+ x x}}
   {with {y {- 4 3}}
         {+ y y}}}
|#
(test (interp (compile (parse `{+ {with {x {+ 1 2}}
                                        {+ x x}}
                                  {with {y {- 4 3}}
                                        {+ y y}}})))
      (numV 8))
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {with {x {- 4 3}}
                                           {+ x x}}})))
      (numV 2))
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (compile (parse `{with {x {+ 1 2}}
                                     {with {y {- 4 3}}
                                           {+ x x}}})))
      (numV 6))

;; ----------

(test (interp
       (compile
        (parse `{with {f {fun {x} {+ x 1}}}
                      {f 3}})))
      (numV 4))
(test (interp (compile (parse `{{fun {x} {+ x 1}} 3})))
      (numV 4))
(test (interp (compile (parse `{fun {x} {+ x 1}})))
      (funV 'x (compile (parse `{+ x 1}))))
(test/exn (interp (compile (parse `{1 2})))
          "expected function")
(test/exn (interp (compile (parse `{+ 1 {fun {x} x}})))
          "expected number")
(test (interp (compile (parse `{with {f {with {x 3}
                                              {fun {y} {+ x y}}}}
                                     {f 2}})))
      (numV 5))

(test/exn (interp (compile (parse `{with {z {fun {x} {+ x y}}}
                                         {with {y 10}
                                               {z 3}}})))
          "free identifier")
;; A: 13 -- wrong
;; B: free identifier -- right

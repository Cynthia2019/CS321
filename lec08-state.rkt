#lang plai
(print-only-errors)

(define-type BFAE
  [num (n number?)]
  [add (lhs BFAE?)
       (rhs BFAE?)]
  [sub (lhs BFAE?)
       (rhs BFAE?)]
  [id (name symbol?)]
  [fun (param-name symbol?)
       (body BFAE?)]
  [app (fun-expr BFAE?)
       (arg-expr BFAE?)]
  [newbox  (init-expr BFAE?)]
  [openbox (box-expr BFAE?)]
  [setbox  (box-expr BFAE?)
           (new-expr BFAE?)]
  [seqn (expr1 BFAE?)
        (expr2 BFAE?)])

(define-type BFAE-Value
  [numV     (n number?)]
  [closureV (param-name symbol?)
            (body BFAE?)
            (ds DefSub?)]
  [boxV     (container (box/c BFAE-Value?))])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value BFAE-Value?)
         (rest DefSub?)])

;; ----------------------------------------------------------------------

;; parse : s-expression -> BFAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid BFAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(with) ; in lieu of a compiler
            (check-pieces s-exp "with" 3)
            (check-pieces (second s-exp) "with binding pair" 2)
            (app (fun (first (second s-exp)) (parse (third s-exp)))
                 (parse (second (second s-exp))))]
           [(newbox)
            (check-pieces s-exp "newbox" 2)
            (newbox (parse (second s-exp)))]
           [(setbox)
            (check-pieces s-exp "setbox" 3)
            (setbox (parse (second s-exp))
                    (parse (third s-exp)))]
           [(openbox)
            (check-pieces s-exp "openbox" 2)
            (openbox (parse (second s-exp)))]
           [(seqn)
            (check-pieces s-exp "seqn" 3)
            (seqn (parse (second s-exp))
                  (parse (third s-exp)))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "wat")]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;; ----------------------------------------------------------------------

;; interp : BFAE? DefSub? -> BFAE-Value?
(define (interp a-bfae ds)
  (type-case BFAE a-bfae
    [num (n)   (numV n)]
    [add (l r) (numop + l r ds)]
    [sub (l r) (numop - l r ds)]
    [id (name) (lookup name ds)]
    [fun (param-name body) (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (define arg-val (interp arg-expr ds))
         (type-case BFAE-Value fun-val
           [closureV (param-name body closed-ds)
                     (interp body
                             (aSub param-name
                                   arg-val
                                   closed-ds))]
           [else (error 'interp "expected function")])]
    [newbox (init-expr)
            (boxV (box (interp init-expr ds)))]
    [openbox (box-expr)
             (define box-val (interp box-expr ds))
             (unless (boxV? box-val)
               (error 'interp "expected box"))
             (unbox (boxV-container box-val))]
    [setbox (box-expr new-expr)
            (define box-val (interp box-expr ds))
            (unless (boxV? box-val)
              (error 'interp "expected box"))
            (define new-val (interp new-expr ds))
            (set-box! (boxV-container box-val)
                      new-val)
            box-val]
    [seqn (expr1 expr2)
          (interp expr1 ds)
          (interp expr2 ds)]))

;; numop : (number? number? -> number?) BFAE? BFAE? DefSub? -> BFAE-Value?
(define (numop op l r ds)
  (define l-val (interp l ds))
  (unless (numV? l-val)
    (error 'interp "expected number, got ~a" l-val))
  (define r-val (interp r ds))
  (unless (numV? r-val)
    (error 'interp "expected number, got ~a" r-val))
  (numV (op (numV-n l-val) (numV-n r-val))))

;; lookup : symbol? DefSub? -> BFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

(define initial-def-sub (mtSub))

(test (interp (parse `{newbox 10})
              initial-def-sub)
      (boxV (box (numV 10))))
(test (interp (parse `{openbox {newbox 10}})
              initial-def-sub)
      (numV 10))
(test (interp (parse `{openbox {newbox {newbox 5}}})
              initial-def-sub)
      (boxV (box (numV 5))))
(test (interp (parse `{openbox {openbox {newbox {newbox 5}}}})
              initial-def-sub)
      (numV 5))
(test/exn (interp (parse `{openbox 5})
                  initial-def-sub)
          "expected box")

(test (interp (parse `{seqn {openbox {newbox 10}}
                            {+ 2 1}})
              initial-def-sub)
      (numV 3))
(test (interp (parse `{with {b {newbox 0}}
                            {seqn {setbox b 10}
                                  {openbox b}}})
              initial-def-sub)
      (numV 10))
(test (interp (parse `{with {b {newbox 0}}
                            {seqn {openbox b}
                                  {setbox b 10}}})
              initial-def-sub)
      (boxV (box (numV 10))))

;; ----------------------------------------------------------------------

(test (interp (parse `{fun {x} {+ x 1}})
              initial-def-sub)
      (closureV 'x (add (id 'x) (num 1))
                (mtSub)))
(test (interp (parse `{with {y 3} {fun {x} {+ x y}}})
              initial-def-sub)
      (closureV 'x (add (id 'x) (id 'y))
                (aSub 'y (numV 3) (mtSub))))
(test (interp (parse `{{with {y 3} {fun {x} {+ x y}}}
                       5})
              initial-def-sub)
      (numV 8))
(test (interp (parse `{with {y 100}
                            {{with {y 3} {fun {x} {+ x y}}}
                             5}})
              initial-def-sub)
      (numV 8))


(test/exn (interp (parse `{with {z {fun {x} {+ x y}}}
                                {with {y 10}
                                      {z 3}}})
                  initial-def-sub)
          "free identifier")
;; A: 13 -- wrong
;; B: free identifier -- right

;; ----------

;; 5 -> 5
(test (interp (parse `5)
              initial-def-sub)
      (numV 5))
;; {+ 1 2} -> 3
(test (interp (parse `{+ 1 2})
              initial-def-sub)
      (numV 3))
;; {- 3 4} -> -1
(test (interp (parse `{- 3 4})
              initial-def-sub)
      (numV -1))
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp (parse `{+ {+ 1 2} {- 3 4}})
              initial-def-sub)
      (numV 2))

#|
{with {x {+ 1 2}}
      {+ x x}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {+ x x}})
              initial-def-sub)
      (numV 6))
#|
x
|#
(test/exn (interp (parse `x)
                  initial-def-sub)
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
              initial-def-sub)
      (numV 8))
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
              initial-def-sub)
      (numV 8))
#|
{with {x {+ 1 2}}
      {with {x {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}})
              initial-def-sub)
      (numV 2))
#|
{with {x {+ 1 2}}
      {with {y {- 4 3}}
            {+ x x}}}
|#
(test (interp (parse `{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}})
              initial-def-sub)
      (numV 6))

;; ----------

(test (interp (parse `{with {f {fun {x} {+ x 1}}}
                            {f 3}})
              initial-def-sub)
      (numV 4))
(test (interp (parse `{{fun {x} {+ x 1}} 3})
              initial-def-sub)
      (numV 4))
(test (interp (parse `{fun {x} {+ x 1}})
              initial-def-sub)
      (closureV 'x (parse `{+ x 1}) (mtSub)))
(test/exn (interp (parse `{1 2})
                  initial-def-sub)
          "expected function")
(test/exn (interp (parse `{+ 1 {fun {x} x}})
                  initial-def-sub)
          "expected number")
(test (interp (parse `{with {f {with {x 3}
                                     {fun {y} {+ x y}}}}
                            {f 2}})
              initial-def-sub)
      (numV 5))

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
<RFAE> = <num>
       | {+ <RFAE> <RFAE>}
       | {- <RFAE> <RFAE>}
       | {fun {<id>} <RFAE>}
       | {<RFAE> <RFAE>}           ;; function application
       | <id>
       | {struct {<id> <RFAE>}*}   ;; all fields must be distinct
       | {get <RFAE> <id>}
       | {set <RFAE> <id> <RFAE>}
       | {seqn <RFAE> <RFAE>}
|#

(define-type RFAE
  [num (n number?)]
  [add (lhs RFAE?)
       (rhs RFAE?)]
  [sub (lhs RFAE?)
       (rhs RFAE?)]
  [id (name symbol?)]
  [fun (param-name symbol?)
       (body RFAE?)]
  [app (fun-expr RFAE?)
       (arg-expr RFAE?)]
  [stru (init-expr (listof pair?))]
  [setstru (rec-expr RFAE?)
           (name symbol?)
           (new-expr RFAE?)]
  [getstru (rec-expr RFAE?)
           (name symbol?)]
  [seqn (expr1 RFAE?)
        (expr2 RFAE?)])

(define-type Store
  [mtSto]
  [aSto (address integer?)
        (name (listof symbol?))
        (value (listof RFAE-Value?))
        (rest Store?)])

(define-type Value*Store
  [v*s (v RFAE-Value?)
       (s Store?)])

(define-type RFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body RFAE?)
            (ds DefSub?)]
  [structV (address integer?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value RFAE-Value?)
         (rest DefSub?)])

;; ----------------------------------------------------------------------

;; parse : s-expression -> RFAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid RFAE"))
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
           [(struct)
            (stru (map (lambda(x)
                         (check-pieces x "struct item" 2)
                         (cons (first x) (parse (second x)))) (rest s-exp)))]
           [(set)
            (check-pieces s-exp "set" 4)
            (setstru (parse (second s-exp))
                     (third s-exp)
                     (parse (fourth s-exp)))]
           [(get)
            (check-pieces s-exp "get" 3)
            (getstru (parse (second s-exp))
                     (third s-exp))]
           [(seqn)
            (check-pieces s-exp "seqn" 3)
            (seqn (parse (second s-exp))
                  (parse (third s-exp)))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected RFAE, got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;; ----------------------------------------------------------------------

(test (parse '{struct {a 3} {b 4}})
      (stru (list (cons 'a (num 3)) (cons 'b (num 4)))))

(test (parse '{struct {z {get {struct {z 0}} y}}})
      (stru (list (cons 'z (getstru (stru (list (cons 'z (num 0)))) 'y)))))

;; ----------------------------------------------------------------------

; size : any -> number?
; computes a (very rough!) approximation of
; the size a PLAI object takes in memory
(define (size s)
  (cond
    [(struct? s)
     (size (struct->vector s))]
    [(vector? s)
     (for/fold ([tot 0])
               ([ele (in-vector s)])
       (+ tot (size ele)))]
    [(pair? s)
     (+ 1 (size (car s)) (size (cdr s)))]
    [else 1]))

;; interp-expr : s-expression -> RFAE-Value?
(define (interp-expr s-exp)
  (type-case Value*Store (interp s-exp (mtSub) (mtSto))
    [v*s (v s)
         (type-case RFAE-Value v
           [numV (n) n]
           [closureV (param-name body local-ds) 'function]
           [structV (address) 'struct])]))

;; ----------------------------------------------------------------------

(define (malloc st)
  (type-case Store st
    [mtSto () 1]
    [aSto (addr name val rest) (+ 1 addr)]))

(define (first-addr st)
  (type-case Store st
    [mtSto () 0]
    [aSto (addr n v rst) addr]))

(define (struct-init records ds st)
  (type-case Store st
    [mtSto () error 'struct-rd]
    [aSto (addr name val st-rest)
          (if (empty? records)
              (v*s (structV (first-addr st)) st)
                  (type-case Value*Store (interp (cdr (first records)) ds st-rest)
                    [v*s (val1 st2)
                         (let ([st3 (aSto (malloc st2)
                                          (cons (car (first records)) name)
                                          (cons val1 val)
                                          st2)])
                           (struct-init (rest records) ds st3))]))]))

;; ----------------------------------------------------------------------

(define (lookup-store record-addr record-name st)
  (type-case Store st
    [mtSto () (error 'lookup-st "unknown field")]
    [aSto (addr named-lst val-lst rest)
          (if (equal? addr record-addr)
              (look-up-name-val record-name named-lst val-lst)
              (lookup-store record-addr record-name rest))]))

(define (look-up-name-val record-name named-lst val-lst)
  (if (empty? named-lst)
      (error 'look-up-name-val "unknown field")
      (if (symbol=? record-name (first named-lst))
          (first val-lst)
          (look-up-name-val record-name (rest named-lst) (rest val-lst)))))

;; ----------------------------------------------------------------------

(define (set-store record-addr target new-val st)
  (type-case Store st
    [mtSto () (error 'set "unknown field")]
    [aSto (addr name val st-rest)
          (if (eq? record-addr addr)
              (set-store-name-val target new-val st)
              (aSto addr name val (set-store record-addr target new-val st-rest)))]))

(define (set-store-name-val target new-val st)
  (type-case Store st
    [aSto (addr name val st-rest)
          (set-store-name-val-lst addr target new-val '() '() name val st-rest)]
    [else (error 'set "unknown field")]))

(define (set-store-name-val-lst adr target new-val prev-name prev-val name-lst val-lst st-rest)
  (if (empty? name-lst)
      (error 'set "unknown field")
      (if (equal? target (first name-lst))
          (aSto adr (append prev-name name-lst) (append prev-val (cons new-val (rest val-lst))) st-rest)
          (set-store-name-val-lst adr target new-val (append prev-name (list (first name-lst))) (append prev-val (list (first val-lst))) (rest name-lst) (rest val-lst) st-rest))))

;; ----------------------------------------------------------------------

;; interp : RFAE? DefSub? Store? -> Value*Store?
(define (interp a-rfae ds st)
  ;;(printf "size ~a\n" (size st))
  (type-case RFAE a-rfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (numop + l r ds st)]
    [sub (l r) (numop - l r ds st)]
    [id (name)
        (v*s (lookup name ds)
             st)]
    [fun (param-name body)
         (v*s (closureV param-name body ds)
              st)]
    [app (fun-expr arg-expr)
         (interp-two fun-expr arg-expr ds st
                     (lambda (fun-val arg-val st3)
                       (type-case RFAE-Value fun-val
                         [closureV (param-name body closed-ds)
                                   (interp body
                                           (aSub param-name arg-val closed-ds)
                                           st3)]
                         [else (error 'interp "expected function, got: ~a" fun-val)])))]
    [stru (init-expr)
          (struct-init init-expr
                       ds
                       (aSto (malloc st)
                             '()
                             '()
                             st))]
    [getstru (struct-expr name)
             (type-case Value*Store (interp struct-expr ds st)
               [v*s (val1 st2) (type-case RFAE-Value val1
                                 [structV (addr) (v*s (lookup-store addr name st2)
                                                      st2)]
                                 [else (error 'interp
                                              "expected record: ~a"
                                              struct-expr)])])]
    [setstru (struct-expr name new-expr)
             (type-case Value*Store (interp struct-expr ds st)
               [v*s (val1 st2)
                    (type-case RFAE-Value val1
                      [structV (addr) (type-case Value*Store (interp new-expr ds st2)
                                        [v*s (val2 st3) (v*s (lookup-store addr name st3)
                                                             (set-store addr name val2 st3))])]
                      [else (error 'interp
                                   "expected record: ~a"
                                   struct-expr)])])]
    [seqn (expr1 expr2)
          (interp-two expr1 expr2 ds st
                      (lambda (v1 v2 st3) (v*s v2 st3)))]))

;; ----------------------------------------------------------------------

;; interp-two : RFAE? RFAE? DefSub? Store? (RFAE-Value? RFAE-Value? Store? -> Value*Store?) -> Value*Store?
(define (interp-two expr1 expr2 ds st finish)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (finish val1 val2 st3)])]))

;; numop : (number? number? -> number?) RFAE? RFAE? DefSub? Store?
;;    -> Value*Store?
(define (numop op l r ds st)
  (interp-two l r ds st
              (lambda (l-val r-val st3)
                (unless (numV? l-val)
                  (error 'interp "expected number, got ~a" l-val))
                (unless (numV? r-val)
                  (error 'interp "expected number, got ~a" r-val))
                (v*s (numV (op (numV-n l-val) (numV-n r-val)))
                     st3))))

;; lookup : symbol? DefSub? -> RFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; ----------------------------------------------------------------------

(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")
(test (interp-expr (parse '{get {struct {y {get {struct {z 0} {a 0}} z}}} y}))
      0)
(test/exn (interp-expr (parse '{get {struct {y {get {struct {z 0} {a 0}} z}}} z}))
          "unknown field")
(test/exn (interp-expr (parse '{get {struct {a 0} 
                                      {b {struct {d 7} 
                                           {e 50}}}} 
                                    d}))
          "unknown field")
(test/exn (interp-expr (parse '{get {struct {x {struct {a 4}}} {b 4}} a}))
          "unknown field")
(test/exn (interp-expr (parse `{+ {struct {z 1}} 3}))
          "expected number")
(test/exn (interp-expr (parse '{struct {z b}}))
          "free identifier")
(test (interp-expr (parse `{struct}))
      'struct)
(test (interp-expr (parse `{struct {z 1}}))
      'struct)
(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {struct {x 1}}}))
      5)
(test (interp-expr (parse '{set {struct {x 42}} x 2}))
      42)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}

                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      5)

(test (interp-expr (parse '{set {struct {x 42} {y 50}} x 2}))
      42)


;; ----------------------------------------------------------------------

(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) x 11)))
      1)
(test (interp-expr (parse `(set (struct (x 1) (y 2) (z 3)) y 11)))
      2)
(test (interp-expr (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r x 17) (get r x)))))
      17)
(test (interp-expr (parse `(with (r (struct (x 1) (y 2) (z 3))) (seqn (set r y 17) (get r y)))))
      17)
(test (interp-expr (parse '(with (x (struct (a 1) (b 2) (c 3))) (set x b (seqn (set x b 5) 7)))))
      5)

                    
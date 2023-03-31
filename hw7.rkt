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


;<EFAE> = <num>
;       | {+ <EFAE> <EFAE>}
;       | {- <EFAE> <EFAE>}
;       | <id>
;       | {fun {<id>} <EFAE>}
;       | {<EFAE> <EFAE>} ;; function application
;       | {if0 <EFAE> <EFAE> <EFAE>}
;       | {throw <id> <EFAE>}
;       | {try <EFAE1> {catch {tag <id1> as <id2>} <EFAE2>}}

(define-type EFAE
  [num (n number?)]
  [add (lhs EFAE?)
       (rhs EFAE?)]
  [sub (lhs EFAE?)
       (rhs EFAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body EFAE?)]
  [app (fun-expr EFAE?)
       (arg-expr EFAE?)]
  [if0 (tst EFAE?)
       (thn EFAE?)
       (els EFAE?)]
  [throw (tag symbol?)
         (throw-expr EFAE?)]
  [try-catch (try-body EFAE?)
             (tag symbol?)
             (exn-name symbol?)
             (catch-body EFAE?)])

(define-type EFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body EFAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value EFAE-Value?)
         (rest DefSub?)])


;; ----------------------------------------------------------------------


;; parse : s-expression -> KFAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid KFAE"))
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
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got ~a" (first (second s-exp))))
            (app (fun (first (second s-exp)) (parse (third s-exp)))
                 (parse (second (second s-exp))))]
           [(if0)
            (check-pieces s-exp "if0" 4)
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [(throw)
            (check-pieces s-exp "throw" 3)
            (throw (second s-exp)
                   (parse (third s-exp)))]
           [(try)
            (check-pieces s-exp "try" 3)
            (check-pieces (third s-exp) "catch" 3)
            (try-catch (parse (second s-exp))
                       (second (second (third s-exp)))
                       (fourth (second (third s-exp)))
                       (parse (third (third s-exp))))]
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

(test (parse `{+ 2 {try {+ 4 {throw x 5}}
                        {catch {tag x as e} {+ 3 e}}}})
      (add (num 2) (try-catch (add (num 4) (throw 'x (num 5))) 'x 'e (add (num 3) (id 'e)))))

(test (parse `{try {+ 2 {try {+ 3 {throw y 5}}
                             {catch {tag x as e} {+ 6 e}}}}
                   {catch {tag y as e} {+ 10 e}}})
      (try-catch (add (num 2) (try-catch (add (num 3) (throw 'y (num 5))) 'x 'e (add (num 6) (id 'e)))) 'y 'e (add (num 10) (id 'e))))


;;--------------------------------------------------------

;; lookup : symbol? DefSub? -> EFAE?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; numop : (number? number? -> number?)
;;         EFAE? EFAE? DefSub? (EFAE-Value? -> KFAE-Value?) -> EFAE-Value?
(define (numop op l r ds k catch-k)
  (interp l ds
          (lambda (l-val)
            (interp r ds
                    (lambda (r-val)
                      (unless (and (numV? l-val) (numV? r-val))
                        (error 'interp "expected number"))
                      (k (numV (op (numV-n l-val) (numV-n r-val)))))
                    catch-k))
          catch-k))

;; interp-expr : EFAE -> number or ’function
(define (interp-expr an-efae)
  (define output (interp an-efae
                         (mtSub)
                         (λ (res) res)
                         (λ (tag val) (error 'interp "missing catch: ~a ~a" tag val))))
  (type-case EFAE-Value output
    [numV (n) n]
    [closureV (param-name body local-ds) 'function]))


;; interp : EFAE? DefSub?
(define (interp a-efae ds k catch-k)
  (type-case EFAE a-efae
    [num (n) (k (numV n))]
    [id (name) (k (lookup name ds))]
    [fun (param-name body) (k (closureV param-name body ds))]
    [add (l r) (numop + l r ds k catch-k)]
    [sub (l r) (numop - l r ds k catch-k)]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (interp arg-expr ds
                           (lambda (arg-val)
                             (type-case EFAE-Value fun-val
                               [closureV (param-name body closed-ds)
                                         (interp body (aSub param-name
                                                            arg-val
                                                            closed-ds)
                                                 (lambda (ret-val)
                                                   (k ret-val))
                                                 catch-k)]
                               [else (error 'interp "expected function")]))
                           catch-k))
                 catch-k)]
    [if0 (tst thn els)
         (interp tst ds
                 (lambda (tst-val)
                   (type-case EFAE-Value tst-val
                     [numV (n)
                           (if (equal? n 0)
                               (interp thn ds
                                       (lambda (thn-val)
                                         (k thn-val))
                                       catch-k)
                               (interp els ds
                                       (lambda (els-val)
                                         (k els-val))
                                       catch-k))]
                     [closureV (param-name body local-ds)
                               (interp els ds
                                       (lambda (els-val)
                                         (k els-val))
                                       catch-k)]))
                 catch-k)]
    [throw (tag throw-expr)
           (interp throw-expr ds
                   (lambda (throw-val) (catch-k tag throw-val))
                   catch-k)]
    [try-catch (try-body tag exn-name catch-body)
               (interp try-body ds
                       k
                       (lambda (throw-tag throw-val)
                         (if (symbol=? tag throw-tag)
                             (interp catch-body (aSub exn-name throw-val ds) k catch-k)
                             (catch-k throw-tag throw-val))))]))


(test (interp-expr (parse `{+ 2 {try {+ 4 {throw x 5}}
                                     {catch {tag x as e} {+ 3 e}}}}))
      10)

(test (interp-expr (parse `{try {+ 2 {try {+ 3 {throw y 5}}
                                          {catch {tag x as e} {+ 6 e}}}}
                                {catch {tag y as e} {+ 10 e}}}))
      15)

(test/exn (interp-expr (parse `{try {throw a 1} {catch {tag a as b} {throw a 1}}}))
          "missing catch")

(test (interp-expr (parse `{with {f {fun {x} {throw a {+ x 1}}}}
                                 {try {throw a {+ {f 3} 10}}
                                      {catch {tag a as j} {+ j 5}}}}))
      9)
#lang plaitypus

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

;; you may use these definitions in your solution

(print-only-errors #t)

(define-type TLFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TLFAE) (r : TLFAE)]
  [sub (l : TLFAE) (r : TLFAE)]
  [eql (l : TLFAE) (r : TLFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TLFAE) (thn : TLFAE) (els : TLFAE)]
  [fun (arg : symbol) (typ : Type) (body : TLFAE)]
  [app (rator : TLFAE) (rand : TLFAE)]
  [consl (fst : TLFAE) (rst : TLFAE)]
  [firstl (lst : TLFAE)]
  [restl (lst : TLFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TLFAE)]
  [makevector (size : TLFAE) (initial : TLFAE)]
  [set (vec : TLFAE) (index : TLFAE) (val : TLFAE)]
  [lengthl (col : TLFAE)]
  [get (col : TLFAE) (index : TLFAE)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

(define-type Type
  [numberT]
  [booleanT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)]
  [vectorT (typ : Type)])

(define parse : (s-expression -> TLFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (case (s-exp->symbol s-exp)
         [(true)  (bool #t)]
         [(false) (bool #f)]
         [else (id (s-exp->symbol s-exp))])]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid TLFAE")]
             [(s-exp-symbol? (first as-list))
              (case (s-exp->symbol (first as-list))
                [(+)
                 (check-pieces as-list "add" 3)
                 (add (parse (second as-list))
                      (parse (third as-list)))]
                [(-)
                 (check-pieces as-list "sub" 3)
                 (sub (parse (second as-list))
                      (parse (third as-list)))]
                [(=)
                 (check-pieces as-list "eql" 3)
                 (eql (parse (second as-list))
                      (parse (third as-list)))]
                [(if)
                 (check-pieces as-list "if" 4)
                 (ifthenelse (parse (second as-list))
                             (parse (third as-list))
                             (parse (fourth as-list)))]
                [(fun)
                 (check-pieces as-list "fun" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected parameter list"))
                 (define param-list (s-exp->list (second as-list)))
                 (check-pieces param-list "parameter list" 3)
                 (unless (s-exp-symbol? (first param-list))
                   (error 'parse "expected symbol as parameter name"))
                 (unless (and (s-exp-symbol? (second param-list))
                              (equal? ': (s-exp->symbol (second param-list))))
                   (error 'parse "expected `:`"))
                 (fun (s-exp->symbol (first param-list))
                      (parse-type (third param-list))
                      (parse (third as-list)))]
                [(cons)
                 (check-pieces as-list "cons" 3)
                 (consl (parse (second as-list))
                        (parse (third as-list)))]
                [(first)
                 (check-pieces as-list "first" 2)
                 (firstl (parse (second as-list)))]
                [(rest)
                 (check-pieces as-list "rest" 2)
                 (restl (parse (second as-list)))]
                [(nil)
                 (check-pieces as-list "nil" 2)
                 (nil (parse-type (second as-list)))]
                [(empty?)
                 (check-pieces as-list "empty?" 2)
                 (mtl? (parse (second as-list)))]
                [(make-vector)
                 (check-pieces as-list "make-vector" 3)
                 (makevector (parse (second as-list))
                             (parse (third as-list)))]
                [(set)
                 (check-pieces as-list "set" 4)
                 (set (parse (second as-list))
                      (parse (third as-list))
                      (parse (fourth as-list)))]
                [(length)
                 (check-pieces as-list "length" 2)
                 (lengthl (parse (second as-list)))]
                [(get)
                 (check-pieces as-list "get" 3)
                 (get (parse (second as-list))
                      (parse (third as-list)))]
                [else (parse-app as-list)])]
             [else (parse-app as-list)])]
      [else
       (error 'parse "expected TLFAE")])))

(define parse-app : ((listof s-expression) -> TLFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(and (s-exp-symbol? s-exp)
                (equal? 'boolean (s-exp->symbol s-exp)))
           (booleanT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (case (length as-list)
             [(2)
              (unless (s-exp-symbol? (first as-list))
                (error 'parse "expected `listof` or `vectorof`"))
              (case (s-exp->symbol (first as-list))
                [(listof)
                 (listT (parse-type (second as-list)))]
                [(vectorof)
                 (vectorT (parse-type (second as-list)))]
                [else
                 (error 'parse "expected `listof` or `vectorof`")])]
             [(3)
              (unless (and (s-exp-symbol? (second as-list))
                           (equal? '-> (s-exp->symbol (second as-list))))
                (error 'parse "expected `->`"))
              (arrowT (parse-type (first as-list))
                      (parse-type (third as-list)))]
             [else (error 'parse-type "expected type")])]
          [else (error 'parse-type "expected type")])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))


;;---------------------------------------------------
;;typechecks

(define lookup-type : (symbol TypeEnv -> Type)
  (lambda (name gamma)
    (type-case TypeEnv gamma
      [mtEnv () (error 'typecheck "free identifier")]
      [aBind (n2 t r) (if (equal? name n2)
                          t
                          (lookup-type name r))])))

(define typecheck : (TLFAE TypeEnv -> Type)
  (λ (a-tlfae gamma)
    (type-case TLFAE a-tlfae
      [num (n) (numberT)]
      [bool (n) (booleanT)]
      [add (l r)
           (unless (and (equal? (typecheck l gamma) (numberT))
                        (equal? (typecheck r gamma) (numberT)))
             (error 'typecheck "expected number"))
           (numberT)]
      [sub (l r)
           (unless (and (equal? (typecheck l gamma) (numberT))
                        (equal? (typecheck r gamma) (numberT)))
             (error 'typecheck "expected number"))
           (numberT)]
      [id (name)
          (lookup-type name gamma)]
      [eql (l r)
           (unless (and (equal? (typecheck l gamma) (numberT))
                        (equal? (typecheck r gamma) (numberT)))
             (error 'typecheck "expected number"))
           (booleanT)]
      [ifthenelse (tst thn els)
                  (unless (equal? (booleanT) (typecheck tst gamma))
                    (error 'typecheck "expected boolean"))
                  (define thn-type (typecheck thn gamma))
                  (define els-type (typecheck els gamma))
                  (unless (equal? thn-type els-type)
                    (error 'typecheck "type mismatch"))
                  thn-type]
      [fun (param-name param-type body)
           (arrowT param-type
                   (typecheck body
                              (aBind param-name
                                     param-type
                                     gamma)))]
      [app (fun-expr arg-expr)
           (define fun-type (typecheck fun-expr gamma))
           (define arg-type (typecheck arg-expr gamma))
           (type-case Type fun-type
             [arrowT (dom-type rng-type)
                     (unless (equal? dom-type arg-type)
                       (error 'typecheck "argument type mismatch"))
                     rng-type]
             [else (error 'typecheck "expected function")])]
      [consl (fst rst)
             (define fst-type (typecheck fst gamma))
             (define rst-type (typecheck rst gamma))
             (type-case Type rst-type
               [listT (typ-type)
                      (unless (equal? typ-type fst-type)
                        (error 'typecheck "argument type mismatch"))
                      rst-type]
               [else (error 'typecheck "expected list")])]
      [firstl (lst)
              (define lst-type (typecheck lst gamma))
              (type-case Type lst-type
                [listT (typ-type)
                       typ-type]
                [else (error 'typecheck "expected list")])]
      [restl (lst)
             (define lst-type (typecheck lst gamma))
             (type-case Type lst-type
               [listT (typ-type)
                      lst-type]
               [else (error 'typecheck "expected list")])]
      [nil (typ) 
           (listT typ)]
      [mtl? (lst)
            (type-case Type (typecheck lst gamma)
              [listT (typ-type) (booleanT)]
              [else (error 'typecheck "expected list")])]
      [makevector (size initial)
                  (unless (equal? (numberT) (typecheck size gamma))
                    (error 'typecheck "expected number"))
                  (vectorT (typecheck initial gamma))]
      [set (vec index val)
           (define vec-type (typecheck vec gamma))
           (define index-type (typecheck index gamma))
           (define val-type (typecheck val gamma))
           (type-case Type vec-type
             [vectorT (typ-type)
                      (unless (equal? index-type (numberT))
                        (error 'typecheck "expected number"))
                      (unless (equal? typ-type val-type)
                        (error 'typecheck "argument type mismatch"))
                      val-type]
             [else (error 'typecheck "expected vector")])]
      [lengthl (col)
               (define col-type (typecheck col gamma))
               (type-case Type col-type
                 [listT (typ-type)
                        (numberT)]
                 [vectorT (typ-type)
                          (numberT)]
                 [else (error 'typecheck "expected list or vector")])]
      [get (col index)
           (define col-type (typecheck col gamma))
           (define index-type (typecheck index gamma))
           (type-case Type col-type
             [listT (typ-type)
                    (unless (equal? index-type (numberT))
                      (error 'typecheck "expected number"))
                    typ-type]
             [vectorT (typ-type)
                      (unless (equal? index-type (numberT))
                        (error 'typecheck "expected number"))
                      typ-type]
             [else (error 'typecheck "expected list or vector")])])))


;;-----------------
;; typecheck-expr : TLFAE -> Type
(define typecheck-expr : (TLFAE -> Type)
  (lambda (a-tlfae)
    (typecheck a-tlfae (mtEnv))))

;;tests
(test (typecheck (parse `5)
                 (mtEnv))
      (numberT))
(test (typecheck (parse `{+ 2 3})
                 (mtEnv))
      (numberT))
(test (typecheck (parse `{- 2 3})
                 (mtEnv))
      (numberT))
(test (typecheck (parse `{+ 1 {- 2 3}})
                 (mtEnv))
      (numberT))
(test (typecheck (parse `{fun {x : number} {+ x 5}})
                 (mtEnv))
      (arrowT (numberT) (numberT)))
(test (typecheck (parse `{{fun {x : number} {+ x 5}} 7})
                 (mtEnv))
      (numberT))
(test/exn (typecheck (parse `{1 1})
                     (mtEnv))
          "expected function")
(test/exn (typecheck (parse `{{fun {f : (number -> number)}
                                   {fun {x : number} {f x}}}
                              3})
                     (mtEnv))
          "argument type mismatch")
(test (typecheck-expr (parse `{{{fun {f : (number -> number)}
                                     {fun {x : number} {f x}}}
                                {fun {x : number} {+ x 5}}}
                               5}))
      (numberT))
(test (typecheck-expr (parse '(rest (cons 4 (cons 5 (nil number))))))
      (listT (numberT)))
(test (typecheck-expr
       (parse '(rest (cons (fun (x : number) 6) (nil (number -> number))))))
      (listT (arrowT (numberT) (numberT))))
(test (typecheck-expr (parse '(rest (nil number))))
      (listT (numberT)))
(test (typecheck-expr (parse '(rest (cons false (nil boolean)))))
      (listT (booleanT)))
(test (typecheck-expr
       (parse '(rest (cons (fun (x : number) (= x 6)) (nil (number -> boolean))))))
      (listT (arrowT (numberT) (booleanT))))
(test (typecheck-expr (parse '(rest (nil boolean))))
      (listT (booleanT)))
(test (typecheck-expr
       (parse
        '(first
          (rest
           (cons
            (if false (fun (x : number) x) (fun (y : number) (+ y 3)))
            (nil (number -> number)))))))
      (arrowT (numberT) (numberT)))
(test (typecheck-expr
       (parse
        '((first
           (rest
            (cons
             (if false (fun (x : number) x) (fun (y : number) (+ y 3)))
             (nil (number -> number)))))
          5)))
      (numberT))
(test/exn (typecheck-expr
           (parse
            '((first
               (rest
                (cons
                 (if false (fun (x : number) x) (fun (y : number) (+ y 3)))
                 (nil (number -> number)))))
              false)))
          "type mismatch")
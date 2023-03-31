#lang plaitypus

(print-only-errors #t)

(define-type Type
  [numberT]
  [arrowT (param : Type) (result : Type)]
  ;; NEW
  [boxT   (contents-type : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

(define-type TBFAE
  [num (n : number)]
  [add (lhs : TBFAE)
       (rhs : TBFAE)]
  [sub (lhs : TBFAE)
       (rhs : TBFAE)]
  [id (name : symbol)]
  [fun (param-name : symbol)
       (param-type : Type)
       (body : TBFAE)]
  [app (fun-expr : TBFAE)
       (arg-expr : TBFAE)]
  ;; NEW
  [newbox  (init-expr : TBFAE)]
  [setbox  (box-expr : TBFAE)
           (new-value-expr : TBFAE)]
  [openbox (box-expr : TBFAE)]
  [seqn    (expr1 : TBFAE)
           (expr2 : TBFAE)])

;; ----------------------------------------------------------------------

;; If you gaze long into an abyss, the abyss also gazes into you.
;;   - Friedrich Nietzsche, Beyond Good and Evil
(define parse : (s-expression -> TBFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (id (s-exp->symbol s-exp))]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid FAE")]
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
                [(with)
                 (check-pieces as-list "with" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected binding pair"))
                 (define b-p (s-exp->list (second as-list)))
                 (check-pieces b-p "binding pair" 4)
                 (unless (s-exp-symbol? (first b-p))
                   (error 'parse "expected symbol as variable name"))
                 (unless (and (s-exp-symbol? (second b-p))
                              (equal? ': (s-exp->symbol (second b-p))))
                   (error 'parse "expected `:`"))
                 (app (fun (s-exp->symbol (first b-p))
                           (parse-type (third b-p))
                           (parse (third as-list)))
                      (parse (fourth b-p)))]
                [(newbox)
                 (check-pieces as-list "newbox" 2)
                 (newbox (parse (second as-list)))]
                [(setbox)
                 (check-pieces as-list "setbox" 3)
                 (setbox (parse (second as-list))
                         (parse (third as-list)))]
                [(openbox)
                 (check-pieces as-list "openbox" 2)
                 (openbox (parse (second as-list)))]
                [(seqn)
                 (check-pieces as-list "seqn" 3)
                 (seqn (parse (second as-list))
                       (parse (third as-list)))]
                [else
                 (parse-app as-list)])]
             [else
              (parse-app as-list)])]
      [else
       (error 'parse "expected TBFAE")])))

(define parse-app : ((listof s-expression) -> TBFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (cond [(= (length as-list) 3)
                  (unless (and (s-exp-symbol? (second as-list))
                               (equal? '-> (s-exp->symbol (second as-list))))
                    (error 'parse "expected `->`"))
                  (arrowT (parse-type (first as-list))
                          (parse-type (third as-list)))]
                 [(= (length as-list) 2)
                  (unless (and (s-exp-symbol? (first as-list))
                               (equal? 'boxof (s-exp->symbol (first as-list))))
                    (error 'parse "expected `boxof`"))
                  (boxT (parse-type (second as-list)))]
                 [else
                  (error 'parse "expected function of box type")])])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))

;; ----------------------------------------------------------------------

(define typecheck : (TBFAE TypeEnv -> Type)
  (lambda (a-tfae gamma)
    (type-case TBFAE a-tfae
      [num (n)
           (numberT)]
      [add (l r)
           (numop l r gamma)]
      [sub (l r)
           (numop l r gamma)]
      [id (name)
          (lookup-type name gamma)]
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
      [newbox (init-expr)
              #|
                      Γ ⊢ e_1 : τ_1
              ------------------------------
              Γ ⊢ {newbox e_1} : (boxof τ_1)
              |#
              (define tau1 (typecheck init-expr gamma))
              (boxT tau1)]
      [setbox (box-expr new-value-expr)
              #|
              Γ ⊢ e_1 : (boxof τ_1)       Γ ⊢ e_2 : τ_1
              -----------------------------------------
                     Γ ⊢ {setbox e_1 e_2} : τ_1
              |#
              (define tau1 (typecheck new-value-expr gamma))
              (type-case Type (typecheck box-expr gamma)
                [boxT (element-type)
                      (unless (equal? tau1 element-type)
                        (error 'typecheck "type mismatch"))
                      tau1]
                [else (error 'typecheck "expected box")])]
      [openbox (box-expr)
               #|
                Γ ⊢ e_1 : (boxof τ_1)
               -----------------------
               Γ ⊢ {openbox e_1} : τ_1
               |#
               (type-case Type (typecheck box-expr gamma)
                 [boxT (tau1)
                       tau1]
                 [else (error 'typecheck "expected box")])]
      [seqn (expr1 expr2)
            #|
            Γ ⊢ e_1 : τ_1        Γ ⊢ e_1 : τ_2
            ----------------------------------
                 Γ ⊢ {seqn e_1 e_2} : τ_2
            |#
            (typecheck expr1 gamma)
            (define tau2 (typecheck expr2 gamma))
            tau2])))

(define numop : (TBFAE TBFAE TypeEnv -> Type)
  (lambda (l r gamma)
    (define l-type (typecheck l gamma))
    (define r-type (typecheck r gamma))
    (unless (and (numberT? l-type)
                 (numberT? r-type))
      (error 'typecheck "expected number"))
    (numberT)))

(define lookup-type : (symbol TypeEnv -> Type)
  (lambda (name gamma)
    (type-case TypeEnv gamma
      [mtEnv () (error 'typecheck "free identifier")]
      [aBind (n2 t r) (if (equal? name n2)
                          t
                          (lookup-type name r))])))

;; NEW
(test (typecheck (parse `{newbox 5})
                 (mtEnv))
      (boxT (numberT)))

(test (typecheck (parse `{newbox {newbox 5}})
                 (mtEnv))
      (boxT (boxT (numberT))))

(test (typecheck (parse `{openbox {newbox 5}})
                 (mtEnv))
      (numberT))

(test (typecheck (parse `{with {b : (boxof number) {newbox 3}}
                               {seqn {setbox b 5}
                                     {openbox b}}})
                 (mtEnv))
      (numberT))

(test/exn (typecheck (parse `{with {b : (boxof number) {newbox 3}}
                                   {seqn {setbox b {fun {x : number} x}}
                                         {openbox b}}})
                     (mtEnv))
          "type mismatch")

(test/exn (typecheck (parse `{openbox 5})
                     (mtEnv))
          "expected box")

(test/exn (typecheck (parse `{seqn {openbox 5}
                                   5})
                     (mtEnv))
          "expected box")


;; ----------------------------------------------------------------------

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

(test/exn (typecheck (parse `{+ 3 {fun {x : number} {+ x 5}}})
                     (mtEnv))
          "expected number")
(test/exn (typecheck (parse `{3 4})
                     (mtEnv))
          "expected function")

(test (typecheck (parse `{fun {f : (number -> number)}
                              {fun {x : number} {f x}}})
                 (mtEnv))
      (parse-type `((number -> number) -> (number -> number))))
(test/exn (typecheck (parse `{{fun {f : (number -> number)}
                                   {fun {x : number} {f x}}}
                              3})
                     (mtEnv))
          "argument type mismatch")
(test (typecheck (parse `{{fun {f : (number -> number)}
                               {fun {x : number} {f x}}}
                          {fun {y : number} {+ y 8}}})
                 (mtEnv))
      (parse-type `(number -> number)))
(test/exn (typecheck (parse `{{fun {f : (number -> number)}
                                   {fun {x : number} {f x}}}
                              {fun {y : (number -> number)}
                                   {y 8}}})
                     (mtEnv))
          "argument type mismatch")

(test (typecheck (parse `{{{fun {f : (number -> number)}
                                {fun {x : number} {f x}}}
                           {fun {y : number} {+ y 8}}}
                          5376})
                 (mtEnv))
      (parse-type `number))

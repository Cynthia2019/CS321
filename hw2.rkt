#lang plai

(print-only-errors)

(define eight-principles (list
                          "Know your rights."
                          "Acknowledge your sources."
                          "Protect your work."
                          "Avoid suspicion."
                          "Do your own work."
                          "Never falsify a record or permit another person to do so."
                          "Never fabricate data, citations, or experimental results."
                          "Always tell the truth when discussing your work with your instructor."))

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)
       (rhs WAE?)]
  [sub (lhs WAE?)
       (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

;Binding Identifiers
(define (binding-ids-helper wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (binding-ids-helper l)
                       (binding-ids-helper r))]
    [sub (l r) (append (binding-ids-helper l)
                       (binding-ids-helper r))]
    [with (name expr body)
          (cons name (append 
                      (binding-ids-helper expr)
                      (binding-ids-helper body)))]
    [id (name) empty]
    ))
(define (binding-ids wae)
  (remove-duplicates
   (sort (binding-ids-helper wae) symbol<?)))
;test1
(test (binding-ids (with 'x (num 2) (add (id 'x) (num 1)))) '(x))
;test2
(test (binding-ids (id 'x)) '())
;test3
(test (binding-ids (add (num 1) (num 2))) '())
;test4
(test (binding-ids (with 'x (with 'y (num 3) (add (id 'y) (num 1)))
                         (add (id 'x) (id 'y))))
      '(x y))
;test5
(test (binding-ids (with 'x (add (with 'y (num 2) (id 'x)) (num 2))
                         (add (id 'x) (id 'y))))
      '(x y))
;test6
(test (binding-ids (with 'x (add (with 'x (num 3) (id 'x)) (num 3))
                         (add (id 'x) (id 'x))))
      '(x))

;Bound Identifiers
(define (bound-ids-helper wae lst)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (bound-ids-helper l lst)
                       (bound-ids-helper r lst))]
    [sub (l r) (append (bound-ids-helper l lst)
                       (bound-ids-helper r lst))]
    [with (name expr body)
          (append 
           (bound-ids-helper expr lst)
           (bound-ids-helper body (cons name lst)))]
    [id (name) (if (member name lst)
                   (list name)
                   empty)]
    ))
(define (bound-ids wae)
  (remove-duplicates
   (sort (bound-ids-helper wae empty) symbol<?)))

;test1
(test (bound-ids (with 'x (num 2) (add (id 'x) (num 1)))) '(x))
;test2
(test (bound-ids (id 'x)) '())
;test3
(test (bound-ids (add (num 1) (num 2))) '())
;test4
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'y) (num 1)))
                       (add (id 'x) (id 'y))))
      '(x y))
;test5
(test (bound-ids (with 'x (add (with 'x (num 3) (id 'x)) (num 3))
                       (add (id 'x) (id 'x))))
      '(x))
;test6
(test (bound-ids (add (id 'x) (id 'x)))
      '())
(test (bound-ids (with 'x (add (num 1) (num 2))
                       (add (id 'x) (id 'y))))
      '(x))
;test7
(test (bound-ids (with 'x (add (num 1) (num 2))
                       (with 'y (sub (num 4) (num 3))
                             (add (id 'x) (id 'x)))))
      '(x))
;test8
(test (bound-ids (add (with 'x (add (num 1) (num 2))
                            (add (id 'x) (id 'x)))
                      (with 'y (sub (num 4) (num 3))
                            (add (id 'y) (id 'y)))))
      '(x y))
;test9
(test (bound-ids (with 'y (id 'x) (id 'y)))
      '(y))

;Free Identifiers
(define (free-ids-helper wae lst)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (free-ids-helper l lst)
                       (free-ids-helper r lst))]
    [sub (l r) (append (free-ids-helper l lst)
                       (free-ids-helper r lst))]
    [with (name expr body)
          (append 
           (free-ids-helper expr lst)
           (free-ids-helper body (cons name lst)))]
    [id (name) (if (member name lst)
                   empty
                   (list name))]
    ))
(define (free-ids wae)
  (remove-duplicates
   (sort (free-ids-helper wae empty) symbol<?)))
;test1
(test (free-ids (with 'y (id 'x) (id 'y)))
      '(x))
;test2
(test (free-ids (id 'x))
      '(x))
;test3
(test (free-ids (with 'x (num 2) (add (id 'y) (num 1)))) '(y))
;test4
(test (free-ids (add (id 'y) (id 'y)))
      '(y))
;test5
(test (free-ids (with 'x (add (num 1) (num 2))
                      (add (id 'x) (id 'y))))
      '(y))
;test6 {with {x {with y {- y 0} {+ x z}}}}
(test (free-ids (with 'x (add (num 1) (num 2))
                      (with 'y (sub (id 'y) (num 0))
                            (add (id 'x) (id 'z)))))
      '(y z))
;Shadowed Identifiers
(define (shadow-ids-helper wae lst)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (shadow-ids-helper l lst)
                       (shadow-ids-helper r lst))]
    [sub (l r) (append (shadow-ids-helper l lst)
                       (shadow-ids-helper r lst))]
    [with (name expr body)
          (if (member name lst)
              (cons name
                    (append 
                     (shadow-ids-helper expr lst)
                     (shadow-ids-helper body (cons name lst))))
              (append 
               (shadow-ids-helper expr lst)
               (shadow-ids-helper body (cons name lst))))]
    [id (name) empty]
    ))
(define (shadowed-ids wae)
  (remove-duplicates
   (sort (shadow-ids-helper wae empty) symbol<?)))

;test1
(test (shadowed-ids (with 'x (num 2) (with 'x (num 3) (add (id 'x) (num 1)))))
      '(x))
;test2
(test (shadowed-ids (with 'x (num 2) (add (id 'x) (num 2))))
      '())
;test3
(test (shadowed-ids (with 'y (id 'x) (id 'y)))
      '())
;test4
(test (shadowed-ids (with 'x (add (num 1) (num 2))
                      (add (id 'x) (id 'y))))
      '())
;test5
(test (shadowed-ids (add (with 'x (add (num 1) (num 2))
                            (add (id 'x) (id 'x)))
                      (with 'y (sub (num 4) (num 3))
                            (add (id 'y) (id 'y)))))
      '())
;test6
(test (shadowed-ids (with 'x (add (with 'x (num 3) (id 'x)) (num 3))
                       (add (id 'x) (id 'x))))
      '())
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
<WAE> ::= <num>
       |  {+ <WAE> <WAE>}
       |  {- <WAE> <WAE>}
       |  {with {<id> <WAE>} <WAE>}
       |  <id>
|#

(define-type WAE
  [num (n number?)]
  [add (l WAE?) (r WAE?)]
  [sub (l WAE?) (r WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])


#| binding-ids |#
(define (binding-ids-raw a-wae)
  (type-case WAE a-wae
    [num (n) empty]
    [add (lhs rhs)
         (append (binding-ids-raw lhs) (binding-ids-raw rhs))]
    [sub (lhs rhs)
         (append (binding-ids-raw lhs) (binding-ids-raw rhs))]
    [with (name named-expr body)
          (cons name (append (binding-ids-raw named-expr)
                             (binding-ids-raw body)))]
    [id (name) empty]))

(define (binding-ids a-wae)
  (sort (remove-duplicates (binding-ids-raw a-wae))
        symbol<?))

(test (binding-ids (id 'x))
      '())
(test (binding-ids (add (id 'x) (id 'x)))
      '())
(test (binding-ids (with 'x (add (with 'y (num 2) (id 'x)) (num 2))
                         (add (id 'x) (id 'y))))
      '(x y))
(test (binding-ids (add (with 'x (add (num 1) (num 2))
                              (add (id 'x) (id 'x)))
                        (with 'y (sub (num 4) (num 3))
                              (add (id 'y) (id 'y)))))
      '(x y))
(test (binding-ids (with 'x (add (num 1) (num 2))
                         (with 'y (sub (num 4) (num 3))
                               (add (id 'x) (id 'x)))))
      '(x y))

#| bound-ids |#

(define (bound-ids-raw a-wae lst)
  (type-case WAE a-wae
    [num (n) empty]
    [add (lhs rhs)
         (append (bound-ids-raw lhs lst) (bound-ids-raw rhs lst))]
    [sub (lhs rhs)
         (append (bound-ids-raw lhs lst) (bound-ids-raw rhs lst))]
    [with (name named-expr body)
          (append (bound-ids-raw named-expr lst)
                  (bound-ids-raw body (cons name lst)))]
    [id (name) (if (member name lst)
                   (list name)
                   empty)]))

(define (bound-ids a-wae)
  (sort (remove-duplicates (bound-ids-raw a-wae empty))
        symbol<?))

(test (bound-ids (id 'x))
      '())
(test (bound-ids (add (id 'x) (id 'x)))
      '())
(test (bound-ids (with 'x (add (num 1) (num 2))
                       (add (id 'x) (id 'y))))
      '(x))
(test (bound-ids (add (with 'x (add (num 1) (num 2))
                            (add (id 'x) (id 'x)))
                      (with 'y (sub (num 4) (num 3))
                            (add (id 'y) (id 'y)))))
      '(x y))
(test (bound-ids (with 'x (add (num 1) (num 2))
                       (with 'y (sub (num 4) (num 3))
                             (add (id 'x) (id 'x)))))
      '(x))


#| free-ids |#
(define (free-ids-raw a-wae lst)
  (type-case WAE a-wae
    [num (n) empty]
    [add (lhs rhs)
         (append (free-ids-raw lhs lst) (free-ids-raw rhs lst))]
    [sub (lhs rhs)
         (append (free-ids-raw lhs lst) (free-ids-raw rhs lst))]
    [with (name named-expr body)
          (append (free-ids-raw named-expr lst)
                  (free-ids-raw body (cons name lst)))]
    [id (name) (if (member name lst)
                   empty
                   (list name))]))

(define (free-ids a-wae)
  (sort (remove-duplicates (free-ids-raw a-wae empty))
        symbol<?))

(test (free-ids (id 'x))
      '(x))
(test (free-ids (add (id 'x) (id 'x)))
      '(x))
(test (free-ids (with 'x (add (num 1) (num 2))
                      (add (id 'x) (id 'y))))
      '(y))
(test (free-ids (add (with 'x (add (id 'x) (num 2))
                           (add (id 'x) (id 'x)))
                     (with 'y (sub (num 4) (num 3))
                           (add (id 'y) (id 'y)))))
      '(x))
(test (free-ids (with 'x (add (num 1) (num 2))
                      (with 'y (sub (id 'y) (num 3))
                            (add (id 'x) (id 'z)))))
      '(y z))


#| shadowed-ids |#
(define (shadowed-ids-raw a-wae lst)
  (type-case WAE a-wae
    [num (n) empty]
    [add (lhs rhs)
         (append (shadowed-ids-raw lhs lst) (shadowed-ids-raw rhs lst))]
    [sub (lhs rhs)
         (append (shadowed-ids-raw lhs lst) (shadowed-ids-raw rhs lst))]
    [with (name named-expr body)
          (if (member name lst)
              (cons name (append (shadowed-ids-raw named-expr lst)
                                 (shadowed-ids-raw body (cons name lst))))
              (append (shadowed-ids-raw named-expr lst)
                      (shadowed-ids-raw body (cons name lst))))]
    [id (name) empty]))

(define (shadowed-ids a-wae)
  (sort (remove-duplicates (shadowed-ids-raw a-wae empty))
        symbol<?))

(test (shadowed-ids (id 'x))
      '())
(test (shadowed-ids (add (id 'x) (id 'x)))
      '())
(test (shadowed-ids (with 'x (add (num 1) (num 2))
                      (add (id 'x) (id 'y))))
      '())
(test (shadowed-ids (with 'x (with 'x (id 'y) (id 'x))
                      (add (id 'x) (id 'y))))
      '())
(test (shadowed-ids (add (with 'x (add (id 'x) (num 2))
                           (add (id 'x) (id 'x)))
                     (with 'y (sub (num 4) (num 3))
                           (add (id 'y)
                                (with 'y (sub (id 'y) (num 3))
                                      (add (id 'y) (id 'z)))))))
      '(y))
(test (shadowed-ids (with 'x (add (num 1) (num 2))
                      (with 'x (sub (id 'y) (num 3))
                            (add (id 'x) (id 'z)))))
      '(x))
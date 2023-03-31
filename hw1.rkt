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

;Trees
(define-type Tree
  [positive-leaf (val natural?)]
  [negative-leaf (val natural?)]
  [interior-node (left Tree?) (right Tree?)])

(define (contains? t n)
  (type-case Tree t
    [positive-leaf (num) (equal? num n)]
    [negative-leaf (num) (equal? (* -1 num) n)]
    [interior-node (l r) (or (contains? l n)
                             (contains? r n))]))
;test1
(test (contains? (interior-node (interior-node (positive-leaf 5)
                                               (negative-leaf 4))
                                (positive-leaf 3))
                 -5)
      false)
;test2
(test (contains? (interior-node (positive-leaf 5)
                                (negative-leaf 4))
                 -4)
      true)
;test3
(test (contains? (negative-leaf 4)
                 -4)
      true)
;test4
(test (contains? (interior-node (interior-node (negative-leaf 3)
                                               (negative-leaf 4))
                                (interior-node (negative-leaf 5)
                                               (negative-leaf 6)))
                 -5)
      true)
;Smallest
(define (smallest t)
  (type-case Tree t
    [positive-leaf (num) num]
    [negative-leaf (num) (* -1 num)]
    [interior-node (l r) (if (< (smallest l) (smallest r))
                             (smallest l)
                             (smallest r))]))
;test1
(test (smallest (negative-leaf 4)) -4)
;test2
(test (smallest (interior-node (interior-node (positive-leaf 5)
                                              (negative-leaf 4))
                               (positive-leaf 3)))
      -4)
;test3
(test (smallest (interior-node (interior-node (negative-leaf 3)
                                              (negative-leaf 4))
                               (interior-node (negative-leaf 5)
                                              (negative-leaf 6))))
      -6)
;test4
(test (smallest (interior-node (interior-node (positive-leaf 0)
                                              (positive-leaf 1))
                               (interior-node (positive-leaf 2)
                                              (positive-leaf 10000))))
      0)

;Balance
(define (balanced? t)
  (equal? 0 (helper t)))
(define (helper t)
  (type-case Tree t
    [positive-leaf (num) num]
    [negative-leaf (num) (* -1 num)]
    [interior-node (l r) (+ (helper l) (helper r))]))

;test1
(test (balanced? (negative-leaf 4)) false)
;test2
(test (balanced? (interior-node (interior-node (positive-leaf 5)
                                               (negative-leaf 5))
                                (positive-leaf 0)))
      true)
;test3
(test (balanced? (interior-node (interior-node (negative-leaf 3)
                                               (negative-leaf 4))
                                (interior-node (negative-leaf 5)
                                               (negative-leaf 6))))
      false)
;test4
(test (balanced? (interior-node (interior-node (positive-leaf 0)
                                               (positive-leaf 0))
                                (interior-node (positive-leaf 0)
                                               (positive-leaf 0))))
      true)
;test5
(test (balanced? (interior-node (interior-node (negative-leaf 3)
                                               (negative-leaf 4))
                                (interior-node (positive-leaf 3)
                                               (positive-leaf 4))))
      true)
;More Balance
(define (deep-balanced? t)
  (type-case Tree t
    [positive-leaf (v) true]
    [negative-leaf (v) true]
    [interior-node (l r) (and (and (deep-balanced? l)
                                   (deep-balanced? r))
                              (balanced? t))]))

;test1
(test (deep-balanced? (negative-leaf 4)) true)
;test2
(test (deep-balanced? (interior-node (interior-node (positive-leaf 5)
                                                    (negative-leaf 5))
                                     (positive-leaf 0)))
      true)
;test3
(test (deep-balanced? (interior-node (interior-node (negative-leaf 3)
                                                    (negative-leaf 4))
                                     (interior-node (positive-leaf 3)
                                                    (positive-leaf 4))))
      false)
;test4
(test (deep-balanced? (interior-node (interior-node (positive-leaf 0)
                                                    (positive-leaf 0))
                                     (interior-node (positive-leaf 0)
                                                    (positive-leaf 0))))
      true)
;test5
(test (deep-balanced? (positive-leaf 2)) true)
;test6
(test (deep-balanced? (interior-node (negative-leaf 1) (positive-leaf 1))) true)
;Negation
(define (negate t)
  (type-case Tree t
    [positive-leaf (num) (negative-leaf num)]
    [negative-leaf (num) (positive-leaf num)]
    [interior-node (l r) (interior-node (negate l) (negate r))]))

;test1
(test (negate (negative-leaf 3)) (positive-leaf 3))
;test2
(test (negate (positive-leaf 3)) (negative-leaf 3))
;test3
(test (negate (positive-leaf 0)) (negative-leaf 0))
;test4
(test (negate (interior-node (interior-node (negative-leaf 3)
                                            (negative-leaf 4))
                             (interior-node (positive-leaf 3)
                                            (positive-leaf 4))))
      (interior-node (interior-node (positive-leaf 3)
                                    (positive-leaf 4))
                     (interior-node (negative-leaf 3)
                                    (negative-leaf 4))))

;Addition
(define (add t n)
  (type-case Tree t
    [positive-leaf (num) (if (< (+ num n) 0)
                             (negative-leaf (* -1 (+ num n)))
                             (positive-leaf (+ num n)))]
    [negative-leaf (num) (if (> (+ (* -1 num) n) 0)
                             (positive-leaf (+ (* -1 num) n))
                             (negative-leaf (* -1 (+ (* -1 num) n))))]
    [interior-node (l r) (interior-node (add l n) (add r n))]))

;test1
(test (add (negative-leaf 3) 3) (negative-leaf 0))
;test2
(test (add (positive-leaf 3) 3) (positive-leaf 6))
;test3
(test (add (positive-leaf 0) 100) (positive-leaf 100))
;test4
(test (add (interior-node (interior-node (negative-leaf 3)
                                         (negative-leaf 4))
                          (interior-node (positive-leaf 3)
                                         (positive-leaf 4))) 10)
      (interior-node (interior-node (positive-leaf 7)
                                    (positive-leaf 6))
                     (interior-node (positive-leaf 13)
                                    (positive-leaf 14))))
;test5
(test (add (positive-leaf 3) -5) (negative-leaf 2))
;test6
(test (add (interior-node (negative-leaf 2) (positive-leaf 1)) 1)
      (interior-node (negative-leaf 1) (positive-leaf 2)))
;test7
(test (add (interior-node (negative-leaf 2) (positive-leaf 0)) 1)
      (interior-node (negative-leaf 1) (positive-leaf 1)))
;test8
(test (add (interior-node (negative-leaf 0) (positive-leaf 0)) -1)
      (interior-node (negative-leaf 1) (negative-leaf 1)))
;test9
(test (add (interior-node (negative-leaf 0) (positive-leaf 0)) -4)
      (interior-node (negative-leaf 4) (negative-leaf 4)))

;Transmutation
(define (positive-thinking t)
  (type-case Tree t
    [positive-leaf (num) (positive-leaf num)]
    [negative-leaf (num) false]
    [interior-node (l r) (local [(define subl (positive-thinking l)) (define subr (positive-thinking r))]
                           (if (and subl subr)
                               (interior-node subl subr)
                               (if subl
                                   subl
                                   (if subr
                                       subr
                                       false)))
                           )
                   ]))
;test1
(test (positive-thinking (negative-leaf 3)) false)
;test2
(test (positive-thinking (positive-leaf 3)) (positive-leaf 3))
;test3
(test (positive-thinking (interior-node (interior-node (negative-leaf 3)
                                                       (negative-leaf 4))
                                        (interior-node (positive-leaf 3)
                                                       (positive-leaf 4))))
      (interior-node (positive-leaf 3)
                     (positive-leaf 4)))
;test4
(test (positive-thinking (interior-node (positive-leaf 3)
                                        (negative-leaf 4)))
      (positive-leaf 3))
;test5
(test (positive-thinking (interior-node (negative-leaf 3)
                                        (negative-leaf 4)))
      false)
;test6
(test (positive-thinking (interior-node (negative-leaf 3)
                                        (positive-leaf 4)))
      (positive-leaf 4))
;test7
(test (positive-thinking (interior-node (interior-node (positive-leaf 0)
                                                       (positive-leaf 0))
                                        (interior-node (negative-leaf 1)
                                                       (positive-leaf 0))))
      (interior-node (interior-node (positive-leaf 0)
                                    (positive-leaf 0))
                     (positive-leaf 0)))

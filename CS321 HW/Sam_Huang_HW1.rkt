#lang plai
(+ 2 2)


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

; Question 3: Trees

(define-type Tree
    [positive-leaf (val natural?)]
    [negative-leaf (val natural?)]
    [interior-node (left Tree?) (right Tree?)])

(define (contains? t num)
  (type-case Tree t
    [positive-leaf (v) (equal? v num)]
    [negative-leaf (v) (equal? v (- 0 num))]
    [interior-node (l r) (or (contains? l num)
                             (contains? r num))]))

(test (contains? (interior-node (interior-node (positive-leaf 5)
                                                 (negative-leaf 4))
                               (positive-leaf 3))
                -4)
      true)
(test (contains? (interior-node (interior-node (positive-leaf 5)
                                                 (negative-leaf 4))
                               (positive-leaf 3))
                4)
      false)
(test (contains? (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 3))
                2)
      true)
(test (contains? (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 3))
                -2)
      false)
(test (contains? (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 0))
                0)
      true)
(test (contains? (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 3))
                0)
      false)

; Question 4: Smallest
(define (smallest t)
  (type-case Tree t
    [positive-leaf (v) v]
    [negative-leaf (v) (- 0 v)]
    [interior-node (l r) (min (smallest l)
                             (smallest r))]))

(test (smallest (positive-leaf 1))
      1)
(test (smallest (negative-leaf 1))
      -1)
(test (smallest (interior-node (positive-leaf 0)
                                 (negative-leaf 0)))
      0)
(test (smallest (interior-node (positive-leaf 3)
                                 (positive-leaf 5)))
      3)
(test (smallest (interior-node (negative-leaf 3)
                                 (negative-leaf 2)))
      -3)
(test (smallest (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 3)))
      -4)

; Question 5: Balance
(define (sum t)
  (type-case Tree t
    [positive-leaf (v) v]
    [negative-leaf (v) (- 0 v)]
    [interior-node (l r) (+ (sum l)
                             (sum r))]))

(define (balanced? t)
  (equal? (sum t) 0))

(test (balanced? (negative-leaf 0))
      true)
(test (balanced? (negative-leaf 1))
      false)
(test (balanced? (positive-leaf 0))
      true)
(test (balanced? (positive-leaf 1))
      false)
(test (balanced? (interior-node (interior-node (positive-leaf 3)
                                                 (negative-leaf 4))
                               (positive-leaf 1)))
      true)
(test (balanced? (interior-node (interior-node (positive-leaf 2)
                                                 (negative-leaf 4))
                               (positive-leaf 3)))
      false)
(test (balanced? (interior-node (interior-node (positive-leaf 0)
                                                 (negative-leaf 0))
                               (positive-leaf 0)))
      true)

; Question 6: More Balance
(define (deep-balanced? t)
  (type-case Tree t
    [positive-leaf (v) true]
    [negative-leaf (v) true]
    [interior-node (l r) (and (and (deep-balanced? l)
                                   (deep-balanced? r))
                              (balanced? t))]))
(test (deep-balanced? (positive-leaf 1))
      true)
(test (deep-balanced? (negative-leaf 1))
      true)
(test (deep-balanced? (interior-node (positive-leaf 0)
                                     (positive-leaf 0)))
      true)
(test (deep-balanced? (interior-node (positive-leaf 3)
                                     (negative-leaf 3)))
      true)
(test (deep-balanced? (interior-node (positive-leaf 0)
                                     (negative-leaf 3)))
      false)
(test (deep-balanced? (interior-node (interior-node (positive-leaf 0)
                                                 (negative-leaf 0))
                               (positive-leaf 0)))
      true)
(test (deep-balanced? (interior-node (interior-node (positive-leaf 1)
                                                 (negative-leaf 1))
                               (positive-leaf 0)))
      true)
(test (deep-balanced? (interior-node (interior-node (positive-leaf 1)
                                                 (negative-leaf 1))
                               (positive-leaf 1)))
      false)
(test (deep-balanced? (interior-node (interior-node (negative-leaf 0)
                                                 (negative-leaf 0))
                                     (interior-node (positive-leaf 3)
                                                 (negative-leaf 3))))
      true)
(test (deep-balanced? (interior-node (interior-node (negative-leaf 0)
                                                 (negative-leaf 0))
                                     (interior-node (positive-leaf 4)
                                                 (negative-leaf 3))))
      false)

; Question 7: Negation
(define (negate t)
  (type-case Tree t
    [positive-leaf (v) (negative-leaf v)]
    [negative-leaf (v) (positive-leaf v)]
    [interior-node (l r) (interior-node (negate l)
                                        (negate r))]))

(test (negate (positive-leaf 1))
      (negative-leaf 1))
(test (negate (negative-leaf 1))
      (positive-leaf 1))
(test (negate (interior-node (interior-node (positive-leaf 0)
                                            (negative-leaf 4))
                               (positive-leaf 3)))
      (interior-node (interior-node (negative-leaf 0)
                                    (positive-leaf 4))
                     (negative-leaf 3)))

; Question 8: Addition
(define (add t number)
  (type-case Tree t
    [positive-leaf (v) (if (< number (- 0 v))
                           (negative-leaf (- (- 0 number) v))
                           (positive-leaf (+ v number)))]
    [negative-leaf (v) (if (< number v)
                           (negative-leaf (- v number))
                           (positive-leaf (- number v)))]
    [interior-node (l r) (interior-node (add l number)
                                        (add r number))]))

(test (add (positive-leaf 1) 2)
      (positive-leaf 3))
(test (add (negative-leaf 2) 1)
      (negative-leaf 1))
(test (add (negative-leaf 2) 3)
      (positive-leaf 1))
(test (add (negative-leaf 2) 2)
      (positive-leaf 0))
(test (add (interior-node (interior-node (positive-leaf 1)
                                         (negative-leaf 4))
                          (negative-leaf 3))
           3)
      (interior-node (interior-node (positive-leaf 4)
                                    (negative-leaf 1))
                     (positive-leaf 0)))
(test (add (interior-node (interior-node (positive-leaf 1)
                                         (negative-leaf 4))
                          (negative-leaf 3))
           3)
      (interior-node (interior-node (positive-leaf 4)
                                    (negative-leaf 1))
                     (positive-leaf 0)))
(test (add (interior-node (interior-node (positive-leaf 1)
                                         (negative-leaf 4))
                          (positive-leaf 3))
           -3)
      (interior-node (interior-node (negative-leaf 2)
                                    (negative-leaf 7))
                     (positive-leaf 0)))

; Question 9: Transmutation
(define (positive-thinking t)
  (type-case Tree t
    [positive-leaf (v) (positive-leaf v)]
    [negative-leaf (v) false]
    [interior-node (l r) (cond
                           [(equal? false (positive-thinking l))
                            (positive-thinking r)]
                           [(equal? false (positive-thinking r))
                            (positive-thinking l)]
                           [else (interior-node (positive-thinking l)
                                                (positive-thinking r))])]))

(test (positive-thinking (positive-leaf 1))
      (positive-leaf 1))
(test (positive-thinking (negative-leaf 1))
      false)
(test (positive-thinking (interior-node (negative-leaf 0)
                                        (negative-leaf 0)))
      false)
(test (positive-thinking (interior-node (positive-leaf 0)
                                     (positive-leaf 0)))
      (interior-node (positive-leaf 0)
                     (positive-leaf 0)))
(test (positive-thinking (interior-node (positive-leaf 3)
                                     (negative-leaf 3)))
      (positive-leaf 3))
(test (positive-thinking (interior-node (negative-leaf 3)
                                     (positive-leaf 3)))
      (positive-leaf 3))
(test (positive-thinking (interior-node (negative-leaf 0)
                                     (negative-leaf 3)))
      false)
(test (positive-thinking (interior-node (interior-node (positive-leaf 1)
                                                       (negative-leaf 4))
                                        (positive-leaf 3)))
      (interior-node (positive-leaf 1) (positive-leaf 3)))
(test (positive-thinking (interior-node (positive-leaf 3)
                                        (interior-node (positive-leaf 1)
                                                       (negative-leaf 4))))
      (interior-node (positive-leaf 3) (positive-leaf 1)))
(test (positive-thinking (interior-node (negative-leaf 3)
                                        (interior-node (negative-leaf 1)
                                                       (negative-leaf 4))))
      false)
(test (positive-thinking (interior-node (interior-node (negative-leaf 1)
                                                       (negative-leaf 2))
                                        (interior-node (positive-leaf 3)
                                                       (negative-leaf 4))))
      (positive-leaf 3))
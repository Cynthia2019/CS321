#lang plai/gc2/mutator

(allocator-setup "lec13.rkt" 200)

(define cons0 (cons 2 (cons 3 empty)))
(define cons1 (cons 1 cons0))

(test/location=? cons0 (rest cons1))
(test/value=? (first cons1) 1)

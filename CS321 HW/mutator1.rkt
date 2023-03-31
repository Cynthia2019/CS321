#lang plai/gc2/mutator

(allocator-setup "gc.rkt" 30)
(define (count-down n)
  (cond
    [(zero? n) (count-down 20)]
    [else (count-down (- n 1))]))
(count-down 0)

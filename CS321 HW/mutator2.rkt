#lang plai/gc2/mutator

(allocator-setup "gc.rkt" 130)
(define (mk-list n)
  (cond
    [(zero? n) '()]
    [else (cons n (mk-list (- n 1)))]))
(define (forever)
  (mk-list 10)
  (forever))
(forever)

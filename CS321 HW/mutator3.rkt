#lang plai/gc2/mutator

(allocator-setup "gc.rkt" 180)
(define (proc-lst n)
  (cond
    [(zero? n) (lambda () 0)]
    [else (let ([n1 (proc-lst (- n 1))])
            (lambda () (+ (n1) n)))]))
(define (forever)
  ((proc-lst 10))
  (forever))
(forever)

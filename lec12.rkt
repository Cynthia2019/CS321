#lang plai/gc2/collector

(print-only-errors)

#|
heap:    | 1 | ??? | ??? | ??? | ...
flat:    ... | 'flat | <payload>   | ...
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
closure: ... | 'clos | <code-ptr>  | <fv0> | <fv1> | ... | ...
|#


;; invariant: address 0 holds the allocation pointer
(define (init-allocator)
  (heap-set! 0 1))

(define (malloc n)
  (define address (heap-ref 0))
  (heap-set! 0 (+ address n))
  (when (>= (+ address n) (heap-size))
    (error 'malloc "out of memory"))
  address)

#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> location
(define (gc:alloc-flat value)
  (define address (malloc 2))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : location -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : location -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected a flat @ ~a" address))
  (heap-ref (+ address 1)))


#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> location
(define (gc:cons root1 root2)
  (define address (malloc 3))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : location -> boolean
(define (gc:cons? address)
  (equal? 'cons (heap-ref address)))
;; gc:first : location -> location
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected pair @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : location -> location
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected pair @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : location location -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected pair @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : location location -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected pair @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) -> location
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 2 (length free-vars))))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (for ([fv (in-list free-vars)]
        [i (in-range (length free-vars))])
    (heap-set! (+ address 2 i) (read-root fv)))
  address)
;; gc:closure? : location -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : location -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : location integer -> location
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 2 i)))

;; ----------------------------------------------------------------------
;; Tests

(test (let ([h (vector 'x 'x 'x 'x 'x 'x)]) ; size 6
        (with-heap h
          (init-allocator)
          (gc:alloc-flat 5)
          h))
      (vector 3 'flat 5 'x 'x 'x))

(test (let ([h (vector 'x 'x 'x 'x 'x 'x)]) ; size 6
        (with-heap h
          (init-allocator)
          (define f (gc:alloc-flat 5))
          (gc:deref f)))
      5)
(test (let ([h (vector 'x 'x 'x 'x 'x 'x 'x 'x 'x 'x 'x 'x 'x 'x)]) ; size 14
        (with-heap h
          (init-allocator)
          (define f (gc:alloc-flat 5))
          (define g (gc:alloc-flat 6))
          (gc:cons (simple-root f) (simple-root g))
          h))
      (vector 8 'flat 5 'flat 6 'cons 1 3 'x 'x 'x 'x 'x 'x))

;; + mutator tests (lec13-mutator.rkt)
;; + random mutator tests (lec13-random-mutator.rkt)

#lang plai/gc2/collector

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
heap:    | 'free | 'free | 'free | ...                          NEW!
flat:    ... | 'flat | <payload>   | ...
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...  
|#

(define (init-allocator) 
  (heap-set! 0 (+ 4 (/ (- (heap-size) 4) 2)))
  (heap-set! 1 true)
  (heap-set! 2 4)
  (heap-set! 3 4)
  (for ([i (in-range 4 (heap-size))])
    (heap-set! i 'free)))

;;validate pointer 
(define (validate-pointer a)
  (unless (and (integer? a)
               (>= a 0)
               (< a (heap-size))
               (member (heap-ref a) '(flat cons clos)))
    (error 'validate-pointer "invalid pointer @ ~a" a)))

;;validate heap
(define (validate-heap)
  (define (loop i)
    (when (< i (heap-ref 0))
      (case (heap-ref i)
        [(flat) (loop (+ i 2))]
        [(cons) (validate-pointer (heap-ref (+ i 1)))
                (validate-pointer (heap-ref (+ i 2)))
                (loop (+ i 3))]
        [(clos) (for ([j (in-range (heap-ref (+ i 2)))])
                  (validate-pointer (heap-ref (+ i 3 j))))
                (loop (+ i 3 (heap-ref (+ i 2))))]
        [(free) (loop (+ i 1))]
        [else (error 'validate-heap "unexpected tag @ ~a" i)])))
  (loop (if (heap-ref 1)
            (+ 4 (/ (- (heap-size) 4) 2))
            4)))

;; malloc : size root1 root2 -> address
(define (malloc n root1 root2)
  (define address (heap-ref 0))
  (if (heap-ref 1)
      (cond
        [(>= (+ address n) (heap-size))
         (collect-garbage root1 root2)
         (define address (heap-ref 0))
         (heap-set! 0 (+ address n))
         (if (heap-ref 1)
             (when (>= (heap-ref 0) (heap-size))
               (error 'malloc "out of memory"))
             (when (>= (heap-ref 0) (+ 4 (/ (- (heap-size) 4) 2)))
               (error 'malloc "out of memory")))
         address]
        [else (heap-set! 0 (+ address n))
              address])
      (cond
        [(>= (+ address n) (+ 4 (/ (- (heap-size) 4) 2)))
         (collect-garbage root1 root2)
         (define address (heap-ref 0))
         (heap-set! 0 (+ address n))
         (if (heap-ref 1)
             (when (>= (heap-ref 0) (heap-size))
               (error 'malloc "out of memory"))
             (when (>= (heap-ref 0) (+ 4 (/ (- (heap-size) 4) 2)))
               (error 'malloc "out of memory")))
         address]
        [else (heap-set! 0 (+ address n))
              address])
      ))
;;collect0-garbage
(define (collect-garbage root1 root2)
  (add-roots (get-root-set))
  (add-roots root1)
  (add-roots root2)
  (traverse-to!)
  (swap-space!))

(define (add-roots roots)
  (cond [(false? roots) (void)]
        [(root? roots)  (define right (heap-ref 3))
                        (if (symbol=? 'f (heap-ref (read-root roots)))
                            (set-root! roots (heap-ref (+ (read-root roots) 1)))
                            (begin (add-loc (read-root roots))
                                   (set-root! roots right)))]
        [(list? roots)  (for-each add-roots roots)]
        [else (error 'add-roots "unknown roots: ~a" roots)]))

(define (add-loc ptr)
  (define left (heap-ref 2))
  (define right (heap-ref 3))
  (case (heap-ref ptr)
    [(free) (error 'add-loc "dangling pointer! ~a" ptr)]
    [(flat) (heap-set! right 'flat)
            (heap-set! (+ right 1) (heap-ref (+ ptr 1)))
            (heap-set! ptr 'f)
            (heap-set! (+ ptr 1) right)
            (heap-set! 3 (+ right 2))]
    [(cons) (heap-set! right 'cons)
            (heap-set! (+ right 1) (heap-ref (+ ptr 1)))
            (heap-set! (+ right 2) (heap-ref (+ ptr 2)))
            (heap-set! ptr 'f)
            (heap-set! (+ ptr 1) right)
            (heap-set! 3 (+ right 3))]
    [(clos) (heap-set! right 'clos)
            (heap-set! (+ right 1) (heap-ref (+ ptr 1)))
            (heap-set! (+ right 2) (heap-ref (+ ptr 2)))
            (define n-var (heap-ref (+ ptr 2)))
            (for ([i (in-range n-var)])
              (heap-set! (+ right 3 i) (heap-ref (+ ptr 3 i))))
            (heap-set! ptr 'f)
            (heap-set! (+ ptr 1) right)
            (heap-set! 3 (+ right 3 n-var))]
    [else (error 'add-loc "found an unknown tag @ ~a" ptr)]))

(define (traverse-to!)
  (if (> (heap-ref 2) (heap-ref 3))
      (error 'traverse-to! "left greater than right @ ~a ~a" (heap-ref 2) (heap-ref 3))
      (if (equal? (heap-ref 2) (heap-ref 3))
          void
          (traverse-var!))))

(define (traverse-var!)
  (define left (heap-ref 2))
  (define right (heap-ref 3))
  (case (heap-ref left)
    [(free) (error 'traverse-var! "invalid variant @ ~a" (heap-ref 2))]
    [(flat) (heap-set! 2 (+ (heap-ref 2) 2))
            (traverse-to!)]
    [(cons) (define first-ptr (+ left 1))
            (define rest-ptr (+ left 2))
            (case (heap-ref (heap-ref first-ptr))
              [(f) (heap-set! (+ left 1) (heap-ref (+ (heap-ref first-ptr) 1)))]
              [else (define temp (heap-ref 3))
                    (add-loc (heap-ref first-ptr))
                    (heap-set! (+ left 1) temp)])
            (case  (heap-ref (heap-ref rest-ptr))
              [(f) (heap-set! (+ left 2) (heap-ref (+ (heap-ref rest-ptr) 1)))]
              [else (define temp (heap-ref 3))
                    (add-loc (heap-ref rest-ptr))
                    (heap-set! (+ left 2) temp)])
            (heap-set! 2 (+ (heap-ref 2) 3))
            (traverse-to!)]
    [(clos) (define n-var (heap-ref (+ left 2)))
            (for ([i (in-range n-var)])
              (define fv-ptr (+ left 3 i))
              (case  (heap-ref (heap-ref fv-ptr))
                [(f) (heap-set! (+ left 3 i) (heap-ref (+ (heap-ref fv-ptr) 1)))]
                [else  (define temp (heap-ref 3)) 
                       (add-loc (heap-ref fv-ptr))
                       (heap-set! (+ left 3 i) temp)]))
            (heap-set! 2 (+ (heap-ref 2) 3 n-var))
            (traverse-to!)]
    [else (error 'traverse-var! "found an unknown tag @ ~a" left)]))

(define (swap-space!)
  (define start-left 4)
  (define start-right (+ 4 (/ (- (heap-size) 4) 2)))
  (heap-set! 0 (heap-ref 3))
  (define (reset-left-to-right!)
    (heap-set! 2 start-right)
    (heap-set! 3 start-right))
  (define (reset-right-to-left!)
    (heap-set! 2 start-left)
    (heap-set! 3 start-left))
  (if (heap-ref 1)
      (reset-left-to-right!)
      (reset-right-to-left!))
  (heap-set! 1 (not (heap-ref 1))))
 

;; ----------------------------------------------------------------------

#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> address
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : location -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : location -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))


#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> location
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : location -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : location -> location
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : location -> location
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : location location -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : location location -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) ->  location
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars))
                          free-vars #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([i  (in-range (length free-vars))]
        [fv (in-list free-vars)])
    (heap-set! (+ address 3 i) (read-root fv)))
  address)
;; gc:closure? :  location -> boolean
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
  (heap-ref (+ address 3 i)))

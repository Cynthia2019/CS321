#lang plai

(let ([mk-rec (lambda (f)
                (let ([bob
                    (lambda (fred)
                      (let ([fac (lambda (x)
                                   ((fred fred) x))])
                        (f fac)))])
               (bob bob)))])
  (let ([fac (mk-rec (lambda (fac)
                       (lambda (n)
                         (if (zero? n)
                             1
                             (* n (fac (- n 1)))))))])
    (fac 5)))

(let ([mk-rec (lambda (f)
                (let ([bob
                    (lambda (fred)
                      (let ([fac (lambda (x)
                                   ((fred fred) x))])
                        (f fac)))])
               (bob bob)))])
  (let ([fib (mk-rec (lambda (fib)
                       (lambda (n)
                         (cond [(= n 0) 1]
                               [(= n 1) 1]
                               [else (+ (fib (- n 1))
                                        (fib (- n 2)))]))))]
        )
    (fib 5)))

(let ([mk-rec (lambda (f)
                (let ([bob
                    (lambda (fred)
                      (let ([fac (lambda (x)
                                   ((fred fred) x))])
                        (f fac)))])
               (bob bob)))])
  (let ([sum (mk-rec
              (lambda (sum)
                (lambda (lon)
                  (if (empty? lon)
                      0
                      (+ (first lon)
                         (sum (rest lon)))))))])
    (sum '(1 2 3 4 5))))




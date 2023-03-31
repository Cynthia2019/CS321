#lang plai

(require plai/random-mutator)

(save-random-mutator "tmp.rkt" "gc.rkt" #:gc2? #t)

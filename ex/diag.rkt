#lang racket

(require "composable.rkt")

(define*
  [(((diag x y z) `fst) `fst) = x]
  [(((diag x y z) `snd) `snd) = y]
  [  (diag x y z)             = z])

(define*
  [(((diag* x y z) `fst) `fst) = x]
  [(((diag* x y z) `snd) `snd) = y]
  [(((diag* x y z) `fst) `snd) = ((z `fst) `snd)]
  [(((diag* x y z) `snd) `fst) = ((z `snd) `fst)])

(define*
  [((quad `fst) `fst) = 1]
  [((quad `fst) `snd) = 2]
  [((quad `snd) `fst) = 3]
  [((quad `snd) `snd) = 4])

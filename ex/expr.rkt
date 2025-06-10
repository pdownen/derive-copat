#lang racket

(require "composable.rkt")

(define-object
  [(arith `eval n) (try-if (number? n))
   = n]
  [(arith `eval `(add ,l ,r))
   = (+ (arith `eval l) (arith `eval r))]
  [(arith `eval `(mul ,l ,r))
   = (* (arith `eval l) (arith `eval r))])

(define expr0 `(add 1 (mul 2 3)))

(define-object
  [(arith-wrong `eval `(neg ,e))
   = (- (arith-wrong `eval e))]
  [(arith-wrong `eval e) = (arith `eval e)])

(define expr1 `(add 1 (neg (mul 2 3))))

(define arith-ext
  (arith `compose
   (object
    [(self `eval `(neg ,e))
     = (- (self `eval e))])))

(define-object
  [(arith-ext* `eval n) (try-if (number? n))
   = n]
  [(arith-ext* `eval `(add ,l ,r))
   = (+ (arith-ext* `eval l) (arith-ext* `eval r))]
  [(arith-ext* `eval `(mul ,l ,r))
   = (* (arith-ext* `eval l) (arith-ext* `eval r))]
  [(arith-ext* `eval `(neg ,e))
   = (- (arith-ext* `eval e))])

(define (with-env dict)
  (object [(_ `env) = dict]))

(define (alg dict)
  (arith-ext `compose
   (with-env dict)
   (object
    [(self `eval x) (try-if (symbol? x))
     = (dict-ref (self `env) x)])))

(define (alg* dict)
  (object
   [(self `eval n) (try-if (number? n)) = n]
   [(self `eval `(add ,l ,r))
    = (+ (self `eval l) (self `eval r))]
   [(self `eval `(mul ,l ,r))
    = (* (self `eval l) (self `eval r))]
   [(self `eval `(neg ,e))
    = (- (self `eval e))]
   [(_ `env) = dict]
   [(self `eval x) (try-if (symbol? x))
    = (dict-ref (self `env) x)]))

(define env-xy `((x . 10) (y . 20)))

(define expr2 `(add x (neg (mul 2 y))))

#lang plai

(define table empty)

(define (remember v)
  (local [(define n (length table))]
    (begin
      (set! table (append table (list v)))
      n)))

(define (lookup key)
  (list-ref table key))

(define (web-read/k prompt cont)
  (local [(define key (remember cont))]
    `(,prompt "To continue, call resume/k with " ,key " and value")))

(define (resume/k key val)
  (local [(define cont (lookup key))]
    (cont val)))

(define (do-g cont)
  (web-read/k "First" (lambda (v1)
                        (web-read/k "Second" (lambda (v2)
                                               (cont (+ v1 v2)))))))

(define (g)
  (do-g identity))
#lang plai

; Programming Languages
; Homework Assignment 3
; 20170504 Juan Lee




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                                                  ;
;                                  CODES GIVEN BY PROFESSOR                                        ;
;                                                                                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                                                  ;
;                                    CODES FOR ASSIGNMENT 3                                        ;
;                                                                                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; WAE abstract syntax trees

; modified for Assignment 3
; constructor 'num' is changed for holding list of numbers instead single number.
(define-type PWAE
  [num (lon list?)]
  [add  (left PWAE?) (right PWAE?)]
  [sub  (left PWAE?) (right PWAE?)]
  [with (name symbol?) (init PWAE?) (body PWAE?)]
  [id   (name symbol?)]
  [pooh (exprs list?) (op symbol?)])

; parse-sexpr : sexpr -> WAE
;; to convert s-expressions into WAEs

; modified for Assignment 3
; parsing for num to hold list of numbers
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num (list sexp))]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(list 'pooh l ... f) (pooh (map parse-sexpr l) f)]
    [(list a ...) (num a)]
    [(? symbol?) (id sexp)]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument

; map-subst : list-of-PWAE symbol PWAE -> list-of-PWAE
; substitute all elements in list with symbol and PWAE
(define (map-subst l from to)
  (define (f n)
    (subst n from to))
  (map f l))

; modified for Assignment 3
(define (subst expr from to)
  (type-case PWAE expr
    [num (l) expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [pooh (l f) (pooh (map-subst l from to) f)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]))

;; evaluates WAE expressions by reducing them to numbers

; reduce : list-of-numbers (number number -> number) -> number
; to reduce the elements with given operator
(define (reduce l f init)
  (cond
    [(> (length l) 1) (reduce (cons (f (first l) (first (rest l))) (rest (rest l))) f init)]
    [(= (length l) 1) l]
    [else init]))

; modified for Assignment 3
; type-case for add and sub is changed for applying bin-op
(define (eval expr)
  (type-case PWAE expr
    [num (n) n]
    [add (l r) (bin-op + (eval l) (eval r))]
    [sub (l r) (bin-op - (eval l) (eval r))]
    [pooh (l f) (cond
                  [(symbol=? f '+) (first (reduce (map eval l) (lambda (a b) (bin-op + a b)) '(0)))]
                  [(symbol=? f '-) (first (reduce (map eval l) (lambda (a b) (bin-op - a b)) '(0)))])]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]))

; run : string -> listof number
;; evaluate a WAE program contained in a string
(define (run str)
  (eval (parse str)))

;bin-op : (number number -> number) (listof number) (listof number) -> (listof number))
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists, and return the list of all of the results
(define (bin-op op ls rs)
  (define (helper l rs)
    ;; f : number -> number
    (define (f n)
      (op l n))
    (map f rs))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))

; tests for Assignment 3

(test (run "{+ {2 1} {3 4}}") '(5 6 4 5))
(test (run "{+ {- {+ 1 3} 2} {10 -10}}") '(12 -8))

(test (run "{+ 3 7}") '(10))
(test (run "{- 10 {3 5}}") '(7 5))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))

(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))

(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 -}") '(-1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {x 20} {pooh 1 x +}}} {with {y 10} {pooh x y -}}}") '(11))
(test (run "{with {x {pooh 1 2 3 4 5 +}} x}") '(15))
(test (run "{pooh {with {x {pooh {1 2} {3 4} 1 +}} x} 2 3 -}") '(0 1 1 2))
(test (run "{pooh 1 2 3 4 5 +}") '(15))
(test (run "{pooh {1 2 3} {4 5} -}") '(-3 -4 -2 -3 -1 -2))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh 1 2 3 4 +}") '(10))
(test (run "{pooh {3 4} {-4 0} 5 +}") '(4 8 5 9))
(test (run "{pooh 1 2 3 4 -}") '(-8))
(test (run "{pooh {4 1} 1 {5 6 7} -}") '(-2 -3 -4 -5 -6 -7))
(test (run "{+ {pooh 1 {4 9} -3 {2 0 1} +} {- {pooh {3 4} {2} -} 4}}") '(1 2 -1 0 0 1 6 7 4 5 5 6))
(test (run "{pooh 1 {pooh 1 2 -} 3 +}") '(3))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{pooh {2 1} {3 4} +}") '(5 6 4 5))
(test (run "{with {x {1 2}} {pooh x {+ {1 2} 1} -}}") '(-1 -2 0 -1))
(test (run "{with {x {1 2}} {pooh x {pooh {1 2} 1 +} -}}") '(-1 -2 0 -1))
(test (run "{+ {+ {pooh 1 2 -} 5} {pooh 3 4 -}}") '(3))
(test (run "{pooh {+ {pooh 1 2 -} 5} {- 3 4} +}") '(3))
(test (run "{pooh {pooh {pooh 1 2 -} 5 +} {pooh 3 4 -} +}") '(3))
(test (run "{+ {+ {- 1 2} 5} {- 3 4}}") '(3))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {y {1 -2}} {pooh 1 y 2 -}}} {+ x x}}") '(-4 -1 -1 2))
(test (run "{pooh {0 1} {2 3} {4 5} 6 +}") '(12 13 13 14 13 14 14 15))
(test (run "{with {x {pooh 8 7 -}} {with {x 10} {+ x 3}}}") '(13))
(test (run "{pooh {pooh 1 2 {2 3} {1 2} -} {2 1 3 2} {1 2} +}") '(-1 0 -2 -1 0 1 -1 0 -2 -1 -3 -2 -1 0 -2 -1 -2 -1 -3 -2 -1 0 -2 -1 -3 -2 -4 -3 -2 -1 -3 -2))
(test (run "{with {x {pooh {1 2} {2 3} 1 +}} {pooh x 1 2 +}}") '(7 8 8 9))
(test (run "{with {x {pooh 3 4 -}} {pooh {+ {pooh 1 2 -} 5} x +}}") '(3))
(test (run "{with {x {with {x 20} {pooh 1 x +}}} {with {y 10} {pooh x y -}}}") '(11))
(test (run "{with {x {pooh 1 2 3 4 5 +}} x}") '(15))
(test (run "{pooh {with {x {pooh {1 2} {3 4} 1 +}} x} 2 3 -}") '(0 1 1 2))
(test (run "{pooh {1 2 3} {4 5} -}") '(-3 -4 -2 -3 -1 -2))
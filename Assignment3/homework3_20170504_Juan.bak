#lang plai

; Programming Languages
; Homework Assignment 2
; author@ 20170504 Juan Lee (juanlee@kaist.ac.kr)

; type-WAE
; defined type for num, add, sub, with, and id
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?) (named-expr WAE?) (body WAE?)]
  [id (name symbol?)])


; subst: WAE symbol number -> WAE
; to substitute the symbols in WAE as number
(define (subst wae x val)
  (type-case WAE wae
    [num (n) wae]
    [add (l r) (add (subst l x val) (subst r x val))]
    [sub (l r) (sub (subst l x val) (subst r x val))]
    [with (y i b) (with y
                        (subst i x val)
                        (if (symbol=? y x) b
                            (subst b x val)))]
    [id (s) (if (symbol=? s x) (num val) wae)]))

(test (subst (with 'y (num 17) (id 'x)) 'x 10) (with 'y (num 17) (num 10)))
(test (subst (with 'y (id 'x) (id 'y)) 'x 10) (with 'y (num 10) (id 'y)))
(test (subst (with 'x (id 'y) (id 'x)) 'x 10) (with 'x (id 'y) (id 'x)))


; interp: WAE -> number
; to interprete the WAE
(define (interp wae)
  (type-case WAE wae
    [num (n) n]
    [add (l r) (+ (interp l) (interp r))]
    [sub (l r) (- (interp l) (interp r))]
    [with (x i b) (interp (subst b x (interp i)))]
    [id (s) (error 'interp "free identifier")]))

(test (interp (add (num 1) (add (num 2) (num 3)))) 6)
(test (interp (with 'x (num 10) (add (num 1) (id 'x)))) 11)


;;;;;;;;;; No. 1 ;;;;;;;;;;


; symbol<? : symbol symbol -> boolean
; to determine the right one is positioned later in alphabetical order.
(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))

(test (symbol<? 'a 'b) #t)
(test (symbol<? 'ate 'ape) #f)


; fi-subst: WAE symbol WAE -> WAE
; to substitute the symbols in WAE as given uninterpreted WAE
(define (fi-subst wae x val)
  (type-case WAE wae
    [num (n) wae]
    [add (l r) (add (fi-subst l x val) (fi-subst r x val))]
    [sub (l r) (sub (fi-subst l x val) (fi-subst r x val))]
    [with (y i b) (with y
                        (fi-subst i x val)
                        (if (symbol=? y x) b
                            (fi-subst b x val)))]
    [id (s) (if (symbol=? s x) val wae)]))

(test (fi-subst (with 'y (num 17) (id 'x)) 'x (num 10)) (with 'y (num 17) (num 10)))
(test (fi-subst (with 'y (id 'x) (id 'y)) 'x (num 10)) (with 'y (num 10) (id 'y)))
(test (fi-subst (with 'x (id 'y) (id 'x)) 'x (num 10)) (with 'x (id 'y) (id 'x)))


; fi-helper: WAE -> list-of-symbols
; to take the free identifiers out of given WAE with allowing duplicate in unsorted form
(define (fi-helper wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (fi-helper l) (fi-helper r))]
    [sub (l r) (append (fi-helper l) (fi-helper r))]
    [with (x i b) (append (fi-helper i) (fi-helper (fi-subst b x i)))]
    [id (s) (list s)]))

(test (fi-helper (with 'x (num 4) (add (id 'x) (sub (num 3) (id 'x))))) empty)
(test (fi-helper (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (fi-helper (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(t t y t b a))


; free-ids: WAE -> list-of-symbols
; to sort and get rid of duplicates from the result of fi-helper
(define (free-ids wae)
  (sort (remove-duplicates (fi-helper wae))
        symbol<?))

(test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
(test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
(test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
(test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))


;;;;;;;;;; No. 2 ;;;;;;;;;;


; binding-ids: WAE -> list-of-symbols
; to take the binding identifiers out of given WAE with allowing duplicates in unsorted form
(define (bngi-helper wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (bngi-helper l) (bngi-helper r))]
    [sub (l r) (append (bngi-helper l) (bngi-helper r))]
    [with (x i b) (append (list x) (bngi-helper b) (bngi-helper i))]
    [id (s) empty]))

(test (bngi-helper (add (num 3) (sub (id 'x) (id 'y)))) empty)
(test (bngi-helper (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(y x))
(test (bngi-helper (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(z w w z))


; binding-ids: WAE -> list-of-symbols
; to sort and remove duplicates from the result of bngi-helper
(define (binding-ids wae)
  (sort (remove-duplicates (bngi-helper wae))
        symbol<?))

(test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
(test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))


;;;;;;;;;; No. 3 ;;;;;;;;;;


; bi-helper: WAE -> list-of-symbols
; to take the bound identifiers out of given WAE with allowing duplicate in unsorted form
(define (bi-helper wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (bi-helper l) (bi-helper r))]
    [sub (l r) (append (bi-helper l) (bi-helper r))]
    [with (x i b) (append (bi-helper i) (bi-helper b) (if (member x (free-ids b)) (list x) empty))]
    [id (s) empty]))

(test (bi-helper (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bi-helper (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(x a))


; bound-identifiers: WAE -> list-of-symbols
; to sort and get rid of duplicates from the result of bi-helper
(define (bound-ids wae)
  (sort (remove-duplicates (bi-helper wae))
        symbol<?))

(test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
(test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))
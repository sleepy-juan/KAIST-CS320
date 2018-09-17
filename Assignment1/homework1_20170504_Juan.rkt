#lang plai

; Programming Languages
; Homework Assignment 1
; author@ 20170504 Juan Lee (juanlee@kaist.ac.kr)


;;;;;;;;;; No. 1 ;;;;;;;;;;

; area-square : integer -> integer
; to compute the area of square with the length of side.

(define (area-square length)
  (* length length))

(test (area-square 10) 100)
(test (area-square 19) 361)


;;;;;;;;;; No. 2 ;;;;;;;;;;

; volume-cuboid : integer integer integer -> integer
; to compute the volume of cuboid with given the lengths of three sides

(define (volume-cuboid s1 s2 s3)
  (* s1 s2 s3))

(test (volume-cuboid 1 2 3) 6)
(test (volume-cuboid 3 3 4) 36)


;;;;;;;;;; No. 3 ;;;;;;;;;;

; is-multiple-of? : integer integer -> boolean
; to return whether the first integer is a multiple of the second one or not.

(define (is-multiple-of? f s)
  (= (remainder f s) 0))

(test (is-multiple-of? 6 3) #t)
(test (is-multiple-of? 7 4) #f)


;;;;;;;;;; No. 4 ;;;;;;;;;;

; factorial : integer -> integer
; to compute the factorial of given integer

(define (factorial n)
  (define (helper n val)
    (if (= n 1) val (helper (- n 1) (* val n))))
  (helper n 1))

(test (factorial 4) 24)
(test (factorial 5) 120)


;;;;;;;;;; No. 5 ;;;;;;;;;;

; fibonacci : integer -> integer
; to compute the n-th fibonacci number where n is given

(define (fibonacci n)
  (define (helper n a b)
    (if (= n 1) b (helper (- n 1) b (+ a b))))
  (helper n 0 1))

(test (fibonacci 3) 2)
(test (fibonacci 8) 21)


;;;;;;;;;; No. 6 ;;;;;;;;;;

; COURSE is a type with three constructor CS320, CS311 and CS330.
; CS320 has two attributes: number of quizzes and number of homeworks.
; CS311 has one attribute: number of homeworks.
; CS330 has two attributes: number of projects and number of homeworks.

(define-type COURSE
  [CS320 (quiz number?)
         (homework number?)]
  [CS311 (homework number?)]
  [CS330 (project number?)
         (homework number?)])

(define cs320 (CS320 5 10))
(test (CS311? cs320) #f)
(test (CS320-quiz cs320) 5)


;;;;;;;;;; No. 7 ;;;;;;;;;;

; total-assignments: COURSE -> integer
; to return the total number of quizzes, homeworks, and projects of given course

(define (total-assignments course)
  (type-case COURSE course
    [CS320 (q h) (+ q h)]
    [CS311 (h) h]
    [CS330 (p h) (+ p h)]))

(define cs311 (CS311 7))
(define cs330 (CS330 1 8))

(test (total-assignments cs320) 15)
(test (total-assignments cs311) 7)
(test (total-assignments cs330) 9)


;;;;;;;;;; No. 8 ;;;;;;;;;;

; get-homework: COURSE -> integer
; to return the number of homework of given course

(define (get-homework course)
  (type-case COURSE course
    [CS320 (q h) h]
    [CS311 (h) h]
    [CS330 (p h) h]))

(test (get-homework cs320) 10)
(test (get-homework cs311) 7)
(test (get-homework cs330) 8)

; total-homework: list of COURSE -> integer
; to return the total number of homeworks of given courses

(define (total-homework courses)
  (if (empty? courses) 0
      (+ (get-homework (first courses)) (total-homework (rest courses)))))

(test (total-homework (list cs320 cs311)) 17)
(test (total-homework (list cs320 cs330)) 18)
(test (total-homework (list cs320 cs330 cs311)) 25)


;;;;;;;;;; No. 9 ;;;;;;;;;;

; my-map: function list -> list of numbers
; to produce the new list of computed elements by given function from given elements

(define (my-map f l)
  (if (empty? l) empty
      (cons (f (first l)) (my-map f (rest l)))))

(test (my-map (lambda (x) (+ 1 x)) (list 1 2 3)) (list 2 3 4))
(test (my-map (lambda (x) (* x x)) (list 2 3 4)) (list 4 9 16))


;;;;;;;;;; No. 10 ;;;;;;;;;;

; my-filter: function list -> list of numbers
; to produce the new list of elements which satisfy the given function

(define (my-filter f l)
  (if (empty? l) empty
      (if (f (first l))
          (cons (first l) (my-filter f (rest l)))
          (my-filter f (rest l)))))

(test (my-filter (lambda (x) (> x 0)) (list -1 0 4 2 -5 2 3 -1)) (list 4 2 2 3))
(test (my-filter (lambda (x) (< (* x x) 10)) (list -2 -3 -4 1 2)) (list -2 -3 1 2))
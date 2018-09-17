#lang plai

; Programming Languages
; Homework Assignment 6
; 20170504 Juan Lee

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                 String -> Sexp                 ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                Type Definitions                ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parameters: a datatype for storing paramters
; it will be used for multi-variable fun paramters.
(define-type Parameters
  [mtParameter]
  [aParameter (param symbol?) (rest Parameters?)])

; Arguments: a datatype for storing arguments
; it will be used for multi-varialbe app arguments.
(define-type Arguments
  [mtArgument]
  [aArgument (arg FWAE?) (rest Arguments?)])

; Records: a datatype for storing records
; it has two components for each: id and FWAE
(define-type Records
  [mtRecord]
  [aRecord (id symbol?) (val FWAE?) (rest Records?)])

; RecordsV: a datatype for storng interpreted records
; it has two components for each: id and FWAE-Value
(define-type RecordsV
  [mtRecordV]
  [aRecordV (id symbol?) (val FWAE-Value?) (rest RecordsV?)])

; FWAE: a datatype for num, add, sub, with, id, fun, app
(define-type FWAE
  [num (n number?)]
  [add (lhs FWAE?) (rhs FWAE?)]
  [sub (lhs FWAE?) (rhs FWAE?)]
  [with (id symbol?) (value FWAE?) (body FWAE?)]
  [id (name symbol?)]
  [fun (params Parameters?) (body FWAE?)]
  [app (ftn FWAE?) (args Arguments?)]
  [record (records Records?)]
  [getField (record FWAE?) (name symbol?)])

; FWAE-Value: a datatype for the result of the FWAE
(define-type FWAE-Value
  [numV (n number?)]
  [closureV (param Parameters?) (body FWAE?) (ds DefrdSub?)]
  [recordV (record RecordsV?)])

; DefrdSub: a datatpe for the deffered substitution
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FWAE-Value?) (ds DefrdSub?)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                  Parse Sexpr                   ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-params: list -> Parameters
; to parse from a list of symbols to Paramters type
(define (parse-params params)
  (if (empty? params)
      (mtParameter)
      (aParameter (first params) (parse-params (rest params)))))
(test (parse-params '(x y z)) (aParameter 'x (aParameter 'y (aParameter 'z (mtParameter)))))
(test (parse-params empty) (mtParameter))

; parse-arguments: list -> Arguments
; to parse from a list of FWAEs to Arguments type
(define (parse-arguments args)
  (if (empty? args)
      (mtArgument)
      (aArgument (first args) (parse-arguments (rest args)))))
(test (parse-arguments (list (num 1) (num 2))) (aArgument (num 1) (aArgument (num 2) (mtArgument))))
(test (parse-arguments empty) (mtArgument))

; parse-records: list-of-symbols list-of-FWAEs -> Records
; to parse from two lists to produce Records
(define (parse-records ids fwaes)
  (if (empty? ids)
      (mtRecord)
      (aRecord (first ids) (first fwaes) (parse-records (rest ids) (rest fwaes)))))
(test (parse-records (list 'x 'y 'z) (list (num 1) (num 2) (num 3))) (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord)))))
(test (parse-records empty empty) (mtRecord))

; parse-sexpr: sexp -> FWAE
; to parse from sexp to FWAE language
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list params ...) body) (if (check-duplicates params) (error 'parse "bad symtax" sexp)
                                            (fun (parse-params params) (parse-sexpr body)))]
    [(list 'record l ...) (if (check-duplicates (map first l))
                              (error 'parse "duplicate fields" sexp)
                              (record (parse-records (map first l) (map (lambda (x) (parse-sexpr (first (rest x)))) l))))]
    [(list 'getField record name) (getField (parse-sexpr record) name)]
    [(list ftn args ...) (app (parse-sexpr ftn) (parse-arguments (map parse-sexpr args)))]
    [else (error 'parse "bad symtax: ~a" sexp)]))
(test (parse-sexpr 3) (num 3))
(test (parse-sexpr (list '+ (list '- 1 2) (list '+ 1 2))) (add (sub (num 1) (num 2)) (add (num 1) (num 2))))
(test (parse-sexpr 'x) (id 'x))
(test (parse-sexpr (list 'fun (list 'x 'y) (list '+ 'x 'y))) (fun (aParameter 'x (aParameter 'y (mtParameter))) (add (id 'x) (id 'y))))
(test (parse-sexpr (list 'f 1 (list '+ 1 2))) (app (id 'f) (aArgument (num 1) (aArgument (add (num 1) (num 2)) (mtArgument)))))
(test (parse-sexpr (list 'record (list 'x 1) (list 'y 2) (list 'z 3))) (record (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord))))))
(test (parse-sexpr (list 'getField (list 'record (list 'x 1) (list 'y 2) (list 'z 3)) 'y)) (getField (record (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord))))) 'y))

; parse: string -> FWAE
; to parse from string to FWAE. This simply wrap string->sexpr and parse-sexpr
(define (parse str)
  (parse-sexpr (string->sexpr str)))
(test (parse "1") (num 1))
(test (parse "{+ 1 2}") (add (num 1) (num 2)))
(test (parse "{- 1 {+ 1 {- 5 2}}}") (sub (num 1) (add (num 1) (sub (num 5) (num 2)))))
(test (parse "{with {x 3} {+ x 3}}") (with 'x (num 3) (add (id 'x) (num 3))))
(test (parse "{with {x {with {y 3} {+ y y}}} {with {z 3} {+ x {+ y z}}}}") (with 'x (with 'y (num 3) (add (id 'y) (id 'y))) (with 'z (num 3) (add (id 'x) (add (id 'y) (id 'z))))))
(test (parse "x") (id 'x))
(test (parse "{+ x y}") (add (id 'x) (id 'y)))
(test (parse "{fun {x y z} {+ x {+ y z}}}") (fun (parse-params (list 'x 'y 'z)) (add (id 'x) (add (id 'y) (id 'z)))))
(test (parse "{{fun {x y} {+ x y}} 10 11}") (app (fun (parse-params (list 'x 'y)) (add (id 'x) (id 'y))) (parse-arguments (map parse-sexpr (list 10 11)))))
(test (parse "{record {x 1} {y 2} {z 3}}") (record (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord))))))
(test (parse "{getField {record {x 1} {y 2}} y}") (getField (record (aRecord 'x (num 1) (aRecord 'y (num 2) (mtRecord)))) 'y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                 Interpreting                   ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; num-op: (number number -> number) -> (FWAE-Value FWAE-Value -> FWAE-Value)
; to produce a function which takes two FWAE-Values and results in FWAE-Value by taking a function which takes two numbers and produces a number.
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(test ((num-op +) (numV 1) (numV 2)) (numV 3))

; num+: FWAE-Value FWAE-Value -> FWAE-Value
; to produce the sum of two FWAE-Values
(define num+ (num-op +))

; num-: FWAE-Value FWAE-Value -> FWAE-Value
; to produce the sub of two FWAE-Values
(define num- (num-op -))

; lookup: symbol DefrdSub -> FWAE-Value
; to look up the value from given defrdSub which has same symbol as given symbol.
(define (lookup s ds)
        (type-case DefrdSub ds
          [mtSub () (error 'lookup "free identifier")]
          [aSub (x val rest)
                (if (symbol=? x s)
                    val
                    (lookup s rest))]))
(test (lookup 'x (aSub 'y (numV 3) (aSub 'x (numV 4) (mtSub)))) (numV 4))

; map-arguments : (FWAE -> FWAE-Value) Arguments -> list
; apply map function to Arguments and produces the list
(define (map-arguments f args)
  (type-case Arguments args
    [mtArgument () empty]
    [aArgument (arg rest) (cons (f arg) (map-arguments f rest))]))
(test (map-arguments num-n (aArgument (num 1) (aArgument (num 2) (mtArgument)))) (list 1 2))

; check-match: Parameters Arguments -> boolean
; check whether the length of parameters and arguments are same.
(define (check-match params args)
  (cond
    [(and (mtParameter? params) (mtArgument? args)) #t]
    [(not (or (mtParameter? params) (mtArgument? args)))
     (check-match (aParameter-rest params) (aArgument-rest args))]
    [else #f]))
(test (check-match (parse-params (list 'x 'y 'z)) (parse-arguments (list (num 1) (num 2) (num 3)))) #t)
(test (check-match (parse-params (list 'x 'y 'z)) (parse-arguments (list (num 1) (num 2)))) #f)

; append-sub : Parameters list DefrdSub -> DefrdSub
; to append parameters and arguments to given DefrdSub and produces merged DefrdSub
; where given list is interpreted Arguments
(define (append-sub params args-val ds)
  (if (mtParameter? params)
      ds
      (aSub (aParameter-param params) (first args-val) (append-sub (aParameter-rest params) (rest args-val) ds))))
(test (append-sub (aParameter 'x (mtParameter)) (list (numV 1)) (aSub 'a (numV 2) (aSub 'b (numV 3) (mtSub)))) (aSub 'x (numV 1) (aSub 'a (numV 2) (aSub 'b (numV 3) (mtSub)))))

; lookup-record: RecordsV symbol -> FWAE
; to look up FWAE from RecordsV which has name of symbol
(define (lookup-record rec name)
  (type-case RecordsV rec
    [mtRecordV () (error 'lookup-record "no such field")]
    [aRecordV (id val rest)
             (if (symbol=? name id)
                 val
                 (lookup-record rest name))]))
(test (lookup-record (aRecordV 'x (numV 1) (aRecordV 'y (numV 2) (aRecordV 'z (numV 3) (mtRecordV)))) 'y) (numV 2))

; map-record : (FWAE -> FWAE-Value) Records -> RecordsV
; to apply map function to Records to produce RecordsV
(define (map-record f rec)
  (type-case Records rec
    [mtRecord () (mtRecordV)]
    [aRecord (id val rest)
             (aRecordV id (f val) (map-record f rest))]))
(test (map-record (lambda (x) (numV (num-n x))) (aRecord 'x (num 1) (aRecord 'y (num 2) (mtRecord)))) (aRecordV 'x (numV 1) (aRecordV 'y (numV 2) (mtRecordV))))

; interp: FWAE DefrdSub -> FWAE-Value
; to interprete given FWAE and produce FWAE-Value
(define (interp fwae ds)
  (type-case FWAE fwae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id (s) (lookup s ds)]
    [fun (params body) (closureV params body ds)]
    [app (ftn args) (local [(define f-val (interp ftn ds))
                            (define f-params (closureV-param f-val))
                            (define f-body (closureV-body f-val))
                            (define f-ds (closureV-ds f-val))
                            (define args-val (map-arguments (lambda (x) (interp x ds)) args))]
                      (if (not (check-match f-params args))
                          (error 'interp "wrong arity")
                          (interp f-body (append-sub f-params args-val f-ds))))]
    [record (rec) (recordV (map-record (lambda (x) (interp x ds)) rec))]
    [getField (rec name)
              (local [(define rec-val (interp rec ds))
                      (define found (lookup-record (recordV-record rec-val) name))]
                found)]))

; eval : string -> FWAE-Value
; evaluate given string to FWAE-Value
(define (eval string)
  (interp (parse string) (mtSub)))

(test (eval "1") (numV 1))
(test (eval "{+ 1 2}") (numV 3))
(test (eval "{with {x {with {x 3} {- 5 x}}} {+ 1 x}}") (numV 3))
(test (eval "{with {x 3} {with {x 5} {+ 1 x}}}") (numV 6))
(test (eval "{with {f {fun {x} {+ 1 x}}} {f 10}}") (numV 11))
(test (eval "{with {f {fun {x} {+ x x}}} {- 20 {f 10}}}") (numV 0))
(test (eval "{- 20 {{fun {x} {+ x x}} 17}}") (numV -14))
(test (eval "{{with {y 10} {fun {x} {+ y x}}} {with {y 7} y}}") (numV 17))
(test (eval "{fun {x} {+ x 1}}") (closureV (aParameter 'x (mtParameter)) (add (id 'x) (num 1)) (mtSub)))
(test (eval "{with {a 10} {fun {b} {+ a b}}}") (closureV (aParameter 'b (mtParameter)) (add (id 'a) (id 'b)) (aSub 'a (numV 10) (mtSub))))
(test (eval "{{fun {x y} {+ x y}} 10 11}") (numV 21))
(test (eval "{with {f {fun {x y} {+ x y}}} {with {g {fun {x y} {- x y}}} {g {f 2 4} {f 1 2}}}}") (numV 3))
(test (eval "{getField {getField {record {r {record {z 0}}}} r} z}") (numV 0))
(test (eval "{record {a 10} {b {+ 1 2}}}") (recordV (aRecordV 'a (numV 10) (aRecordV 'b (numV 3) (mtRecordV)))))
(test (eval "{getField {record {a 10} {b {+ 1 2}}} b}") (numV 3))

; run : string -> number OR string
; to unbox the result of eval function, if the result is function(closureV) or record(recordV), it simple returns 'function or 'record
(define (run string)
  (local [(define val (eval string))]
    (cond
      [(numV? val) (numV-n val)]
      [(closureV? val) 'function]
      [(recordV? val) 'record])))

; test cases are given in below

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;         Test Cases given by Professor          ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (run "{record {a 10} {b {+ 1 2}}}")
      'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}")
      3)
(test/exn (run "{getField {record {b 10} {b {+ 1 2}}} b}")
          "duplicate fields")
(test/exn (run "{getField {record {a 10}} b}")
          "no such field")
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}")
      12)
(test (run "{getField {record {r {record {z 0}}}} r}")
      'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}")
      0)
(test/exn (run "{record {z {getField {record {z 0}} y}}}")
          "no such field")
(test (run "{with {f {fun {a b} {+ a b}}}
                  {with {g {fun {x} {- x 5}}}
                        {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}}
                  {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}}
                  {with {g {fun {x} {+ x x}}}
                        {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {getField {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {getField a a} b}}}
                  {with {g {fun {x} {+ 5 x}}}
                        {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}}
                  {getField {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {getField {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}}
                  {f {getField {getField {record {a {record {a 10} {b {- 5 2}}}} {b {getField {record {x 50}} x}}} a} b}}}") 8)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") 'record)
(test (run "{record {a {- 2 1}}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {- 2 1}}} a}") 1)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
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

; sequence of BFAEs
(define-type Sequence
  [mtSeq]
  [aSeq (val BFAE?) (rest Sequence?)])

; Records: a datatype for storing records
; it has two components for each: id and BFAE
(define-type Records
  [mtRecord]
  [aRecord (id symbol?) (val BFAE?) (rest Records?)])

; address for records
(define-type Address
  [mtAddr]
  [aAddr (address integer?) (rest Address?)])

; definition of BFAE
(define-type BFAE
  [num (n number?)]
  [add (lhs BFAE?) (rhs BFAE?)]
  [sub (lhs BFAE?) (rhs BFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body BFAE?)]
  [app (ftn BFAE?) (arg BFAE?)]
  [rec (records Records?)]
  [getField (records BFAE?) (name symbol?)]
  [setField (records BFAE?) (name symbol?) (value BFAE?)]
  [newbox (val BFAE?)]
  [setbox (box BFAE?) (val BFAE?)]
  [openbox (box BFAE?)]
  [seqn (seq Sequence?)])

; BFAE-Value: a datatype for the result of the BFAE
(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV (address integer?)]
  [recordV (record Address?)]
  [recordElement (name symbol?) (value BFAE-Value?)])

; DefrdSub: a datatpe for the deffered substitution
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds DefrdSub?)])

; Store
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])

; Value * Store
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                  Parse Sexpr                   ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-sequence: list-of-BFAEs -> Sequence
; parse list of BFAEs into Sequence
(define (parse-sequence bfaes)
  (if (empty? bfaes)
      (mtSeq)
      (aSeq (parse (first bfaes)) (parse-sequence (rest bfaes)))))

; parse-records: list-of-symbols list-of-BFAEs -> Records
; to parse from two lists to produce Records
(define (parse-records ids bfaes)
  (if (empty? ids)
      (mtRecord)
      (aRecord (first ids) (first bfaes) (parse-records (rest ids) (rest bfaes)))))
(test (parse-records (list 'x 'y 'z) (list (num 1) (num 2) (num 3))) (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord)))))
(test (parse-records empty empty) (mtRecord))

; parse: sexp -> BFAE
; to parse from sexp to BFAE language
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list param) body) (fun param (parse body))]
    [(list 'rec l ...) (if (check-duplicates (map first l))
                              (error 'parse "duplicate fields" sexp)
                              (rec (parse-records (map first l) (map (lambda (x) (parse (first (rest x)))) l))))]
    [(list 'get record name) (getField (parse record) name)]
    [(list 'set record name value) (setField (parse record) name (parse value))]
    [(list 'newbox val) (newbox (parse val))]
    [(list 'setbox box val) (setbox (parse box) (parse val))]
    [(list 'openbox box) (openbox (parse box))]
    [(list 'seqn bfaes ...) (if (empty? bfaes)
                                (error 'parse "bad syntax: ~a" sexp)
                                (seqn (parse-sequence bfaes)))]
    [(list ftn args) (app (parse ftn) (parse args))]
    [else (error 'parse "bad symtax: ~a" sexp)]))

; parse-string: string -> BFAE
; to parse from string to BFAE
(define (parse-string str)
  (parse (string->sexpr str)))

(test (parse-string "12") (num 12))
(test (parse-string "{+ 1 2}") (add (num 1) (num 2)))
(test (parse-string "{- {+ 1 2} {+ 1 4}}") (sub (add (num 1) (num 2)) (add (num 1) (num 4))))
(test (parse-string "x") (id 'x))
(test (parse-string "{fun {x} {+ 1 {- x 3}}}") (fun 'x (add (num 1) (sub (id 'x) (num 3)))))
(test (parse-string "{fun {x} {fun {y} {+ x y}}}") (fun 'x (fun 'y (add (id 'x) (id 'y)))))
(test (parse-string "{{fun {x} {+ 1 x}} 3}") (app (fun 'x (add (num 1) (id 'x))) (num 3)))
(test (parse-string "{newbox 3}") (newbox (num 3)))
(test (parse-string "{setbox {newbox 3} 5}") (setbox (newbox (num 3)) (num 5)))
(test (parse-string "{setbox {{fun {x} {newbox {+ x 1}}} 3} 6}") (setbox (app (fun 'x (newbox (add (id 'x) (num 1)))) (num 3)) (num 6)))
(test (parse-string "{openbox {newbox 3}}") (openbox (newbox (num 3))))
(test (parse-string "{seqn {+ x 1} {+ x 3}}") (seqn (aSeq (add (id 'x) (num 1)) (aSeq (add (id 'x) (num 3)) (mtSeq)))))
(test (parse-string "{seqn x y z}") (seqn (aSeq (id 'x) (aSeq (id 'y) (aSeq (id 'z) (mtSeq))))))
(test (parse-string "{rec {x 1} {y 2} {z 3}}") (rec (aRecord 'x (num 1) (aRecord 'y (num 2) (aRecord 'z (num 3) (mtRecord))))))
(test (parse-string "{get {rec {x 1} {y 2}} y}") (getField (rec (aRecord 'x (num 1) (aRecord 'y (num 2) (mtRecord)))) 'y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;                 Interpreting                   ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; num-op: (number number -> number) -> (BFAE-Value BFAE-Value -> BFAE-Value)
; to produce a function which takes two BFAE-Values and results in BFAE-Value by taking a function which takes two numbers and produces a number.
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(test ((num-op +) (numV 1) (numV 2)) (numV 3))

; num+: BFAE-Value BFAE-Value -> BFAE-Value
; to produce the sum of two BFAE-Values
(define num+ (num-op +))

; num-: BFAE-Value BFAE-Value -> BFAE-Value
; to produce the sub of two BFAE-Values
(define num- (num-op -))

; lookup: symbol DefrdSub -> BFAE-Value
; to look up the value from given defrdSub which has same symbol as given symbol.
(define (lookup s ds)
        (type-case DefrdSub ds
          [mtSub () (error 'lookup "free identifier")]
          [aSub (x val rest)
                (if (symbol=? x s)
                    val
                    (lookup s rest))]))
(test (lookup 'x (aSub 'y (numV 3) (aSub 'x (numV 4) (mtSub)))) (numV 4))

; store-lookup: integer Store -> BFAE-Value
; to look up the value from store
(define (store-lookup ptr st)
  (type-case Store st
    [mtSto () (error 'lookup "unallocated")]
    [aSto (addr val rest)
          (if (= addr ptr)
              val
              (store-lookup ptr rest))]))
(test (store-lookup 3 (aSto 0 (numV 1) (aSto 1 (numV 2) (aSto 2 (numV 3) (aSto 3 (numV 4) (aSto 4 (numV 5) (mtSto))))))) (numV 4))

; malloc: Store -> integer
; to allocate the empty memory
(define (malloc st)
  (+ 1 (max-address st)))

; max-address: Store -> integer
; to get the maximum address of store
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st1) (max n (max-address st1))]))

; set-store: Store integer BFAE-Value -> Store
; to set the cell with address integer of Store as BFAE-Value
(define (set-store st addr value)
  (type-case Store st
    [mtSto () (error 'free "address for free is invalid")]
    [aSto (n v st1)
          (if (= n addr)
              (aSto n value st1)
              (aSto n v (set-store st1 addr value)))]))

; interp-two : BFAE BFAE DefrdSub Store (BFAE-Value BFAE-Value Store -> Value*Store) -> Value*Store
; to produce the result of two consecutive operations
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         [type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)]]]))

; interp-seq : Sequence DefrdSub Store BFAE-Value-> Value*Store
; to produce the result of consecutive sequence operations
(define (interp-seq seq ds st val)
  (type-case Sequence seq
    [mtSeq () (v*s val st)]
    [aSeq (bfae rest)
          (local [(define interp-bfae (interp bfae ds st))
                  (define val1 (v*s-value interp-bfae))
                  (define st1 (v*s-store interp-bfae))]
            (interp-seq rest ds st1 val1))]))

; store-records : Record DefrdSub Store -> Value*Store
; to store given records and return the addresses of them
(define (store-records rec ds st)
  (define (helper rec st addr)
    (type-case Records rec
      [mtRecord () (v*s (recordV addr) st)]
      [aRecord (id bfae rest)
               (local [(define interp-bfae (interp bfae ds st))
                       (define interp-value (v*s-value interp-bfae))
                       (define interp-store (v*s-store interp-bfae))
                       (define val (recordElement id interp-value))
                       (define a (malloc interp-store))]
                 (helper rest (aSto a val interp-store) (aAddr a addr)))]))
  (helper rec st (mtAddr)))

; records-lookup : Address symbol Store -> BFAE-Value
; to look up given symbol in Address within Store
(define (records-lookup addr name st)
  (type-case Address addr
    [mtAddr () (error 'lookup "wrong record id")]
    [aAddr (addr rest)
           (local [(define looked-up (store-lookup addr st))
                   (define looked-name (recordElement-name looked-up))
                   (define looked-value (recordElement-value looked-up))]
             (if (symbol=? looked-name name)
                 looked-value
                 (records-lookup rest name st)))]))

; records-lookup-address : Address symbol Store -> integer
; to look up integer
(define (records-lookup-address addr name st)
  (type-case Address addr
    [mtAddr () (error 'lookup "wrong record id")]
    [aAddr (addr rest)
           (local [(define looked-up (store-lookup addr st))
                   (define looked-name (recordElement-name looked-up))
                   (define looked-value (recordElement-value looked-up))]
             (if (symbol=? looked-name name)
                 addr
                 (records-lookup-address rest name st)))]))

; interp: BFAE DefrdSub Store -> BFAE-Value
; to interprete given BFAE and produce BFAE-Value
(define (interp bfae ds st)
  (type-case BFAE bfae
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id (s) (v*s (lookup s ds) st)]
    [fun (params body) (v*s (closureV params body ds) st)]
    [app (ftn arg) (local [(define interp-ftn (interp ftn ds st))
                           (define ftn-value (v*s-value interp-ftn))
                           (define ftn-store (v*s-store interp-ftn))
                           (define interp-arg (interp arg ds ftn-store))
                           (define arg-value (v*s-value interp-arg))
                           (define arg-store (v*s-store interp-arg))
                           (define ftn-param (closureV-param ftn-value))
                           (define ftn-body (closureV-body ftn-value))
                           (define ftn-ds (closureV-ds ftn-value))]
                     (interp ftn-body (aSub ftn-param arg-value ftn-ds) arg-store))]
    [newbox (val)
            (type-case Value*Store (interp val ds st)
              [v*s (v1 st1)
                   (local [(define a (malloc st1))]
                     (v*s (boxV a) (aSto a v1 st1)))])]
    [openbox (bx-expr)
             (type-case Value*Store (interp bx-expr ds st)
               [v*s (bx-val st1)
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [setbox (bx-expr val-expr)
            (interp-two bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (v*s val
                               (set-store st1 (boxV-address bx-val) val))))]
    [seqn (seq) (interp-seq seq ds st 0)]
    [rec (rec) (store-records rec ds st)]
    [getField (rec name) (local [(define interp-record (interp rec ds st))
                                 (define address (recordV-record (v*s-value interp-record)))
                                 (define st1 (v*s-store interp-record))]
                           (v*s (records-lookup address name st1) st1))]
    [setField (rec name value) (local [(define interp-record (interp rec ds st))
                                 (define address (recordV-record (v*s-value interp-record)))
                                 (define st1 (v*s-store interp-record))
                                 (define a (records-lookup-address address name st1))
                                 (define interp-value (interp value ds st1))
                                 (define interp-value-value (v*s-value interp-value))
                                 (define interp-value-store (v*s-store interp-value))]
                           (v*s interp-value-value (set-store interp-value-store a (recordElement name interp-value-value))))]))

; interp-expr BFAE -> BFAE-Value OR 'func 'box 'record
; to interprete given BFAE and return the value of that
(define (interp-expr bfae)
  (type-case BFAE-Value (v*s-value (interp bfae (mtSub) (mtSto)))
    [numV (n) n]
    [closureV (param body ds) 'func]
    [boxV (addr) 'box]
    [recordV (record) 'record]
    [recordElement (name value) (error 'interp "recordElement cannot be the result of interp")]))

(test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b 2}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 2)
             (aSto 1 (numV 2) (mtSto))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                ;
;         Test Cases given by Professor          ;
;                                                ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)

(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)
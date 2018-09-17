; CS320 Programming Language
; Homework Assignment 12
; Author @ 20170504 Juan Lee (juanlee@kaist.ac.kr)

#lang plai-typed

; EXPR type definition
(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

; TE type definition
(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

; Type type definition
(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [idT (name : symbol)]
  [tvT (name : symbol)])

; EXPR-Value type definition
(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

; TypeEnv type definition
(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol) (type : Type) (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)])

; DefrdSub type definition
(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : EXPR-Value)
        (rest : DefrdSub)]
  [aRecSub (name : symbol)
           (value-box : (boxof 'a))
           (ds : DefrdSub)])

; TypePair
; indicates two tvTs are same.
; order matters.
(define-type TypePair
  [mtTPair]
  [aTPair (left : symbol)
          (right : symbol)
          (rest : TypePair)])

;; ---------------------------------------------------

; lookup-typepair: symbol symbol TypePair -> boolean
(define lookup-typepair : (symbol symbol TypePair -> boolean)
  (lambda (n1 n2 tpair)
    (type-case TypePair tpair
      [mtTPair () false]
      [aTPair (l r rest)
              (if (and (symbol=? n1 l)
                       (symbol=? n2 r))
                  true
                  (lookup-typepair n1 n2 rest))])))

; type-equal?: Type Type TypePair -> boolean
(define type-equal? : (Type Type TypePair -> boolean)
  (lambda (t1 t2 tpair)
    (type-case Type t1
      [numT () (type-case Type t2
                 [numT () true]
                 [else false])]
      [boolT () (type-case Type t2
                  [boolT () true]
                  [else false])]
      [arrowT (a b)
              (type-case Type t2
                [arrowT (a2 b2)
                        (and (type-equal? a a2 tpair)
                             (type-equal? b b2 tpair))]
                [else false])]
      [polyT (forall body)
             (type-case Type t2
               [polyT (forall2 body2)
                      (type-equal? body body2
                                   (aTPair forall forall2 tpair))]
               [else false])]
      [idT (name)
           (type-case Type t2
             [idT (name2) (symbol=? name name2)]
             [else false])]
      [tvT (name)
           (type-case Type t2
             [tvT (name2)
                  (or (lookup-typepair name name2 tpair)
                      (symbol=? name name2))]
             [else false])])))

; parse-type: TE -> Type
(define parse-type : (TE -> Type)
  (lambda (te)
    (type-case TE te
      [numTE () (numT)]
      [boolTE () (boolT)]
      [arrowTE (a b) (arrowT (parse-type a) (parse-type b))]
      [polyTE (forall body) (polyT forall (parse-type body))]
      [idTE (name) (idT name)]
      [tvTE (name) (tvT name)])))

; type-error: EXPR string -> void
(define (type-error expr msg)
  (error 'type-error "no"))

;(define type-error : (EXPR string -> void)
;  (lambda (expr msg)
;    (error 'type-error msg)))

; get-type: symbol TypeEnv -> Type
(define get-type : (symbol TypeEnv -> Type)
  (lambda (name-to-find env)
    (type-case TypeEnv env
      [mtEnv () (error 'get-type "free variable, so no type")]
      [aBind (name ty rest)
             (if (symbol=? name-to-find name)
                 ty
                 (get-type name-to-find rest))]
      [tBind (name var1-name var1-ty var2-name var2-ty rest)
             (get-type name-to-find rest)])))

; validtype: Type TypeEnv -> TypeEnv
(define validtype : (Type TypeEnv -> TypeEnv)
  (lambda (ty env)
    (type-case Type ty
      [numT () (mtEnv)]
      [boolT () (mtEnv)]
      [arrowT (a b) (begin (validtype a env)
                           (validtype b env))]
      [idT (id) (find-type-id id env)]
      [polyT (forall body) (validtype body (aBind forall (tvT forall) env))]
      [tvT (name) (find-type-id name env)])))

; find-type-id: symbol TypeEnv -> TypeEnv
(define find-type-id : (symbol TypeEnv -> TypeEnv)
  (lambda (name-to-find env)
    (type-case TypeEnv env
      [mtEnv () (error 'get-type "free type name, so no type")]
      [aBind (name ty rest)
             (type-case Type ty
               [tvT (name)
                      (if (symbol=? name-to-find name)
                          env
                          (find-type-id name-to-find rest))]
               [else (find-type-id name-to-find rest)])]
      [tBind (name var1-name var1-ty var2-name var2-ty rest)
             (if (symbol=? name-to-find name)
                 env
                 (find-type-id name-to-find rest))])))

; apply-alpha: Type alpha Type -> Type
; to replace alpha as given Type
(define apply-alpha : (Type symbol Type -> Type)
  (lambda (t1 alpha t0)
    (type-case Type t1
      [numT () (numT)]
      [boolT () (boolT)]
      [arrowT (a b) (arrowT (apply-alpha a alpha t0) (apply-alpha b alpha t0))]
      [polyT (forall body)
             (if (symbol=? forall alpha)
                 t1
                 (polyT forall (apply-alpha body alpha t0)))]
      [idT (id) t1]
      [tvT (name)
           (if (symbol=? name alpha)
               t0
               t1)])))

; typecheck: EXPR TypeEnv -> Type
(define typecheck : (EXPR TypeEnv -> Type)
  (lambda (expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (type-error r "num")])]
             [else (type-error l "num")])]
      [sub (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (type-error r "num")])]
             [else (type-error l "num")])]
      [equ (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (boolT)]
                     [else (type-error r "num")])]
             [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (begin
               (validtype param-type env)
               (arrowT param-type
                       (typecheck body (aBind name param-type env)))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (if (type-equal? param-type (typecheck arg env) (mtTPair))
                         result-type
                         (type-error arg (to-string param-type)))]
             [else (type-error fn "function")])]
      [ifthenelse (test-expr then-expr else-expr)
                  (type-case Type (typecheck test-expr env)
                    [boolT () (local [(define test-ty (typecheck then-expr env))]
                                (begin
                                  (if (type-equal? test-ty (typecheck else-expr env) (mtTPair))
                                      test-ty
                                      (type-error else-expr (to-string test-ty)))))]
                    [else (type-error test-expr "bool")])]
      
      [rec (name ty rhs-expr body-expr)
        (local [(define rhs-ty (parse-type ty))
                (define new-env (aBind name rhs-ty env))]
          (begin
            (validtype rhs-ty env)
            (if (equal? rhs-ty (typecheck rhs-expr new-env))
                (typecheck body-expr new-env)
                (type-error rhs-expr (to-string rhs-ty)))))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
        (local [(define var1-ty (parse-type var1-te))
                (define var2-ty (parse-type var2-te))
                (define new-env (tBind type-name
                                       var1-name var1-ty
                                       var2-name var2-ty env))]
          (begin
            (validtype var1-ty new-env)
            (validtype var2-ty new-env)
            (typecheck body-expr
                       (aBind var1-name
                              (arrowT var1-ty
                                      (idT type-name))
                              (aBind var2-name
                                     (arrowT var2-ty
                                             (idT type-name))
                                     new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                                      var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (equal? rhs1-ty rhs2-ty)
                               rhs1-ty
                               (type-error var2-rhs (to-string rhs2-ty))))
                         (type-error dispatch-expr (to-string type-name)))]
                [else (type-error dispatch-expr (to-string type-name))])
              (type-error expr "matching variant names")))]
      [tfun (name expr)
            (polyT name (typecheck expr
                                   (aBind name (tvT name) env)))]
      [tapp (body type)
            (begin
              (validtype (parse-type type) env)
              (type-case Type (typecheck body env)
                [polyT (forall body2)
                       (apply-alpha body2 forall (parse-type type))]
                [else (type-error body  "forall")]))])))
      

;; ---------------------------------------------------

; lookup: symbol DefrdSub -> EXPR-Value
(define lookup : (symbol DefrdSub -> EXPR-Value)
  (lambda (name ds)
    (type-case DefrdSub ds
      [mtSub () (error 'lookup "free variable")]
      [aSub (sub-name val rest-ds)
            (if (symbol=? sub-name name)
                val
                (lookup name rest-ds))]
      [aRecSub (sub-name val-box rest-ds)
               (if (symbol=? sub-name name)
                   (unbox val-box)
                   (lookup name rest-ds))])))

; num+ : (EXPR-Value EXPR-Value -> EXPR-Value)
(define num+ : (EXPR-Value EXPR-Value -> EXPR-Value)
  (lambda (a b)
    (numV (+ (numV-n a) (numV-n b)))))

; num- : (EXPR-Value EXPR-Value -> EXPR-Value)
(define num- : (EXPR-Value EXPR-Value -> EXPR-Value)
  (lambda (a b)
    (numV (- (numV-n a) (numV-n b)))))

; num= : (EXPR-Value EXPR-Value -> EXPR-Value)
(define num= : (EXPR-Value EXPR-Value -> EXPR-Value)
  (lambda (a b)
    (boolV (= (numV-n a) (numV-n b)))))

; true? : (EXPR-Value -> boolean)
(define true? : (EXPR-Value -> boolean)
  (lambda (b)
    (boolV-b b)))

; interp: (EXPR DefrdSub -> EXPR-Value)
(define interp : (EXPR DefrdSub -> EXPR-Value)
  (lambda (expr ds)
    (type-case EXPR expr
      [num (n) (numV n)]
      [bool (b) (boolV b)]
      [add (l r) (num+ (interp l ds) (interp r ds))]
      [sub (l r) (num- (interp l ds) (interp r ds))]
      [equ (l r) (num= (interp l ds) (interp r ds))]
      [id (name) (lookup name ds)]
      [fun (param param-ty body) (closureV param body ds)]
      [app (fun-expr arg-expr)
           (local [(define fun-val (interp fun-expr ds))
                   (define arg-val (interp arg-expr ds))]
             (type-case EXPR-Value fun-val
               [closureV (param body ds)
                         (interp body (aSub param arg-val ds))]
               [constructorV (right?)
                             (variantV right? arg-val)]
               [else (error 'interp "not applicable")]))]
      [ifthenelse (test-expr then-expr else-expr)
                  (if (true? (interp test-expr ds))
                      (interp then-expr ds)
                      (interp else-expr ds))]
      [rec (name ty named-expr body)
        (local [(define value-holder (box (numV 42)))
                (define new-ds
                  (aRecSub name value-holder ds))]
          (begin
            (set-box! value-holder (interp named-expr new-ds))
            (interp body new-ds)))]
      [with-type (name var1-name var1-ty
                       var2-name var2-ty body-expr)
        (interp body-expr
                (aSub var1-name (constructorV false)
                      (aSub var2-name (constructorV true)
                            ds)))]
      [cases (name dispatch-expr var1-name bind1-name rhs1-expr
                                 var2-name bind2-name rhs2-expr)
        (type-case EXPR-Value (interp dispatch-expr ds)
          [variantV (right? val)
                    (if (not right?)
                        (interp rhs1-expr (aSub bind1-name val ds))
                        (interp rhs2-expr (aSub bind2-name val ds)))]
          [else (error 'interp "not a variant result")])]
      [tfun (name expr) (interp expr ds)]
      [tapp (body type) (interp body ds)])))
           
;; ---------------------------------------------------

; eval : EXPR -> EXPR-Value
(define eval : (EXPR -> EXPR-Value)
  (lambda (expr)
    (begin
      (try (typecheck expr (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (interp expr (mtSub)))))
  
;; ---------------------------------------------------
;;
;; Test Cases
;;
;; ---------------------------------------------------

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))
      
(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))
      
(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
      
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))
        
(test (typecheck
       (tfun 'alpha
             (fun 'alpha (arrowTE (numTE) (numTE))
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (polyT 'alpha (arrowT (arrowT (numT) (numT)) (arrowT (tvT 'alpha) (tvT 'alpha)))))
      
(test (typecheck
       (fun 'alpha (arrowTE (numTE) (numTE))
            (tfun 'alpha
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (arrowT (arrowT (numT) (numT)) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))
(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (arrowTE (numTE) (numTE)))
          (mtEnv)) (arrowT (arrowT (numT) (numT)) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))


(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (num 42)) (id 'f)) (aBind 'f (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))) (mtEnv))) (numT))

;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))
(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10))
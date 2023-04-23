#lang plait

;; ============================================================
;; classes without inheritance

(define-type Exp
  (numE [n : Number])
  (plusE [lhs : Exp]
         [rhs : Exp])
  (multE [lhs : Exp]
         [rhs : Exp])
  (trueE)
  (falseE)
  (argE)
  (thisE)
  (idE [s : Symbol])
  (lamE [n : Symbol]
        [arg-type : Type]
        [body : Exp])
  (equalsE [fst : Exp]
           [snd : Exp])
  (newE [class-name : Symbol]
        [args : (Listof Exp)])
  (getE [obj-expr : Exp]
        [field-name : Symbol])
  (sendE [obj-expr : Exp]
         [method-name : Symbol]
         [arg-expr : Exp])
  (ssendE [obj-expr : Exp]
          [class-name : Symbol]
          [method-name : Symbol]
          [arg-expr : Exp])
  (selectE [test : Exp]
           [object : Exp])
  (instanceE [object : Exp]
             [comp : Symbol])
    (appE [fun : Exp]
        [arg : Exp])
  )

(define-type Class
  (classC [super-name : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * Exp))]))

(define-type Value
  (boolV [b : Boolean])
  (numV [n : Number])
  (objV [class-name : Symbol]
        [field-values : (Listof Value)])
  (closV [arg : Symbol]
         [body : Exp]
         [env : Env]))

(define-type Binding
  (bind [name : Symbol]
        [val : Value]))

(define-type-alias Env (Listof Binding))

(define-type Type
  (numT)
  (boolT)
  (objT)
  (arrowT [arg : Type]
          [result : Type])
  (varT [is : (Boxof (Optionof Type))]))

(define-type Type-Binding
  (tbind [name : Symbol]
         [type : Type]))

(define-type-alias Type-Env (Listof Type-Binding))

(define mt-env empty)
(define extend-env cons)

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (find [l : (Listof (Symbol * 'a))] [name : Symbol]) : 'a
  (type-case (Listof (Symbol * 'a)) l
    [empty
     (error 'find (string-append "not found: " (symbol->string name)))]
    [(cons p rst-l)
     (if (symbol=? (fst p) name)
         (snd p)
         (find rst-l name))]))

(module+ test
  (test (find (list (values 'a 1)) 'a)
        1)
  (test (find (list (values 'a 1) (values 'b 2)) 'b)
        2)
  (test/exn (find empty 'a)
            "not found: a")
  (test/exn (find (list (values 'a 1)) 'x)
            "not found: x"))

;; ----------------------------------------

(define recinst : ((Listof (Symbol * Class)) Class Symbol -> Value)
  (lambda (classes class test)
    (type-case Class class
      [(classC csuper-name cfield-names cmethods) (if (equal? csuper-name test)
                                                      (numV 0)
                                                      (if (equal? csuper-name 'Object)
                                                          (numV 1)
                                                          (recinst classes (find classes csuper-name) test)))])
    ))

(define interp : (Exp (Listof (Symbol * Class)) Value Value Env -> Value)
  (lambda (a classes this-val arg-val env)
    (local [(define (recur expr)
              (interp expr classes this-val arg-val env))]
      (type-case Exp a
        [(numE n) (numV n)]
        [(trueE) (boolV #t)]
        [(falseE) (boolV #f)]
        [(plusE l r) (num+ (recur l) (recur r))]
        [(multE l r) (num* (recur l) (recur r))]
        [(thisE) this-val]
        [(idE s) (lookup s env)]
        [(argE) arg-val]
        [(lamE n t body)
         (closV n body env)]
        [(appE fun arg) (type-case Value (interp fun classes this-val arg-val env)
                      [(closV n body c-env)
                       (interp body classes this-val arg-val
                               (extend-env
                                (bind n
                                      (interp arg classes this-val arg-val env))
                                c-env))]
                          [else (error 'interp "not a function")])]
        [(equalsE fst snd) (local [(define f (recur fst))]
                             (local [(define s (recur snd))]
                               (type-case Value f
                               [(objV classname values) (type-case Value s
                                                          [(objV name v) (local [(define fc (find classes classname))]
                                                                           (local [(define sc (find classes name))]
                                                                             (type-case Class fc
                                                                               [(classC fsuper-name ffieldnames fmethodnames) (type-case Class sc
                                                                               [(classC ssuper-name sfieldnames smethodnames) (if (equal? ffieldnames sfieldnames) (if (equal? values v) (boolV #t) (boolV #f)) (boolV #f))])])))]
                                                          [else (boolV #f)])]
                               [else (boolV (equal? f s))])))]
        [(newE class-name field-exprs)
         (local [(define c (if (equal? class-name 'Object)
                               (classC 'Object empty empty)
                               (find classes class-name)))
                 (define vals (map recur field-exprs))]
           (if (= (length vals) (length (classC-field-names c)))
               (objV class-name vals)
               (error 'interp "wrong field count")))]
        [(getE obj-expr field-name)
         (type-case Value (recur obj-expr)
           [(objV class-name field-vals)
            (type-case Class (find classes class-name)
              [(classC superclass field-names methods)
               (find (map2 (lambda (n v) (values n v))
                           field-names
                           field-vals)
                     field-name)])]
           [else (error 'interp "not an object")])]
        [(sendE obj-expr method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (type-case Value obj
             [(objV class-name field-vals)
              (call-method class-name method-name classes
                           obj arg-val)]
             [else (error 'interp "not an object")]))]
        [(ssendE obj-expr class-name method-name arg-expr)
         (local [(define obj (recur obj-expr))
                 (define arg-val (recur arg-expr))]
           (call-method class-name method-name classes
                        obj arg-val))]
        [(selectE test object) (local [(define obj (recur object))]
                                 (local [(define t (recur test))]
                                     (type-case Value t
                                       [(numV n) (type-case Value obj
                                                         [(objV class-name field-vals) (if (equal? t (numV 0))
                                                                                           (call-method class-name 'zero classes obj (numV 0))
                                                                                           (call-method class-name 'nonzero classes obj (numV 0)))]
                                                         [else (error 'interp "not an object")])]
                                        [else (error 'interp "not a number")])))]
        [(instanceE object test) (local [(define obj (recur object))]
                                     (type-case Value obj
                                         [(objV class-name field-vals) (if (equal? class-name test)
                                                                           (numV 0)
                                                                           (if (equal? class-name 'Object)
                                                                               (numV 1)
                                                                               (recinst classes (find classes class-name) test)))]
                                         [else (numV 1)]))]
        ))))

(define (call-method class-name method-name classes
                     obj arg-val)
  (type-case Class (find classes class-name)
    [(classC superclass field-names methods)
     (let ([body-expr (find methods method-name)])
       (interp body-expr
               classes
               obj
               arg-val mt-env))]))

(define (num-op [op : (Number Number -> Number)]
                [op-name : Symbol] 
                [x : Value]
                [y : Value]) : Value
  (cond
    [(and (numV? x) (numV? y))
     (numV (op (numV-n x) (numV-n y)))]
    [else (error 'interp "not a number")]))

(define (num+ x y) (num-op + '+ x y))
(define (num* x y) (num-op * '* x y))

;; ----------------------------------------
;; Examples

(module+ test
  (define posn-class
    (values 'Posn
            (classC 'Object
             (list 'x 'y)
             (list (values 'mdist
                           (plusE (getE (thisE) 'x) (getE (thisE) 'y)))
                   (values 'addDist
                           (plusE (sendE (thisE) 'mdist (numE 0))
                                  (sendE (argE) 'mdist (numE 0))))
                   (values 'addX
                           (plusE (getE (thisE) 'x) (argE)))
                   (values 'multY (multE (argE) (getE (thisE) 'y)))
                   (values 'factory12 (newE 'Posn (list (numE 1) (numE 2))))))))
    
  (define posn3D-class
    (values 'Posn3D
            (classC 'Object
             (list 'x 'y 'z)
             (list (values 'mdist (plusE (getE (thisE) 'z)
                                         (ssendE (thisE) 'Posn 'mdist (argE))))
                   (values 'addDist (ssendE (thisE) 'Posn 'addDist (argE)))))))

  (define new-posn27 (newE 'Posn (list (numE 2) (numE 7))))
  (define new-posn531 (newE 'Posn3D (list (numE 5) (numE 3) (numE 1))))

  (define (interp-posn a)
    (interp a (list posn-class posn3D-class) (numV -1) (numV -1) mt-env)))

;; ----------------------------------------

(module+ test
  (test (interp (numE 10) 
                empty (objV 'Object empty) (numV 0) mt-env)
        (numV 10))
  (test (interp (plusE (numE 10) (numE 17))
                empty (objV 'Object empty) (numV 0)  mt-env)
        (numV 27))
  (test (interp (multE (numE 10) (numE 7))
                empty (objV 'Object empty) (numV 0)  mt-env)
        (numV 70))

  (test (interp-posn (newE 'Posn (list (numE 2) (numE 7))))
        (objV 'Posn (list (numV 2) (numV 7))))

  (test (interp-posn (sendE new-posn27 'mdist (numE 0)))
        (numV 9))
  
  (test (interp-posn (sendE new-posn27 'addX (numE 10)))
        (numV 12))

  (test (interp-posn (sendE (ssendE new-posn27 'Posn 'factory12 (numE 0))
                            'multY
                            (numE 15)))
        (numV 30))

  (test (interp-posn (sendE new-posn531 'addDist new-posn27))
        (numV 18))
  
  (test/exn (interp-posn (plusE (numE 1) new-posn27))
            "not a number")
  (test/exn (interp-posn (getE (numE 1) 'x))
            "not an object")
  (test/exn (interp-posn (sendE (numE 1) 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (ssendE (numE 1) 'Posn 'mdist (numE 0)))
            "not an object")
  (test/exn (interp-posn (newE 'Posn (list (numE 0))))
            "wrong field count"))

;; ============================================================
;; inherit

(define-type ExpI
  (numI [n : Number])
  (plusI [lhs : ExpI]
         [rhs : ExpI])
  (multI [lhs : ExpI]
         [rhs : ExpI])
  (idI [s : Symbol])
  (trueI)
  (falseI)
  (argI)
  (thisI)
  (lamI [n : Symbol]
        [arg-type : Type]
        [body : ExpI])
  (equalsI [fst : ExpI]
           [snd : ExpI])
  (newI [class-name : Symbol]
        [args : (Listof ExpI)])
  (getI [obj-expr : ExpI]
        [field-name : Symbol])
  (sendI [obj-expr : ExpI]
         [method-name : Symbol]
         [arg-expr : ExpI])
  (superI [method-name : Symbol]
          [arg-expr : ExpI])
  (selectI [test : ExpI]
           [object : ExpI])
  (instanceI [object : ExpI]
             [comp : Symbol])
  (appI [fun : ExpI]
        [arg : ExpI]))

(define-type ClassI
  (classI [super-name : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * ExpI))]))

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (exp-i->c [a : ExpI] [super-name : Symbol]) : Exp
  (local [(define (recur expr)
            (exp-i->c expr super-name))]
    (type-case ExpI a
      [(numI n) (numE n)]
      [(plusI l r) (plusE (recur l) (recur r))]
      [(multI l r) (multE (recur l) (recur r))]
      [(idI s) (idE s)]
      [(trueI) (trueE)]
      [(falseI) (falseE)]
      [(argI) (argE)]
      [(thisI) (thisE)]
      [(equalsI fst snd) (equalsE (recur fst) (recur snd))]
      [(lamI n arg-type body) (lamE n arg-type (recur body))]
      [(newI class-name field-exprs)
       (newE class-name (map recur field-exprs))]
      [(getI expr field-name)
       (getE (recur expr) field-name)]
      [(sendI expr method-name arg-expr)
       (sendE (recur expr)
              method-name
              (recur arg-expr))]
      [(superI method-name arg-expr)
       (ssendE (thisE)
               super-name
               method-name
               (recur arg-expr))]
      [(selectI test object) (selectE (recur test) (recur object))]
      [(instanceI object comp) (instanceE (recur object) comp)]
      [(appI fun arg) (appE (recur fun) (recur arg))])))

(module+ test
  (test (exp-i->c (numI 10) 'Object)
        (numE 10))
  (test (exp-i->c (plusI (numI 10) (numI 2)) 'Object)
        (plusE (numE 10) (numE 2)))
  (test (exp-i->c (multI (numI 10) (numI 2)) 'Object)
        (multE (numE 10) (numE 2)))
  (test (exp-i->c (argI) 'Object)
        (argE))
  (test (exp-i->c (thisI) 'Object)
        (thisE))
  (test (exp-i->c (newI 'Object (list (numI 1))) 'Object)
        (newE 'Object (list (numE 1))))
  (test (exp-i->c (getI (numI 1) 'x) 'Object)
        (getE (numE 1) 'x))
  (test (exp-i->c (sendI (numI 1) 'mdist (numI 2)) 'Object)
        (sendE (numE 1) 'mdist (numE 2)))
  (test (exp-i->c (superI 'mdist (numI 2)) 'Posn)
        (ssendE (thisE) 'Posn 'mdist (numE 2))))

;; ----------------------------------------

(define (class-i->c-not-flat [c : ClassI]) : Class
  (type-case ClassI c
    [(classI super-name field-names methods)
     (classC super-name
      field-names
      (map (lambda (m)
             (values (fst m)
                     (exp-i->c (snd m) super-name)))
           methods))]))

(module+ test
  (define posn3d-mdist-i-method
    (values 'mdist
            (plusI (getI (thisI) 'z)
                   (superI 'mdist (argI)))))
  (define posn3d-mdist-c-method
    (values 'mdist
            (plusE (getE (thisE) 'z)
                   (ssendE (thisE) 'Posn 'mdist (argE)))))

  (define posn3d-i-class 
    (values 'Posn3D
            (classI
             'Posn
             (list 'z)
             (list posn3d-mdist-i-method))))
  (define posn3d-c-class-not-flat
    (values 'Posn3D
            (classC 'Posn
                    (list 'z)
                    (list posn3d-mdist-c-method))))

  (test (class-i->c-not-flat (snd posn3d-i-class))
        (snd posn3d-c-class-not-flat)))

;; ----------------------------------------

(define (flatten-class [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case Class (find classes-not-flat name)
    [(classC superclass field-names methods)
     (type-case Class (flatten-super name classes-not-flat i-classes)
       [(classC super-superclass super-field-names super-methods)
        (classC
         superclass
         (add-fields super-field-names field-names)
         (add/replace-methods super-methods methods))])]))

(define (flatten-super [name : Symbol]
                       [classes-not-flat : (Listof (Symbol * Class))] 
                       [i-classes : (Listof (Symbol * ClassI))]) : Class
  (type-case ClassI (find i-classes name)
    [(classI super-name field-names i-methods)
     (if (equal? super-name 'Object)
         (classC 'Object empty empty)
         (flatten-class super-name
                        classes-not-flat
                        i-classes))]))

(module+ test
  (define posn-i-class
    (values
     'Posn
     (classI 'Object
             (list 'x 'y)
             (list (values 'mdist
                           (plusI (getI (thisI) 'x)
                                  (getI (thisI) 'y)))
                   (values 'addDist
                            (plusI (sendI (thisI) 'mdist (numI 0))
                                   (sendI (argI) 'mdist (numI 0))))))))
  (define addDist-c-method
    (values 'addDist
            (plusE (sendE (thisE) 'mdist (numE 0))
                   (sendE (argE) 'mdist (numE 0)))))
  (define posn-c-class-not-flat
    (values
     'Posn
    (classC 'Object
            (list 'x 'y)
            (list (values 'mdist
                          (plusE (getE (thisE) 'x)
                                 (getE (thisE) 'y)))
                  addDist-c-method))))
  (define posn3d-c-class
    (values 'Posn3D
            (classC 'Posn
                    (list 'x 'y 'z)
                    (list posn3d-mdist-c-method
                          addDist-c-method))))

  (test (flatten-class 'Posn3D
                       (list posn-c-class-not-flat
                             posn3d-c-class-not-flat)
                       (list posn-i-class
                             posn3d-i-class))
        (snd posn3d-c-class)))

;; ----------------------------------------

(define add-fields append)

(define (add/replace-methods [methods : (Listof (Symbol * Exp))]
                             [new-methods : (Listof (Symbol * Exp))])
  : (Listof (Symbol * Exp))
  (cond
    [(empty? new-methods) methods]
    [else (add/replace-methods
           (add/replace-method methods (first new-methods))
           (rest new-methods))]))

(define (add/replace-method [methods : (Listof (Symbol * Exp))] 
                            [new-method : (Symbol * Exp)])
  : (Listof (Symbol * Exp))
  (cond
    [(empty? methods) (list new-method)]
    [else
     (if (equal? (fst (first methods))
                 (fst new-method))
         (cons new-method (rest methods))
         (cons (first methods) 
               (add/replace-method (rest methods)
                                   new-method)))]))

(module+ test
  (test (add-fields (list 'x 'y) (list 'z))
        (list 'x 'y 'z))

  (test (add/replace-methods empty empty)
        empty)
  (test (add/replace-methods empty (list (values 'm (numE 0))))
        (list (values 'm (numE 0))))
  (test (add/replace-methods (list (values 'm (numE 0))) empty)
        (list (values 'm (numE 0))))
  (test (add/replace-methods (list (values 'm (numE 0)))
                             (list (values 'm (numE 1))))
        (list (values 'm (numE 1))))
  (test (add/replace-methods (list (values 'm (numE 0))
                                   (values 'n (numE 2)))
                             (list (values 'm (numE 1))))
        (list (values 'm (numE 1))
              (values 'n (numE 2))))
  (test (add/replace-methods (list (values 'm (numE 0)))
                             (list (values 'm (numE 1))
                                   (values 'n (numE 2))))
        (list (values 'm (numE 1))
              (values 'n (numE 2))))

  (test (add/replace-method (list (values 'm (numE 0)))
                            (values 'm (numE 1)))
        (list (values 'm (numE 1))))
  (test (add/replace-method (list (values 'm (numE 0)))
                            (values 'n (numE 2)))
        (list (values 'm (numE 0))
              (values 'n (numE 2)))))

;; ----------------------------------------

(define (interp-i [i-a : ExpI] [i-classes : (Listof (Symbol * ClassI))]) : Value
  (local [(define a (exp-i->c i-a 'Object))
          (define classes-not-flat
            (map (lambda (i)
                   (values (fst i)
                           (class-i->c-not-flat (snd i))))
                 i-classes))
          (define classes
            (map (lambda (c)
                   (let ([name (fst c)])
                     (values name
                             (flatten-class name classes-not-flat i-classes))))
                 classes-not-flat))]
    (interp a classes (objV 'Object empty) (numV 0) mt-env)))

(module+ test
  (test (interp-i (numI 0) empty)
        (numV 0))

  (test (interp-i
         (sendI (newI 'Posn3D (list (numI 5) (numI 3) (numI 1)))
                'addDist
                (newI 'Posn (list (numI 2) (numI 7))))
         (list posn-i-class
               posn3d-i-class))
        (numV 18)))

;; ============================================================
;; parse & interp-prog

(module+ test
  (print-only-errors #t))

;; ----------------------------------------

(define (parse-class [s : S-Exp]) : (Symbol * ClassI)
  (cond
    [(s-exp-match? `{class SYMBOL extends SYMBOL {ANY ...} ANY ...} s)
     (values (s-exp->symbol (second (s-exp->list s)))
             (classI (s-exp->symbol (fourth (s-exp->list s)))
                     (map parse-field
                          (s-exp->list (fourth (rest (s-exp->list s)))))
                     (map parse-method 
                          (rest (rest (rest (rest (rest (s-exp->list s)))))))))]
    [else (error 'parse-class "invalid input")]))

(define (parse-field [s : S-Exp]) : Symbol
  (cond
   [(s-exp-match? `SYMBOL s)
    (s-exp->symbol s)]
   [else (error 'parse-field "invalid input")]))

(define (parse-method [s : S-Exp]) : (Symbol * ExpI)
  (cond
   [(s-exp-match? `[SYMBOL {arg} ANY] s)
    (values (s-exp->symbol (first (s-exp->list s)))
            (parse (third (s-exp->list s))))]
   [else (error 'parse-method "invalid input")]))

(define (parse [s : S-Exp]) : ExpI
  (cond
   [(s-exp-match? `NUMBER s) (numI (s-exp->number s))]
   [(s-exp-match? `arg s) (argI)]
   [(s-exp-match? `this s) (thisI)]
   [(s-exp-match? `true s) (trueI)]
   [(s-exp-match? `false s) (falseI)]
   [(s-exp-match? `SYMBOL s) (idI (s-exp->symbol s))]
   [(s-exp-match? `{+ ANY ANY} s)
    (plusI (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? `{* ANY ANY} s)
    (multI (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? `{= ANY ANY} s)
    (equalsI (parse (second (s-exp->list s)))
           (parse (third (s-exp->list s))))]
   [(s-exp-match? `{new SYMBOL ANY ...} s)
    (newI (s-exp->symbol (second (s-exp->list s)))
          (map parse (rest (rest (s-exp->list s)))))]
   [(s-exp-match? `{get ANY SYMBOL} s)
    (getI (parse (second (s-exp->list s)))
          (s-exp->symbol (third (s-exp->list s))))]
   [(s-exp-match? `{send ANY SYMBOL ANY} s)
    (sendI (parse (second (s-exp->list s)))
           (s-exp->symbol (third (s-exp->list s)))
           (parse (fourth (s-exp->list s))))]
   [(s-exp-match? `{super SYMBOL ANY} s)
    (superI (s-exp->symbol (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
   [(s-exp-match? `{select ANY ANY} s)
    (selectI (parse (second (s-exp->list s)))
            (parse (third (s-exp->list s))))]
   [(s-exp-match? `{instanceof ANY SYMBOL} s)
    (instanceI (parse (second (s-exp->list s)))
            (s-exp->symbol (third (s-exp->list s))))]
   [(s-exp-match? `{let {[SYMBOL : ANY ANY]} ANY} s)
     (let ([bs (s-exp->list (first
                             (s-exp->list (second
                                           (s-exp->list s)))))])
       (appI (lamI (s-exp->symbol (first bs))
                   (parse-type (third bs))
                   (parse (third (s-exp->list s))))
             (parse (fourth bs))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY]} ANY} s)
     (let ([arg (s-exp->list
                 (first (s-exp->list 
                         (second (s-exp->list s)))))])
       (lamI (s-exp->symbol (first arg))
             (parse-type (third arg))
             (parse (third (s-exp->list s)))))]
    [(s-exp-match? `{ANY ANY} s)
     (appI (parse (first (s-exp->list s)))
           (parse (second (s-exp->list s))))]
   [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type
  (cond
    [(s-exp-match? `num s) 
     (numT)]
    [(s-exp-match? `bool s)
     (boolT)]
    [(s-exp-match? `(ANY -> ANY) s)
     (arrowT (parse-type (first (s-exp->list s)))
             (parse-type (third (s-exp->list s))))]
    [(s-exp-match? `obj s)
     (objT)]
    [(s-exp-match? `? s) 
     (varT (box (none)))]
    [else (error 'parse-type "invalid input")]))

;; typecheck!------------------------------------
(define (typecheck [a : Exp] [tenv : Type-Env])
  (type-case Exp a
    [(numE n) (numT)]
    [(plusE l r) (typecheck-nums l r tenv)]
    [(multE l r) (typecheck-nums l r tenv)]
    [(idE n) (type-lookup n tenv)]
    [(lamE n arg-type body)
     (arrowT arg-type
             (typecheck body 
                        (extend-env (tbind n arg-type)
                                    tenv)))]
    [(appE fun arg)
     (local [(define result-type (varT (box (none))))]
       (begin
         (unify! (arrowT (typecheck arg tenv)
                         result-type)
                 (typecheck fun tenv)
                 fun)
         result-type))]
    [(trueE) ....]
    [(falseE) ....]
    [(argE) ....]
    [(thisE) ....]
    [(equalsE fst snd) ....]
    [(newE class-name args) ....]
    [(getE obj-expr field-name) ....]
    [(sendE obj-expr method-name arg-expr) ....]
    [(ssendE obj-expr class-name method-name arg-expr) ....]
    [(selectE test object) ....]
    [(instanceE object comp) ....]
    
    ))

(define (typecheck-nums l r tenv)
  (begin
    (unify! (typecheck l tenv)
            (numT)
            l)
    (unify! (typecheck r tenv)
            (numT)
            r)
    (numT)))


;; lookup ----------------------------------------
(define (make-lookup [name-of : ('a -> Symbol)] [val-of : ('a -> 'b)])
  (lambda ([name : Symbol] [vals : (Listof 'a)]) : 'b
          (cond
            [(empty? vals)
             (error 'find "free variable")]
            [else (if (equal? name (name-of (first vals)))
                      (val-of (first vals))
                      ((make-lookup name-of val-of) name (rest vals)))])))

(define lookup
  (make-lookup bind-name bind-val))


(define type-lookup
  (make-lookup tbind-name tbind-type))

;; unify! ----------------------------------------
(define (unify! [t1 : Type] [t2 : Type] [expr : Exp])
  (type-case Type t1
    [(varT is1)
     (type-case (Optionof Type) (unbox is1)
       [(some t3) (unify! t3 t2 expr)]
       [(none)
        (local [(define t3 (resolve t2))]
          (if (eq? t1 t3)
              (values)
              (if (occurs? t1 t3)
                  (type-error expr t1 t3)
                  (begin
                    (set-box! is1 (some t3))
                    (values)))))])]
    [else
     (type-case Type t2
       [(varT is2) (unify! t2 t1 expr)]
       [(numT) (type-case Type t1
                 [(numT) (values)]
                 [else (type-error expr t1 t2)])]
       [(boolT) (type-case Type t1
                  [(boolT) (values)]
                  [else (type-error expr t1 t2)])]
       [(arrowT a2 b2) (type-case Type t1
                         [(arrowT a1 b1)
                          (begin
                            (unify! a1 a2 expr)
                            (unify! b1 b2 expr))]
                         [else (type-error expr t1 t2)])]
       [(objT) (type-case Type t1
                 [(objT) (values)]
                 [else (type-error expr t1 t2)])])]))

(define (resolve [t : Type]) : Type
  (type-case Type t
    [(varT is)
     (type-case (Optionof Type) (unbox is)
       [(none) t]
       [(some t2) (resolve t2)])]
    [else t]))

(define (occurs? [r : Type] [t : Type]) : Boolean
  (type-case Type t
    [(numT) #f]
    [(boolT) #f]
    [(arrowT a b)
     (or (occurs? r a)
         (occurs? r b))]
    [(varT is) (or (eq? r t) ; eq? checks for the same box
                   (type-case (Optionof Type) (unbox is)
                     [(none) #f]
                     [(some t2) (occurs? r t2)]))]
    [(objT) #f]))

(define (type-error [a : Exp] [t1 : Type] [t2 : Type])
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append
                       " type "
                       (string-append
                        (to-string t1)
                        (string-append
                         " vs. "
                         (to-string t2))))))))





(module+ test
  (test (parse `0)
        (numI 0))
  (test (parse `arg)
        (argI))
  (test (parse `this)
        (thisI))
  (test (parse `{+ 1 2})
        (plusI (numI 1) (numI 2)))
  (test (parse `{* 1 2})
        (multI (numI 1) (numI 2)))
  (test (parse `{new Posn 1 2})
        (newI 'Posn (list (numI 1) (numI 2))))
  (test (parse `{get 1 x})
        (getI (numI 1) 'x))
  (test (parse `{send 1 m 2})
        (sendI (numI 1) 'm (numI 2)))
  (test (parse `{super m 1})
        (superI 'm (numI 1)))
  (test (parse `x)
            (idI 'x))

  (test (parse-field `x)
        'x)
  (test/exn (parse-field `{x 1})
            "invalid input")

  (test (parse-method `[m {arg} this])
        (values 'm (thisI)))
  (test/exn (parse-method `{m 1 2})
            "invalid input")
  
  (test (parse-class `{class Posn3D extends Posn
                        {x y z}
                        [m1 {arg} arg]
                        [m2 {arg} this]})
        (values 'Posn3D 
                (classI 'Posn
                        (list 'x 'y 'z)
                        (list (values 'm1 (argI))
                              (values 'm2 (thisI))))))
  (test/exn (parse-class `{class})
            "invalid input"))

;; ----------------------------------------

(define (interp-prog [classes : (Listof S-Exp)] [a : S-Exp]) : S-Exp
  (let ([v (interp-i (parse a)
                     (map parse-class classes))])
    (type-case Value v
      [(numV n) (number->s-exp n)]
      [(objV class-name field-vals) `object]
      [(closV n b e) `function]
      [(boolV b) (boolean->s-exp b)])))

(module+ test
  (test (interp-prog
         (list
          `{class Empty extends Object
             {}})
         `{new Empty})
        `object)

  (test (interp-prog 
         (list
          `{class Posn extends Object
             {x y}
             [mdist {arg} {+ {get this x} {get this y}}]
             [addDist {arg} {+ {send arg mdist 0}
                               {send this mdist 0}}]}
          
          `{class Posn3D extends Posn
             {z}
             [mdist {arg} {+ {get this z} 
                             {super mdist arg}}]})
         
         `{send {new Posn3D 5 3 1} addDist {new Posn 2 7}})
        `18))

;Problem 1 Tests
(module+ test
(test (interp-prog (list)
 `{new Object})
 `object)
 (test (interp-prog (list `{class Fish extends Object
 {size color}})
 `{new Object})
 `object)

;Problem 2 Tests
(test (interp-prog (list `{class Snowball extends Object
 {size}
[zero {arg} this]
[nonzero {arg}
 {new Snowball {+ 1 {get this size}}}]})
 `{get {select 0 {new Snowball 1}} size})
 `1)

 (test (interp-prog (list `{class Snowball extends Object
 {size}
[zero {arg} this]
 [nonzero {arg}
 {new Snowball {+ 1 {get this size}}}]})
 `{get {select {+ 1 2} {new Snowball 1}} size})
 `2)

(test/exn (interp-prog (list `{class Snowball extends Object
 {size}
[zero {arg} this]
 [nonzero {arg}
 {new Snowball {+ 1 {get this size}}}]})
 `{get {select {new Snowball 1} {new Snowball 1}} size})
 "not a number")

(test/exn (interp-prog (list `{class Snowball extends Object
 {size}
[zero {arg} this]
 [nonzero {arg}
 {new Snowball {+ 1 {get this size}}}]})
 `{get {select {+ 1 2} {+ 1 2}} size})
 "not an object")

(test/exn (interp-prog (list `{class Snowball extends Object
 {size}
 [nonzero {arg}
 {new Snowball {+ 1 {get this size}}}]})
 `{get {select 0 {new Snowball 1}} size})
 "find: not found: zero")

(test/exn (interp-prog (list `{class Snowball extends Object
 {size}
[zero {arg} this]
 })
 `{get {select {+ 1 2} {new Snowball 1}} size})
          "find: not found: nonzero")



;Problem 3 Tests



(test (interp-prog (list `{class Fish extends Object
 {size color}})
 `{instanceof 1 Object})
 `1)

(test (interp-prog (list `{class Fish extends Object
 {size color}})
 `{instanceof {new Fish 1 2} Object})
 `0)


 (test (interp-prog (list `{class Fish extends Object
 {size color}})
 `{instanceof {new Object} Fish})
 `1)

(test (interp-prog (list `{class Fish extends Object
 {size color}}
                         `{class Cat extends Object
 {size color}}
                         `{class Shark extends Fish
 {teeth}})
 `{instanceof {new Shark 1 2 3} Cat})
 `1)
 
 (test (interp-prog (list `{class Fish extends Object
 {size color}})
 `{instanceof {new Fish 1 2} Fish})
 `0)
 
 (test (interp-prog (list `{class Fish extends Object
 {size color}}
 `{class Shark extends Fish
 {teeth}})
 `{instanceof {new Shark 1 2 3} Fish})
 `0)
 
 (test (interp-prog (list `{class Fish extends Object
 {size color}}
 `{class Shark extends Fish
 {teeth}}
 `{class Hammerhead extends Shark
 {}})
 `{instanceof {new Hammerhead 1 2 3} Fish})
 `0)
 
 (test (interp-prog (list `{class PlainFish extends Object
 {size}}
 `{class ColorFish extends PlainFish
 {color}}
 `{class Bear extends Object
 {size color}
 [rate-food {arg}
 {+ {instanceof arg ColorFish}
 {get arg color}}]})
 `{send {new Bear 100 5} rate-food {new ColorFish 10 3}})
 `3))


;Equality Tests:
(module+ test
(test (interp-prog (list) `{= 1 1}) `#t)
(test (interp-prog (list) `{= 1 2}) `#f)
(test (interp-prog (list) `{= 1 true}) `#f)
(test (interp-prog (list) `{= false false}) `#t)
(test (interp-prog (list `{class Fish extends Object
 {size color}}) `{= (new Fish 1 2) false}) `#f)
(test (interp-prog (list `{class Fish extends Object
 {size color}}
                         `{class Shark extends Object
 {size color}}) `{= (new Fish 1 2) (new Shark 1 2)}) `#t)
(test (interp-prog (list `{class Fish extends Object
 {size color}}
                         `{class Shark extends Object
 {size color}}) `{= (new Fish 1 2) (new Shark 1 3)}) `#f)
(test (interp-prog (list `{class Fish extends Object
 {size color}}
                         `{class Shark extends Object
 {size c}}) `{= (new Fish 1 2) (new Shark 1 2)}) `#f))


;HW8 Tests:
(module+ test
(test (parse `2)
        (numI 2))
  (test (parse `x) ; note: backquote instead of normal quote
        (idI 'x))
  (test (parse `{+ 2 1})
        (plusI (numI 2) (numI 1)))
  (test (parse `{* 3 4})
        (multI (numI 3) (numI 4)))
  (test (parse `{+ {* 3 4} 8})
        (plusI (multI (numI 3) (numI 4))
               (numI 8)))
  (test (parse `{let {[x : num {+ 1 2}]}
                  y})
        (appI (lamI 'x (numT) (idI 'y))
              (plusI (numI 1) (numI 2))))
  (test (parse `{lambda {[x : num]} 9})
        (lamI 'x (numT) (numI 9)))
  (test (parse `{double 9})
        (appI (idI 'double) (numI 9)))
  (test (parse-type `num)
        (numT))
  (test (parse-type `bool)
        (boolT))
  (test (parse-type `(num -> bool))
        (arrowT (numT) (boolT)))
  (test (parse-type `?)
        (varT (box (none))))
  (test (interp-i   (parse `{lambda {[x : num]} {+ x x}}) (list))
        (closV 'x (plusE (idE 'x) (idE 'x)) mt-env))
  (test (interp-prog (list)  `{lambda {[x : num]} {+ x x}})
        `function)
  (test (interp-i (parse `{let {[x : num 5]}
                          {+ x x}})
                (list))
        (numV 10))
  (test (interp-i (parse `{let {[x : num 5]}
                          {let {[x : num {+ 1 x}]}
                            {+ x x}}})
                (list))
        (numV 12))
  (test (interp-i (parse `{let {[x : num 5]}
                          {let {[y : num 6]}
                            x}})
                (list))
        (numV 5))
  (test (interp-i (parse `{{lambda {[x : num]} {+ x x}} 8})
                (list))
        (numV 16))

  (test/exn (interp-i (parse `{1 2}) (list))
            "not a function")
  (test/exn (interp-i (parse `{let {[bad : (num -> num) {lambda {[x : num]} {+ x y}}]}
                              {let {[y : num 5]}
                                {bad 2}}})
                    (list))
            "free variable")
(test/exn (parse `{{+ 1 2}})
            "invalid input")
(test/exn (parse-type `1)
            "invalid input")
  (test (parse-type `obj) (objT))


  (test (typecheck (exp-i->c (parse `10) 'Object) mt-env)
        (numT))
  (test (typecheck (exp-i->c (parse `{+ 10 17}) 'Object) mt-env)
        (numT))
  (test (typecheck (exp-i->c (parse `{* 10 17}) 'Object) mt-env)
        (numT))
  (test (typecheck (exp-i->c (parse `{lambda {[x : num]} 12}) 'Object) mt-env)
        (arrowT (numT) (numT)))
  (test (typecheck (exp-i->c (parse `{lambda {[x : num]} {lambda {[y : bool]} x}}) 'Object) mt-env)
        (arrowT (numT) (arrowT (boolT)  (numT))))

  (test (resolve (typecheck (exp-i->c (parse `{{lambda {[x : num]} 12}
                                     {+ 1 17}}) 'Object)
                            mt-env))
        (numT))

  (test (resolve (typecheck (exp-i->c (parse `{let {[x : num 4]}
                                      {let {[f : (num -> num)
                                               {lambda {[y : num]} {+ x y}}]}
                                        {f x}}}) 'Object)
                            mt-env))
        (numT))

  (test/exn (typecheck (exp-i->c (parse `{1 2}) 'Object)
                       mt-env)
            "no type")
  (test/exn (typecheck (exp-i->c (parse `{{lambda {[x : bool]} x} 2}) 'Object)
                       mt-env)
            "no type")
  (test/exn (typecheck (exp-i->c (parse `{+ 1 {lambda {[x : num]} x}}) 'Object)
                       mt-env)
            "no type")
  (test/exn (typecheck (exp-i->c (parse `{* {lambda {[x : num]} x} 1}) 'Object)
                       mt-env)
            "no type")
)
  (module+ test
  (define a-type-var (varT (box (none))))
  (define an-expr (numE 0))
  
  (test (unify! (numT) (numT) an-expr)
        (values))
  (test (unify! (boolT) (boolT) an-expr)
        (values))
  (test (unify! (arrowT (numT) (boolT)) (arrowT (numT) (boolT)) an-expr)
        (values))
  (test (unify! (varT (box (some (boolT)))) (boolT) an-expr)
        (values))
  (test (unify! (boolT) (varT (box (some (boolT)))) an-expr)
        (values))
  (test (unify! a-type-var a-type-var an-expr)
        (values))
  (test (unify! a-type-var (varT (box (some a-type-var))) an-expr)
        (values))
  
  (test (let ([t (varT (box (none)))])
          (begin
            (unify! t (boolT) an-expr)
            (unify! t (boolT) an-expr)))
        (values))
  
  (test/exn (unify! (numT) (boolT) an-expr)
            "no type")
  (test/exn (unify! (numT) (arrowT (numT) (boolT)) an-expr)
            "no type")
  (test/exn (unify! (arrowT (numT) (numT)) (arrowT (numT) (boolT)) an-expr)
            "no type")
  (test/exn (let ([t (varT (box (none)))])
              (begin
                (unify! t (boolT) an-expr)
                (unify! t (numT) an-expr)))
            "no type")
  (test/exn (unify! a-type-var (arrowT a-type-var (boolT)) an-expr)
            "no type")
  (test/exn (unify! a-type-var (arrowT (boolT) a-type-var) an-expr)
            "no type")
  
  (test (resolve a-type-var)
        a-type-var)
  (test (resolve (varT (box (some (numT)))))
        (numT))
  
  (test (occurs? a-type-var a-type-var)
        #t)
  (test (occurs? a-type-var (varT (box (none))))
        #f)
  (test (occurs? a-type-var (varT (box (some a-type-var))))
        #t)
  (test (occurs? a-type-var (numT))
        #f)
  (test (occurs? a-type-var (boolT))
        #f)
  (test (occurs? a-type-var (arrowT a-type-var (numT)))
        #t)
  (test (occurs? a-type-var (arrowT (numT) a-type-var))
        #t))


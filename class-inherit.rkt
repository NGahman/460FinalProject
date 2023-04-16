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
  )

(define-type Class
  (classC [super-name : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * Exp))]))

(define-type Value
  (boolV [b : Boolean])
  (numV [n : Number])
  (objV [class-name : Symbol]
        [field-values : (Listof Value)]))

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

(define interp : (Exp (Listof (Symbol * Class)) Value Value -> Value)
  (lambda (a classes this-val arg-val)
    (local [(define (recur expr)
              (interp expr classes this-val arg-val))]
      (type-case Exp a
        [(numE n) (numV n)]
        [(trueE) (boolV #t)]
        [(falseE) (boolV #f)]
        [(plusE l r) (num+ (recur l) (recur r))]
        [(multE l r) (num* (recur l) (recur r))]
        [(thisE) this-val]
        [(argE) arg-val]
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
               arg-val))]))

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
    (interp a (list posn-class posn3D-class) (numV -1) (numV -1))))

;; ----------------------------------------

(module+ test
  (test (interp (numE 10) 
                empty (objV 'Object empty) (numV 0))
        (numV 10))
  (test (interp (plusE (numE 10) (numE 17))
                empty (objV 'Object empty) (numV 0))
        (numV 27))
  (test (interp (multE (numE 10) (numE 7))
                empty (objV 'Object empty) (numV 0))
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
  (trueI)
  (falseI)
  (argI)
  (thisI)
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
             [comp : Symbol]))

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
      [(trueI) (trueE)]
      [(falseI) (falseE)]
      [(argI) (argE)]
      [(thisI) (thisE)]
      [(equalsI fst snd) (equalsE (recur fst) (recur snd))]
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
      [(instanceI object comp) (instanceE (recur object) comp)])))

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
    (interp a classes (objV 'Object empty) (numV 0))))

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
   [else (error 'parse "invalid input")]))

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
  (test/exn (parse `x)
            "invalid input")

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
 {size c}}) `{= (new Fish 1 2) (new Shark 1 2)}) `#f)
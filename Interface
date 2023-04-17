(define-type Interface
  (interfaceC [method-names : (Listof Symbol)]))

(define-type Class
  (classC [super-name : Symbol]
          [field-names : (Listof Symbol)]
          [methods : (Listof (Symbol * Exp))]
          [interfaces : (Listof Interface)]))

(define-type Value
  (boolV [b : Boolean])
  (numV [n : Number])
  (objV [class-name : Symbol]
        [field-values : (Listof Value)]
        [interfaces : (Listof Interface)]))

;Could opt for having interfaces to keep track of method signatures?

[(sendE obj-expr method-name arg-expr)
 (local [(define obj (recur obj-expr))
         (define arg-val (recur arg-expr))]
   (type-case Value obj
     [(objV class-name field-vals interfaces)
      (local [(define class (find classes class-name))]
        (let loop ([interfaces interfaces])
          (type-case (Listof Interface) interfaces
            [empty (error 'interp "no method found")]
            [(cons interface rest-interfaces)
             (if (member method-name (Interface-method-names interface) symbol=?)
                 (let ([method (find class (Interface-method-names interface) symbol=? method-name (lambda (m) (fst m)))])
                   (interp (snd method) classes obj arg-val))
                 (loop rest-interfaces))])))]))]

;Modified sendE in the interpreter to check if an objects interfaces contains the method signature

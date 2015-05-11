;;
;; Neural Parametric Curve Connectivity core language module.
;;
;; Copyright 2012-2014 Ivan Raikov and the Okinawa Institute of Science and Technology
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; A full copy of the GPL license can be found at
;; <http://www.gnu.org/licenses/>.
;;

(module picnic-core

        (make-picnic-core picnic-verbose
         picnic:error picnic:warning picnic:version-string
         picnic:env-copy picnic:quantity?
         picnic:rhs? picnic:expr? picnic:subst-term picnic:binding? picnic:bind
         picnic:math-constants
         picnic-intern picnic-scoped eval-picnic-system-decls 
         CONST CONFIG ASGN INITIAL PS SEGPS SET SWC EXTERNAL PRIM LABEL

         )


        (import scheme chicken)

        
        (require-extension srfi-69
                           datatype matchable vector-lib mpi
                           varsubst digraph graph-bfs graph-cycles
                           mathh picnic-utils)


        (require-library srfi-1 srfi-4 irregex files posix data-structures)


        (import 
                (only srfi-1 
                      cons* fold filter-map filter every zip list-tabulate delete-duplicates partition 
                      first second third take
                      lset-union)
                (only srfi-4 
                      s32vector s32vector-length s32vector-ref
                      f64vector f64vector? f64vector-ref f64vector-length f64vector->list list->f64vector)
                (only srfi-13 string= string< string-null? string-concatenate)
                (only irregex string->irregex irregex-match)
                (only files make-pathname)
                (only posix glob)
                (only extras read-lines pp fprintf )
                (only ports with-output-to-port )
                (only data-structures ->string alist-ref compose identity string-split sort atom? intersperse)
                (only lolevel extend-procedure procedure-data extended-procedure?)
                )


        (include "mathh-constants")



        (define (picnic:warning x . rest)
          (let loop ((port (open-output-string)) (objs (cons x rest)))
            (if (null? objs)
                (begin
                  (newline port)
                  (print-error-message (get-output-string port) 
                                       (current-error-port) "picnic warning"))
                (begin (display (car objs) port)
                       (display " " port)
                       (loop port (cdr objs))))))


        (define (picnic:error x . rest)
          (let ((port (open-output-string)))
            (if (port? x)
                (begin
                  (display "[" port)
                  (display (port-name x) port)
                  (display "] " port)))
            (let loop ((objs (if (port? x) rest (cons x rest))))
              (if (null? objs)
                  (begin
                    (newline port)
                    (error 'picnic (get-output-string port)))
                  (let ((obj (car objs)))
                    (if (procedure? obj) 
                        (with-output-to-port port obj)
                        (begin
                          (display obj port)
                          (display " " port)))
                    (loop (cdr objs)))))))


        (include "picnic-version.scm")


        (define (picnic:version-string) 
          (sprintf "PICNIC (http://wiki.call-cc.org/picnic) version ~A~%" picnic-version))




        (define (make-opt pred?) (lambda (x) 
                                   (or (not x) (pred? x))))

        (define (sign x) (if (negative? x) -1.0 1.0))

        (define (f64vector-empty? x) (zero? (f64vector-length x)))


        (define (eval-math x . rest)
          (define prelude
            `(
              (import mathh random-mtzig)
              (define (random-seed) (inexact->exact (current-seconds)))
              (define (random-init seed) (random-mtzig:init seed))
              (define (random-normal mean sdev st)
                (+ mean (* sdev (random-mtzig:randn! st))))
              (define (random-uniform low high st)
                (let ((rlo (if (< low high) low high))
                      (rhi (if (< low high) high low))) 
                  (let ((delta (+ 1 (- rhi rlo)))
                        (v (random-mtzig:randu! st)))
                    (+ rlo (floor (* delta v))) ))
                )
              ))
          (if (null? rest)
              (let ((ex `(begin ,@prelude ,x)))
                (eval ex))
              (let ((ex `(begin ,@prelude (list ,x . ,rest))))
                (eval ex))
              )
          )
        

        (define (expr? x)  
          (or (symbol? x) (number? x) (string? x) 
              (match x 
                     (((? symbol?) ())  #t)
                     (((? symbol?) () . rest)  (expr? rest))
                     (((? symbol?) . rest)  (every expr? rest)) 
                     (((and hd (? expr?)) . rest)  (every expr? rest))
                     (else #f))))


        (define (rhs? x)  
          (or (symbol? x) (number? x) (string? x)
              (match x 
                     (('let bnds body) (and (rhs? body)
                                            (every (lambda (b) 
                                                     (and (symbol? (car b)) (rhs? (cadr b)))) bnds)))
                     (((? symbol?) . rest)  (every rhs? rest)) 
                     (else #f))))


        (define (setexpr? x)  
          (match x 
                 (('population pop)  (symbol? pop))
                 (('section pop sec) (and (symbol? pop) (symbol? sec)))
                 (('union x y)       (and (setexpr? x) (setexpr? y)))
                 (else #f)))


        (define picnic:expr?   expr?)
        (define picnic:rhs?    rhs?)
        (define (picnic:sampler? x)
          (match x
                 ((uniform) #t)
                 ((polynomial c0 c1 c2) #t)
                 (else #f)))
          

        (define-datatype picnic:quantity picnic:quantity?
          (SYSNAME    (name symbol?) )
          (LABEL      (v symbol?) )
          (CONFIG     (name symbol?) )
          (CONST      (name symbol?) (value number?) )
          (ASGN       (name symbol?) (value number?) (rhs rhs?) )
          (INITIAL    (name symbol?) (rhs rhs?) )
          (SEGPS      (name    symbol?) 
                      (gfun    symbol?)
                      (sfun    picnic:sampler?)
                      (initial (lambda (x) (or (not x) (rhs? x))))
                      (nsegs   integer?)
                      (nsegpts integer?)
                      )
          (PS         (name     symbol?) 
                      (gfun     symbol?)
                      (sfun     picnic:sampler?)
                      (initial  (lambda (x) (or (not x) (rhs? x))))
                      (npts     integer?)
                      )
          (SWC        (name     symbol?) 
                      (path     string?)
                      (type     integer?)
                      (nsegs    integer?)
                      )
          (SET        (name symbol?)
                      (rhs  setexpr?)
                      )
          (PRIM       (name symbol?) (value identity))
          (EXTERNAL   (local-name symbol?) (name symbol?) (namespace (make-opt symbol?)))
          (EXPORTS    (lst (lambda (x) (and (list? x) (every symbol? x)))))
          (COMPONENT  (name symbol?) (type symbol?) (lst (lambda (x) (and (list? x) (every symbol? x)))) (scope-subst list?))
          (FUNCTOR    (name symbol?) (args (lambda (x) (and (list? x) (every symbol? x)))) (type symbol?)  (decls list?))
          (DISPATCH   (value procedure?))
          )


        (define (picnic-intern sym)
          (string->symbol (string-append "#" (symbol->string sym))))


        (define (picnic-scoped scope sym)
          (let ((ss (map ->string scope)))
            (if (null? ss) 
                (->string sym)
                (string->symbol (string-concatenate (intersperse (append ss (list (->string sym))) "."))))
            ))


        (define fresh (compose string->symbol symbol->string gensym))


        (define (alist? x)
          (every (lambda (x) (and (pair? x) (symbol? (car x)))) x))


        (define (lookup-def k lst . rest)
          (let-optionals rest ((default #f))
                         (let ((k (->string k))) 
                           (let recur ((kv #f) (lst lst))
                             (if (or kv (null? lst))
                                 (if (not kv) default
                                     (match kv ((k v) v) (else (cdr kv))))
                                 (let ((kv (car lst)))
                                   (recur (and (string=? (->string (car kv)) k) kv)
                                          (cdr lst)) ))))))


        (define (picnic:subst-term t subst k)
          (assert (every symbol? (map car subst)))
          (if (null? subst) t
              (match t
                     (('if c t e)
                      `(if ,(k c subst) ,(k t subst) ,(k e subst)))
                     
                     (('let bs e)
                      (let ((r `(let ,(map (lambda (b) `(,(car b) ,(k (cadr b) subst))) bs) ,(k e subst))))
                        (k r subst)))
                     
                     ((f . es)
                      (cons (k f subst) (map (lambda (e) (k e subst)) es)))
                     
                     ((? symbol? )  (lookup-def t subst t))
                     
                     ((? atom? ) t))
              ))
        

        (define (picnic:binding? t) 
          (and (list? t) (eq? 'let (car t)) (cdr t)))

        (define (picnic:bind ks vs e) `(let ,(zip ks vs) ,e))

        (define picnic:env-copy hash-table-copy)

        (define picnic:math-constants
          (zip 
           `(E 1/E E^2 E^PI/4 LOG2E LOG10E LN2 LN3 LNPI LN10 1/LN2 1/LN10 PI PI/2
               PI/4 1/PI 2/PI 2/SQRTPI SQRTPI PI^2 DEGREE SQRT2 1/SQRT2 SQRT3 SQRT5
               SQRT10 CUBERT2 CUBERT3 4THRT2 GAMMA1/2 GAMMA1/3 GAMMA2/3 PHI LNPHI
               1/LNPHI EULER E^EULER SIN1 COS1 ZETA3)
           (list E 1/E E^2 E^PI/4 LOG2E LOG10E LN2 LN3 LNPI LN10 1/LN2 1/LN10 PI PI/2
                 PI/4 1/PI 2/PI 2/SQRTPI SQRTPI PI^2 DEGREE SQRT2 1/SQRT2 SQRT3 SQRT5
                 SQRT10 CUBERT2 CUBERT3 4THRT2 GAMMA1/2 GAMMA1/3 GAMMA2/3 PHI LNPHI
                 1/LNPHI EULER E^EULER SIN1 COS1 ZETA3)))
        


        (define (make-picnic-core . alst)

          (define local-config (lookup-def 'config alst))

          ;; floating point precision (single or double; default is double)
          (define  inttype        'int)
          (define  fptype (lookup-def 'fpprec alst 'double))
          (define  boundstype     'bounds)
          (define  rngstatetype   'rngstate)
          (define  stringtype     'string)
          (define  pathtype       'path)
          (define  pointtype      'point)
          (define  pointsettype   'pointset)
          (define  projectiontype 'projection)
          (define  settype        'set)
          (define  proctype       'proc)

          (define builtin-arith-ops
            `(+ - * / pow neg abs atan asin acos sin cos exp ln
                sqrt tan cosh sinh tanh hypot gamma lgamma log10 log2 log1p ldexp cube
                > < <= >= = and or round ceiling floor max min
                randomSeed randomInit randomNormal randomUniform ))

          (define builtin-projection-ops
                `(Projection SegmentProjection)
                )

          (define builtin-point-ops
                `(pointCoord)
                )

          (define builtin-path-ops
                `(LineSegment Harmonic)
                )

          (define builtin-bounds-ops
                `(Bounds)
                )

          (define builtin-pointset-ops
                `(PointsFromFile UniformRandomPointProcess)
                )

          (define builtin-ops (append builtin-projection-ops 
                                      builtin-bounds-ops 
                                      builtin-path-ops 
                                      builtin-point-ops 
                                      builtin-pointset-ops
                                      builtin-arith-ops 
                                      ))

          (define (add-primitives! env)
            (let (
                  (pointset-procs
                   (list load-points-from-file UniformRandomPointProcess)
                   )

                  (pointset-exprs
                   '(load-points-from-file UniformRandomPointProcess)
                   )

                  (point-procs
                   (list pointCoord)
                   )

                  (point-exprs
                   '(pointCoord)
                   )

                  (path-procs
                   (list make-line-segment make-harmonic)
                   )

                  (path-exprs
                   '(make-line-segment make-harmonic)
                   )

                  (bounds-procs
                   (list Bounds)
                   )

                  (bounds-exprs
                   '(Bounds)
                   )

                  (projection-procs
                   (list projection segment-projection)
                   )

                  (projection-exprs
                   '(projection segment-projection)
                   )

                  (prim-exprs
                   '(fp+ fp- fp* fp/ expt fpneg
                     abs atan asin acos sin cos exp log sqrt tan 
                     cosh sinh tanh hypot gamma lgamma log10 log2 log1p ldexp
                     (lambda (x) (* x x x))
                     fp> fp< fp<= fp>= fp=
                     (lambda (x y) (and x y)) (lambda (x y) (or x y)) 
                     round ceiling floor fpmax fpmin
                     random-seed random-init random-normal random-uniform
                     ))
                  )

              (for-each (lambda (n v qb fms rt) 
                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-projection-ops
                        projection-procs
                        projection-exprs
                        `((,fptype ,settype  ,settype) (,fptype ,settype  ,settype))
                        `(,projectiontype ,projectiontype)
                        )

              (for-each (lambda (n v qb fms rt) 
                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-path-ops
                        path-procs
                        path-exprs
                        `((,pointtype ,fptype  ,fptype  ,fptype)
                          (,inttype ,fptype ,fptype ,fptype ,inttype))
                        `(,pathtype ,pathtype)
                        )

              (for-each (lambda (n v qb fms rt) 
                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-point-ops
                        point-procs
                        point-exprs
                        `(( ,inttype ,pointtype))
                        `(,fptype)
                        )

              (for-each (lambda (n v qb fms rt) 
                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-bounds-ops
                        bounds-procs
                        bounds-exprs
                        `((,fptype ,fptype ,fptype ,fptype))
                        `(,boundstype)
                        )

              (for-each (lambda (n v qb fms rt) 
                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-pointset-ops
                        pointset-procs
                        pointset-exprs
                        `((,stringtype) (,inttype ,rngstatetype ,rngstatetype ,boundstype))
                        `(,pointsettype ,pointsettype)
                        )


              (for-each (lambda (n v qb fms rt) 

                          (let ((fb (extend-procedure 
                                     v `((name ,n) (eval-body ,qb)
                                         (rt ,rt) (formals ,fms)))))
                            (hash-table-set! env n fb)))
                        builtin-arith-ops
                        (apply eval-math prim-exprs)
                        prim-exprs
                        `((,fptype ,fptype) (,fptype ,fptype) (,fptype ,fptype) (,fptype ,fptype) 
                          (,fptype ,fptype) (,fptype)
                          (,fptype) (,fptype) (,fptype) (,fptype) (,fptype) (,fptype) (,fptype)
                          (,fptype) (,fptype) (,fptype)
                          (,fptype) (,fptype) (,fptype) (,fptype) (,fptype) (,fptype) (,fptype)
                          (,fptype) (,fptype) (,fptype)
                          (,fptype) 
                          (bool bool) (bool bool) (bool bool) (bool bool) (bool bool) (bool bool) (bool bool) 
                          (,fptype) (,fptype) (,fptype) (,fptype ,fptype) (,fptype ,fptype) 
                          () (int) (,fptype ,fptype ,rngstatetype) (,fptype ,fptype ,rngstatetype) 
                          )
                        `(,fptype ,fptype ,fptype ,fptype 
                                  ,fptype ,fptype
                                  ,fptype ,fptype ,fptype ,fptype ,fptype ,fptype ,fptype
                                  ,fptype ,fptype ,fptype
                                  ,fptype ,fptype ,fptype ,fptype ,fptype ,fptype ,fptype
                                  ,fptype ,fptype ,fptype
                                  ,fptype 
                                  bool bool bool bool bool bool bool 
                                  ,fptype ,fptype ,fptype ,fptype ,fptype 
                                  int ,rngstatetype ,fptype ,fptype 
                                   )
                        ))
            )


          (define (add-constants! env)
            (for-each (lambda (kv) (hash-table-set! env (car kv) (cadr kv)))
                      picnic:math-constants))


          (define (enumdeps expr)
            (let loop ((expr expr) (ax (list)) (lbs (list)))
              (match expr 
                     (('let bs e)  (let let-loop ((bs bs) (ax ax) (lbs lbs))
                                     (if (null? bs) (loop e ax lbs)
                                         (let ((x   (first  (car bs)))
                                               (ex  (second (car bs))))
                                           (let* ((lbs1  (cons x lbs))
                                                  (ax1   (loop ex ax lbs)))
                                             (let-loop (cdr bs) ax1 lbs1))))))

                     ((s . es)     (if (symbol? s) (fold (lambda (e ax) (loop e ax lbs)) ax es) 
                                       (fold (lambda (e ax) (loop e ax lbs)) ax (cons s es))))
                     (id           (if (and (symbol? id) (not (member id lbs))) (cons id ax) ax)))))


          (define (binop-fold op lst)
            (if (null? lst) lst
                (match lst
                       ((x)   x)
                       ((x y) `(,op ,x ,y))
                       ((x y . rest) `(,op (,op ,x ,y) ,(binop-fold op rest)))
                       ((x . rest) `(,op ,x ,(binop-fold op rest))))))


          ;; if argument is constant, return the negative of that constant,
          ;; otherwise return `(neg ,expr)
          (define (negate expr)
            (if (number? expr) (- expr)
                `(neg ,expr)))

          ;; 1. make sure all constants in an expression are flonums
          ;; 2. fold expressions like (+ a b c d) into nested binops 
          (define (make-normalize-expr arity-check symbol-check)
            (lambda (expr loc)
              (let recur ((expr expr) (lbs '()))
                (match expr 
                       (('let bs e)         (let ((normalize-bnd  (lambda (lbs) (lambda (x) `(,(first x) ,(recur (second x) lbs)))))
                                                  (lbs1 (append (map first bs) lbs)))
                                              `(let ,(map (normalize-bnd lbs1) bs) ,(recur e lbs1))))
                       (('if c t e)         `(if ,(recur c lbs) ,(recur t lbs) ,(recur e lbs))) 
                       (('+ . es)           (binop-fold '+ (map (lambda (x) (recur x lbs)) es)))
                       (('- . es)           (let ((es1 (map (lambda (x) (recur x lbs)) es)))
                                              (binop-fold '+ (cons (car es1) (map negate (cdr es1))))))
                       (('* . es)           (binop-fold '* (map (lambda (x) (recur x lbs)) es)))
                       (('/ . es)           (binop-fold '/ (map (lambda (x) (recur x lbs)) es)))
                       (('fix n)            n)
                       ((s . es)            (begin
                                              (arity-check s es loc)
                                              (cons s (map (lambda (x) (recur x lbs)) es))))
                       (x                   (cond ((number? x) (exact->inexact x))
                                                  ((symbol? x) (begin (symbol-check x loc lbs) x))
                                                  (else x)))
                       
                       ))))

          (define base-env
            (let ((env (make-hash-table)))
              (add-primitives! env)
              (add-constants! env)
              env))
          
          (define (make-const-env picnic-env)
            (let ((env (picnic:env-copy base-env)))
              (hash-table-for-each picnic-env
                                   (lambda (sym en)
                                     (cond  ((picnic:quantity? en)  
                                             (cases picnic:quantity en
                                                    (CONFIG (name)  
                                                            (let ((value (lookup-def name local-config)))
                                                              (if (not value)
                                                                  (picnic:error 'make-const-env 
                                                                                ": unknown configuration entry" name))
                                                              (hash-table-set! env name value)))
                                                    (CONST (name value)  
                                                           (hash-table-set! env name value))
                                                    (PRIM (name value)  
                                                          (hash-table-set! env name value))))
                                            ((procedure? en)
                                             (hash-table-set! env sym en)))))
              env))

          (define (make-const-ftenv picnic-env)
            (let ((env (make-hash-table)))
              (hash-table-for-each
               picnic-env
               (lambda (sym en)
                 (cond  ((picnic:quantity? en)  
                         (cases picnic:quantity en
                                (CONFIG (name)  
                                       (hash-table-set! env name fptype))
                                (CONST (name value)  
                                       (hash-table-set! env name fptype))
                                (PRIM (name value)  
                                      (hash-table-set! env name fptype))))
                        ((procedure? en)
                         (let ((d (procedure-data en)))
                           (hash-table-set! env sym (lookup-def 'rt d)))))))
              env))


          (define (const-env-entry->value en)
            (cond  ((picnic:quantity? en)  
                    (cases picnic:quantity en
                           (CONFIG (name)  (let ((v (lookup-def name local-config)))
                                             (or (and v v)
                                                 (picnic:error 'const-env-entry->value
                                                               "unknown configuration entry" name))))
                           (CONST (name value)  value)
                           (PRIM (name value)  value)
                           ))
                   ((procedure? en)  en)
                   ((or (number? en) (symbol? en))   en)
                   (else (picnic:error 'const-env-entry->value 
                                       "unknown type of const env entry" en))
                   ))


          (define (system name)
            (let ((env  (picnic:env-copy base-env))
                  (name (if (symbol? name) name (string->symbol name))))
              (hash-table-set! env (picnic-intern 'dispatch)  (DISPATCH picnic-dispatch))
              (hash-table-set! env (picnic-intern 'name)      (SYSNAME name))
              (hash-table-set! env (picnic-intern 'exports)   (EXPORTS (list)))
              (hash-table-set! env (picnic-intern 'toplevel)  (COMPONENT 'toplevel 'toplevel (list) (list)))
              env))


          (define (add-external! picnic-env)
            (lambda (sym typ)
              (match typ
                     ('output
                      (begin
                        (if (not (hash-table-exists? picnic-env sym))
                            (picnic:error 'add-external! "exported quantity " sym " is not defined"))
                        (let* ((exports-sym   (picnic-intern 'exports))
                               (exports       (hash-table-ref picnic-env exports-sym)))
                          (cases picnic:quantity exports
                                 (EXPORTS (lst) (hash-table-set! picnic-env exports-sym (EXPORTS (append lst (list sym)))))
                                 (else  (picnic:error 'add-external! "invalid exports entry " exports))))))
                     
                     (('input sym lsym ns . rest)
                      (let (
                            (lsym (or lsym sym))
                            )
                        (if (hash-table-exists? picnic-env lsym)
                            (picnic:error 'add-import! "import symbol " lsym " is already defined"))
                        
                        ((env-extend! picnic-env) lsym '(external) 'none 
                         `(name ,sym) `(namespace ,ns))))
                     
                     )))


          (define (make-symbol-check picnic-env)
            (lambda (s loc . rest)
              (let-optionals rest ((lbs '()))

                             (if (and (not (hash-table-exists? picnic-env s)) 
                                      (not (member s lbs)))
                                 (begin
                                   (pp (hash-table->alist picnic-env))
                                   (picnic:error 'symbol-check s " in the definition of " loc " is not defined")
                                   )
                                 ))
              ))


          (define (make-arity-check picnic-env)
            (lambda (s args loc)
              (if (hash-table-exists? picnic-env s)
                  (let ((op (hash-table-ref picnic-env s)))
                    (if (extended-procedure? op)
                        (let* ((fd   (procedure-data op))
                               (fms   (lookup-def 'formals fd)))
                          (if (not (= (length fms) (length args)))
                              (picnic:error 'arity-check "procedure " s 
                                          " called with incorrect number of arguments: "
                                          args)))))
                  (picnic:error 'arity-check "symbol " s "(" loc ")" " is not defined")
                  )))


          (define (env-extend! picnic-env)
            (lambda (name type initial . alst)
              (let* ((sym (if (symbol? name) name (string->symbol name)))
                     (arity-check (make-arity-check picnic-env))
                     (symbol-check (make-symbol-check picnic-env))
                     (normalize-expr (make-normalize-expr arity-check symbol-check)))

                (if (hash-table-exists? picnic-env sym)
                    (picnic:error 'env-extend! "quantity " sym " already defined")
                    (match type

                           (('label)   
                            (begin
                              (if (not (symbol? initial)) 
                                  (picnic:error 'env-extend! "label definitions require symbolic value"))
                              (hash-table-set! picnic-env sym (LABEL initial))))

                           (('external)  
                            (begin
                              (let* (
                                     (ns             (lookup-def 'namespace alst))
                                     (external-name  (lookup-def 'name alst))
                                     (x              (EXTERNAL name external-name ns))
                                     )
                                (hash-table-set! picnic-env sym x)
                                )))
                           
                           (('prim)
                            (let* ((rhs (lookup-def 'rhs alst))
                                   (val (if (and rhs (procedure? initial) )
                                            (extend-procedure initial rhs)
                                            initial)))
                              (hash-table-set! picnic-env sym (PRIM name val))))

                           (('config)   
                            (hash-table-set! picnic-env sym (CONFIG name)))

                           (('const)   
                            (if (not (number? initial))
                                (picnic:error 'env-extend! "constant definitions require numeric value" name initial)
                                (hash-table-set! picnic-env sym (CONST name initial))
                                ))

                           (('asgn)
                            (let* (
                                   (rhs (lookup-def 'rhs alst))
                                   )
                              
                              (if (not (eq? initial 'none))
                                  (picnic:error 'env-extend! 
                                              "state function definitions must have initial value of '(none)"))
                              (if (not rhs) 
                                  (picnic:error 'env-extend! "state function definitions require an equation"))
                              (let ((expr1 (normalize-expr rhs (sprintf "assignment ~A" sym))))
                                (hash-table-set! picnic-env sym (ASGN name 0.0 expr1)))
                              ))

                           (('initial)
                            (let* (
                                   (rhs (lookup-def 'rhs alst))
                                   )
                              
                              (if (not (eq? initial 'none))
                                  (picnic:error 'env-extend! 
                                              "initial state function definitions must have initial value of '(none)"))
                              (if (not rhs) 
                                  (picnic:error 'env-extend! "initial state function definitions require an equation"))
                              (let ((expr1 (normalize-expr rhs (sprintf "initial ~A" sym))))
                                (hash-table-set! picnic-env sym (INITIAL name expr1)))
                              ))

                           (('process)    
                            (let* (
                                   (alst  (filter identity alst))
                                   (gfun  (lookup-def 'gfun alst))
                                   (sfun  (or (lookup-def 'sfun alst) '(uniform)))
                                   (npts  (lookup-def 'npts alst))
                                   (initial (lookup-def 'initial alst))
                                   (local-env (let ((local-env (hash-table-copy picnic-env)))
                                                (hash-table-set! local-env name #t)
                                                local-env))
                                   (symbol-check (make-symbol-check local-env))
                                   (normalize-expr (make-normalize-expr arity-check symbol-check))
                                   )

                              (if (not (and (symbol? gfun)
                                            (procedure? (hash-table-ref local-env gfun))))
                                  (picnic:error 'env-extend! "process definitions require a generating function"))

                              (let ((gfun-proc (hash-table-ref local-env gfun)))
                                (let* ((fd   (procedure-data gfun-proc))
                                       (fms  (lookup-def 'formals fd)))
                                  (if (not (or (= (length fms) 3) (= (length fms) 2)))
                                      (picnic:error 'env-extend! "process generating function must take two or three arguments"))
                                  ))

                              (let ((initial-expr
                                     (and initial
                                          (normalize-expr initial
                                                          (sprintf "initial value for process ~A" sym)))))

                                (hash-table-set! picnic-env sym (PS name gfun sfun initial-expr (or npts 3))))
                              
                              ))

                           (('segmented-process)  
                            (let* (
                                   (alst    (filter identity alst))
                                   (gfun    (lookup-def 'gfun alst))
                                   (sfun    (or (lookup-def 'sfun alst) '(uniform)))
                                   (nsegs   (lookup-def 'nsegs alst))
                                   (nsegpts (lookup-def 'nsegpts alst))
                                   (initial (lookup-def 'initial alst))
                                   (local-env (let ((local-env (hash-table-copy picnic-env)))
                                                (hash-table-set! local-env name #t)
                                                local-env))
                                   (symbol-check (make-symbol-check local-env))
                                   (normalize-expr (make-normalize-expr arity-check symbol-check))
                                   )
                              
                              (if (not (and (symbol? gfun)
                                            (procedure? (hash-table-ref local-env gfun))))
                                  (picnic:error 'env-extend! "segmented process definitions require a generating function"))
                              
                              (let ((gfun-proc (hash-table-ref local-env gfun)))
                                (let* ((fd   (procedure-data gfun-proc))
                                       (fms  (lookup-def 'formals fd)))
                                  (if (not (or (= (length fms) 3) (= (length fms) 2)))
                                      (picnic:error 'env-extend! "segmented process generating function must take two or three arguments"))
                                  ))


                              (if (not (and nsegs nsegpts))
                                  (picnic:error 'env-extend! "segmented process definitions require number of points and number of segments"))
                              
                              (let ((initial-expr
                                     (and initial
                                          (normalize-expr initial
                                                          (sprintf "initial value for process ~A" sym)))))

                                (hash-table-set! picnic-env sym (SEGPS name gfun sfun initial-expr nsegs nsegpts)))
                              
                              ))

                           (('swc-directory)  
                            (let* (
                                   (alst    (filter identity alst))
                                   (path    (lookup-def 'path alst))
                                   (type    (lookup-def 'type alst))
                                   (nsegs   (lookup-def 'nsegs alst))
                                   )
                              (hash-table-set! picnic-env sym (SWC name path type nsegs))
                              ))


                           (('set)  
                            (let* (
                                   (rhs  initial)
                                   (local-env (let ((local-env (hash-table-copy picnic-env)))
                                                (hash-table-set! local-env name #t)
                                                local-env))
                                   (symbol-check (make-symbol-check local-env))
                                   )
                              (hash-table-set! picnic-env sym (SET name rhs))
                              
                              ))


                           (else
                            (begin 
                              (hash-table-set! picnic-env sym `(,type (name ,sym) . ,initial))))

                           ))
                ))
            )


          (define (infer picnic-env ftenv body)
            (let recur ((expr body) (lb (list)))
              (match expr 
                     (('if c t e)
                      (let ((ct (recur c lb))
                            (tt (recur t lb))
                            (et (recur e lb)))
                        (and ct tt et 
                             (begin
                               (if (not (equal? ct 'bool)) 
                                   (picnic:error 'infer "if condition type must be boolean"))
                               (if (equal? tt et) tt
                                   (picnic:error 'infer "type mismatch in if statement: then = " tt
                                               " else = " et))))))
                     (('let bs e)
                      (let* ((rlb (lambda (x) (recur x lb)))
                             (tbs (map rlb (map second bs)))
                             (lb1 (append (zip (map first bs) tbs) lb)))
                        (recur e lb1)))
                     
                     ((s . es)    
                      (let* ((f    (hash-table-ref picnic-env s))
                             (lst  (procedure-data f)))
                        (and lst 
                             (let ((rt   (lookup-def 'rt   lst))
                                   (fms  (lookup-def 'formals lst)))
                               (and rt fms
                                    (begin
                                      (for-each (lambda (x ft)
                                                  (if (and (symbol? x) (not (hash-table-exists? ftenv x)))
                                                      (hash-table-set! ftenv x ft)))
                                                es fms)
                                      (let* ((rlb (lambda (x) (recur x lb)))
                                             (ets (map rlb es)))
                                        (and (every identity ets)
                                             (every (lambda (xt ft) (equal? xt ft)) ets fms)
                                             rt))))))))
                     
                     (id    (cond ((symbol? id)     (or (lookup-def id lb) (hash-table-ref ftenv id)))
                                  ((number? id)     fptype)
                                  ((boolean? id)    'bool)
                                  (else #f))))))
          

          (define (defun! picnic-env)

            (lambda (name formals body)

              (let* ((const-env (make-const-env picnic-env))
                     (local-env (let ((local-env (hash-table-copy picnic-env)))
                                  (for-each (lambda (s) (hash-table-set! local-env s #t))  formals)
                                  local-env))
                     (arity-check (make-arity-check local-env))
                     (symbol-check (make-symbol-check local-env))
                     (normalize-expr (make-normalize-expr arity-check symbol-check))
                     (sym (if (symbol? name) name (string->symbol name))))

                (letrec ((enumconsts
                          (lambda (lb)
                            (lambda (expr ax)
                              (match expr 
                                     (('let bs e)  (let ((ec (enumconsts (append (map first bs) lb))))
                                                     (ec e (fold ec ax (map second bs)))))

                                     (('if . es)   (fold (enumconsts lb) ax es))

                                     ((s . es)     (cond ((and (symbol? s) (not (member s builtin-ops))
                                                               (hash-table-exists? const-env s))
                                                          (let ((v (const-env-entry->value (hash-table-ref const-env s))))
                                                            (cons (cons s v) (fold (enumconsts lb) ax es))))

                                                         ((and (symbol? s) (not (member s builtin-ops)) (not (member s lb)))
                                                          (picnic:error 'defun "quantity " s " not defined"))

                                                         (else (fold (enumconsts lb) ax es))
                                                         ))

                                     (s            (cond 
                                                    ((and (symbol? s) (not (member s lb)) 
                                                          (hash-table-exists? const-env s))
                                                     (let ((v (const-env-entry->value (hash-table-ref const-env s))))
                                                       (cons (cons s v) ax) ))

                                                    ((and (symbol? s) (not (member s lb)))
                                                     (picnic:error 'defun "quantity " s " not defined"))

                                                    (else ax)))

                                     ))
                            ))
                         )


                  (if (hash-table-exists? picnic-env sym)
                      (picnic:error 'defun! "quantity " sym " already defined")
                      (let* (
                             (body    (normalize-expr body (sprintf "function ~A" sym)))
                             (consts  (delete-duplicates ((enumconsts formals) body (list)) 
                                                         (lambda (x y) (equal? (car x) (car y)))))
                             (eval-body (let ((svs (map (lambda (sv)  
                                                          (let ((s (car sv))
                                                                (v (if (procedure? (cdr sv)) 
                                                                       (lookup-def 'eval-body (procedure-data (cdr sv)))
                                                                       (cdr sv))))
                                                            `(,s ,v))) consts)))
                                          (if (null? svs) `(lambda ,formals ,body)
                                              `(let ,svs (lambda ,formals ,body)))))
                             (f      (eval eval-body))
                             )

                        (let* ((ftenv  (make-const-ftenv picnic-env))
                               (rt     (infer picnic-env ftenv body))
                               (ftypes (filter-map (lambda (x) 
                                                     (or (and (hash-table-exists? ftenv x)
                                                              (hash-table-ref ftenv x)) 'double))
                                                   formals))
                               (ef     (extend-procedure f 
                                                         `((name ,sym) (body ,body) (eval-body ,eval-body) 
                                                           (rt ,rt) (formals ,ftypes) (vars ,formals)
                                                           (consts ,(filter (lambda (x) (not (member x builtin-ops))) consts)))))
                               )

                          (hash-table-set! picnic-env sym ef))
                        ))
                  ))
              ))

          (define (symbol-list? lst)
            (and (list? lst) (every symbol? lst)))

          (define (sysname picnic-env)
            (let ((v (hash-table-ref picnic-env (picnic-intern 'name))))
              (and v (cases picnic:quantity v
                            (SYSNAME (name)  name)))
              ))
          

          (define (extended picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (not (picnic:quantity? x)) (not (procedure? x)) 
                                 (match x 
                                        (((? symbol-list?) ('name name) . rest)  `(,sym ,x))
                                        (else #f)))))
                        (hash-table-keys picnic-env)))
          

          (define (extended-with-tag picnic-env tag)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (not (picnic:quantity? x)) (not (procedure? x)) 
                                 (match x 
                                        (((? (lambda (x) (equal? x tag))) ('name name) . rest)  
                                         `(,sym ,x))
                                        (else #f)))))
                        (hash-table-keys picnic-env)))
          

          (define (components picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (COMPONENT (name type lst _)  `(,name ,type ,sym))
                                        (else #f)))))
                        (hash-table-keys picnic-env)))


          (define (component-name picnic-env sym)
            (let ((x (hash-table-ref picnic-env sym)))
              (and (picnic:quantity? x)
                   (cases picnic:quantity x
                          (COMPONENT (name type lst _)  name)
                          (else #f)))))


          (define (component-symbols picnic-env sym)
            (let ((x (hash-table-ref picnic-env sym)))
              (and (picnic:quantity? x)
                   (cases picnic:quantity x
                          (COMPONENT (name type lst _)  lst)
                          (else #f)))))


          (define (component-scope-subst picnic-env sym)
            (let ((x (hash-table-ref picnic-env sym)))
              (and (picnic:quantity? x)
                   (cases picnic:quantity x
                          (COMPONENT (name type lst scope-subst)  scope-subst)
                          (else #f)))))


          (define (component-exports picnic-env sym)
            (let ((all-exports (cases picnic:quantity (hash-table-ref picnic-env (picnic-intern 'exports))
                                      (EXPORTS (lst)  lst))))
              (let ((x  (hash-table-ref picnic-env sym)))
                (and (picnic:quantity? x)
                     (cases picnic:quantity x
                            (COMPONENT (name type lst _)  
                                       (begin
                                         (filter (lambda (x) (member x lst)) all-exports)))
                            (else #f))))))

          (define (component-imports picnic-env sym)
            (let ((all-imports 
                   (filter-map
                    (lambda (sym) 
                      (let ((x (hash-table-ref picnic-env sym)))
                        (and (picnic:quantity? x)
                             (cases picnic:quantity x
                                    (EXTERNAL (local-name name namespace)
                                              (list local-name name namespace))
                                    (else #f)))))
                    (hash-table-keys picnic-env))))
              (let ((x (hash-table-ref picnic-env sym)))
                (and (picnic:quantity? x)
                     (cases picnic:quantity x
                            (COMPONENT (name type lst _)  
                                       (begin
                                         (filter (lambda (x) (member (car x) lst)) all-imports)))
                            (else #f))))))


          (define (component-subcomps picnic-env sym)

            (define (component-type x)
              (cases picnic:quantity x
                     (COMPONENT (name type lst _) type)
                     (else #f)))

            (define (component-name x)
              (cases picnic:quantity x
                     (COMPONENT (name type lst _) name)
                     (else #f)))

            (let ((en (hash-table-ref picnic-env sym)))
              (and (picnic:quantity? en)
                   (cases picnic:quantity en
                          (COMPONENT (name type lst _)  
                                     (filter-map 
                                      (lambda (s) 
                                        (let ((x (hash-table-ref picnic-env s)))
                                          (and (iscomp? x) `(,(component-type x) ,(component-name x) ,s)))) lst))
                          (else #f)))))

          (define (component-extend! picnic-env)
            (lambda (comp-name sym)
              (let ((x (hash-table-ref picnic-env comp-name)))
                (if (picnic:quantity? x)
                    (cases picnic:quantity x
                           (COMPONENT (name type lst scope-subst)  
                                      (let ((en1 (COMPONENT name type (delete-duplicates (append lst (list sym))) scope-subst)))
                                        (hash-table-set! picnic-env comp-name en1)))
                           (else (picnic:error 'component-extend! "invalid component " comp-name)))
                    (picnic:error 'component-extend! "invalid component " comp-name)))))


          (define (component-enumdeps picnic-env sym)

            (let ((x (hash-table-ref picnic-env sym)))
              (and (picnic:quantity? x)
                   (cases picnic:quantity x

                          (COMPONENT 
                           (name type lst scope-subst)  
                           (delete-duplicates
                            (append
                             (fold (lambda (qsym ax)
                                     (let* ((q   (hash-table-ref picnic-env qsym))
                                            (rhs (qrhs q)))
                                       (or (and rhs (append (enumdeps rhs) ax)) ax)))
                                   '()
                                   lst)
                             (fold (lambda (x ax) (append (component-enumdeps picnic-env (third x)) ax))
                                   '()
                                   (component-subcomps picnic-env sym)))))

                          (else #f)))))


          (define (component-env picnic-env sym . syms)
            (fold 
             (lambda (sym env)
               (let ((comp (hash-table-ref picnic-env sym)))
                 (and (picnic:quantity? comp)
                      (cases picnic:quantity comp
                             (COMPONENT 
                              (name type lst scope-subst)  
                              (let* ((depnames (component-enumdeps picnic-env sym))
                                     (subnames (map third (component-subcomps picnic-env sym)))
                                     (cnames   lst))
                                (let* ((syms (delete-duplicates (append depnames subnames cnames)))
                                       (vals (map (lambda (x) (hash-table-ref picnic-env x)) syms)))
                                  (for-each (lambda (s v) (hash-table-set! env s v)) 
                                            syms vals)
                                  env
                                  )))
                             (else env)))))
             (picnic:env-copy base-env)
             (cons sym syms)))


          (define (exports picnic-env)
            (cases picnic:quantity (hash-table-ref picnic-env (picnic-intern 'exports))
                   (EXPORTS (lst)  lst)))


          (define (imports picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (EXTERNAL (local-name name namespace)
                                                  (list local-name name namespace))
                                        (else #f)))))
                        (hash-table-keys picnic-env)))



          (define (configs picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (CONFIG (name)  (list name (lookup-def name local-config) ))
                                        (else #f)))))
                        (hash-table-keys picnic-env)))


          (define (consts picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (CONST (name value)  (list name value) )
                                        (else #f)))))
                        (hash-table-keys picnic-env)))



          (define (states picnic-env)
            (fold (lambda (sym ax) 
                    (let ((x (hash-table-ref picnic-env sym)))
                      (if (picnic:quantity? x)
                          (cases picnic:quantity x
                                 (PS (name gfun sfun initial-expr npts)
                                     (cons name ax))
                                 (SEGPS (name gfun sfun initial-expr nsegs nsegpts)
                                        (cons name ax))
                                 (else ax))
                          ax)))
                  (list) (hash-table-keys picnic-env)))


          (define (processes picnic-env)
            (fold (lambda (sym ax) 
		    (let ((x (hash-table-ref picnic-env sym)))
		      (if (picnic:quantity? x)
                          (cases picnic:quantity x
                                 (PS (name gfun sfun initial npts)
                                     (cons name ax))
                                 (else ax))
                          ax)))
                  (list) (hash-table-keys picnic-env)))

          (define (segmented-processes picnic-env)
            (fold (lambda (sym ax) 
		    (let ((x (hash-table-ref picnic-env sym)))
		      (if (picnic:quantity? x)
                          (cases picnic:quantity x
                                 (SEGPS (name gfun sfun initial-expr nsegs nsegpts)
                                        (cons name ax))
                                 (else ax))
                          ax)))
                  (list) (hash-table-keys picnic-env)))


          (define (initials picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (INITIAL (name rhs) name)
                                        (else #f)))))
                        (hash-table-keys picnic-env)))

          (define (asgns picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (ASGN (name value rhs) name)
                                        (else #f)))))
                        (hash-table-keys picnic-env)))


          (define (defuns picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (procedure? x) (not (member sym builtin-ops)) (list sym x))))
                        (hash-table-keys picnic-env)))

          (define (sets picnic-env)
            (filter-map (lambda (sym) 
                          (let ((x (hash-table-ref picnic-env sym)))
                            (and (picnic:quantity? x)
                                 (cases picnic:quantity x
                                        (SET (name rhs) name)
                                        (else #f)))))
                        (hash-table-keys picnic-env)))


          (define (toplevel picnic-env)
            (cases picnic:quantity (hash-table-ref picnic-env (picnic-intern 'toplevel))
                   (COMPONENT (name type lst _) `(,type ,lst))))

          
          (define (eval-simple-expr env expr)
            (cond ((number? expr) expr)
                  ((symbol? expr) (hash-table-ref env expr))
                  ((pair? expr)   (match expr
                                         (('if cexpr then-expr else-expr)
                                          (let ((cval (eval-simple-expr env cexpr))
                                                (then-val (eval-simple-expr env then-expr))
                                                (else-val (eval-simple-expr env else-expr))
                                                )
                                            (if cval then-val else-val)
                                            ))
                                         (else
                                          (let ((expr1 (map (lambda (x) (eval-simple-expr env x)) expr)))
                                            (apply (car expr1) (cdr expr1))))))
                  ))

          (define (eval-const picnic-env expr qname)
            (let* ((arity-check (make-arity-check picnic-env))
                   (symbol-check (make-symbol-check picnic-env))
                   (normalize-expr (make-normalize-expr arity-check symbol-check)))
              (let ((expr1 (normalize-expr expr (sprintf "constant ~A" qname)))
                    (const-env (make-const-env picnic-env)))
                (condition-case
                 (exact->inexact (eval-simple-expr const-env expr1))
                 [var () expr1])
                )))


          (define (iscomp? x)
            (cond ((picnic:quantity? x)
                   (cases picnic:quantity x
                          (COMPONENT  (name type lst _)  #t)
                          (else #f)))
                  (else #f)))

          (define (isdep? x)
            (cond ((picnic:quantity? x)
                   (cases picnic:quantity x
                          (SET     (name rhs)  #t)
                          (ASGN    (name value rhs)  #t)
                          (INITIAL (name rhs)  #t)
                          (EXTERNAL   (ln name ns) #t)
                          (else #f)))
                  ((and (list? x) (every pair? (cdr x)))  (alist-ref 'dep?  (cdr x)))
                  (else #f)))


          (define (isstate? x)
            (and (picnic:quantity? x)
                 (cases picnic:quantity x
                        (PS        (name gfun sfun initial npts)  #t)
                        (SEGPS     (name gfun sfun initial-expr nsegs nsegpts) #t)
                        (else #f))
                 ))


          (define (qrhs x)
            (and (picnic:quantity? x)
                 (cases picnic:quantity x
                        (SET (name rhs)   (let recur ((rhs rhs))
                                            (match rhs 
                                                   (('section v l) (list v))
                                                   (('union l r) (append (recur l) (recur r)))
                                                   (else rhs))))
                        (PS (name gfun sfun initial npts)   gfun)
                        (SEGPS (name gfun sfun initial-expr nsegs nsegpts) gfun)
                        (ASGN  (name value rhs)  rhs)
                        (INITIAL  (name rhs)  rhs)
                        (else #f))))


          ;; create equation dependency graph
          (define (make-eqng picnic-env)
            (let* ((sysname    (sysname picnic-env))
                   (g          (make-digraph sysname (string-append (symbol->string sysname) 
                                                                    " equation dependency graph")))
                   (add-node!  (g 'add-node!))
                   (add-edge!  (g 'add-edge!))
                   (picnic-list  (filter (lambda (sym) 
                                         (let ((x (hash-table-ref picnic-env sym)))
                                           (or (isstate? x) (isdep? x))))
                                       (hash-table-keys picnic-env)))
                   (picnic-ids      (list-tabulate (length picnic-list) identity))
                   (name->id-map  (zip picnic-list picnic-ids)))

              (let-values (((state-list asgn-list)  
                            (partition (lambda (sym) (isstate? (hash-table-ref picnic-env sym)))
                                       picnic-list)))
                
                ;; insert equations in the dependency graph
                (for-each (lambda (i n) (add-node! i n)) picnic-ids picnic-list)
                ;; create dependency edges in the graph
                (for-each (lambda (e) 
                            (match e ((ni . nj) (begin
                                                  (let ((i (car (alist-ref ni name->id-map)))
                                                        (j (car (alist-ref nj name->id-map))))
                                                    (add-edge! (list i j (format "~A=>~A" ni nj))))))
                                   (else (picnic:error 'make-eqng "invalid edge " e))))
                          (fold (lambda (qsym ax) 
                                  (let* ((q   (hash-table-ref picnic-env qsym))
                                         (rhs (qrhs q)))
                                    (if rhs 
                                        (let* ((deps (filter (if (isstate? q)
                                                                 (lambda (sym) 
                                                                   (if (not (hash-table-exists? picnic-env sym))
                                                                       (picnic:error 'make-eqng "undefined symbol " sym 
                                                                                   " in definition of quantity " qsym))
                                                                   (and (let ((x (hash-table-ref picnic-env sym)))
                                                                          (and (isdep? x) (not (eq? sym qsym))))))
                                                                 (lambda (sym) 
                                                                   (if (not (hash-table-exists? picnic-env sym))
                                                                       (picnic:error 'make-eqng "undefined symbol " sym 
                                                                                   " in definition of quantity " qsym))
                                                                   (and (let ((x (hash-table-ref picnic-env sym)))
                                                                          (isdep? x)))))
                                                             (enumdeps rhs)))

                                               (edges (map (lambda (d) (cons qsym d)) deps)))
                                          (if edges (append edges ax) ax))
                                        ax)))
                                (list) picnic-list))
                (let ((cycles (graph-cycles-fold g (lambda (cycle ax) (cons cycle ax)) (list))))
                  (if (null? cycles) (list state-list asgn-list g)
                      (picnic:error 'make-eqng "equation cycle detected: " (car cycles)))))))


          ;; given a graph, create a partial ordering based on BFS distance from root
          (define (graph->bfs-dist-poset g #!key (root-labels #f))
            (define node-info (g 'node-info))
            (let ((roots (if root-labels
                             (let ((node-map (map reverse ((g 'nodes)))))
                               (filter-map 
                                (lambda (x) (let ((xn (alist-ref x node-map))) (and xn (first xn))))
                                root-labels))
                             ((g 'roots)))))
            (let-values (((dists dmax) (graph-bfs-dist g roots)))
              (let loop ((poset  (make-vector (+ 1 dmax) (list)))
                         (i      (- (s32vector-length dists) 1)))
                (if (>= i 0)
                    (let* ((c     (s32vector-ref dists i))
                           (info  (and (>= c 0) (node-info i))))
                      (if info
                          (vector-set! poset c (cons (cons i info) (vector-ref poset c))))
                      (loop poset (- i 1)))
                    (begin
                      (list->vector (reverse (vector->list poset)))
                      ))
                ))
            ))


          (define (make-eval-poset picnic-env eqposet)
            (vector-map 
             (lambda (i lst) 
               (filter-map (lambda (id+sym)
                             (let* ((sym  (cdr id+sym))
                                    (x    (hash-table-ref picnic-env sym)))
                               (and (picnic:quantity? x)
                                    (cases picnic:quantity x
                                           (PS  (name gfun sfun initial npts)
                                                (list 'ps sym gfun))
                                           (SEGPS  (name gfun sfun initial nsegs nsegpts)
                                                   (list 'segps sym gfun))
                                           (ASGN  (name value rhs)
                                                  (list 'a sym rhs))
                                           (INITIAL  (name rhs)
                                                  (list 'init sym rhs))
                                           (SET  (name rhs)
                                                 (list 'set sym rhs))
                                           (SWC  (name path type nsegs)
                                                 (list 'swc sym path type nsegs))
                                           (else picnic:error 'make-eval-poset
                                                 "invalid quantity in equation poset: " sym)))))
                           lst))
             eqposet))


        (define (eval-set-expr env)  
          (lambda (expr)
            (match expr
                   (('population pop)  (hash-table-ref env pop))
                   (('section pop sec) (let ((pop (hash-table-ref env pop)))
                                         (alist-ref sec pop)))
                   (('union x y)       (lset-union equal? x y))
                   (else #f))))


          (define (eval-expr env)
            (lambda (expr)
              (let ((val (match expr
                                (('if c t f) 
                                 (let ((ee (eval-expr env)))
                                   (condition-case
                                    (if (ee c) (ee t) (ee f))
                                    [var () 
                                         (picnic:error 'eval-expr " exception in " expr ": \n"
                                                     (lambda () (print-error-message var)))])))

                                ((s . es)   
                                 (condition-case 
                                  (let ((op   (hash-table-ref env s))
                                        (args (map (eval-expr env) es)))
                                    (if (extended-procedure? op)
                                        (let* ((fd  (procedure-data op))
                                               (vs  (lookup-def 'formals fd)))
                                          (if (not (= (length vs) (length args)))
                                              (picnic:error 'eval-expr "procedure " s 
                                                          " called with incorrect number of arguments"))))
                                    (apply op args))
                                  [var () 
                                       (picnic:error 'eval-expr " exception in " expr ": \n"
                                                   (lambda () (print-error-message var)))]))
                                
                                (s                  
                                 (cond ((symbol? s) (hash-table-ref env s))
                                       ((or (number? s) (string? s)) s)
                                       (else (picnic:error 'eval-expr "unknown expression " s)))))))
                val)))


          (define (eval-poset picnic-env eqposet)
            (let ((my-env (hash-table-copy picnic-env)))
              (vector-for-each 
               (lambda (i lst) 
                 (for-each 
                  (lambda (id+sym)
                    (let* ((sym  (cdr id+sym))
                           (x    (hash-table-ref my-env sym)))
                      (and (picnic:quantity? x)
                           (cases picnic:quantity x
                                  (SET  (name rhs)
                                         (let ((v ((eval-set-expr my-env) rhs)))
                                           (hash-table-set! my-env sym v)))
                                  (ASGN  (name value rhs)
                                         (let ((v ((eval-expr my-env) rhs)))
                                           (hash-table-set! my-env sym v)))
                                  (INITIAL  (name rhs)
                                         (let ((v ((eval-expr my-env) rhs)))
                                           (hash-table-set! my-env sym v)))
                                  (else picnic:error 'eval-poset
                                        "invalid quantity in equation poset: " sym)))))
                  lst))
               eqposet)
              my-env
              ))


          (define (depgraph picnic-env)
            (match-let (((state-list asgn-list g)  (make-eqng picnic-env))) g))


          (define (depgraph* picnic-env)
            (match-let (((state-list asgn-list g)  (make-eqng picnic-env))) 
                       (list state-list asgn-list g)))


          ;; Dispatcher
          (define (picnic-dispatch selector)
            (case selector
              ((add-external!)     add-external!)
              ((defun!)            defun!)
              ((depgraph)          depgraph)
              ((depgraph*)         depgraph*)
              ((depgraph->bfs-dist-poset)  graph->bfs-dist-poset)
              ((make-eval-poset)   make-eval-poset)
              ((eval-const)        eval-const)
              ((eval-poset)        eval-poset)
              ((env-extend!)       env-extend!)
              ((subst-expr)        (subst-driver (lambda (x) (and (symbol? x) x)) 
                                                 picnic:binding? 
                                                 identity 
                                                 picnic:bind 
                                                 picnic:subst-term))
              ((make-const-env)      make-const-env)
              ((system)              system)
              ((sysname)             sysname)
              ((asgns)               asgns)
              ((initials)            initials)
              ((states)              states)
              ((processes)           processes)
              ((segmented-processes) segmented-processes)
              ((sets)                sets)
              ((defuns)              defuns)
              ((consts)              consts)
              ((configs)             configs)
              ((exports)             exports)
              ((imports)             imports)
              ((toplevel)            toplevel)
              ((components)          components)
              ((component-env)       component-env)
              ((component-name)      component-name)
              ((component-symbols)   component-symbols)
              ((component-exports)   component-exports)
              ((component-imports)   component-imports)
              ((component-subcomps)  component-subcomps)
              ((component-scope-subst)  component-scope-subst)
              ((component-extend!)   component-extend!)
              ((extended)            extended)
              ((extended-with-tag)   extended-with-tag)
              (else
               (picnic:error 'selector "unknown message " selector " sent to an picnic-core object"))))

          picnic-dispatch)


        (define (eval-picnic-system-decls picnic-core name sys declarations #!key 
                                        (parse-expr (lambda (x . rest) x))
                                        (initial-scope #f))

          (define (eval-const x loc) (and x ((picnic-core 'eval-const) sys x loc)))
          (define env-extend!  ((picnic-core 'env-extend!) sys))
          (define (compute-qid id scope scope-subst) (or (and scope scope-subst (picnic-scoped scope id)) id))
          (define (update-subst id qid subst) (if (equal? id qid) subst
                                                  (subst-extend id qid subst) ))
          (define subst-expr  (subst-driver (lambda (x) (and (symbol? x) x))
                                            picnic:binding? 
                                            identity 
                                            picnic:bind 
                                            picnic:subst-term))
          (define (subst-set-expr x subst-env)
            (match x 
                 (('population pop)  `(population ,(subst-expr pop subst-env)))
                 (('section pop sec) `(section ,(subst-expr pop subst-env) ,sec))
                 (('union x y)       `(union ,(subst-set-expr x subst-env)
                                             ,(subst-set-expr y subst-env)))
                 (else #f)))


          (let ((res
                 (let loop ((ds declarations) (qs (list)) (scope initial-scope) (scope-subst '()))

                   (if (null? ds)  
                       (let ((qs (reverse qs)))
                         (if (not scope)
                             (let* ((top-syms   ((picnic-core 'component-symbols ) sys (picnic-intern 'toplevel)))
                                    (top-syms1  (append qs top-syms)))
                               (hash-table-set! sys (picnic-intern 'toplevel) (COMPONENT 'toplevel 'toplevel top-syms1 '()))))
                         (list qs scope-subst))
                       (let ((decl (car ds)))
                         (if (null? decl)
                             (loop (cdr ds) qs scope scope-subst)
                             (match-let 
                              (((qs1 scope-subst1)
                                (match decl

                                       ;; labels
                                       (((or 'label 'LABEL) (and id (? symbol?)) '= (and v (? symbol?)))
                                        (let* ((qid  (compute-qid id scope scope-subst)))
                                          (env-extend! qid '(label) v)
                                          (list (cons qid qs) (update-subst id qid scope-subst))))
                                       
                                       ;; imported quantities
                                       (((or 'input 'INPUT) . lst) 
                                        (cond ((every (lambda (x) (or (symbol? x) (list? x))) lst)
                                               (fold
                                                (lambda (x ax) 
                                                  (match-let (((qs scope-subst) ax))
                                                             (match x
                                                                    ((? symbol?) 
                                                                     (let ((qid (compute-qid x scope scope-subst)))
                                                                       (((picnic-core 'add-external!) sys) x `(input ,x ,qid #f))
                                                                       (list (cons qid qs) (update-subst x qid scope-subst))))
                                                                    ((id1 (or 'as 'AS) x1 . rest) 
                                                                     (let ((qid (compute-qid x1 scope scope-subst)))
                                                                       (((picnic-core 'add-external!) sys) x `(input ,id1 ,qid #f ,@rest))
                                                                       (list (cons qid qs) (update-subst x1 qid scope-subst) )))
                                                                    ((id1 (or 'from 'FROM) n1 . rest) 
                                                                     (let ((qid (compute-qid id1 scope scope-subst)))
                                                                       (((picnic-core 'add-external!) sys) x `(input ,id1 ,qid ,n1 ,@rest))
                                                                       (list (cons qid qs) (update-subst id1 qid scope-subst) )))
                                                                    ((id1 (or 'as 'AS) x1 (or 'from 'FROM) n1 . rest)
                                                                     (let ((qid (compute-qid x1 scope scope-subst)))
                                                                       (((picnic-core 'add-external!) sys) x `(input ,id1 ,qid ,n1 ,@rest))
                                                                       (list (cons qid qs) (update-subst x1 qid scope-subst) )))
                                                                    (((and id1 (? symbol?)) . rest)
                                                                     (let ((qid (compute-qid id1 scope scope-subst)))
                                                                       (((picnic-core 'add-external!) sys) id1 `(input ,id1 ,qid #f ,@rest))
                                                                       (list (cons qid qs) (update-subst id1 qid scope-subst))))
                                                                    )))
                                                (list qs scope-subst) lst))
                                              (else (picnic:error 'eval-picnic-system-decls 
                                                                "import statement must be of the form: "
                                                                "input id1 [as x1] ... "))))
                                       
                                       ;; exported quantities
                                       (((or 'output 'OUTPUT) . (and lst (? (lambda (x) (every symbol? x)))))
                                        (let ((lst1 (map (lambda (x) (compute-qid x scope scope-subst)) lst)))
                                          (for-each (lambda (x) (((picnic-core 'add-external!) sys) x 'output)) lst1)
                                          (list qs scope-subst)))
                                       
                                       ;; constant read from a config file
                                       (((or 'config 'CONFIG) (and id (? symbol?)) . rest)
                                        (let* (
                                               (qid    (compute-qid id scope scope-subst))
                                               (alst   (filter identity rest))
                                               )
                                          (apply env-extend! (list qid '(config) #f))
                                          (list (cons qid qs) (update-subst id qid scope-subst))
                                          ))


                                       ;; constant during point generation
                                       (((or 'const 'CONST) (and id (? symbol?)) '= (and expr (? expr? )) . rest)
                                        (let* ((qid    (compute-qid id scope scope-subst))
                                               (qexpr  (subst-expr (parse-expr expr `(const ,qid)) scope-subst))
                                               (qval   (eval-const qexpr id))
                                               (alst   (filter identity rest))
                                               )
                                          (apply env-extend! (list qid '(const) qval))
                                          (list (cons qid qs) (update-subst id qid scope-subst))
                                          ))

                                       ;; process equation
                                       (((or 'p 'process 'PROCESS) ((and id (? symbol?))) '= . rest)

                                        (let* ((qid     (compute-qid id scope scope-subst))
                                               (scope-subst1 (update-subst id qid scope-subst))
                                               (alst    (filter identity rest))
                                               (gfun    ((lambda (x) (and x (subst-expr (parse-expr x `(process ,id)) scope-subst)))
                                                         (lookup-def 'generator alst)))
                                               (sfun    (lookup-def 'sampler alst))
                                               (initial ((lambda (x) (and x (subst-expr (parse-expr x `(process ,id)) scope-subst)))
                                                         (lookup-def 'initial alst)))
                                               (npts    ((lambda (x) (if x (subst-expr (parse-expr x `(process ,id)) scope-subst) 2))
                                                         (lookup-def 'npts alst)))
                                               )

                                          (apply env-extend!
                                                 (list qid '(process) #f
                                                       (and npts `(npts ,(eval-const npts (sprintf "~A.npts" id)) ))
                                                       (and gfun `(gfun ,gfun))
                                                       (or (and sfun `(sfun ,sfun)) `(sfun (uniform)))
                                                       (and initial `(initial ,initial))
                                                       ))
                                          (list (cons qid qs) scope-subst1)))
                                       
                                       ;; segmented process equation
                                       (((or 'segp 'segmented-process 'SEGMENTED-PROCESS) 
                                         ((and id (? symbol?))) '= . rest)

                                        (let* ((qid     (compute-qid id scope scope-subst))
                                               (scope-subst1 (update-subst id qid scope-subst))
                                               (alst    (filter identity rest))
                                               (gfun    ((lambda (x) (and x (subst-expr (parse-expr x `(segprocess ,id)) scope-subst)))
                                                          (lookup-def 'generator alst)))
                                               (sfun    (lookup-def 'sampler alst))
                                               (initial ((lambda (x) (and x (subst-expr (parse-expr x `(segprocess ,id)) scope-subst)))
                                                          (lookup-def 'initial alst)))
                                               (nsegs    ((lambda (x) (and x (subst-expr (parse-expr x `(segprocess ,id)) scope-subst)))
                                                          (lookup-def 'nsegs alst)))
                                               (nsegpts ((lambda (x) (and x (subst-expr (parse-expr x `(segprocess ,id)) scope-subst)))
                                                         (lookup-def 'nsegpts alst)))
                                               )

                                          (apply env-extend!
                                                 (list qid '(segmented-process) #f
                                                       (and nsegs `(nsegs ,(eval-const nsegs (sprintf "~A.nsegs" id)) ))
                                                       (and nsegpts `(nsegpts ,(eval-const nsegpts (sprintf "~A.nsegpts" id)) ))
                                                       (and gfun `(gfun ,gfun))
                                                       (or (and sfun `(sfun ,sfun)) `(sfun (uniform)))
                                                       (and initial `(initial ,initial))
                                                       ))
                                          (list (cons qid qs) scope-subst1)))


                                       ;; directory of SWC files
                                       (((or 'swcdir 'swc-directory 'SWC-DIRECTORY) 
                                         ((and id (? symbol?))) '= . rest)

                                        (let* (
                                               (qid     (compute-qid id scope scope-subst))
                                               (scope-subst1 (update-subst id qid scope-subst))
                                               (alst    (filter identity rest))
                                               (type    (lookup-def 'type alst))
                                               (nsegs   ((lambda (x) (and x (subst-expr (parse-expr x `(swcdir ,id)) scope-subst)))
                                                         (lookup-def 'nsegs alst)))
                                               (path    (lookup-def 'path alst))
                                               )

                                          (apply env-extend!
                                                 (list qid '(swc-directory) #f
                                                       (and nsegs `(nsegs ,(eval-const nsegs (sprintf "~A.nsegs" id)) ))
                                                       (and type `(type ,type))
                                                       (and path `(path ,path))
                                                       ))

                                          (list (cons qid qs) scope-subst1)))


                                       ;; population set
                                       (((or 'set 'SET) (and id (? symbol?)) '= (and rhs (? setexpr?)))

                                        (d "set: id = ~A~%" id)

                                        (let* ((loc    `(set ,id)))

                                          (let* ((qid (compute-qid id scope scope-subst))
                                                 (qexpr (subst-set-expr rhs scope-subst)))

                                            (d "subst-set-expr: id = ~A rhs = ~A qexpr = ~A scope-subst = ~A~%" 
                                               id rhs qexpr scope-subst)

                                            (apply env-extend! (cons* qid '(set) qexpr '()))
                                            (list (cons qid qs) (update-subst id qid scope-subst)))
                                          ))
                                
                                       
                                       ;; algebraic assignment
                                       (((and id (? symbol?)) '= (and expr (? expr?) ) . rest)
                                        (let* ((qid    (compute-qid id scope scope-subst))
                                               (qexpr  (subst-expr (parse-expr expr `(asgn ,id)) scope-subst))
                                               (alst   (filter identity rest))
                                               )
                                          (apply env-extend! (list qid '(asgn) 'none `(rhs ,qexpr)))
                                          (list (cons qid qs) (update-subst id qid scope-subst))))
                                       
                                       ;; single-state algebraic assignment
                                       (('initial (and id (? symbol?)) '= (and expr (? expr?) ) . rest)
                                        (let* ((qid    (compute-qid id scope scope-subst))
                                               (qexpr  (subst-expr (parse-expr expr `(initial ,id)) scope-subst))
                                               (alst   (filter identity rest))
                                               )
                                          (apply env-extend! (list qid '(initial) 'none `(rhs ,qexpr)))
                                          (list (cons qid qs) (update-subst id qid scope-subst))))
                                       
                                       ;; user-defined function 
                                       (((or 'fun 'FUN 'rel 'REL 'defun 'DEFUN) (and id (? symbol?)) 
                                         (and idlist (? (lambda (x) (every symbol? x)))) 
                                         (and expr (? expr?)))

                                        (let* ((qid          (compute-qid id scope scope-subst))
                                               (scope-subst1 (fold (lambda (x ax) (subst-remove x ax))
                                                                   scope-subst
                                                                   idlist))
                                               (qexpr         (subst-expr (parse-expr expr `(defun ,qid)) 
                                                                          scope-subst1))
                                               )
                                          (((picnic-core 'defun!) sys) qid idlist qexpr)
                                          (list (cons qid qs) (update-subst id qid scope-subst))))
                                       
                                       ;; compiled primitives
                                       (((or 'prim 'PRIM) id value) 
                                        (cond ((symbol? id)  (env-extend! id '(prim) value))
                                              (else (picnic:error 'eval-picnic-system-decls 
                                                                "prim declarations must be of the form: "
                                                                "prim id value"))))

                                       (((or 'sysname 'SYSNAME) name)  
                                        (if (symbol? name)
                                            (hash-table-set! sys (picnic-intern 'name) (SYSNAME name))
                                            (picnic:error 'eval-picnic-system-decls
                                                        "system name must be a symbol")))
                                       
                                       (((or 'component 'COMPONENT)
                                         ((or 'type 'TYPE) typ) 
                                         ((or 'name 'NAME) name) . lst)

                                        (let ((name1 (let ((x (and (hash-table-exists? 
                                                                    sys (or (lookup-def name scope-subst) name))
                                                                   (hash-table-ref 
                                                                    sys (or (lookup-def name scope-subst) name)))))
                                                       (or (and x (picnic:quantity? x)
                                                                (cases picnic:quantity x
                                                                       (LABEL (v)  v)
                                                                       (else name)))
                                                           name))))

                                          (let* ((sym   (fresh "comp"))
                                                 (scope (if scope (cons sym scope) (list sym))))
                                            (match-let (((cqs scope-subst1)   (loop lst (list) scope scope-subst)))
                                                       (let ((comp  (COMPONENT name1 typ cqs scope-subst1)))
                                                         (hash-table-set! sys sym comp)
                                                         (list (cons sym qs) scope-subst1))))))

                                       (((or 'component 'COMPONENT) ((or 'type 'TYPE) typ)  . lst)  
                                        (let* ((sym   (fresh "comp"))
                                               (scope (if scope (cons sym scope) (list sym))))

                                          (match-let (((cqs scope-subst1)   (loop lst (list) scope scope-subst)))
                                                     (let ((comp  (COMPONENT sym typ cqs scope-subst1)))
                                                       (hash-table-set! sys sym comp)
                                                       (list (cons sym qs) scope-subst1)))))

                                       (((or 'component 'COMPONENT)  ((or 'name 'NAME) name) '= 
                                         (and functor-name (? symbol?)) 
                                         (and args (? list?)))

                                        (if (and scope scope-subst) 
                                            (picnic:error 'eval-picnic-system-decls
                                                        "functor instantiation is not permitted in nested scope"))

                                        (match-let
                                         (((functor-args functor-type functor-lst)
                                           (let ((x (hash-table-ref sys functor-name)))
                                             (or (and (picnic:quantity? x)
                                                      (cases picnic:quantity x
                                                             (FUNCTOR (sym args typ lst)  (list args typ lst))
                                                             (else #f)))
                                                 (picnic:error 'eval-picnic-system-decls! functor-name 
                                                             " is not a functor" )))))

                                         (if (not (<= (length functor-args)  (length args)))
                                             (let ((n (length args)))
                                               (picnic:error 'eval-picnic-system-decls! "functor " functor-name 
                                                           " requires at least " (length functor-args) " arguments; "
                                                           args  " (total " n ") "
                                                           (if (= n 1) "was" "were") " given" )))


                                         (match-let
                                          (((cqs1 scope-subst1)   (loop args (list) name scope-subst)))
                                          (let ((cqs1-names (sort (map ->string cqs1) string< ))
                                                (args-names (let ((qs (map (lambda (x) 
                                                                             (->string (compute-qid x name scope-subst1)) )
                                                                           functor-args)))
                                                              (sort qs string<))))

                                            (if (not (every (lambda (x) (member x cqs1-names string=)) args-names))
                                                (picnic:error 'eval-picnic-system-decls! "functor " functor-name 
                                                            " instantiation did not include required arguments " 
                                                            (filter (lambda (x) (not (member x cqs1-names string=))) args-names)))
                                            
                                            (match-let
                                             (((cqs2 scope-subst2)   (loop functor-lst (list) name scope-subst1)))
                                             (let* ((sym    (fresh "comp"))
                                                    (comp   (COMPONENT name functor-type (append cqs1 cqs2) scope-subst2)))
                                               (hash-table-set! sys sym comp)
                                               
                                               (list (cons sym qs) scope-subst)))))))
                                       
                                       ((or 
                                         ((or 'functor 'FUNCTOR) ((or 'name 'NAME) name) ((or 'type 'TYPE) typ)
                                          (and args (? list?))  '= . lst)
                                         ((or 'functor 'FUNCTOR) ((or 'type 'TYPE) typ) ((or 'name 'NAME) name)
                                          (and args (? list?))  '= . lst))

                                        (if (and scope scope-subst) 
                                            (picnic:error 'eval-picnic-system-decls
                                                        "functor declaration is not permitted in nested scope"))
                                        (let* ((sym      (string->symbol (->string name)))
                                               (functor  (FUNCTOR sym args typ lst)))
                                          (if (hash-table-exists? sys sym)
                                              (picnic:error 'eval-picnic-system-decls! "functor " sym " already defined"))
                                          (hash-table-set! sys sym functor)
                                          (list (cons sym qs) scope-subst)))
                                       
                                       (((or 'const 'CONST) . _)
                                        (picnic:error 'eval-picnic-system-decls "declaration: " decl
                                                    "constant declarations must be of the form: "
                                                    "const id = expr"))
                                       
                                       ((id '= . _) 
                                        (picnic:error 'eval-picnic-system-decls 
                                                    "declaration " decl
                                                    "algebraic equations must be of the form: "
                                                    "id = expr")) 
                                       
                                       (((or 'reaction 'REACTION) . _)
                                        (picnic:error 'eval-picnic-system-decls 
                                                    "declaration " decl 
                                                    "reaction declarations must be of the form: "
                                                    "reaction (id ...)"))
                                       
                                       (((or 'fun 'FUN 'rel 'REL 'defun 'DEFUN) . _) 
                                        (picnic:error 'eval-picnic-system-decls "function declarations must be of the form: "
                                                    "fun id (arg1 arg2 ...) expr"))
                                       
                                       (((or 'prim 'PRIM) . _) 
                                        (picnic:error 'eval-picnic-system-decls "prim declarations must be of the form: "
                                                    "prim id value"))
                                       
                                       (((or 'component 'COMPONENT) . _)  
                                        (picnic:error 'eval-picnic-system-decls "invalid component: " decl))
                                       
                                       (((or 'sysname 'SYSNAME) . _)  
                                        (picnic:error 'eval-picnic-system-decls "system name must be of the form (sysname name)"))
                                       
                                       ;; anything that doesn't match is possibly
                                       ;; declarations recognized by the picnic extension
                                       ;; modules
                                       (((and tag (? symbol?))  . lst)
                                        (match-let (((typ name alst)  
                                                     (let loop ((lst lst) (ax (list tag)))
                                                       (if (null? lst)
                                                           (list (list (car (reverse ax))) #f (cdr (reverse ax)))
                                                           (match lst
                                                                  (((? symbol?) . rest) 
                                                                   (loop (cdr lst) (cons (car lst) ax) ))
                                                                  (((x . rest)) 
                                                                   (if (and (symbol? x) (every list? rest))
                                                                       (list (reverse ax) x rest)
                                                                       (list (reverse ax) #f lst)))
                                                                  (else  (list (reverse ax) #f lst)))))))
                                                   
                                                   (let* ((name (or name (fresh tag)))
                                                          (qid  name))
                                                     (env-extend! qid  typ (if scope (append alst `((scope ,scope))) alst))
                                                     (list (cons qid qs) (update-subst name qid scope-subst)))))

                                       (else
                                        (picnic:error 'eval-picnic-system-decls 
                                                    "declaration " decl ": "
                                                    "extended declarations must be of the form: "
                                                    "declaration (name (properties ...)"
                                                    ))
                                       )))
                              (loop (cdr ds) qs1 scope scope-subst1))
                             ))
                       ))
                 ))
            res
            ))
)

        

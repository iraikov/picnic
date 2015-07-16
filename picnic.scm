;;
;; Neural Parametric Curve Connectivity Language
;;
;; Copyright 2012-2015 Ivan Raikov.
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
;;


(import scheme chicken)

(require-extension srfi-1 setup-api picnic-core)
(require-library iexpr ersatz-lib picnic-utils)
(require-extension datatype matchable lalr-driver getopt-long)
(import (prefix iexpr iexpr: )
	(prefix ersatz-lib ersatz: )
        (only picnic-utils load-config-file make-output-fname)
        (only setup-api compile)
	)

(define rest cdr)

(define-datatype picnic:model picnic:model?
  (ModelSource (source-path string?) (in-format symbol?) (name symbol?) 
	       (decls list?) 
	       (user-templates user-template-list?)
	       (iexpr boolean?) (parse-expr procedure?))
  (SingleModel (source-path string?) (in-format symbol?) (name symbol?) 
	       (sys hash-table?) (decls list?) (user-templates user-template-list?)
	       (iexpr boolean?) (parse-expr procedure?))
  )


(define-record-type section-descriptor 
  (make-section-descriptor label start-index processes perturbations)
  section-descriptor? 
  (label section-descriptor-label)
  (start-index section-descriptor-start-index)
  (processes section-descriptor-processes)
  (perturbations section-descriptor-perturbations)
  )


(define-record-type projection-descriptor 
  (make-projection-descriptor label poset imports)
  projection-descriptor? 
  (label projection-descriptor-label)
  (poset projection-descriptor-poset)
  (imports projection-descriptor-imports)
  )



 
(define (d fstr . args)
  (let ([port (current-error-port)])
    (if (positive? (picnic-verbose)) 
        (begin (apply fprintf port fstr args)
               (flush-output port) ) )))


(define (user-template-list? ts)
  (every (lambda (x) (and (string? (car x))
                          (every string? (cadr x))
                          (every ersatz:tstmt? (caddr x)))) ts))


(define (lookup-def k lst . rest)
  (let-optionals rest ((default #f))
      (let ((kv (assoc k lst)))
	(if (not kv) default
	    (match kv ((k v) v) (else (cdr kv)))))))


(define ($ x)  (and x (string->symbol (->string x))))


;;; Procedures for string concatenation and pretty-printing

(define (s+ . lst)    (string-concatenate (map ->string lst)))
(define (sw+ lst)     (string-intersperse (filter-map (lambda (x) (and x (->string x))) lst) " "))
(define (s\ p . lst)  (string-intersperse (map ->string lst) p))
(define (slp p lst)   (string-intersperse (map ->string lst) p))
(define nl "\n")


(define (warn port message . specialising-msgs)
  (print-error-message message (current-output-port) "Warning")
  (print (string-concatenate (map ->string specialising-msgs))))

;;; Error procedure for the XML parser

(define (parser-error port message . specialising-msgs)
  (error (string-append message (string-concatenate (map ->string specialising-msgs)))))

(define ssax:warn warn)

(define (defopt x)
  (lookup-def x opt-defaults))

(define opt-grammar
  `(
    (input-format
     "specify input format (picnic, s-exp)"
     (single-char #\i)
     (value (required FORMAT)
	    (transformer ,string->symbol)))

    (compile "compile generated model code" 
             (single-char #\c))

    (config-file "use the given hoc configuration file to obtain parameter values"
                 (value (required FILENAME)))

    (template
     "instantiate the given template from the model file by setting the given variables to the respective values"
     (value (required "NAME[:VAR=VAL...]"))
     (multiple #t)
     )

    (template-prefix 
     "output instantiated templates to <PREFIX><template_name> (default is <model-name>_<template_name>)"
     (value (required PREFIX) ))

    (debug "print additional debugging information" 
           (single-char #\v))

    (version "print the current version and exit")

    (help         (single-char #\h))


    ))


;; Use args:usage to generate a formatted list of options (from OPTS),
;; suitable for embedding into help text.
(define (picnic:usage)
  (print "Usage: " (car (argv)) "  <list of files to be processed> [options...] ")
  (newline)
  (print "The following options are recognized: ")
  (newline)
  (print (parameterize ((indent 5) (width 30)) (usage opt-grammar)))
  (exit 1))


;; Process arguments and collate options and arguments into OPTIONS
;; alist, and operands (filenames) into OPERANDS.  You can handle
;; options as they are processed, or afterwards.

(define opts    (getopt-long (command-line-arguments) opt-grammar))
(define opt     (make-option-dispatch opts opt-grammar))


(define picnic-config (make-parameter '()))
(if (opt 'config-file)
    (picnic-config (load-config-file (opt 'config-file))))


(define (picnic-constructor name config declarations parse-expr)
  (let* ((picnic   (make-picnic-core `(config . ,config)))
	 (sys      ((picnic 'system) name))
	 (qs       (eval-picnic-system-decls picnic name sys declarations parse-expr: parse-expr)))
    (list sys picnic qs)))


(define (sexp->model-decls doc)
  (match doc
	 ((or ('picnic-model model-name model-decls)
	      ('picnic-model (model-name . model-decls)))
	  (list model-name model-decls))
	 ((or ('picnic-model model-name model-decls user-templates)
	      ('picnic-model (model-name . model-decls) user-templates))
	  (list model-name model-decls 
		(map (lambda (x) (list (->string (car x)) 
				       (map ->string (cadr x))
				       (ersatz:statements-from-string
					(ersatz:template-std-env) 
					(caddr x))))
			     user-templates)))
	 (else (error 'sexp->model "unknown model format"))
	 ))


(define (sexp-model-decls->model options model-name model-decls parse-expr)
  (let* ((model+picnic  (picnic-constructor model-name (picnic-config) model-decls parse-expr))
	 (model (first model+picnic))
	 (picnic  (second model+picnic)))
      (if (assoc 'depgraph options) (print "dependency graph: " ((picnic 'depgraph*) model)))
      (if (assoc 'exports options)  (print "exports: " ((picnic 'exports) model)))	
      (if (assoc 'imports options)  (print "imports: " ((picnic 'imports) model)))
      (if (assoc 'components options)
	  (for-each (lambda (x) 
		      (print "component " x ": " ((picnic 'component-exports) model (second x)))
		      (print "component " x " subcomponents: " ((picnic 'component-subcomps) model (second x))))
		    ((picnic 'components) model)))
      model))
	 


(include "expr-parser.scm")


(define (instantiate-template user-templates template-name template-vars)
  (let ((tmpl (assoc (->string template-name) user-templates string=?)))
    (if (not tmpl)
	(error 'picnic "template not found" template-name))
    (let ((ctx (ersatz:init-context models: template-vars )))
      (display
       (ersatz:eval-statements (caddr tmpl)
			       env: (ersatz:template-std-env)
			       models: template-vars ctx: ctx))
      )))


(define (process-template model-name template-name template-args template-out user-templates source-path)

  (let (
	(template-vars (cons (cons 'model_name
				   (ersatz:Tstr (->string model-name)) )
			     (map (lambda (x) 
				    (let ((kv (string-split x "=")))
				      (cons ($ (car kv))
					    (ersatz:Tstr (cadr kv)))))
				  template-args)))
	)

    (let* ((dirname (pathname-directory source-path))
	   (output-name (if (string-prefix? "." template-out)
			    (make-pathname dirname (s+ model-name template-out)) 
			    (make-pathname dirname (s+ model-name "_" template-out)) )))
      (with-output-to-file output-name
	(lambda () (instantiate-template user-templates template-name template-vars))
	))
    ))




(define (model-source->model source-path in-format model-name model-decls user-templates iexpr parse-expr)

  (case in-format
    
    ((sexp picnic)
     (SingleModel source-path in-format model-name
                  (sexp-model-decls->model 
                   `() model-name model-decls parse-expr)
                  model-decls user-templates iexpr parse-expr))
    
    (else (error 'picnic "invalid input format"))
    ))
        
  
(define (qrhs x)
  (and (picnic:quantity? x)
       (cases picnic:quantity x
              (SET  (name rhs)  `(SetExpr ,rhs))
              (ASGN  (name value rhs)  rhs)
              (INITIAL (name rhs)  rhs)
              (else #f))))

(define (qinit x)
  (and (picnic:quantity? x)
       (cases picnic:quantity x
              (PS (name gfun sfun init npts)   init)
              (SEGPS (name gfun sfun init nsegs nsegpts)   init)
              (else #f))))

(define (gfun x)
  (and (picnic:quantity? x)
       (cases picnic:quantity x
              (PS (name gfun sfun init npts)   gfun)
              (SEGPS (name gfun sfun init nsegs nsegpts)   gfun)
              (else #f))))

(define (process-model opt source-path in-format prefix sys model-decls iexpr? parse-expr)

  (define (cid x)  (second x))
  (define (cn x)   (first x))
		
  (match-let ((($ picnic:quantity 'DISPATCH dis) 
	       (hash-table-ref sys (picnic-intern 'dispatch))))
				    
     (let* (
	    (sysname     ((lambda (x) (or (and prefix ($ (s+ prefix "_" x))) x)) ((dis 'sysname) sys)))
	    (dirname     (pathname-directory source-path))
            (scm-fname   (make-output-fname dirname sysname  ".scm"))

            (eval-const  (let ((eval-const (dis 'eval-const)))
                           (lambda (x q) (eval-const sys x q))))
            (consts      ((dis 'consts)  sys))
            (defuns      ((dis 'defuns)  sys))
            (asgns       ((dis 'asgns)   sys))
            (initials    ((dis 'initials)   sys))
            (sets        ((dis 'sets)   sys))
            (configs     ((dis 'configs)  sys))
            (imports     ((dis 'imports)  sys))
            (exports     ((dis 'exports)  sys))
            (components  ((dis 'components) sys))
            (subcomps    (dis 'component-subcomps))

            (component-exports (dis 'component-exports))
            (component-imports (dis 'component-imports))

            (g ((dis 'depgraph) sys))
            

            (cell-forests
             (filter-map (match-lambda 
                          ((name 'cell-forest id) (list name id 'global))
                          ((name 'local-cell-forest id) (list name id 'local))
                          (else #f)) 
                         components))

            (cell-section-comps
             (map (lambda (forest)
                    (let ((subcomponents (subcomps sys (cid forest))))
                      (cons forest
                            (filter-map 
                             (match-lambda 
                              (('section name id) (list name id))
                              (else #f))
                             subcomponents))))
                  cell-forests))

            (cell-swc-section-comps
             (map (lambda (forest)
                    (let ((subcomponents (subcomps sys (cid forest))))
                      (cons forest
                            (filter-map 
                             (match-lambda 
                              (('swc-section name id) (list name id))
                              (else #f))
                             subcomponents))))
                  cell-forests))

            (cell-layout-comps
             (map (lambda (forest)
                    (let ((subcomponents (subcomps sys (cid forest))))
                      (cons forest
                            (filter-map 
                             (match-lambda 
                              (('layout name id) (list name id))
                              (else #f))
                             subcomponents))))
                  cell-forests))

            (forest-pointset-comps
             (map (lambda (forest)
                    (let ((subcomponents (subcomps sys (cid forest))))
                      (cons forest
                            (filter-map 
                             (match-lambda 
                              (('pointset name id) (list name id))
                              (else #f))
                             subcomponents))))
                  cell-forests))

            (projection-comps
             (filter-map (match-lambda 
                          ((name 'projection id) (list name id))
                          (else #f))
                         components))

            (cell-layouts 
             (map (lambda (forest+layouts)
                    (let ((forest  (first forest+layouts))
                          (layouts (cdr forest+layouts)))
                      (cons forest
                            (map (lambda (layout)
                                   (let ((exports (component-exports sys (cid layout))))
                                     (let* (
                                            (pointset-name (first exports))
                                            (poset ((dis 'depgraph->bfs-dist-poset) g 
                                                    root-labels: (list pointset-name)))
                                            )
                                       (d "poset = ~A~%" poset)
                                       (d "pointset in ~A = ~A~%" layout pointset-name)
                                       (vector->list poset)
                                       ))
                                   ) layouts))
                      ))
                    cell-layout-comps))

            (forest-pointsets 
             (filter-map
              (lambda (forest+pointsets)
                (let ((forest    (first forest+pointsets))
                      (pointsets (cdr forest+pointsets)))
                  (if (null? pointsets) #f
                      (cons forest
                            (map (lambda (pointset)
                                   (let ((exports (component-exports sys (cid pointset))))
                                     (let* (
                                            (pointset-name (first exports))
                                            (poset ((dis 'depgraph->bfs-dist-poset) g 
                                                    root-labels: (list pointset-name)))
                                            )
                                       (d "poset = ~A~%" poset)
                                       (d "pointset in ~A = ~A~%" forest pointset-name)
                                       (list (cn pointset) (vector->list poset))
                                       ))
                                   ) pointsets)))
                  ))
              forest-pointset-comps))


            (cell-sections 
             (map
              (lambda (sections)
                (let ((forest (first sections)))
                  (cons forest
                        (reverse
                         (second
                          (fold
                           (match-lambda* ((section (start-index lst))
                             (let* (
                                   (label    (cn section))
                                   (exports  (component-exports sys (cid section)))
                                   (imports  (component-imports sys (cid section)))
                                   (perturbs (filter-map (lambda (x) 
                                                           (let ((comp (and (eq? (car x) 'perturbation) (second x))))
                                                             (component-exports sys comp)
                                                             ))
                                                         (subcomps sys (cid section))))
                                   (processes (map (lambda (prs)
                                                     (let* ((process-name (first prs))
                                                            (n (second prs))
                                                            (n-value ((dis 'eval-const) sys n process-name))
                                                            (generator (gfun (hash-table-ref sys process-name)))
                                                            (init (qinit (hash-table-ref sys process-name)))
                                                            )
                                                       (d "process in ~A = ~A~%" section process-name)
                                                       (d "process generator function = ~A~%" generator)
                                                       (list process-name n n-value)))
                                                   (let recur ((prs '()) (exports exports))
                                                     (if (null? exports) 
                                                         (reverse prs)
                                                         (recur (cons (take exports 2) prs) 
                                                                (drop exports 2))))
                                                   ))
                                   )
                               (d "label of ~A = ~A~%" (cid section) label)
                               (d "exports in ~A = ~A~%" section exports)
                               (d "imports in ~A = ~A~%" section imports)
                               (d "processes in ~A = ~A~%" section processes)
                               (d "perturbations in ~A = ~A~%" section perturbs)
                               (list 
                                (fold (lambda (x ax) (+ (third x) ax)) start-index processes)
                                (cons (cons label (make-section-descriptor label start-index processes perturbs)) lst))
                               )))
                           (list 0 '())
                           (rest sections)))
                         ))
                  ))
              cell-section-comps))

            (cell-swc-sections 
              (map
               (lambda (sections)
                 (let ((forest (first sections)))
                   (cons forest
                         (reverse
                          (second
                           (fold
                            (match-lambda* ((section (start-index lst))
                             (let* (
                                    (label    (cn section))
                                    (exports  (component-exports sys (cid section)))
                                    (imports  (component-imports sys (cid section)))
                                    (swcs     (let recur ((swcs '()) (exports exports))
                                                (if (null? exports) 
                                                    (reverse swcs)
                                                    (recur (cons (car exports) swcs) 
                                                           (cdr exports))))
                                              )
                                   )
                               (d "label of ~A = ~A~%" (cid section) label)
                               (d "exports in ~A = ~A~%" section exports)
                               (d "imports in ~A = ~A~%" section imports)
                               (d "swcs in ~A = ~A~%" section swcs)
                               (list 
                                (fold (lambda (x ax) (+ 1 ax)) start-index swcs)
                                (cons (cons label (make-section-descriptor label start-index swcs '())) lst))
                               )))
                            (list 0 '())
                            (rest sections)))
                          ))
                   ))
               cell-swc-section-comps)
              )

            ;; TODO: check that source/target populations are either:
            ;; local/global
            ;; global/global
            (projections 
             (fold-right
              (lambda (projection-comp ax)
                (d "projection-comp = ~A~%" projection-comp)
                (let ((exports (component-exports sys (cid projection-comp)))
                      (imports (component-imports sys (cid projection-comp))))
                  (d "projection exports = ~A~%" exports)
                  (d "projection imports = ~A~%" imports)
                  (append 
                   (map 
                    (lambda (name)
                      (let* (
                             (label (string->symbol (last (string-split (->string name) "."))))
                             (poset ((dis 'depgraph->bfs-dist-poset) g 
                                     root-labels: (list name)))
                             (poset (vector->list poset))
                             )
                        (d "projection poset = ~A~%" poset)
                        (make-projection-descriptor label poset imports)))
                    exports) ax)
                  ))
              '()
              projection-comps))

            )

       (with-output-to-file scm-fname 
         (lambda () 
           (begin
             (for-each (lambda (b) (printf "~A~%" b)) prelude/scheme)

             (for-each pp (map (lambda (x) `(define . ,x)) consts))
             (for-each pp (map (lambda (x) `(define . ,x)) configs))
             
             (for-each pp (filter-map (lambda (x) (defun-codegen/scheme x)) defuns))
             
             
             (d "cell sections = ~A~%" cell-sections)
       
             (for-each 
              (match-lambda
               ((forest layout . rest)
                (let ((sections (map cdr (alist-ref forest cell-sections)))
                      (swc-sections (map cdr (alist-ref forest cell-swc-sections))))
                  (pp (forest-codegen/scheme sys forest layout sections swc-sections))
                  )))
              cell-layouts)
             
             (for-each 
              (match-lambda
               ((forest . pointsets)
                (for-each pp (forest-pointset-codegen/scheme sys forest pointsets))))
              forest-pointsets)
             
             (d "projections = ~A~%" projections)
             
             (for-each 
              (lambda (projection)
                (pp (projection-codegen/scheme sys cell-forests cell-sections projection)))
              projections)
             
             (for-each pp `((MPI:finalize)))
             
             ))
         )
       
       (if (opt 'compile)
           (compile -O3 ,scm-fname))
       )
     ))


(define prelude/scheme
  `(#<<EOF
(use srfi-1 mathh matchable kd-tree mpi getopt-long picnic-utils)
(include "mathh-constants")

(define (choose lst n) (list-ref lst (random n)))

(define picnic-write-pointsets (make-parameter #f))
(define picnic-write-layouts (make-parameter #f))
(define picnic-write-sections (make-parameter #f))
(define local-config (make-parameter '()))


(MPI:init)

(define opt-grammar
  `(

    (write-pointsets "write generated or loaded pointsets to files"
                     (single-char #\p))
    
    (write-layouts "write layouts to files"
                   (single-char #\l))
    
    (write-sections "write generated sections to files"
                    (single-char #\s))

    (random-seeds "Use the given seeds for random number generation"
                  (value (required SEED-LIST)
                         (transformer ,(lambda (x) (map string->number
                                                        (string-split x ","))))))
    
    (verbose "print additional debugging information" 
             (single-char #\v))
    
    (help         (single-char #\h))
    ))

;; Process arguments and collate options and arguments into OPTIONS
;; alist, and operands (filenames) into OPERANDS.  You can handle
;; options as they are processed, or afterwards.

(define opts    (getopt-long (command-line-arguments) opt-grammar))
(define opt     (make-option-dispatch opts opt-grammar))

;; Use usage to generate a formatted list of options (from OPTS),
;; suitable for embedding into help text.
(define (my-usage)
  (print "Usage: " (car (argv)) " [options...] ")
  (newline)
  (print "The following options are recognized: ")
  (newline)
  (print (parameterize ((indent 5)) (usage opt-grammar)))
  (exit 1))

(if (opt 'help)
    (my-usage))

(if (opt 'verbose)
    (picnic-verbose 1))

(if (opt 'write-pointsets)
    (picnic-write-pointsets #t))

(if (opt 'write-layouts)
    (picnic-write-layouts #t))

(if (opt 'write-sections)
    (picnic-write-sections #t))

(if (picnic-verbose)
    (pp (local-config) (current-error-port)))

(define my-comm (MPI:get-comm-world))
(define myrank  (MPI:comm-rank my-comm))
(define mysize  (MPI:comm-size my-comm))

(define-syntax
  SetExpr
  (syntax-rules
      (population section union)
    ((SetExpr (population p))
     (lambda (repr) 
       (case repr 
             ((list) (map (lambda (cell)
                            (list (cell-index cell)
                                  (cell-origin cell)))
                          p))
             ((tree) (let ((pts (map (lambda (cell)
                                       (list (cell-index cell)
                                             (cell-origin cell)))
                                     p)))
                       (list->kd-tree pts
                                      make-point: (lambda (v) (second v))
                                      make-value: (lambda (i v) (list (first v) 0.0)))

                       ))
             )))
    ((SetExpr (section p t))
     (lambda (repr)
       (case repr
         ((list)
          (map (lambda (cell) 
                 (list (cell-index cell) 
                       (cell-section-ref (quote t) cell)))
               p))
         ((tree)
          (cells-sections->kd-tree p (quote t)))
         )))
    ((SetExpr (union x y))
     (lambda (repr) (append ((SetExpr x) repr) ((SetExpr y) repr))))
    ))

(define neg -)

(define random-seeds (make-parameter (apply circular-list (or (opt 'random-seeds) (list 13 17 19 23 29 37)))))

(define (randomSeed)
  (let ((v (car (random-seeds))))
     (random-seeds (cdr (random-seeds)))
     v))
(define randomInit random-init)

(define randomNormal random-normal)
(define randomUniform random-uniform)

(define PointsFromFile load-points-from-file)
(define LineSegment make-line-segment)
(define Harmonic make-harmonic)


(define (SegmentProjection label r source target) 
  (segment-projection label
                      (source 'tree) (target 'list) 
                      r my-comm myrank mysize))
(define (Projection label r source target) 
  (projection label
              (source 'tree) (target 'list) 
              r my-comm myrank mysize))


EOF
    ))



(define (expr-codegen/scheme x)
  (cond
   ((or (symbol? x) (number? x) (string? x)) x)
   (else
    (match x 
           (('let bnds body) 
            `(let* ,(map (lambda (x) (list (car x) (expr-codegen/scheme (cadr x)))) bnds) 
               ,(expr-codegen/scheme body)))
           (((? symbol?) . rest)  
            (cons (car x) (map expr-codegen/scheme (cdr x))))
           (else #f))))
  )


(define (defun-codegen/scheme en)
  (let ((data (procedure-data (second en))))
    (and data
         (let ((name (lookup-def 'name data))
               (eval-body (lookup-def 'eval-body data))
               (rt (lookup-def 'rt data))
               (formals (lookup-def 'formals data)))
           `(define ,name ,(expr-codegen/scheme eval-body))))
    ))

                                
(define (invoke-generator/scheme sys section-name section-start-index
                                 section-processes section-perturbations
                                 layout-name forest-name forest-type)
  (let* ((origin (gensym 'p))

         (make-section (cases picnic:quantity 
                              (hash-table-ref sys (first (car section-processes)))
                              (PS (name gfun sfun init npts)   
                                  'make-section)
                              (SEGPS (name gfun sfun init npts)   
                                     'make-segmented-section)))

         (perturbation-exprs (map
                              (match-lambda
                               ((process-name process-n)
                                (cases picnic:quantity (hash-table-ref sys process-name)
                                       (PS (name gfun sfun init npts)   
                                           (let ((init-var (and init (gensym 'v))))
                                             (list 
                                              (if init 
                                                  `(,gfun gid ,origin ,init-var) 
                                                  `(,gfun gid ,origin))
                                              init
                                              init-var
                                              process-n)))
                                       
                                       (SEGPS (name gfun sfun init nsegs nsegpts)   
                                              (error 'invoke-generator/scheme
                                                     "perturbation process cannot be segmented"
                                                     process-name))
                                       )))
                              section-perturbations))

         (make-perturbations (lambda (expr)
                               (fold (match-lambda*
                                      (((pexpr init init-var n) ax)
                                        (let ((pvar (gensym 'p)))
                                          (if init
                                              `(let* ((,init-var ,init)
                                                      (,pvar (list-tabulate (inexact->exact ,n) (lambda (i) ,pexpr))))
                                                 (fold (lambda (p ax) (compose-curves p ax)) ,ax ,pvar))
                                              `(let* ((,pvar (list-tabulate (inexact->exact ,n) (lambda (i) ,pexpr))))
                                                 (fold (lambda (p ax) (compose-curves p ax)) ,ax ,pvar))
                                              ))
                                        ))
                                     expr
                                     perturbation-exprs)))
                             

         (exprs  (map

                  (match-lambda
                   ((process-name process-n . _)
                    
                    (cases picnic:quantity (hash-table-ref sys process-name)
                           (PS (name gfun sfun init npts)   
                               (let ((init-var (and init (gensym 'v))))
                                 (list 
                                  `(make-process
                                    ,(make-perturbations
                                      (if init 
                                          `(,gfun gid ,origin ,init-var) 
                                          `(,gfun gid ,origin) ))
                                    ,(case (car sfun)
                                       ((uniform) `(sample-uniform))
                                       ((polynomial) `(sample-polynomial . ,(cdr sfun)))
                                       (else (error 'picnic "unknown sampling method" sfun)))
                                    (inexact->exact ,npts))
                                  init
                                  init-var
                                  process-n)))
                           
                           (SEGPS (name gfun sfun init nsegs nsegpts)   
                                  (let ((init-var (and init (gensym 'v))))
                                    (list 
                                     `(make-segmented-process
                                       ,(make-perturbations
                                         (if init 
                                             `(,gfun gid ,origin ,init-var) 
                                             `(,gfun gid ,origin) ))
                                       ,(case (car sfun)
                                          ((uniform) `(sample-uniform))
                                          ((polynomial) `(sample-polynomial . ,(cdr sfun)))
                                          (else (error 'picnic "unknown sampling method" sfun)))
                                       (inexact->exact ,nsegs)
                                       (inexact->exact ,nsegpts))
                                     init
                                     init-var
                                     process-n)))
                           )))
                  section-processes))
         )

     ((lambda (x) (fold (match-lambda*
                         (((expr init init-var n) ax) 
                          (if init `(let ((,init-var ,init)) ,ax) ax)))
                        x exprs))
      `(let ((result
              (fold-right 
               (match-lambda* 
                (((gid ,origin) lst)
                 (match-let (((i pts)
                              (fold (match-lambda*
                                (((f n) (i lst))
                                 (list (+ i n)
                                       (append
                                        (list-tabulate 
                                         n (lambda (j) (list (+ i j 1) (f)))) lst))))
                               (list (inexact->exact ,section-start-index) '())
                               (list . ,(map (match-lambda
                                              ((expr init init-var n)
                                               `(list (lambda () ,expr) 
                                                      (inexact->exact ,n))))
                                             exprs))
                               )))

                            (cons (,make-section gid ,origin (quote ,section-name) pts)
                                  lst))
                 ))
                '()
                ,layout-name)))
         (if (picnic-write-sections)
             ,(case forest-type
                ((local)
                 `(write-sections (quote ,forest-name) (quote ,section-name) ,layout-name result myrank))
                ((global)
                 `(write-sections (quote ,forest-name) (quote ,section-name) ,layout-name result))))
         result
         ))

     ))
  
                                
(define (invoke-swc-loader/scheme sys section-name section-start-index
                                 section-swcs layout-name forest-name forest-type)
  (d "invoke-swc-loader: sections-swcs = ~A~%" section-swcs)
  (let* (
         (origin (gensym 'p))

         (make-section 'make-segmented-section)

         (swc-exprs
          (map
           
           (match-lambda*
            ((swc-name)
             (d "invoke-swc-loader: swc quantity = ~A~%" 
                (hash-table-ref sys swc-name))
             
             (cases picnic:quantity (hash-table-ref sys swc-name)
                    
                    (SWC (name path type nsegs)   
                         `(load-swcdir ,path (quote ,name) ,type (inexact->exact ,nsegs)) )
                    )))

           section-swcs))

         ;; 
         )

      `(let*
           (
            (swc-pools (list . ,swc-exprs))


            (result
             (fold-right 
              (match-lambda* 
               (((gid ,origin) lst)
                (match-let
                 (((i pts)
                   (fold 

                    (match-lambda*
                     ((f (i lst))
                      (list (+ i 1)
                            (append
                             (list-tabulate 
                              1 (lambda (j) (list (+ i j 1) (f gid ,origin))))
                             lst))))

                    (list (inexact->exact ,section-start-index) '())
                    (map (lambda (swc-pool)
                           (let ((swc-pool-n (length swc-pool)))
                             (lambda (cell-index cell-origin) 
                               (match-let (((type g gdistv gsegv) (choose swc-pool swc-pool-n)))
                                          (tree-graph->section-points cell-index cell-origin type g gdistv gsegv)))))
                         swc-pools)
                    )))
                 
                 (cons (,make-section gid ,origin (quote ,section-name) pts)
                       lst))
                ))
              '()
              ,layout-name))
            )

         (if (picnic-write-sections)
             ,(case forest-type
                ((local)
                 `(write-sections (quote ,forest-name) (quote ,section-name) ,layout-name result myrank))
                ((global)
                 `(write-sections (quote ,forest-name) (quote ,section-name) ,layout-name result))))
         result
         ))

     )
  


(define (forest-pointset-codegen/scheme sys forest pointsets)

  (define (forest-type x)  (third x))
  (define (cid x)  (second x))
  (define (cn x)   (first x))
		

  (d "forest = ~A~%" forest)

  (map (lambda (name+poset)
         (d "pointset = ~A~%" name+poset)
         (let (
               (pointset-name (first name+poset))
               (poset (second name+poset))
               )
           
           `(define  
              
              ,pointset-name
              
              (let* ((pts (kd-tree->list*
                           (car ,(fold-right 
                                  (lambda (xs ax)
                                    (fold (match-lambda*
                                           (((id . sym) ax)
                                            (let ((rhs (qrhs (hash-table-ref sys sym))))
                                              `(let ((,sym ,rhs)) ,ax))))
                                          ax xs))
                                  (cdr (last (last poset)))
                                  poset))
                           )))
                
                (if (picnic-write-pointsets)
                    (write-pointset (quote ,pointset-name) pts))

                pts))
           ))

       pointsets))



(define (forest-codegen/scheme sys forest layout sections swc-sections)

  (define (forest-type x)  (third x))
  (define (cid x)  (second x))
  (define (cn x)   (first x))
		

  (d "forest = ~A~%" forest)
  (d "layout = ~A~%" layout)
  (d "sections = ~A~%" sections)
  (d "swc-sections = ~A~%" swc-sections)


  (let (
        (layout-name
         (gensym
          (string->symbol
           (string-append
            (->string (cn forest))
            "_layout"))))
                 
        (section-names
         (map (lambda (section)
                (gensym
                 (string->symbol
                  (string-append
                   (->string (cn forest))
                   (->string (section-descriptor-label section))))))
              sections))

        (swc-section-names
         (map (lambda (section)
                (gensym
                 (string->symbol
                  (string-append
                   (->string (cn forest))
                   (->string (section-descriptor-label section))))))
              swc-sections))
        )

    `(define  

       ,(cid forest)

       (let*
           
           (
            (,layout-name 
             (let* ((pts (kd-tree->list*
                          (car ,(fold-right 
                                 (lambda (xs ax)
                                   (fold (match-lambda*
                                          (((id . sym) ax)
                                           (let ((rhs (qrhs (hash-table-ref sys sym))))
                                             `(let ((,sym ,rhs)) ,ax))))
                                         ax xs))
                                 (cdr (last (last layout)))
                                 layout))
                          ))
                    (layout
                     ,(case (forest-type forest)
                        ((local)
                         `(let recur ((pts pts) (myindex 0) (ax '()))
                            (if (null? pts) ax
                                (let ((ax1 (if (= (modulo myindex mysize) myrank)
                                               (cons (car pts) ax) ax)))
                                  (recur (cdr pts) (+ 1 myindex) ax1)))
                            ))
                        ((global)
                         'pts)))
                    )
               (if (picnic-write-pointsets)
                   (write-pointset (quote ,(cn forest)) pts))
               (if (picnic-write-layouts)
                   ,(case (forest-type forest)
                      ((local)
                       `(write-layout (quote ,(cn forest)) layout myrank))
                      ((global)
                       `(write-layout (quote ,(cn forest)) layout))))
               layout
               ))
            
            ,@(map 
               (lambda (section section-name)
                 (let ((section-perturbations (section-descriptor-perturbations section))
                       (section-processes (section-descriptor-processes section))
                       (section-label (section-descriptor-label section))
                       (section-start-index (section-descriptor-start-index section)))
                   `(,section-name 
                     ,(invoke-generator/scheme sys section-label section-start-index
                                               section-processes section-perturbations
                                               layout-name (cn forest) (forest-type forest)))
                   ))
              sections 
              section-names)
            
            ,@(map 
               (lambda (section section-name)
                 (let (
                       (section-swcs  (section-descriptor-processes section))
                       (section-label (section-descriptor-label section))
                       (section-start-index (section-descriptor-start-index section))
                       )
                   `(,section-name 
                     ,(invoke-swc-loader/scheme sys section-label section-start-index
                                                section-swcs layout-name
                                                (cn forest) (forest-type forest)))
                   ))
              swc-sections 
              swc-section-names)
            
            )
         
          (fold-right
           (match-lambda*
            (((gid p) ,@(append section-names swc-section-names) lst)
             (cons (make-cell (quote ,(cn forest)) gid p 
                              (list . ,(append section-names swc-section-names)))
                   lst)
             ))
           '()
           ,layout-name . ,(append section-names swc-section-names))
         
         ))
    ))



(define (projection-codegen/scheme sys cell-forests cell-sections projection)

  (define (resolve-forest-imports sym imports)
    (let ((x (member sym imports)))
      (d "resolve-forest-imports: sym = ~A imports = ~A cell-forests = ~A x = ~A~%" 
         sym imports cell-forests x)
      (and x (lookup-def (second sym) cell-forests))))
         
  (define (rewrite-projection expr label)
    (cond
     ((or (symbol? expr) (number? expr) (string? expr)) expr)
     (else
      (match expr
             (('let bnds body) 
              `(let* ,(map (lambda (x) (list (car x) (rewrite-projection (cadr x) label))) bnds) 
                 ,(rewrite-projection body label)))
             (((or 'SegmentProjection 'Projection) . rest)
              (cons (car expr) (cons `(quote ,label) rest)))
             (((? symbol?) . rest)  
              (cons (car expr) (map (lambda (x) (rewrite-projection x label)) (cdr expr))))
             (else expr)))
    ))
  

  (let* (
         (label   (projection-descriptor-label projection))
         (poset   (projection-descriptor-poset projection))
         (imports (projection-descriptor-imports projection))

         (dd (d "projection label = ~A~%" label))
         (dd (d "projection imports = ~A~%" imports))
         (dd (d "projection poset = ~A~%" poset))
         (dd (d "cell-sections = ~A~%" cell-sections))
         (dd (d "cell-forests = ~A~%" cell-forests))

         (projection-name
          (gensym
           (string->symbol
            (string-append (->string label) "_projection"))))
         )

    `(define  

       ,projection-name

       
       ,((lambda (body) 
           (if (not (null? imports))
               `(let ,(map (lambda (x)
                             (let ((sym (first x))
                                   (ns  (third x)))
                               (case ns 
                                 ((cell-forests)
                                  `(,sym ,(first (resolve-forest-imports x imports))))
                                 (else (error 'projection-codegen "unknown import namespace" ns)))
                               ))
                           imports)
                  ,body)
               body))
         (fold-right 
          (lambda (xs ax)
            (fold (match-lambda*
                   (((id . sym) ax)
                    (let ((rhs (qrhs (hash-table-ref sys sym))))
                      (d "projection poset sym = ~A rhs = ~A~%" sym rhs)
                      (let ((rhs1 (rewrite-projection rhs label)))
                        (if rhs1 `(let ((,sym ,rhs1)) ,ax) ax))
                    ))
                   )
                  ax xs))
          (cdr (last (last poset)))
          poset))
       )
    ))

  
(define (main opt operands)

  (if (opt 'version)
      (begin
	(print (picnic:version-string))
	(exit 0)))

  (if (null? operands)

      (picnic:usage)

      (let* (
	    (model-sources
	     (map
              (lambda (operand)
                (let* (
                       (read-sexp  
                        (lambda (name) 
                          (call-with-input-file name read)))

                       (read-iexpr
                        (lambda (name) 
                          (call-with-input-file name 
                            (lambda (port) 
                              (let ((content
                                     (iexpr:tree->list
                                      (iexpr:parse operand port))))
                                (car content))))))
                       
                       (in-format
                        (cond ((opt 'input-format) => 
                               (lambda (x) 
                                 (case ($ x)
                                   ((picnic)      'picnic)
                                   ((s-exp sexp)  'sexp)
                                   (else          (error 'picnic "unknown input format" x)))))
                              (else
                               (case ((lambda (x) (or (not x) ($ x)))
                                      (pathname-extension operand))
                                 ((s-exp sexp)  'sexp)
                                 (else 'picnic)))))

                       (doc.iexpr
                        (case in-format
                          ((picnic)  
                           (let ((content (read-sexp operand)))
                             (if (eq? content 'picnic-model)
                                 (cons (read-iexpr operand) #t)
                                 (cons content #f))))
                          ((sexp)  
                           (cons (read-sexp operand) #f))
                          (else    (error 'picnic "unknown input format" in-format))))
                       
                       (dd          (if (opt 'debug)
                                        (begin
                                          (pp (car doc.iexpr))
                                          (picnic-verbose 1))))
			   
                       (parse-expr
                        (case in-format
                          ((sexp)         identity)
                          ((picnic)              (if (cdr doc.iexpr) 
                                                   (lambda (x #!optional loc) 
                                                     (if (string? x) (picnic:parse-string-expr x loc)
                                                         (picnic:parse-sym-expr x loc)))
                                                   picnic:parse-sym-expr))
                          (else    (error 'picnic "unknown input format" in-format))))

                       
                       (model-name.model-decls
                        (case in-format
                          ((sexp picnic)         (sexp->model-decls (car doc.iexpr)))
                          (else    (error 'picnic "unknown input format" in-format))))
                       
                       )

                  (ModelSource
                   operand in-format
                   (car model-name.model-decls)
                   (filter (lambda (x) (not (null? x))) (cadr model-name.model-decls))
                   (match model-name.model-decls 
                          ((_ _ user-templates)
                           user-templates)
                          (else '()))
                   (cdr doc.iexpr) 
                   parse-expr)
                  ))
              operands))

	    (models
             (map (lambda (x) 
                    (cases picnic:model x
                           
                           (ModelSource (source-path in-format model-name model-decls user-templates iexpr parse-expr)
                                        (model-source->model source-path in-format model-name 
                                                             model-decls user-templates iexpr parse-expr))
                           
                           
                           (else (error 'name "invalid model source" x))))
                  
                  model-sources))
            )
	
	(let ((template-insts (opt 'template)))

          (for-each
           
           (lambda (model)
             
             (cases picnic:model model
                    
                    (SingleModel (source-path in-format model-name sys model-decls user-templates iexpr? parse-expr)
				 
                                 (process-model opt source-path in-format #f sys model-decls iexpr? parse-expr)
                                 
                                 (if template-insts
                                     (for-each
                                      (lambda (template-inst)
                                        (match-let (((template-name . template-args)
                                                     (string-split template-inst ":")))
                                                   (let ((output-file-suffix (or (opt 'template-prefix) template-name)))
                                                     (process-template model-name template-name template-args 
                                                                       output-file-suffix user-templates source-path))
                                                   ))
                                      template-insts))
                                 )

		  
		  (else (error 'picnic "invalid model" model))))

           models))
        )
      ))


(main opt (opt '@))


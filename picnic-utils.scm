;;
;; Neural Parametric Curve Connectivity spatial and geometric utility procedures.
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

(module picnic-utils

        *


        (import scheme chicken)

        
        (require-extension srfi-69 datatype matchable vector-lib regex
                           mpi mathh typeclass kd-tree random-mtzig
                           lalr-driver digraph graph-dfs)


        (require-library srfi-1 srfi-4 srfi-13 irregex files posix data-structures
                         bvsp-spline parametric-curve)


        (import 
                (only srfi-1 
                      fold fold-right filter-map filter every zip list-tabulate delete-duplicates partition 
                      first second third take drop concatenate)
                (only srfi-4 
                      s32vector s32vector-length s32vector-ref s32vector-set! make-s32vector
                      f64vector f64vector? f64vector-ref f64vector-set! f64vector-length f64vector->list list->f64vector make-f64vector)
                (only srfi-13 string= string< string-null? string-prefix? string-trim-both)
                (only irregex string->irregex irregex-match)
                (only files make-pathname)
                (only posix glob find-files)
                (only extras read-lines pp fprintf )
                (only ports with-output-to-port )
                (only data-structures ->string alist-ref compose identity string-split sort atom?)
                (only lolevel extend-procedure procedure-data extended-procedure?)
                (prefix bvsp-spline bvsp-spline:)
                (prefix parametric-curve pcurve:)
                )

        (define picnic-verbose (make-parameter 0))


        (define (d fstr . args)
          (let ([port (current-error-port)])
            (if (positive? (picnic-verbose)) 
                (begin (apply fprintf port fstr args)
                       (flush-output port) ) )))


        (include "mathh-constants")

        (define (find-index pred lst)
          (let recur ((lst lst) (i 0))
            (cond ((null? lst) #f)
                  ((pred (car lst)) i)
                  (else (recur (cdr lst) (+ i 1)))
                  )))

        (define (sign x) (if (negative? x) -1.0 1.0))

        (define (f64vector-empty? x) (zero? (f64vector-length x)))

        (define (random-init seed) (init seed))

        (define (random-uniform low high st)
          (let ((rlo (if (< low high) low high))
                (rhi (if (< low high) high low))) 
            (let ((delta (+ 1 (- rhi rlo)))
                  (v (randu! st)))
              (+ rlo (floor (* delta v)))
              ))
          )


        (define (random-normal mean sdev st)
          (+ mean (* sdev (randn! st))))

        (import-instance (<KdTree> KdTree3d)
                         (<Point> Point3d))
        
        ;; convenience procedure to access to results of kd-tree-nearest-neighbor queries
        (define (kdnn-point x) (cadr x))
        (define (kdnn-distance x) (caddr x))
        (define (kdnn-index x) (caar x))
        (define (kdnn-parent-index x) (car (cadar x)))
        (define (kdnn-parent-distance x) (cadr (cadar x)))


        (define point->list f64vector->list)
        

        
        (define-record-type pointset (make-pointset prefix id points boundary)
          pointset? 
          (prefix pointset-prefix)
          (id pointset-id)
          (points pointset-points)
          (boundary pointset-boundary)
          )

        (define-record-type genpoint (make-genpoint coords parent-index parent-distance segment)
          genpoint? 
          (coords genpoint-coords)
          (parent-index genpoint-parent-index)
          (parent-distance genpoint-parent-distance)
          (segment genpoint-segment)
          )

        (define-record-type swcpoint (make-swcpoint id type coords radius pre)
          swcpoint? 
          (id swcpoint-id)
          (type swcpoint-type)
          (coords swcpoint-coords)
          (radius swcpoint-radius)
          (pre swcpoint-pre)
          )

        (define-record-type layer-point (make-layer-point id coords radius layer)
          layer-point? 
          (id layer-point-id)
          (coords layer-point-coords)
          (radius layer-point-radius)
          (layer layer-point-layer)
          )

        
        (define-record-type cell (make-cell ty index origin sections)
          cell? 
          (ty cell-type)
          (index cell-index)
          (origin cell-origin)
          (sections cell-sections)
          )
        
        
        (define (cell-section-ref name cell)
          (let ((v (alist-ref name (cell-sections cell))))
            (if (not v) (error 'cell-section-ref "unable to find section" name cell)
                v)))

        
        (define (write-pointset name pts)
            (call-with-output-file (sprintf "~A.pointset.dat" name)
              (lambda (out)
                (for-each (match-lambda
                           ((gid p)
                            (fprintf out "~A ~A ~A~%" 
                                     (coord 0 p)
                                     (coord 1 p)
                                     (coord 2 p))))
                          pts))
              ))

        
        (define (write-layout name pts #!optional rank)
            (call-with-output-file (if rank 
                                       (sprintf "~A.~A.layout.dat" name rank)
                                       (sprintf "~A.layout.dat" name))
              (lambda (out)
                (for-each (match-lambda
                           ((gid p)
                            (fprintf out "~A ~A ~A ~A~%" 
                                     gid
                                     (coord 0 p)
                                     (coord 1 p)
                                     (coord 2 p))))
                          pts))
              ))

        (define (write-sections forest-name section-name layout sections #!optional rank)
          (call-with-output-file (if rank
                                     (sprintf "~A.~A.~A.section.dat" forest-name section-name rank)
                                     (sprintf "~A.~A.section.dat" forest-name section-name))
            (lambda (out)
              (for-each
               (match-lambda*
                (((gid p) section)
                 (fprintf out "~A " gid)
                 (for-each 
                  (lambda (neurites)
                    (for-each
                     (lambda (gd)
                       (let ((p (genpoint-coords gd)))
                         (fprintf out "~A ~A ~A "
                                  (coord 0 p)
                                  (coord 1 p)
                                  (coord 2 p))))
                     (cdr neurites)))
                  (cdr section))
                 (fprintf out "~%")
                 ))
               layout 
               sections))))


        (define (cells-sections->kd-tree cells section-name #!key
                                         (make-value
                                          (lambda (i v) 
                                            (list (genpoint-parent-index v)
                                                  (genpoint-parent-distance v))))
                                         (make-point
                                          (lambda (v) (genpoint-coords v))))
          (let ((t 
                 (let recur ((cells cells) (points '()))
                   (if (null? cells)
                       (list->kd-tree
                        points
                        make-value: make-value
                        make-point: make-point)
                       (let ((cell (car cells)))
                         (recur (cdr cells) 
                                (let inner ((sections (append (cell-section-ref section-name cell)))
                                            (points points))
                                  (if (null? sections) points
                                      (inner
                                       (cdr sections)
                                       (append (cdr (car sections)) points))
                                      ))
                                ))
                       ))
                 ))
            t))

        (define (sections->kd-tree cells #!key
                                   (make-value
                                    (lambda (i v) 
                                      (list (genpoint-parent-index v)
                                            (genpoint-parent-distance v))))
                                   (make-point
                                    (lambda (v) (genpoint-coords v))))
          (let ((t 
                 (let recur ((cells cells) (points '()))
                   (if (null? cells)
                       (list->kd-tree
                        points
                        make-value: make-value
                        make-point: make-point)
                       (let ((sections (car cells)))
                         (let inner ((sections sections) (points points))
                           (if (null? sections)
                               (recur (cdr cells) points)
                               (let ((section (car sections)))
                                 (inner (cdr sections) 
                                        (append (cdr (cadr section)) points))
                                 ))
                           ))
                       ))
                 ))
            t))


        (define (cells-origins->kd-tree cells)
          (let ((t 
                 (let recur ((cells cells) (points '()))
                   (if (null? cells)
                       (list->kd-tree
                        points
                        make-value: (lambda (i v) 
                                      (list (genpoint-parent-index v)
                                            (genpoint-parent-distance v)))
                        make-point: (lambda (v) (genpoint-coords v))
                        )
                       (let ((cell (car cells)))
                         (recur (cdr cells) 
                                (cons (make-genpoint (cell-origin cell) (cell-index cell) 0. 0)
                                      points)))
                       ))
                 ))
            t))

        (define (pointCoord axis p)
          (coord (inexact->exact axis) p))

        ;; Samples a parametric curve at regular intervals in the range xmin..xmax inclusive.
        (define (sample-uniform)
          (lambda (n)
            (let* (
                   (xmin  0.0)
                   (xmax  1.0)
                   (delta (- xmax xmin))
                   (dx    (if (zero? delta) 0
                              (if (< n 2)
                                (error 'sample-uniform "number of iterations must be >= 2")
                                (/ (- xmax xmin) (- n 1)))))
                   )
              (list-tabulate n (lambda (i) (+ xmin (* dx i))))
              )))


        ;; Samples a parametric curve according to a polynomial
        ;; c0 + c1 x + c2 x^2 in the range xmin..xmax inclusive.
        (define (sample-polynomial c0 c1 c2)
          (lambda (n)
            (let* (
                   (f (lambda (x) (+ c0 (* x c1) (* x x c2))))
                   (dx (/ 1.0 n))
                   )
              (let recur ((i 0.0) (fi 0.0) (lst '()))
                (let ((fi1 (+ fi (f i))))
                  (if (<= fi1 1.0)
                      (recur (+ i dx) fi1 (cons fi1 lst))
                      (reverse lst))))
              )))


        (define (compose-curves c1 c2)
          (let ((c (pcurve:compose-curve (list + + +) c1 c2)))
;            (print "compose-curves: c1 = ") (pp (pcurve:iterate-curve c1 10))
;            (print "compose-curves: c2 = ") (pp (pcurve:iterate-curve c2 10))
;            (print "compose-curves: c = ") (pp (pcurve:iterate-curve c 10))
            c))
              

        (define (make-simple-curve fx fy fz n) 
          (let ((c (pcurve:simple-curve n 1 (list fx fy fz) 0.0 1.0)))
            c
            ))
        

        (define (make-harmonic axis amp period phase n)
          (let* ((freq (/ (* 2 PI) (/ 1.0 period)))
                 (pf   (lambda (t) (* amp (cos (+ (* freq t) phase)))))
                 (zf   (lambda (t) 0.0))
                 (c (pcurve:simple-curve 
                    (inexact->exact n) 1
                    (cond ((= axis 0)
                           (list pf zf zf))
                          ((= axis 1)
                           (list zf pf zf))
                          ((= axis 2)
                           (list pf zf zf))
                          (else 
                           (error 'make-harmonic "invalid axis" axis))
                          )
                    0.0 1.0)))
            c
            ))
        

        (define (make-line-segment p dx dy dz) 
          (let ((c (pcurve:line-segment 3 (list dx dy dz))))
            (pcurve:translate-curve (point->list p) c)
            ))
        
        
        ;; auxiliary function to create segment points
        (define (make-segment si np sp xyz)
          (list-tabulate 
           np
           (lambda (i) (let* ((pi (+ sp i))
                              (p (make-point 
                                  (f64vector-ref (car xyz) pi)
                                  (f64vector-ref (cadr xyz) pi)
                                  (f64vector-ref (caddr xyz) pi))))
                         (list si p)
                         ))
           ))


          

        ;;
        ;; Creates a process of the given segments and number of points per
        ;; segment from the given curve.
        ;;
        (define (make-segmented-process c f ns np)
          (let ((xyz ((pcurve:sample-curve* c) (f (* ns np)))))
            (let ((np1 (floor (/ (f64vector-length (car xyz)) ns))))
              (let recur ((si ns) (ax '()))
                (if (positive? si)
                    (let ((sp (* (- si 1) np1)))
                      (recur (- si 1) (append (make-segment si np1 sp xyz) ax)))
                    ax)
                ))
            ))

        ;;
        ;; Non-segmented process
        ;;
        (define (make-process c f np)
          (let ((xyz ((pcurve:sample-curve* c) (f np))))
            (list-tabulate 
             (f64vector-length (car xyz))
             (lambda (i) 
               (make-point 
                (f64vector-ref (car xyz) i)
                (f64vector-ref (cadr xyz) i)
                (f64vector-ref (caddr xyz) i)))
             ))
          )
        
        
        ;;
        ;; Creates a named section containing points from the given segmented processes.
        ;;
        (define (make-segmented-section gid p label ps)
          `(,label . 
                   ,(fold (lambda (i+proc ax)
                            (let ((seci (car i+proc)) 
                                  (proc (cadr i+proc)))
                              (cons 
                               `(,seci . 
                                       ,(map (lambda (sp)
                                               (let ((segi (car sp))
                                                     (dpoint (cadr sp)))
                                                 (let ((soma-distance (sqrt (dist2 p dpoint))))
                                                   (make-genpoint dpoint gid soma-distance segi))
                                                 ))
                                             proc))
                               ax)
                              ))
                          '() ps)
                   ))
        
        ;;
        ;; Non-segmented named section
        ;;
        (define (make-section gid p label ps)
          `(,label . 
                   ,(fold (lambda (i+proc ax)
                            (let* ((seci (car i+proc)) 
                                   (proc (cadr i+proc))
                                   (pts (map (lambda (dpoint)
                                               (let ((soma-distance (sqrt (dist2 p dpoint))))
                                                 (make-genpoint dpoint gid soma-distance #f)))
                                             proc)))
                              (d "make-section: label = ~A gid = ~A p = ~A pts = ~A~%" 
                                 label gid p proc)
                              (cons `(,seci . ,pts) ax)
                              ))
                          '() ps)
                   ))
        
        
        
        (define (make-gen-kd-tree data #!key (threshold 0.0))
          
          (define (update-bb p x-min y-min z-min x-max y-max z-max)
            (let ((x (coord 0 p)) (y (coord 1 p)) (z (coord 2 p)))
              (if (< x (x-min)) (x-min x))
              (if (< y (y-min)) (y-min y))
              (if (< z (z-min)) (z-min z))
              (if (> x (x-max)) (x-max x))
              (if (> y (y-max)) (y-max y))
              (if (> z (z-max)) (z-max z))
              ))


          (let* (
                 (t (list->kd-tree
                     (filter (lambda (x) (<= threshold (cdr x))) data)
                     make-value: (lambda (i v) (cdr v))
                     make-point: (lambda (v) (apply make-point (car v)))
                     offset: 0
                     ))
                 (n (kd-tree-size t))
                 (x-min (make-parameter +inf.0))
                 (y-min (make-parameter +inf.0))
                 (z-min (make-parameter +inf.0))
                 (x-max (make-parameter -inf.0))
                 (y-max (make-parameter -inf.0))
                 (z-max (make-parameter -inf.0))
                 (bb (begin (kd-tree-for-each
                             (lambda (p) (update-bb p x-min y-min z-min
                                                    x-max y-max z-max))
                             t)
                            (list (x-min) (y-min) (z-min) (x-max) (y-max) (z-max))))
                 )

            (cons bb t)

            ))





        (define (genpoint-projection prefix my-comm myrank size cells fibers zone cell-start fiber-start)

          (d "rank ~A: prefix = ~A zone = ~A length cells = ~A~%" myrank prefix zone (length cells))

          (fold (lambda (cell ax)

                  (d "rank ~A: cell = ~A~%" myrank cell)

                  (let* ((i (+ cell-start (car cell)))
                         (root (modulo i size))
                         (sections (cadr cell)))
                    
                    (fold 
                     
                     (lambda (sec ax)
                       
                       (let ((seci (car sec))
                             (gxs  (cdr sec)))
                         
                         (let ((query-data
                                (fold 
                                 (lambda (gd ax)
                                   (d "rank ~A: querying point ~A (~A)~%" 
                                      myrank (genpoint-coords gd) 
                                      (genpoint-parent-index gd))
                                   (fold
                                    (lambda (x ax) 
                                      (let (
                                            (source (car x))
                                            (target i)
                                            (distance (cadr x))
                                            (segi (genpoint-segment gd))
                                            )
                                        (if (not segi)
                                            (error 'genpoint-projection "point does not have segment index" gd))
                                        (append (list source target distance segi seci) ax)
                                        ))
                                    ax
                                    (delete-duplicates
                                     (map (lambda (x) 
                                            (d "rank ~A: query result = ~A (~A) (~A) ~%" 
                                               myrank (kdnn-point x) (kdnn-distance x) (kdnn-parent-index x))
                                            (list (+ fiber-start (kdnn-parent-index x))
                                                  (+ (kdnn-distance x) (genpoint-parent-distance gd)  (kdnn-parent-distance x))
                                                  ))
                                          (kd-tree-near-neighbors* fibers zone (genpoint-coords gd)))
                                     (lambda (u v)
                                       (= (car u) (car v)))
                                     )
                                    ))
                                 '() gxs)))
                           (let* ((res0 (MPI:gatherv-f64vector (list->f64vector query-data) root my-comm))

                                  (res1 (or (and (= myrank root) (filter (lambda (x) (not (f64vector-empty? x))) res0)) '())))
                             
                             (append res1 ax))
                           
                           ))
                       )
                     ax sections)
                    ))
                '() cells)
          )


        

        (define (point-projection prefix my-comm myrank size pts fibers zone point-start nn-filter)
          (fold (lambda (px ax)

                  (d "~A: rank ~A: px = ~A zone=~A~%"  prefix myrank px zone)

                  (let* ((i (+ point-start (car px)))
                         (root (modulo i size))
                         (dd (d "~A: rank ~A: querying point ~A (root ~A)~%" prefix myrank px root))
                         (query-data
                          (let ((pd (cadr px))) 
                            (fold
                             (lambda (x ax) 
                               (let ((source (car x))
                                     (target i)
                                     (distance (cadr x)))
                                 (if (and (> distance  0.) (not (= source target)))
                                     (append (list source target distance) ax)
                                     ax)
                                 ))
                             '()
                             (delete-duplicates
                              (map (lambda (x) 
                                     (let ((res (list (car (cadar x))  
                                                      (+ (caddr x) (cadr (cadar x))))))
                                       (d "~A: x = ~A res = ~A~%" prefix x res)
                                       res))
                                   (nn-filter pd (kd-tree-near-neighbors* fibers zone pd))
                                   )
                              (lambda (u v) (= (car u) (car v)))
                              )
                             ))
                          ))


                    (let* ((res0 (MPI:gatherv-f64vector (list->f64vector query-data) root my-comm))
                           (res1 (or (and (= myrank root) (filter (lambda (x) (not (f64vector-empty? x))) res0)) '())))
                      (append res1 ax))
                    ))

                '() pts))
        




        (define-datatype layer-boundary layer-boundary?
          (Bounds (top number?) (left number?) (bottom number?) (right number?))
          (BoundsXZ (top number?) (left number?) (bottom number?) (right number?)
                    (n integer?) (k integer?) (x f64vector?) (y f64vector?) (d f64vector?) (d2 f64vector?))
          (BoundsYZ (top number?) (left number?) (bottom number?) (right number?)
                    (n integer?) (k integer?) (x f64vector?) (y f64vector?) (d f64vector?) (d2 f64vector?))
          )



        (define (boundary-z-extent-function boundary)
          (cases layer-boundary boundary
                 (Bounds (top left bottom right) 
                         (lambda (x y) 0.))
                 (BoundsXZ (top left bottom right n k x y d d2) 
                           (lambda (xp yp) 
                             (let-values (((y0tab y1tab y2tab res)
                                           (bvsp-spline:evaluate n k x y d d2 (f64vector xp) 0)))
                               (f64vector-ref y0tab 0))))
                 (BoundsYZ (top left bottom right n k x y d d2) 
                           (lambda (xp yp) 
                             (let-values (((y0tab y1tab y2tab res)
                                           (bvsp-spline:evaluate n k x y d d2 (f64vector yp) 0)))
                               (f64vector-ref y0tab 0))))
                 ))


        (define (point2d-rejection top left bottom right)
            (lambda (p)
              (let ((x (coord 0 p)) (y (coord 1 p)))
                (and (fp> x left)  (fp< x right) (fp> y bottom) (fp< y top) p)))
            )


        (define (compute-point3d p zu z-extent-function)
          (let* ((x (coord 0 p))
                 (y (coord 1 p))
                 (z-extent (z-extent-function x y)))
            (if (zero? zu)
                (make-point x y zu)
                (make-point x y (fp* zu z-extent)))
            ))


        (define (cluster-point-rejection p cluster-pts mean-distance)
          (let ((D (* 4 mean-distance mean-distance))
                (nn (kd-tree-nearest-neighbor cluster-pts p)))
            (and (< (dist2 p nn) D) p)))



        (define (XZAxis n k x-points z-points boundary)
          
          (if (not (>= n 3)) 
              (error 'generate-boundary "XZAxis requires at least 3 interpolation points (n >= 3)"))
          
          (cases layer-boundary boundary
                 (Bounds (top left bottom right)  

                         (let-values (((d d2 constr errc diagn)
                                       (bvsp-spline:compute n k x-points z-points)))
                           
                           (if (not (zero? errc)) 
                               (error 'generate-boundary "error in constructing spline from boundary points" errc))
                           
                           (BoundsXZ top left bottom right n k x-points z-points d d2)))
                 
                 (else (error 'generate-boundary "boundary argument to XZAxis is already a pseudo-3D boundary")))
          )


        (define (Grid x-spacing y-spacing z-spacing boundary)

          (match-let (((top left bottom right)
                       (cases layer-boundary boundary
                                   (Bounds (top left bottom right) 
                                           (list top left bottom right))
                                   (BoundsXZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   (BoundsYZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   )))

          (let* (
                 (x-extent   (- right left))
                 (y-extent   (- top bottom))
                 (z-extent-function
                  (boundary-z-extent-function boundary))
                 (compute-grid-points3d
                  (lambda (p z-spacing z-extent-function)
                    (let* ((x (coord 0 p))
                           (y (coord 1 p))
                           (z-extent (z-extent-function x y)))
                      (let recur ((points '()) (z (/ z-spacing 2.)))
                        (if (> z z-extent)
                            points
                            (recur (cons (make-point x y z) points) (+ z z-spacing)))
                        ))
                    ))
                 )
            
            (d "Grid: x-spacing = ~A~%" x-spacing)
            (d "Grid: y-spacing = ~A~%" y-spacing)
            (d "Grid: z-spacing = ~A~%" z-spacing)
            
            (d "Grid: x-extent = ~A~%" x-extent)
            (d "Grid: y-extent = ~A~%" y-extent)
            
            (let ((x-points (let recur ((points '()) (x (/ x-spacing 2.)))
                              (if (> x x-extent)
                                  (list->f64vector (reverse points))
                                  (recur (cons x points) (+ x x-spacing)))))
                  (y-points (let recur ((points '()) (y (/ y-spacing 2.)))
                              (if (> y y-extent)
                                  (list->f64vector (reverse points))
                                  (recur (cons y points) (+ y y-spacing)))))
                  )
              
              (let ((nx (f64vector-length x-points))
                    (ny (f64vector-length y-points))
                    )
                
                (let recur ((i 0) (j 0) (ax '()))
                  (if (< i nx)
                      (let ((x (f64vector-ref x-points i)))
                        (if (< j ny)
                            (let* ((y   (f64vector-ref y-points j))
                                   (p   (make-point x y))
                                   (p3ds (if (zero? z-spacing)
                                             (list (make-point x y 0.0))
                                             (compute-grid-points3d p z-spacing z-extent-function)))
                                   )
                              (recur i (+ 1 j) (if p3ds (append p3ds ax) ax)))
                            (recur (+ 1 i) 0 ax)))
                      (let* ((t (list->kd-tree ax))
                             (n (kd-tree-size t)))
                        (list t boundary)
                        ))
                  )))
            ))
          )

        (define (UniformRandomPointProcess n x-seed y-seed boundary)

          (match-let (((top left bottom right)
                       (cases layer-boundary boundary
                                   (Bounds (top left bottom right) 
                                           (list top left bottom right))
                                   (BoundsXZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   (BoundsYZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   )))

          (let* (
                 (x-extent   (- right left))
                 (y-extent   (- top bottom))
                 (z-extent-function (boundary-z-extent-function boundary))
                 )

            (let ((x-points (f64vector-randu! (inexact->exact n) (init x-seed)))
                  (y-points (f64vector-randu! (inexact->exact n) (init y-seed)))
                  (z-points (f64vector-randu! (inexact->exact n) (init (current-milliseconds)))))
              
              (let ((point-rejection1 (point2d-rejection top left bottom right)))
                
                (let recur ((i 0) (ax '()))
                  (if (< i n)
                      (let ((x (f64vector-ref x-points i))
                            (y (f64vector-ref y-points i))
                            (z (f64vector-ref z-points i)))
                        (let ((p (make-point (fp* x x-extent) (fp* y y-extent))))
                          (let ((p3d 
                                 (and (point-rejection1 p)
                                      (compute-point3d p z z-extent-function))))
                            (recur (+ 1 i) (if p3d (cons p3d ax) ax)))))
                      (let* ((t (list->kd-tree ax))
                             (n (kd-tree-size t)))

                        (list t boundary))))
                ))
            ))
          )


        (define (ClusteredRandomPointProcess cluster-pts n mean-distance x-seed y-seed boundary)

          (match-let (((top left bottom right)
                       (cases layer-boundary boundary
                                   (Bounds (top left bottom right) 
                                           (list top left bottom right))
                                   (BoundsXZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   (BoundsYZ (top left bottom right n k x y d d2) 
                                             (list top left bottom right))
                                   )))


          (let* (
                 (x-extent   (- right left))
                 (y-extent   (- top bottom))
                 (z-extent-function (boundary-z-extent-function boundary))
                 )

            (let recur ((pts '()) (x-seed x-seed) (y-seed y-seed))

              (let ((x-points (f64vector-randu! n (init x-seed)))
                    (y-points (f64vector-randu! n (init y-seed)))
                    (z-points (f64vector-randu! n (init (current-milliseconds)))))
                
                (let ((point-rejection1 (point2d-rejection top left bottom right)))
                  
                  (let inner-recur ((j 0) (ax pts))
                    (if (< j n)
                        (let ((x (f64vector-ref x-points j))
                              (y (f64vector-ref y-points j))
                              (z (f64vector-ref z-points j)))
                          (let ((p (make-point (fp* x x-extent) (fp* y y-extent))))
                            (let ((p3d 
                                   (and (point-rejection1 p)
                                        (compute-point3d p z z-extent-function))))
                              (let ((pp (cluster-point-rejection p3d cluster-pts mean-distance)))
                                (inner-recur (+ 1 j)  (if pp (cons pp ax) ax))))))

                        (if (< (length ax) n)
                            (recur ax (+ 1 x-seed) (+ 1 y-seed))
                            (let* ((t (list->kd-tree (take ax n)))
                                   (n (kd-tree-size t)))
                              
                              (list t boundary))))
                    ))
                ))
            ))
          )



        
        (define comment-pat (string->irregex "^#.*"))


        (define (load-points-from-file filename)

          (let ((in (open-input-file filename)))
            
            (if (not in) (error 'load-points-from-file "file not found" filename))

            (let* ((lines
                    (filter (lambda (line) (not (irregex-match comment-pat line)))
                            (read-lines in)))

                   (point-data
                    (filter-map
                     (lambda (line) 
                       (let ((lst (map string->number (string-split line " \t"))))
                         (and (not (null? lst)) (apply make-point lst))))
                     lines))

                   (point-tree (list->kd-tree point-data))
                   )
              
              (list point-tree)
              
              ))
          )


        (define (make-swc-tree-graph lst label)
          
          (let* (
                 (g              (make-digraph label #f))
                 (node-info      (g 'node-info))
                 (node-info-set! (g 'node-info-set!))
                 (add-node!      (g 'add-node!))
                 (add-edge!      (g 'add-edge!))
                 )

            ;; insert nodes
            (let recur ((lst lst))

              (if (not (null? lst))

                  (let ((point (car lst)))

                    (let ((node-id (swcpoint-id point)))

                      (add-node! node-id point)

                      (recur (cdr lst))))))

            ;; insert edges
            (let recur ((lst lst))
              
              (if (not (null? lst))
                  
                  (let ((point (car lst)))
                    

                    (let ((node-id (swcpoint-id point))
                          (pre-id  (swcpoint-pre point)))

                      (if (> pre-id 0)

                          (let* ((pre-point   (node-info pre-id))
                                 (pre-coords  (and pre-point (swcpoint-coords pre-point)))
                                 (node-coords (swcpoint-coords point))
                                 (distance    (sqrt (dist2 node-coords pre-coords))))
                            
                            (add-edge! (list pre-id node-id distance))))
                        
                      (recur (cdr lst))
                      ))
                  ))
            g 
            ))


        (define (swc-tree-graph->section-points cell-index cell-origin type g gdistv gsegv)
          
          (let* ((node-info (g 'node-info))
                 (succ      (g 'succ))
                 (offset    (let ((cell-loc (point->list cell-origin))
                                  (root-loc (point->list (swcpoint-coords (node-info 1)))))
                              (map - cell-loc root-loc))))

            (d "swc-tree-graph->section-points: offset = ~A~%" offset)


            (let recur ((n 1) (lst '()))

              (let* (
                     (point (node-info n))
                     (point-type (swcpoint-type point))
                     (point-pre (swcpoint-pre point))
                     (proceed? (or (= point-type type)
                                   (case (swcpoint-type point)
                                     ((0 1 5 6) #t)
                                     (else #f))))
                     )

                (d "swc-tree-graph->section-points: n = ~A point-type = ~A proceed? = ~A~%" 
                   n point-type proceed?)

                (d "swc-tree-graph->section-points: succ n = ~A~%" (succ n))
                  
                (if proceed?

                    (let (
                          (point1 (list
                                   (s32vector-ref gsegv n)
                                   (apply make-point (map + offset (point->list (swcpoint-coords point))))))
                          )

                      (fold (lambda (x ax) (recur x ax))
                            (cons point1 lst)
                            (succ n)))

                    lst)

                ))
            ))


        (define (make-layer-tree-graph topology-sections topology-layers topology points label)
          
          (let* (
                 (g              (make-digraph label topology-layers))
                 (node-info      (g 'node-info))
                 (node-info-set! (g 'node-info-set!))
                 (add-node!      (g 'add-node!))
                 (add-edge!      (g 'add-edge!))
                 )

            ;; insert nodes
            (let recur ((lst points))

              (if (not (null? lst))

                  (let ((point (car lst)))

                    (let ((node-id (layer-point-id point)))

                      (add-node! node-id point)

                      (recur (cdr lst))))))

            ;; insert edges from dendritic topology
            (let recur ((lst (car topology)))

              (if (not (null? lst))
                  
                  (match-let (((dest-id src-id) (car lst)))
              
                             (let* ((dest-point   (node-info dest-id))
                                    (dest-coords  (layer-point-coords dest-point))
                                    (node-point   (node-info src-id))
                                    (node-coords  (layer-point-coords node-point))
                                    (distance     (sqrt (dist2 dest-coords node-coords))))
                               (add-edge! (list src-id dest-id distance))))
                  
                  (recur (cdr lst))
                  ))

            g 
            ))


        (define (tree-graph-distances+segments g nseg)


          (define n        ((g 'capacity)))
          (define distv    (make-f64vector (+ 1 n) -1.0))
          (define rdistv   (make-f64vector (+ 1 n) -1.0))
          (define segv     (make-s32vector (+ 1 n) -1))


          ;; determine distances from root
          (define (traverse-dist es)
            (if (null? es) distv
                (match-let (((i j dist) (car es)))
                  (if (>= (f64vector-ref distv j) 0.0)
                      (traverse-dist (cdr es))
                      (let ((idist (f64vector-ref distv i)))
                        (f64vector-set! distv j (+ idist dist))
                        (let ((distv1 (traverse-dist ((g 'out-edges) j))))
                          (traverse-dist es)))
                      ))
                ))
          
	 
          ;; determine distances from end (reverse distance)
          (define (traverse-rdist es)
            (if (null? es) rdistv
                (match-let (((i j dist) (car es)))
                  (if (>= (f64vector-ref rdistv i) 0.0)
                      (traverse-rdist (cdr es))
                      (let ((jdist (f64vector-ref distv j)))
                        (f64vector-set! rdistv i (+ jdist dist))
                        (let ((rdistv1 (traverse-rdist ((g 'in-edges) i))))
                          (traverse-rdist es)))
                      ))
                ))


          (define (compute-segv distv rdistv)
            (let recur ((n n))
              (if (>= n 1)
                  (let* ((dist  (f64vector-ref distv n))
                         (rdist (f64vector-ref rdistv n))
                         (len   (and (positive? dist) (positive? rdist) (+ dist rdist)))
                         (delta (and len (round (/ len nseg))))
                         (seg   (and delta (round (/ dist delta)))))
                    (if seg (s32vector-set! segv n (exact->inexact seg)))
                    (recur (- n 1))
                    ))
              ))
          
          (let ((in-edges (g 'in-edges)) 
                (out-edges (g 'out-edges)) 
                (terminals ((g 'terminals)))
                (roots ((g 'roots))))
            (for-each (lambda (x) (f64vector-set! distv x 0.0)) roots)
            (for-each (lambda (x) (s32vector-set! segv x 0)) roots)
            (for-each (lambda (x) (f64vector-set! rdistv x 0.0)) terminals)
            (traverse-dist (concatenate (map (lambda (x) (out-edges x)) roots)))
            (traverse-rdist (concatenate (map (lambda (x) (in-edges x)) terminals)))
            (compute-segv distv rdistv)
            (list distv segv)
          ))


  
        (define (load-swc filename label type nseg)
          
          (let ((in (open-input-file filename)))
            
            (if (not in) (error 'load-swc "file not found" filename))
            
            (let* (
                   (lines
                    (let ((lines (read-lines in)))
                      (close-input-port in)
                      (filter (lambda (line) (not (irregex-match comment-pat line))) 
                              lines)))

                   (swc-data
                    (filter-map
                     (lambda (line) 
                       (let ((lst (map string->number (string-split line " \t"))))
                         (and (not (null? lst)) 
                              (match-let (((id my-type x y z radius pre) lst))
                                         (make-swcpoint id my-type (make-point x y z)
                                                        radius pre)))
                         ))
                     lines))

                   (swc-graph (make-swc-tree-graph swc-data label))

                   (dist+segs  (tree-graph-distances+segments swc-graph nseg))

                   )

              (cons type (cons swc-graph dist+segs)))
          ))



        (define (load-swcdir path label type nseg)
          
          (let ((pat ".*.swc"))

            (let ((flst (find-files path
                                    test: (regexp pat)
                                    action: cons
                                    seed: (list) 
                                    limit: 0)))

              (d "load-swcdir: flst = ~A~%" flst)

              (map (lambda (fn) (load-swc fn label type nseg)) (sort flst string<?))
              ))
          )


        (define (load-matrix-from-lines lines)
          (let ((dimensions-line (car lines)))
            (match-let (((m n) (map string->number (string-split dimensions-line " \t"))))
                       (let ((matrix-lines (take (cdr lines) m))
                             (rest-lines (drop (cdr lines) m)))
                         `(,m ,n
                              ,(map (lambda (line) (map string->number (string-split line " \t"))) matrix-lines)
                              ,rest-lines)))
            ))

          
        (define (load-layer-tree nlayers topology-filename points-filename label)
          
          (let (
                (topology-in (open-input-file topology-filename))
                (points-in (open-input-file points-filename))
                )
            
            (if (not topology-in) (error 'load-layer-tree "topology file not found" topology-filename))
            (if (not points-in) (error 'load-layer-tree "points file not found" points-filename))
            
            (let* (
                   (topology-lines
                    (let ((lines (read-lines topology-in)))
                      (close-input-port topology-in)
                      (filter (lambda (line) (not (irregex-match comment-pat line))) lines)))

                   (points-lines
                    (let ((lines (read-lines points-in)))
                      (close-input-port points-in)
                      (filter (lambda (line) (not (irregex-match comment-pat line))) lines)))

                   (topology-layers
                    (cadr
                     (let ((layer-lines (take topology-lines nlayers)))
                       (fold (match-lambda* 
                              ((line (i lst))
                               (match-let (((nsecs . sec-ids) (map string->number (string-split line " \t"))))
                                          (if (= (length sec-ids) nsecs)
                                              (list (+ 1 i) (cons (cons i sec-ids) lst))
                                              (error 'load-layer-tree "number of sections mismatch in layer description" nsecs sec-ids))
                                          )))
                             '(0 ()) layer-lines))))

                   (topology-sections
                    (let ((rest-lines (drop topology-lines nlayers)))
                      (let ((points-sections-line (car rest-lines)))
                        (match-let (((nsections . point-numbers) (map string->number (string-split points-sections-line " \t"))))
                                   (if (not (= nsections (length point-numbers)))
                                       (error 'load-layer-tree "number of sections mismatch in section description"))
                                   point-numbers))
                      ))

                   (topology-data
                    (let ((rest-lines (drop topology-lines (+ 1 nlayers))))
                      (match-let (((mdend ndend tdend rest-lines) (load-matrix-from-lines rest-lines)))
                                 (if (not (= ndend 2)) 
                                     (error 'load-layer-tree "invalid dendrite topology dimensions" mdend ndend))
                                   (match-let (((msoma nsoma tsoma rest-lines) (load-matrix-from-lines rest-lines)))
                                              (if (not (= nsoma 2)) 
                                                  (error 'load-layer-tree "invalid soma topology dimensions" msoma nsoma))
                                              (list tdend tsoma)
                                              ))
                      ))
            
                   (points-lines 
                    (let ((points-header (map string->number (string-split (car points-lines) " \t"))))
                      (if (not (= (car points-header) (length (cdr points-lines))))
                          (error 'load-layer-tree "number of points mismatch in points matrix" points-header))
                      (cdr points-lines)))

                   (points-data
                    (cadr
                     (fold
                      (match-lambda* ((line (id lst))
                                      (let ((pt (map string->number (string-split line " \t"))))
                                        (match-let (((x y z radius) pt))
                                                   (let ((layer (find-index (lambda (layer) (member id layer)) topology-layers)))
                                                     (list (+ 1 id)
                                                           (cons (make-layer-point id (make-point x y z) radius layer) lst))
                                                     ))
                                        ))
                                     )
                      '(0 ())
                      (cdr points-lines))))


                   (tree-graph (make-layer-tree-graph topology-sections topology-layers topology-data points-data label))

                   )
              
              tree-graph
              
              ))
          )


        (define (segment-projection label source-tree target-sections zone my-comm myrank size)

          (MPI:barrier my-comm)
	  
          (let ((my-results
                 (genpoint-projection label my-comm myrank size target-sections source-tree zone 0 0)))

            (MPI:barrier my-comm)

            (call-with-output-file (sprintf "~Asources~A.dat"  label (if (> size 1) myrank ""))
              (lambda (out-sources)
                (call-with-output-file (sprintf "~Atargets~A.dat"  label (if (> size 1) myrank ""))
                  (lambda (out-targets)
                    (call-with-output-file (sprintf "~Adistances~A.dat"  label (if (> size 1) myrank ""))
                      (lambda (out-distances)
                        (call-with-output-file (sprintf "~Asegments~A.dat"  label (if (> size 1) myrank ""))
                          (lambda (out-segments)
                            (for-each 
                             (lambda (my-data)
                               (let* ((my-entry-len 5)
                                      (my-data-len (/ (f64vector-length my-data) my-entry-len)))
                                 (d "rank ~A: length my-data = ~A~%" myrank my-data-len)
                                 (let recur ((m 0))
                                   (if (< m my-data-len)
                                       (let* (
                                              (my-entry-offset (* m my-entry-len))
                                              (source (inexact->exact (f64vector-ref my-data my-entry-offset)))
                                              (target (inexact->exact (f64vector-ref my-data (+ 1 my-entry-offset))))
                                              (distance (f64vector-ref my-data (+ 2 my-entry-offset)))
                                              (segment (f64vector-ref my-data (+ 3 my-entry-offset)))
                                              (section (f64vector-ref my-data (+ 4 my-entry-offset)))
                                              )
                                         (fprintf out-sources   "~A~%" source)
                                         (fprintf out-targets   "~A~%" target)
                                         (fprintf out-distances "~A~%" distance)
                                         (fprintf out-segments  "~A ~A~%" segment section)
                                         (recur (+ 1 m)))))
                                 ))
                             my-results))
                          ))
                      ))
                  ))
              ))
          )
        

        (define (projection label source-tree target zone my-comm myrank size) 

          (MPI:barrier my-comm)
	  
          (let ((my-results (point-projection label my-comm myrank size target source-tree zone 0 (lambda (x nn) nn))))

          (MPI:barrier my-comm)
            
            (call-with-output-file (sprintf "~Asources~A.dat"  label (if (> size 1) myrank ""))
              (lambda (out-sources)
                (call-with-output-file (sprintf "~Atargets~A.dat"  label (if (> size 1) myrank ""))
                  (lambda (out-targets)
                    (call-with-output-file (sprintf "~Adistances~A.dat"  label (if (> size 1) myrank ""))
                      (lambda (out-distances)
                        (for-each 
                         (lambda (my-data)
                           (let* ((my-entry-len 3)
                                  (my-data-len (/ (f64vector-length my-data) my-entry-len)))
                             (d "~A: rank ~A: length my-data = ~A~%" label myrank my-data-len)
                             (let recur ((m 0))
                               (if (< m my-data-len)
                                   (let ((source (inexact->exact (f64vector-ref my-data (* m my-entry-len))))
                                         (target (inexact->exact (f64vector-ref my-data (+ 1 (* m my-entry-len)))))
                                         (distance (f64vector-ref my-data (+ 2 (* m my-entry-len)))))
                                     (fprintf out-sources "~A~%" source)
                                     (fprintf out-targets "~A~%" target)
                                     (fprintf out-distances "~A~%" distance)
                                     (recur (+ 1 m)))))
                             ))
                         my-results)
                        ))
                    ))
                ))
            ))
        

        (include "calc-parser.scm")

        
        (define (load-config-file filename)
          (let ((in (open-input-file filename)))
            (if (not in) (error 'load-config-file "file not found" filename))
            (init-bindings)
            (let* ((lines (reverse (filter (lambda (x) (not (string-null? x))) (read-lines in))))
                   (properties (filter-map
                                (lambda (line) 
                                  (and (not (string-prefix? "//" line))
                                       (let ((lst (string-split line "=")))
                                         (and (> (length lst) 1)
                                              (let ((key (string->symbol (string-trim-both (car lst) #\space)))
                                                    (val (calc-eval-string (cadr lst))))
                                                (add-binding key val)
                                                (cons key val))))))
                                lines)))
              properties
              ))
          )

        (define (make-output-fname dirname sysname suffix . rest) 
          (let-optionals 
           rest ((x #t))
           (and x
                (let ((dirname (if (string? x) x dirname)))
                  (let ((fname (sprintf "~A~A" sysname suffix)))
                    (or (and dirname (make-pathname dirname fname)) fname)))
                )))

        
)

        

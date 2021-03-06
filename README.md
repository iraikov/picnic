# picnic

A description language for models of geometric neural connectivity.

## Usage

picnic [options...] [input files ...]

## Documentation

The main idea of`Picnic` is to combine experimental data on cell
morphology and synthetic cell geometry.  Cell geometry is described as
sets of 3D points and can be one of the following:

* Neurolucida data: cylinders described by start point, end point, diameter
* Synthetic geometry: points along a line, polynomial curve, or angular displacement

Cell placement can be defined by rectangular grids, regular tilings
(e.g. bricks or hexagons), random point distributions.  Connectivity
currently is simply projections based on Euclidean distances between
cell objects.

### Layers

In `Picnic` terminology, a layer describes the placement of cell
objects in 3D space.  The placement is determined by a set of points,
which can be generated by one of the following methods:

* sampling from typical distributions such as uniform or exponential
* point coordinates loaded from a file
* Regular grid defined by spacing in x, y and z direction
* Regular 2D tiling, such as hexagons or bricks with a given side length. In this case, position x and y coordinates are determined by the center point of each generated tile, and the z coordinate is set to zero.

A layer is defined by a point set described by one of the methods
above, and one or more cell objects that are to be placed at
positions determined by the point set. If there are less cell
objects than there are points in the point set, then the cell
objects are copied until an object is placed at each point.

### Cell objects

A cell object consists of a bounding box and a set of connection
points. The connection points can be loaded from a Neurolucida
file, or can be sampled from the trajectory of a parametric curve.

The set of points that belong to a cell object can be further
divided into compartments, e.g. dendrites and axon, which can be
later used when specifying connectivity.

In addition, random perturbations can be applied to the points of
a cell or one of its compartments.

### Projections

Once layers are defined with the different cell types, connectivity is
specified in `Picnic` as projections between layers.

The single type of projection currently supported by `Picnic` is
based on Euclidean distances between the points of the different cell
object. Given a maximum distance, `Picnic` can determine all cell
points in two layers that are close enough to be considered connected.

### Model description language

The following constructs comprise the model description language: 

 INPUT {ID} | {ID} [AS {LOCAL-ID}] [FROM {NAMESPACE}] ...

Declares one or several imported quantities. If the optional AS
parameter is given, then the quantity is imported as {LOCAL-ID}. If
the optional FROM parameter is given, then the quantity is imported
from namespace {NAMESPACE}.

  OUTPUT {ID}

Declares that an existing quantity be exported.

  CONST {ID} = {EXPR}

Declares a constant quantity (its value will be computed at declaration time).

  FUN {ID} ( {ARG-ID} ... ) {EXPR}

Declares a function (a parameterized expression with no free variables).

  {ID} = {EXPR}

Declares an assigned quantity (an expression that can refer to other quantities in the system).

 PROCESS ( {ID} ) = (GENERATOR {F}) (npts {N})

Declares a process quantity. {F} is the generating function that returns the parametric curves for this process.

  COMPONENT ( TYPE {ID} ) ( NAME {ID} ) {ELEMENTS} )

Declares a system component (a quantity that can contain other quantities).

### Examples

```
 picnic-model 
  GL
       config PFlength
       config PFlengthSlope ;; how much the PF length decreases with depth
                            ;; PFs deeper in the molecular layer tend to be shorter
                            ;; (Pichitpornchai et al, 1994)
       
       config MLdepth
       config PCLdepth
       
       config numAxonGolgi  ;; GoC axonal dimensions
       config GoC_Axon_Xmin
       config GoC_Axon_Xmax
       config GoC_Axon_Ymin
       config GoC_Axon_Ymax
       config GoC_Axon_Zmin
       config GoC_Axon_Zmax
       
       config GoC_nDendML ;; GoC # of apical dendrites
       config GoC_nDendGL ;; GoC # of basolateral dendrites
       
       config GoC_Ad_nseg ;; GoC apical dendrites number of segments
       config GoC_Ad_nsegpts ;; GoC apical dendrites number of points per segment
       
       config GoC_Bd_nseg
       config GoC_Bd_nsegpts
       
       config GoC_PhysApicalDendH
       config GoC_PhysApicalDendR
       config GoC_Atheta_min
       config GoC_Atheta_max
       config GoC_Atheta_stdev

       config GoC_PhysBasolateralDendH
       config GoC_PhysBasolateralDendR
       config GoC_Btheta_min
       config GoC_Btheta_max
       config GoC_Btheta_stdev
       
       config AAtoGoCzone
       config PFtoGoCzone
       config GoCtoGoCzone
       config GoCtoGoCgapzone
       
       config GoCxrange
       config GoCyrange
       
       const xExtent = GoCxrange
       const yExtent = GoCyrange
       
       component (type local-cell-forest) (name GC)
       
       
         component (type layout) (name GCTcoordinates)
                    
                    s = (PointsFromFile ("GCTcoordinates1.dat"))
		    
                    output s

         component (type pointset) (name GC)
                    
                    s = (PointsFromFile ("GCcoordinates.dat"))
		    
                    output s

         component (type pointset) (name GCT)
                    
                    s = (PointsFromFile ("GCTcoordinates.dat"))
		    
                    output s

         component (type section) (name AscendingAxons)
                    
                    fun f (gid origin)
                      let ((dX 0) (dY 0) (dZ (neg (PCLdepth))))
                        LineSegment (origin dX dY dZ)
                    
                    const n = 1
                    
                    p (u) = (generator f) (npts 4)
                    
                    output u n
         
         
        component (type section) (name ParallelFibers)
         
                    component (type perturbation) 
                               
                               fun pf (gid origin init)
                                 let ((period (randomUniform ((PFlength / 50.0) ~ (PFlength / 30.0) ~ init)))
                                      (phase  (randomUniform (0.0 ~ 10.0 ~ init))))
                                   ;; Harmonic (amplitude period phase npts)
                                   Harmonic (0 5.0 period phase 50)
                               
                               const n = 2
                               
                               p (s) = (generator pf) (initial (randomInit (randomSeed ())))
                               
                               output s n
                                                   
                    component (type perturbation) 
                               
                               fun pf (gid origin init)
                                 let ((period (randomUniform ((PFlength / 4.0) ~ (PFlength / 10.0) ~ init)))
                                      (phase  (randomUniform (0.0 ~ 10.0 ~ init))))
                                   ;; Harmonic (amplitude period phase npts)
                                   Harmonic (1 0.5 period phase 50)
                               
                               const n = 2
                               
                               p (s) = (generator pf) (initial (randomInit (randomSeed ())))
                               
                               output s n
                    
                    
                    fun f (gid origin)
                      let ((z (pointCoord (2 origin))) ;; depth of this PF
                           (dX (PFlengthSlope * (z - MLdepth) + (PFlength / 2))) (dY 0) (dZ 0))
                        LineSegment (origin dX dY dZ)
                    
                    fun g (gid origin)
                      let ((z (pointCoord (2 origin))) ;; depth of this PF
                           (dX (PFlengthSlope * (z - MLdepth) + (PFlength / 2))) (dY 0) (dZ 0))
                        LineSegment (origin ~ (neg (dX)) ~ dY ~ dZ)
                    
                    const n = 1
                    
                    ;; process u grows in the positive X direction
                    ;; process v grows in the negative X direction
                    p (u) = (generator f) (sampler (polynomial 0.003 0.0085 0.0085 )) (npts 200)
                    p (v) = (generator g) (sampler (polynomial 0.003 0.0085 0.0085 )) (npts 200)
                    
                    output u n v n

       
       component (type cell-forest) (name GoC)
         component (type layout) (name GolgiCoordinates)
                    s = (PointsFromFile ("GoCcoordinates.dat"))
                    output s
         component (type section) (name BasolateralDendrites)
                    fun f (gid origin init)
                      let (
                           (thetaDeg (randomNormal (GoC_Btheta_min GoC_Btheta_stdev init)))
                           (theta    ((PI / 180) * thetaDeg))
                           (dX (GoC_PhysBasolateralDendR * cos (theta)))
                           (dY (GoC_PhysBasolateralDendR * sin (theta)))
                           (dZ GoC_PhysBasolateralDendH)
                          )
                        LineSegment (origin dX dY dZ)
                    fun g (gid origin init)
                      let (
                           (thetaDeg (randomNormal (GoC_Btheta_max GoC_Btheta_stdev init)))
                           (theta    ((PI / 180) * thetaDeg))
                           (dX (GoC_PhysBasolateralDendR * cos (theta)))
                           (dY (GoC_PhysBasolateralDendR * sin (theta)))
                           (dZ GoC_PhysBasolateralDendH)
                          )
                        LineSegment (origin dX dY dZ)
                    const n = 1
                    segp (u) = (generator f) (initial (randomInit (randomSeed ()))) (nsegs GoC_Bd_nseg) (nsegpts GoC_Bd_nsegpts)
                    segp (v) = (generator g) (initial (randomInit (randomSeed ()))) (nsegs GoC_Bd_nseg) (nsegpts GoC_Bd_nsegpts)
                    output u n v n

         component (type section) (name ApicalDendrites)
                    fun f (gid origin init)
                      let (
                            (thetaDeg (randomNormal (GoC_Atheta_min GoC_Atheta_stdev init)))
                            (theta    ((PI / 180) * thetaDeg))
                            (dX (GoC_PhysApicalDendR * cos (theta)))
                            (dY (GoC_PhysApicalDendR * sin (theta)))
                            (dZ GoC_PhysApicalDendH)
                           )
                        LineSegment (origin dX dY dZ)
                    fun g (gid origin init)
                      let (
                            (thetaDeg (randomNormal (GoC_Atheta_max GoC_Atheta_stdev init)))
                            (theta    ((PI / 180) * thetaDeg))
                            (dX (GoC_PhysApicalDendR * cos (theta)))
                            (dY (GoC_PhysApicalDendR * sin (theta)))
                            (dZ GoC_PhysApicalDendH)
                           )
                        LineSegment (origin dX dY dZ)
                    const n = 1
                    segp (u) = (generator f) (initial (randomInit (randomSeed ()))) (nsegs GoC_Ad_nseg) (nsegpts GoC_Ad_nsegpts)
                    segp (v) = (generator g) (initial (randomInit (randomSeed ()))) (nsegs GoC_Ad_nseg) (nsegpts GoC_Ad_nsegpts)
                    output u n v n

         component (type section) (name Axons)
                    const n = numAxonGolgi
                    fun f (gid origin init)
                      let (
                           (dX (randomUniform (GoC_Axon_Xmin GoC_Axon_Xmax init)))
                           (dY (randomUniform (GoC_Axon_Ymin GoC_Axon_Ymax init)))
                           (dZ (randomUniform (GoC_Axon_Zmin GoC_Axon_Zmax init)))
                          )
                        LineSegment (origin dX dY dZ)
                    p (u) = (generator f) (initial (randomInit (randomSeed ())))
                    output u n
       
       component (type projection) 
            
            input (GC from cell-forests) (GoC from cell-forests)
            
            r = PFtoGoCzone
            
            set source = (section GC ParallelFibers)
            set target = (section GoC ApicalDendrites)
             
            PFtoGoC = (SegmentProjection (r source target))
            
            output PFtoGoC
            
       component (type projection) 
            
            input (GC from cell-forests) (GoC from cell-forests)
            
            r = AAtoGoCzone
             
            set source = (section GC AscendingAxons)
            set target = 
                         union
                           section GoC ApicalDendrites
                           section GoC BasolateralDendrites
            
            AAtoGoC = (SegmentProjection (r source target))
            
            output AAtoGoC
            
       component (type projection) 
            
            input (GoC from cell-forests)
            
            r = GoCtoGoCzone
            
            set source = (section GoC Axons)
            set target = (population GoC)
            
            GoCtoGoC = (Projection (r source target))
             
            output GoCtoGoC

       component (type projection) 
            
            input (GoC from cell-forests)
            
            r = GoCtoGoCgapzone
             
            set source = (population GoC)
            set target = (population GoC)
            
            GoCtoGoCgap = (Projection (r source target))
            
            output GoCtoGoCgap
```


## Version history


1.0 : Initial release


## Requirements


* [mpi](http://wiki.call-cc.org/eggref/4/mpi)
* [kd-tree](http://wiki.call-cc.org/eggref/4/kd-tree)


## License

>
> Copyright 2012-2015 Ivan Raikov.
> 
> This program is free software: you can redistribute it and/or modify
> it under the terms of the GNU General Public License as published by
> the Free Software Foundation, either version 3 of the License, or (at
> your option) any later version.
> 
> This program is distributed in the hope that it will be useful, but
> WITHOUT ANY WARRANTY; without even the implied warranty of
> MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
> General Public License for more details.
> 
>  A full copy of the GPL license can be found at
>  <http://www.gnu.org/licenses/>.
>


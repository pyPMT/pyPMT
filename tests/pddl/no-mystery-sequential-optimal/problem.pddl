(define (problem transport-l4-t1-p3-simplified)
 (:domain transport-strips)

 (:objects
  l0 l1 l2 l3 - location
  t0 - truck
  p0 p1 p2 - package
  level0 level1 level2 - fuellevel
 )

 (:init
  (sum level0 level0 level0)
  (sum level0 level1 level1)
  (sum level0 level2 level2)
  (sum level1 level0 level1)
  (sum level1 level1 level2)
  (sum level2 level0 level2)

  (connected l0 l1)
  (fuelcost level1 l0 l1)
  (connected l0 l2)
  (fuelcost level1 l0 l2)
  (connected l0 l3)
  (fuelcost level2 l0 l3)
  (connected l1 l0)
  (fuelcost level1 l1 l0)
  (connected l1 l2)
  (fuelcost level1 l1 l2)
  (connected l1 l3)
  (fuelcost level2 l1 l3)
  (connected l2 l0)
    (fuelcost level1 l2 l0)
    (connected l2 l1)
    (fuelcost level1 l2 l1)
    (connected l2 l3)
    (fuelcost level1 l2 l3)
    (connected l3 l0)
    (fuelcost level2 l3 l0)
    (connected l3 l1)
    (fuelcost level2 l3 l1)
    (connected l3 l2)
(fuelcost level1 l3 l2)

    (at t0 l2)
    (fuel t0 level2)
(= (total-cost) 0)

    (at p0 l0)
    (at p1 l1)
(at p2 l3)
    )

    (:goal
     (and
      (at p0 l1)
      (at p1 l0)
      (at p2 l0)
     )
    )
(:metric minimize (total-cost)))

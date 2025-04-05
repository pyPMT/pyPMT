(define (problem minimal-cave-diving)
  (:domain cave-diving-adl)
  (:objects
    entrance cave-loc - location
    diver1 - diver
    tank1 tank2 dummy-tank - tank
    zero one two - quantity
  )

  (:init
    ;; Diver availability
    (available diver1)
    (capacity diver1 two)
    
    ;; Tank sequence
    (in-storage tank1)
    (next-tank tank1 tank2)
    (next-tank tank2 dummy-tank)
    
    ;; Cave structure
    (cave-entrance entrance)
    (connected entrance cave-loc)
    (connected cave-loc entrance)
    
    ;; Quantity progression
    (next-quantity zero one)
    (next-quantity one two)
    
    ;; Costs
    (= (hiring-cost diver1) 10)
    (= (other-cost) 1)
    (= (total-cost) 0)
  )

  (:goal
    (and
      (have-photo cave-loc)
      (decompressing diver1)
    )
  )

  (:metric minimize (total-cost))
)
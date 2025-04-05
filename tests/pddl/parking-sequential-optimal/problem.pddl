(define (problem mini-parking)
  (:domain parking)
  (:objects
     car_0 car_1 car_2 - car
     curb_0 curb_1 - curb
  )
  (:init
    (= (total-cost) 0)
    
    ;; Initial configuration
    ;; curb_0: car_0 car_1
    ;; curb_1: car_2
    
    (at-curb car_0)
    (at-curb-num car_0 curb_0)
    (behind-car car_1 car_0)
    (car-clear car_1)
    
    (at-curb car_2)
    (at-curb-num car_2 curb_1)
    (car-clear car_2)
  )
  (:goal
    (and
      ;; Goal configuration
      ;; curb_0: car_2 car_1
      ;; curb_1: car_0
      
      (at-curb-num car_2 curb_0)
      (behind-car car_1 car_2)
      (at-curb-num car_0 curb_1)
    )
  )
  (:metric minimize (total-cost))
)
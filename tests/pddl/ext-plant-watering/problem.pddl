(define (problem instance_4_1)
  (:domain ext-plant-watering)
  (:objects
    tap1 - tap
	agent1 - agent
	plant1 plant2 plant3 plant4 - plant
  )

  (:init
	(= (maxx) 4)
	(= (minx) 1)
	(= (maxy) 4)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 25) ; only 22 out of 25 needed

    (= (x tap1) 3)
	(= (y tap1) 3)
	
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (poured plant4) 0)

	(= (x agent1) 3)
	(= (y agent1) 1)
	(= (carrying agent1) 0)
    (= (max_carry agent1) 5)

    (= (x plant2) 2)
	(= (y plant2) 2)
	
    (= (x plant3) 1)
	(= (y plant3) 1)
	
    (= (x plant4) 1)
	(= (y plant4) 1)
	
    (= (x plant1) 2)
	(= (y plant1) 2)
  )

  (:goal (and 
    (= (poured plant1) 4)
	(= (poured plant2) 2)
	(= (poured plant3) 7)
	(= (poured plant4) 9)
    ; makes sure all agents end empty
	(= (total_poured) (total_loaded)) 
  ))
)

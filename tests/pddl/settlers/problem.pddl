(define (problem simplified-settlers)
(:domain civ)
(:objects
	location0 - place
	location1 - place
	location2 - place
	vehicle0 - vehicle
)
(:init
	(= (resource-use) 0)
	(= (labour) 0)
	(= (pollution) 0)
	
	;; Location0 properties
	(mountain location0)
	(woodland location0)
	(= (housing location0) 0)
	(= (available wood location0) 0)
	(= (available timber location0) 0)
	(= (available ore location0) 0)
	(= (available stone location0) 0)
	(= (available iron location0) 0)
	(= (available coal location0) 0)
	(= (carts-at location0) 0)
	
	;; Location1 properties
	(woodland location1)
	(metalliferous location1)
	(= (housing location1) 0)
	(= (available wood location1) 0)
	(= (available timber location1) 0)
	(= (available ore location1) 0)
	(= (available stone location1) 0)
	(= (available iron location1) 0)
	(= (available coal location1) 0)
	(= (carts-at location1) 0)
	
	;; Location2 properties
	(woodland location2)
	(= (housing location2) 0)
	(= (available wood location2) 0)
	(= (available timber location2) 0)
	(= (available ore location2) 0)
	(= (available stone location2) 0)
	(= (available iron location2) 0)
	(= (available coal location2) 0)
	(= (carts-at location2) 0)
	
	;; Connections between locations
	(connected-by-land location0 location1)
	(connected-by-land location1 location0)
	(connected-by-land location1 location2)
	(connected-by-land location2 location1)
	
	;; Vehicle properties
	(potential vehicle0)
)

(:goal (and
	(>= (housing location0) 1)
	(has-coal-stack location0)
	(connected-by-rail location1 location2)
	)
)

(:metric minimize (+ (* 0 (pollution)) (* 2 (labour))))
)
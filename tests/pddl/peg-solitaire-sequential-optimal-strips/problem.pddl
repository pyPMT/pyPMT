(define (problem pegsolitaire-simple)
    (:domain pegsolitaire-sequential)
    (:objects
        pos-0-0 - location
        pos-0-1 - location
        pos-0-2 - location
        pos-1-0 - location
        pos-1-1 - location
        pos-1-2 - location
        pos-2-0 - location
        pos-2-1 - location
        pos-2-2 - location
    )
    (:init
        (= (total-cost) 0)
        (move-ended)
        
        ;; Define all possible in-line movements (horizontal and vertical)
        (IN-LINE pos-0-0 pos-0-1 pos-0-2)
        (IN-LINE pos-0-2 pos-0-1 pos-0-0)
        (IN-LINE pos-1-0 pos-1-1 pos-1-2)
        (IN-LINE pos-1-2 pos-1-1 pos-1-0)
        (IN-LINE pos-2-0 pos-2-1 pos-2-2)
        (IN-LINE pos-2-2 pos-2-1 pos-2-0)
        
        (IN-LINE pos-0-0 pos-1-0 pos-2-0)
        (IN-LINE pos-2-0 pos-1-0 pos-0-0)
        (IN-LINE pos-0-1 pos-1-1 pos-2-1)
        (IN-LINE pos-2-1 pos-1-1 pos-0-1)
        (IN-LINE pos-0-2 pos-1-2 pos-2-2)
        (IN-LINE pos-2-2 pos-1-2 pos-0-2)
        
        ;; Initial state: 4 pegs and the center is empty
        (occupied pos-0-0)
        (occupied pos-0-2)
        (occupied pos-2-0)
        (occupied pos-2-2)
        
        (free pos-0-1)
        (free pos-1-0)
        (free pos-1-1)
        (free pos-1-2)
        (free pos-2-1)
    )
    (:goal (and
        ;; Goal: Only one peg remains at the center
        (free pos-0-0)
        (free pos-0-1)
        (free pos-0-2)
        (free pos-1-0)
        (occupied pos-1-1)
        (free pos-1-2)
        (free pos-2-0)
        (free pos-2-1)
        (free pos-2-2)
    ))
    (:metric minimize (total-cost))
)
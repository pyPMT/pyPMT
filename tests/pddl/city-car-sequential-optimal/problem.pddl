(define (problem simple-citycar)
    (:domain citycar)
    (:objects
        junction0-0 junction0-1 - junction
        car0 - car
        garage0 - garage
        road0 road1 - road
    )
    (:init
        (same_line junction0-0 junction0-1)
        (same_line junction0-1 junction0-0)
        (diagonal junction0-0 junction0-1)
        (diagonal junction0-1 junction0-0)
        (clear junction0-0)
        (clear junction0-1)
        (at_garage garage0 junction0-0)
        (starting car0 garage0)
        (= (total-cost) 0)
    )
    (:goal
        (and
            (arrived car0 junction0-1)
        )
    )
    (:metric minimize
        (total-cost)
    )
)
(define (domain socks-and-shoes)
 (:requirements :strips :typing :negative-preconditions)
 (:types side - thing)

 (:predicates
  (sock ?x - side)
  (shoe ?x - side)
  )

 (:action put_shoe
  :parameters (?x - side)
  :precondition (sock ?x)
  :effect  (shoe ?x))

 (:action put_sock
  :parameters (?x - side)
  :precondition ()
  :effect (sock ?x))

)
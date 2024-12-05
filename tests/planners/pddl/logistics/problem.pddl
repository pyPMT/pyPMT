(define (problem logistics-4-0)
(:domain logistics)
(:objects
 apn1 - airplane
 apt1 apt2 - airport
 pos2 pos1 - location
 cit2 cit1 - city
 tru2 tru1 - truck
 obj23 obj22 obj21 obj13 obj12 obj11 - package)

(:init 
 (at apn1 apt2)       ; airplane1 at airport2
 (at tru1 pos1)       ; truck1 at position1
 (at obj11 pos1)      ; obj11 at position1
 (at obj12 pos1)      ; obj12 at position1
 (at obj13 pos1)      ; obj13 at position1
 (at tru2 pos2)       ; truck2 at position2
 (at obj21 pos2)      ; obj21 at position2
 (at obj22 pos2)      ; obj22 at position2
 (in-city pos1 cit1)  ; position1 in city1
 (in-city apt1 cit1)  ; airport1 in city1
 (in-city pos2 cit2)  ; position2 in city2
 (in-city apt2 cit2)) ; airport2 in city2

(:goal (and (at obj11 apt1)   ; obj11 at airport1
            (at obj13 apt1)   ; obj13 at airport1
            (at obj21 pos1))) ; obj21 at position1
)
;; Absolute Minimal Pipesworld problem
(define (problem tiniest-pipes)
  (:domain pipesworld_strips)
  (:objects
    ;; Just 1 batch-atom
    B1 - batch-atom
    
    ;; Just 2 areas
    A1 A2 - area
    
    ;; Just 1 unitary pipe
    S12 - pipe
    
    ;; Only 1 product with 1 tank slot per area
    TA1-lco - tank-slot
    TA2-lco - tank-slot
  )
  
  (:init
    ;; Pipeline is in normal state
    (normal S12)
    
    ;; Interface restrictions (only same product)
    (may-interface lco lco)
    
    ;; Simple network topology - just one connection
    (connect A1 A2 S12)
    
    ;; Tank slot locations
    (tank-slot-product-location TA1-lco lco A1)
    (tank-slot-product-location TA2-lco lco A2)
    
    ;; Batch-atom product
    (is-product B1 lco)
    
    ;; Initial location - B1 in the pipe
    (first B1 S12)
    (last B1 S12)
    
    ;; All tank slots are empty
    (not-occupied TA1-lco)
    (not-occupied TA2-lco)
    
    ;; Unitary pipeline
    (unitary S12)
  )
  
  (:goal (and
    ;; We want batch B1 to be in area A1
    (on B1 A1)
    ;; Pipeline should be in normal state
    (normal S12)
  ))
)
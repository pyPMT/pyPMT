(define (problem mprime-x-12)
   (:domain mystery-prime-typed)
   (:objects broccoli turkey lettuce kale hotdog pork wurst arugula
             - food
             excitement intoxication love rest - pleasure
             abrasion grief anger - pain
)
   (:init
(eats lettuce arugula)
(= (locale wurst) 6)

(= (locale pork) 1)
(= (locale lettuce) 4)
          (eats hotdog kale)

          (craves abrasion hotdog)
          (eats wurst broccoli)
(= (harmony rest) 1)

          (craves excitement broccoli)
(= (harmony intoxication) 1)
          (eats broccoli wurst)
          (eats arugula wurst)
          (eats turkey broccoli)
          (craves love hotdog)
          (eats pork wurst)

          (eats hotdog lettuce)
          (craves anger arugula)
          (eats kale pork)
          (eats lettuce wurst)
(= (harmony love) 1)
          (craves grief hotdog)
          (craves rest arugula)
(= (locale broccoli) 2)
          (eats lettuce hotdog)
(= (locale turkey) 3)
          (eats kale hotdog)
(= (locale kale) 1)
          (craves intoxication lettuce)

          (eats wurst lettuce)
          (eats broccoli turkey)
          (eats pork kale)
          (eats wurst arugula)

(= (harmony excitement) 2)

          (eats turkey hotdog)
          (eats arugula lettuce)
(= (locale hotdog) 1)
(= (locale arugula) 0)
          (eats wurst pork)
          (eats hotdog turkey)
)
   (:goal (and (craves anger kale))))

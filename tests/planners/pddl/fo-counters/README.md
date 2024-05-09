# FO-Counters

Presented in: Li, D., Scala, E., Haslum, P., & Bogomolov, S. (2018, January). Effect-Abstraction Based Relaxation for Linear Numeric Planning. In IJCAI (pp. 4787-4793).

This domain extends the counters domain [Frances and Geffner, 2015]. Like in the original formulation, there are N numeric variables, X1, X2, ..., XN , each of which can be increased or decreased by a variable delta, ∆X1, ∆X2, ..., ∆XN , which in turn can be changed by constant steps in the range from 0 to a constant maximum. The goal is to set the values of the counters in ascending order. Instances are split in three groups, with the initial values all 0, ordered inversely to the goal, or randomly chosen (three for each size). Instances scale on the number of counters.

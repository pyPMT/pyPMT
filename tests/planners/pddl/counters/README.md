# Counters

Presented in: Frances, Guillem, and Hector Geffner. "Modeling and computation in planning: Better heuristics from more expressive languages." Proceedings of the International Conference on Automated Planning and Scheduling. Vol. 25. 2015.


A simple planning problem with a set of integer variables $X_1, \dots, X_n$. Actions allow us to increase or decrease by one the value of any variable within the $[0, n]$ interval. Initially, all variables have value 0, and the goal is to achieve the inequalities $X_i \lt X_{i+1}$, for $i \in [0, n − 1]$. It is an interesting problem due to the fact that, given the natural encoding, the initial state of the problem has an $h_{max}$ heuristic value of 1 and an $h_{FF}$ value of $n − 1$, whereas actually the shortest plan for the problem has $1 + 2 + \dots + n − 1 = n(n − 1)/2$ steps. 

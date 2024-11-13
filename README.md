Brach price and cut algorithm for the Vehicle routing problem (VRP)
The code requires CPLEX.

General Branch and cut and price algorithm for the vehicle routing problem with time windows. The model for the VRP is th set partitioning formulation that is derived from the Dantzig-Wolfe decomposition of the network flow formulation of the VRP. The master problem considered all the feasible routes that vehicles can take to fulfilll delivery tasks. The pricing problems consist of finding routes that have a negative reduced cost in the master problem. The pricing subproblems are solved with state of the art dynamic programming algorithms called labeling algorithms.

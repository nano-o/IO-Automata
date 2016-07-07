# IO-Automata
Formalisation of basic I/O automata theory in Isabelle/HOL.
Allows proving that an I/O automaton implements another using a simulation relation, and augmenting an I/O-automaton with history variables.

IOA.thy formalizes IO-Automata, their executions and traces.
Simulations.thy formalizes and proves the soundness theorems for refinement mappings, forward simulations, and backward simulations.

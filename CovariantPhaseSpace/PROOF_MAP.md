# Covariant phase-space Lean verification: proof map

This directory formalizes only claims that are algebraic after their
hypotheses have been stated. It does not claim to formalize PDE existence,
gauge fixing, global quotient regularity, or functional-analytic range
theorems.

| Work-note block | Lean declaration | Formalization boundary |
|---|---|---|
| D2 | `CovariantPhaseSpace.constraint_kernel_eq_generator_range` | Proves both inclusions from flat injectivity, first-class tangency, the Hamiltonian-generator identity, and annihilator completeness. The annihilator-completeness hypothesis is not derived here. |

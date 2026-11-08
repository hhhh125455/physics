# Covariant phase-space proof map

This map is a syntactic traceability index between the work-note blocks and
the Lean declarations. Passing this check confirms that the named declarations
exist; it does not establish that the hypotheses have been verified in a
specific field theory.

| Block | Lean declarations | What is actually formalized |
|---|---|---|
| D1 | Not formalized | Conservation of the covariant symplectic current and the time-cutoff argument are geometric/analytic inputs. |
| D2 | `constraint_kernel_eq` | Abstract algebraic kernel theorem. The annihilator-completeness condition is an explicit hypothesis over the algebraic dual, not a theorem about the continuous dual. |
| D3A | `higherOrderMomentum_recursion`, `iterated_integration_by_parts`, `finite_order_variation_identity`, `higherOrderEuler_eq_F0_sub_D_momentum` | Finite-order momentum recursion, repeated integration by parts, summed first-variation identity, and the identity E = F_0 - D p_0. The spatial integration-by-parts step and the realization of D as a spacetime differential operator remain outside Lean. |
| D3B | `reverse_kernel_inclusion`, `full_kernel_eq_from_bridge` | Abstract bridge from constraint-kernel directions to solution-space gauge directions, conditional on pullback compatibility, surjectivity, CP, and PU. |
| D4 | `pairing_independent_of_lifts`, `quotient_pairing_nondegenerate`, `quotient_pairing_unique`, `cartan_invariance_of_horizontal_closed_form`, `closedness_descends` | Algebraic consequences for quotient pairings and descent. Smooth quotient existence and the geometric Cartan formula are assumptions, not Lean results. |
| D5 | `sphere_scalar_curvature_injective`, `two_sphere_scalar_curvature_injective`, `invariant_observable_excludes_gauge` | Injectivity of the displayed scalar-curvature functions and the abstract invariant-observable separation argument. The metric-curvature calculation and naturality under diffeomorphisms are checked separately. |

## Global proof boundary

The Lean development does **not** formalize the infinite-dimensional
Fréchet-manifold/PDE hypotheses, the ADM tensor-calculus identities, Stokes'
theorem on the spacetime field bundle, parameterized Cauchy uniqueness,
or the existence and regularity of the quotient by spacetime
diffeomorphisms.

For compact-Cauchy vacuum GR, backgrounds with Killing fields require
separate treatment: linearization stability can fail and the solution space
can have conical singularities. The regular-manifold argument must therefore
be restricted to a suitable regular stratum (for example, under the standard
compact-Cauchy hypotheses, a background with no Killing fields), or replaced
by a singular/stratified reduction.

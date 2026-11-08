# Covariant phase-space proof map

This map is a syntactic traceability index between the work-note blocks and
the Lean declarations. Passing this check confirms that the named declarations
exist; it does not establish that the hypotheses have been verified in a
specific field theory.

| Block | Lean declarations | What is actually formalized |
|---|---|---|
| D1 | Not formalized | Conservation of the covariant symplectic current and the time-cutoff argument are geometric/analytic inputs. |
| D2 | `constraint_kernel_eq`, `linearFunctional_factors_through_surjective`, `constraint_kernel_eq_of_surjective` | `constraint_kernel_eq` assumes annihilator factorization; `linearFunctional_factors_through_surjective` and `constraint_kernel_eq_of_surjective` derive it algebraically from a surjective constraint map, with multipliers in the dual of the constraint-value space. To match the work-note notation \(D\chi:V\to\Lambda^*\) and multipliers \(\lambda\in\Lambda\), one still needs the reflexive/Riesz identification \(\Lambda\simeq\Lambda^{**}\). The original constraint_kernel_eq hypothesis is stated over the algebraic dual; the continuous dual version and its Sobolev closed-range hypotheses are not formalized. |
| D3A | `higherOrderMomentum_recursion`, `iterated_integration_by_parts`, `finite_order_variation_identity`, `higherOrderEuler_eq_F0_sub_D_momentum`, `totalBoundary_eq_endpointMomentum_pairing` | Finite-order momentum recursion, repeated integration by parts, summed first-variation identity, and the identity E = F_0 - D p_0. The direct m-indexed endpointMomentum coefficient is now proved to satisfy totalBoundary = sum_j p_j D^j(q). The reversed-index vector-valued momentum formula and its recursion are also proved; their explicit reindexing equivalence is not separately formalized. The spatial integration-by-parts step and the realization of D as a spacetime differential operator remain outside Lean. The general higher-order momentum recursion and canonical/covariant symplectic equivalence are independently derived in Margalef-Bentabol--Villaseñor, arXiv:2204.06383, Sec. VI; the precise notation map remains to be written. |
| D3B | `reverse_kernel_inclusion`, `full_kernel_eq_from_bridge` | Abstract bridge from constraint-kernel directions to solution-space gauge directions, conditional on pullback compatibility, surjectivity, CP, and PU. The covariant/canonical symplectic-form equivalence is established in Margalef-Bentabol--Villaseñor (arXiv:2204.06383), subject to their good-variational-principle and boundary hypotheses; the exact GR normalization still needs specialization. |
| D4 | `pairing_independent_of_lifts`, `quotient_pairing_nondegenerate`, `quotient_pairing_unique`, `cartan_invariance_of_horizontal_closed_form`, `closedness_descends` | Algebraic consequences for quotient pairings and descent. Smooth quotient existence and the geometric Cartan formula are assumptions, not Lean results. |
| D5 | `sphere_scalar_curvature_injective`, `two_sphere_scalar_curvature_injective`, `invariant_observable_excludes_gauge` | Injectivity of the displayed scalar-curvature functions and the abstract invariant-observable separation argument. The metric-curvature calculation and naturality under diffeomorphisms are checked separately. |

## Global proof boundary

For a specifically four-dimensional GR presentation, use
\(M=\mathbb R\times S^3\) and
\(g_a=-dt^2+a^2h_{S^3}\). An independent exact symbolic curvature
calculation gives \(R[g_a]=6/a^2\) and
\(\partial_aR[g_a]=-12/a^3\). The Lean theorem checks injectivity of
\(a\mapsto6/a^2\) for \(a>0\); it does not formalize the tensor-curvature
calculation or the naturality identity
\(\delta_\xi R=\mathcal L_\xi R\). The work note's original
\(\mathbb R\times S^2\) example is a valid 2+1-dimensional counterexample,
but the \(S^3\) version is preferable when explaining the point in 3+1 GR.

The Lean development does **not** formalize the infinite-dimensional
Fréchet-manifold/PDE hypotheses, the ADM tensor-calculus identities, Stokes'
theorem on the spacetime field bundle, parameterized Cauchy uniqueness,
or the existence and regularity of the quotient by spacetime
diffeomorphisms.

For spatially compact, globally hyperbolic vacuum GR, the classical
Isenberg--Marsden slice theorem uses a constant-mean-curvature (CMC) foliation
and yields a stratified solution space whose regular strata are symplectic.
Backgrounds with spacetime symmetries (Killing fields) can produce conical
singularities; the ordinary smooth-manifold argument must not be applied
there. The GR specialization should therefore either restrict to a suitable
regular stratum (with no Killing initial data under the relevant compact-Cauchy
regularity hypotheses) or use singular/stratified reduction.

Do not infer H5 from Ebin's Riemannian slice theorem: the diffeomorphism action
on the full space of Lorentzian metrics need not be proper. The relevant
reference is the slice theorem on the *solution space* of Einstein's equations
by Isenberg--Marsden, not a generic theorem on all Lorentzian metrics.

## Literature anchors

- Lee--Wald / Iyer--Wald: covariant symplectic potential and current.
- Harlow--Wu: boundary-aware covariant phase space and symplectic reduction.
- Arms--Marsden--Moncrief: linearization stability and conical singularities at
  symmetric compact-Cauchy vacuum solutions.
- Isenberg--Marsden: spacetime-diffeomorphism slice theorem for spatially
  compact globally hyperbolic Einstein solutions with CMC foliations.
- Choquet-Bruhat--Geroch: uniqueness of maximal globally hyperbolic
  developments up to data-fixing isometry.
- Mounoud: nonproperness phenomena for diffeomorphism actions on spaces of
  Lorentzian metrics.

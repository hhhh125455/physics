# Covariant phase-space proof map

This map is a syntactic traceability index between the work-note blocks and
the Lean declarations. Passing this check confirms that the named declarations
exist; it does not establish that the hypotheses have been verified in a
specific field theory.

| Block | Lean declarations | What is actually formalized |
|---|---|---|
| D1 | Not formalized | Conservation of the covariant symplectic current and the time-cutoff argument are geometric/analytic inputs. |
| D2 | `constraint_kernel_eq`, `linearFunctional_factors_through_surjective`, `constraint_kernel_eq_of_surjective` | `constraint_kernel_eq` assumes annihilator factorization; `linearFunctional_factors_through_surjective` and `constraint_kernel_eq_of_surjective` derive it algebraically from a surjective constraint map, with multipliers in the dual of the constraint-value space. To match the work-note notation \(D\chi:V\to\Lambda^*\) and multipliers \(\lambda\in\Lambda\), one still needs the reflexive/Riesz identification \(\Lambda\simeq\Lambda^{**}\). The original constraint_kernel_eq hypothesis is stated over the algebraic dual. For a bounded surjective map between Banach spaces, the open mapping theorem supplies the corresponding continuous-dual factorization; the required Sobolev closed-range/surjectivity analysis and open mapping step are not formalized in Lean. The algebraic-dual theorem and the continuous dual theorem therefore remain distinct verification layers. |
| D3A | `higherOrderMomentum_recursion`, `higherOrderMomentum_eq_forward`, `iterated_integration_by_parts`, `finite_order_variation_identity`, `higherOrderEuler_eq_F0_sub_D_momentum`, `totalBoundary_eq_endpointMomentum_pairing` | Finite-order momentum recursion, repeated integration by parts, summed first-variation identity, and E = F_0 - D p_0. The direct m-indexed endpointMomentum coefficient is proved to satisfy totalBoundary = sum_j p_j D^j(q). The forward derivative-order and reverse-indexed vector momentum formulas are now explicitly proved equivalent by finite-sum reflection. Spatial integration by parts and the realization of D as a spacetime differential operator remain outside Lean. Margalef-Bentabol--Villaseñor, arXiv:2204.06383, Sec. VI, independently discusses the higher-order canonical momenta and covariant/canonical symplectic equivalence; the detailed notation map remains to be written. |
| D3B | `reverse_kernel_inclusion`, `full_kernel_eq_from_bridge` | Abstract bridge conditional on pullback compatibility, surjectivity, CP, and **tangent-level** PU: `ker Dr` is assumed to lie in `im R`. Lean assumes this tangent inclusion directly; it does not derive it from nonlinear H4. For vacuum GR, Petersen (arXiv:1802.06028), Theorem 4.7, proves exactly this tangent-level statement by linearized Cauchy uniqueness, so nonlinear H4 is stronger than needed for D3B. The covariant/canonical symplectic-form equivalence is established in Margalef-Bentabol--Villaseñor (arXiv:2204.06383), subject to their hypotheses; the exact GR normalization still needs specialization. |
| D4 | `pairing_independent_of_lifts`, `quotient_pairing_nondegenerate`, `quotient_pairing_unique`, `cartan_invariance_of_horizontal_closed_form`, `closedness_descends` | Algebraic consequences for quotient pairings and descent. Smooth quotient existence and the geometric Cartan formula are assumptions, not Lean results. |
| D5 | `sphere_scalar_curvature_injective`, `two_sphere_scalar_curvature_injective`, `invariant_observable_excludes_gauge` | Injectivity of the displayed scalar-curvature functions and the abstract invariant-observable separation argument. The metric-curvature calculation and naturality under diffeomorphisms are checked separately. |

## Literature overlap and novelty risk

Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*
(arXiv:1402.1282, 2014), is a close prior result. In Def. 3.4, global
parametrizability means nondegeneracy of a pairing between two vertical
cohomologies associated with the constrained hyperbolic system. In Def. 3.6,
global recognizability means nondegeneracy of a pairing between cohomologies
associated with the gauge complex. These are not literally the same as H1's
ADM annihilator factorization or H4's nonlinear parameterized same-data
uniqueness; they are cohomological, linearized hypotheses. Under them,
Lemma 3.17 proves nondegeneracy of the formal pairing on gauge-invariant
solution tangent/cotangent spaces, and Corollary 3.39 descends the formal
presymplectic form to the formal gauge quotient. This overlaps substantially
with the purpose of D2--D4.

The present route is organized differently: it uses the Cauchy-data map,
canonical constraint surface, ADM constraint generators, and a smooth
solution-space quotient. That difference is not by itself enough to establish
novelty. A paper must compare the H1--H5 conditions explicitly with
Khavkine's hypotheses, identify which condition is weaker/stronger or easier
to verify, and prove a genuinely new GR or higher-derivative application.
The general covariant/canonical equivalence of symplectic forms is also already
addressed by Margalef-Bentabol--Villaseñor (arXiv:2204.06383).

Petersen, *On the Cauchy problem for the linearised Einstein equation*
(arXiv:1802.06028, 2018), is another close prior result for the GR
specialization. Theorem 4.7 proves that a linearized vacuum Einstein solution
with zero induced first and second fundamental-form variations is pure gauge;
Lemma 4.13 identifies gauge-producing initial-data variations with induced
spacetime gauge variations; Theorem 4.18 proves the quotient-level linearized
Cauchy map is an isomorphism of locally convex topological vector spaces.
Thus tangent-level PU and CP are already established in vacuum GR, and the
linearized quotient Cauchy map is already well-posed. The remaining possible
contribution is the nonlinear symplectic reduction/local-product theorem and
its relation to Khavkine's cohomological criterion, not the linearized Cauchy
uniqueness statement itself.


A useful first-pass correspondence is:

| This note | Khavkine 2014 | Difference that must be demonstrated |
|---|---|---|
| H1: annihilator/conormal completeness | Global parametrizability of constraints (Def. 3.4) | Analogy only: the note uses a Cauchy/ADM annihilator identity; Khavkine uses nondegeneracy of a pairing between vertical cohomologies of the constrained hyperbolic system. |
| H2/H3: Cauchy map and constraint generators | Hyperbolizability plus the constraint complex | The note requires an actual local Cauchy-data map and identifies its constraint generators with spacetime diffeomorphisms. |
| H4: same-data solution curves are gauge | Global recognizability of gauge transformations (Def. 3.6) | Analogy only: H4 is nonlinear and parameterized; Khavkine's condition is nondegeneracy of a linearized gauge-cohomology pairing, not the same-data uniqueness statement. |
| D2--D4: kernel equality and descent | Lemma 3.17 and Corollary 3.39 | The note aims at a smooth geometric quotient under H5; Khavkine constructs formal tangent/cotangent quotients and a formal reduced symplectic structure. |
| H5: smooth quotient/local slices | Not the same as the cohomological nondegeneracy conditions | A smooth finite-regularity quotient, including stabilizers and strata, is an additional global geometric result. |

Khavkine's Lemma 3.17 proves nondegeneracy of the pairing on gauge-invariant
solution tangent/cotangent spaces under global parametrizability and
recognizability; Corollary 3.39 then descends the presymplectic form. This is
too close to ignore. The strongest defensible positioning for the present
work would be: a nonlinear Cauchy/ADM symplectic-reduction theorem that
combines the known linearized Cauchy result of Petersen with a precise
constraint-annihilator criterion and a smooth quotient/slice construction,
and that proves a concrete result not already covered by Khavkine or
Isenberg--Marsden. That claim is not established until the H1--H5 comparison
and a nontrivial GR application are completed.


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
theorem on the spacetime field bundle, or the existence and regularity of the
quotient by spacetime diffeomorphisms. In D3B, the Lean hypothesis `hPU` is
the tangent-level inclusion `ker Dr ⊆ im R`; the nonlinear H4 statement and
the differentiation of a parameterized diffeomorphism family that would
imply `hPU` remain outside Lean.

For spatially compact, globally hyperbolic vacuum GR, the classical
Isenberg--Marsden slice theorem uses a constant-mean-curvature (CMC) foliation
and yields a stratified solution space whose regular strata are symplectic.
Backgrounds with spacetime symmetries (Killing fields) can produce conical
singularities; the ordinary smooth-manifold argument must not be applied
there. No Killing fields remove continuous isotropy but do not by themselves
exclude residual discrete stabilizers in the identity-component diffeomorphism
group. H5's free-action hypothesis therefore requires trivial full stabilizer;
otherwise use orbifold/stratified reduction. The GR specialization should
restrict to a suitable regular stratum or use singular/stratified reduction.

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

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
| D3B | `reverse_kernel_inclusion`, `full_kernel_eq_from_bridge`, `full_kernel_eq_from_quotient_cauchy_map_properties` | The bridge is conditional on pullback compatibility, surjectivity of the linearized initial-data map, CP, and infinitesimal PU. The new theorem derives the latter two tangent-map properties from algebraic well-definedness/bijectivity of the linearized quotient map plus CP. Petersen (arXiv:1802.06028), Theorems 4.7 and 4.18 and Lemma 4.13, supplies the corresponding vacuum-GR linearized results. Lean does not formalize the topological isomorphism, linearization stability, or the integration of every infinitesimal generator to a path in the chosen nonlinear diffeomorphism group. Therefore `im R` is an infinitesimal gauge subspace here, not automatically `T(G_0\cdot\phi)`. |
| D4 | `pairing_independent_of_lifts`, `quotient_pairing_nondegenerate`, `quotient_pairing_unique`, `cartan_invariance_of_horizontal_closed_form`, `closedness_descends` | Algebraic consequences for quotient pairings and descent. Smooth quotient existence and the geometric Cartan formula are assumptions, not Lean results. |
| D5 | `sphere_scalar_curvature_injective`, `two_sphere_scalar_curvature_injective`, `invariant_observable_excludes_gauge` | Injectivity of the displayed scalar-curvature functions and the abstract invariant-observable separation argument. The metric-curvature calculation and naturality under diffeomorphisms are checked separately. |

## Literature overlap and novelty risk

Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*
(arXiv:1402.1282, 2014), is a close prior result. The exact numbering is:

- **Definition 3.2 (global parametrizability of constraints):** nondegeneracy
  of the natural pairing between the vertical cohomologies in solutions
  associated with the constrained hyperbolic system.
- **Definition 3.3 (global recognizability of gauge transformations):**
  nondegeneracy of the natural pairing between the gauge cohomologies defined
  by the gauge complex and its adjoint.
- **Lemma 3.5:** under those two hypotheses, the natural pairing between the
  formal gauge-invariant solution tangent and cotangent spaces is
  nondegenerate.
- **Lemma 3.11 and Corollary 3.1:** the covariant presymplectic form is
  independent of the Cauchy surface, formally closed, and descends to the
  formal gauge quotient.
- **Theorem 3.2:** the Peierls formula is a two-sided inverse of the descended
  formal covariant symplectic form.

These hypotheses are not literally the same as H1's ADM annihilator
factorization or H4's nonlinear parameterized same-data uniqueness. They are
cohomological conditions on the linearized constrained hyperbolic system and
gauge complex. Nevertheless, the overlap with D2--D4 is substantial and must
be addressed theorem by theorem.

The present route is organized differently: it uses the Cauchy-data map,
canonical constraint surface, ADM constraint generators, and a smooth
solution-space quotient. That difference is not by itself enough to establish
novelty. Khavkine develops formal tangent/cotangent quotients and a formal
reduced symplectic structure; the present note additionally asks for an
actual smooth quotient with local sections and a local-product/submersion
property under H2/H5. A paper must prove that this is a genuinely stronger
geometric result in a precisely specified function-space category, rather
than simply restating the same nondegeneracy argument in ADM language.

The general covariant/canonical equivalence of symplectic forms is also
addressed by Margalef-Bentabol--Villaseñor (arXiv:2204.06383).

Petersen, *On the Cauchy problem for the linearised Einstein equation*
(arXiv:1802.06028, 2018), is another close prior result for the GR
specialization. Theorem 4.7 proves that a linearized vacuum Einstein solution
with zero induced first and second fundamental-form variations is pure gauge;
Lemma 4.13 identifies gauge-producing initial-data variations with induced
spacetime gauge variations; Theorem 4.18 proves the quotient-level linearized
Cauchy map is an isomorphism of locally convex topological vector spaces.
Thus tangent-level PU and the geometric CP formula are already established
in vacuum GR, and the linearized quotient Cauchy map is already well-posed.
The remaining possible contribution is the nonlinear symplectic
reduction/local-product theorem and its relation to Khavkine's cohomological
criterion, not the linearized Cauchy uniqueness statement itself.

A useful first-pass correspondence is:

| This note | Khavkine 2014 | Difference that must be demonstrated |
|---|---|---|
| H1: annihilator/conormal completeness | Global parametrizability of constraints (Def. 3.2) | Analogy only: the note uses a Cauchy/ADM annihilator identity; Khavkine uses nondegeneracy of a pairing between vertical cohomologies of the constrained hyperbolic system. |
| H2/H3: Cauchy map and constraint generators | Hyperbolizability plus the constraint complex | The note requires an actual local Cauchy-data map and identifies its constraint generators with spacetime diffeomorphisms. |
| H4: same-data solution curves are gauge | Global recognizability of gauge transformations (Def. 3.3) | Analogy only: H4 is nonlinear and parameterized; Khavkine's condition is nondegeneracy of a linearized gauge-cohomology pairing, not the same-data uniqueness statement. |
| D2--D4: kernel equality and descent | Lemma 3.5, Lemma 3.11, Corollary 3.1, and Theorem 3.2 | The note aims at a smooth geometric quotient under H5; Khavkine constructs formal tangent/cotangent quotients and a formal reduced symplectic structure with Peierls inverse. |
| H5: smooth quotient/local slices | Not the same as the cohomological nondegeneracy conditions | A smooth finite-regularity quotient, including stabilizers and strata, is an additional global geometric result. |

This comparison makes the novelty bar more precise. The strongest defensible
positioning would be a nonlinear Cauchy/ADM symplectic-reduction theorem that
combines known linearized Cauchy results with a precise admissible-dual
annihilator criterion and a smooth quotient/slice construction, and proves a
concrete result not already covered by Khavkine or Isenberg--Marsden. That
claim is not established until the H1--H5 comparison and a nontrivial GR
application are completed.

## Reduced GR hypothesis set for D3B

For compact-Cauchy vacuum GR, the full nonlinear H2 local-product condition
and nonlinear H4 parameterized same-data uniqueness are stronger than the
pointwise kernel proof requires. A reduced route is:

1. No KIDs plus the injective-symbol/split-range result for the linearized
   constraint map gives the regular constraint surface and linearization
   stability (Carlotto 2021, §4.1, Theorem 4.6; Fischer--Marsden 1975).
2. Petersen's Theorems 4.7 and 4.18, together with Lemma 4.13 and the ADM
   lapse-shift/constraint-generator comparison, give infinitesimal PU and
   surjectivity of the linearized Cauchy map.
3. The cutoff-flow lemma in the GR audit upgrades each smooth infinitesimal
   gauge generator to a jointly smooth path of compactly supported
   diffeomorphisms, if H0's group contains these isotopies.
4. Retain the covariant/canonical pullback identity and the H5 CMC slice
   theorem with trivial full stabilizer.

Thus H2 may be weakened to its pullback-compatibility part plus the
pointwise surjectivity of the linearized Cauchy map; H4 may be replaced by
linearization stability, infinitesimal PU, and cutoff-flow. This proves the
kernel identity in the chosen local function-space model, but does not by
itself establish novelty: Khavkine's formal reduction and
Isenberg--Marsden's CMC stratified symplectic quotient are close prior work.
The exact group topology for H5 and the chosen admissible dual for H1 remain
to be fixed.

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
the infinitesimal inclusion `ker Dr ⊆ im R`. Petersen's Theorem 4.7 proves
this for the linearized vacuum Einstein equation. The remaining passage to
the actual nonlinear tangent spaces has two independent inputs:

1. **Linearization stability.** In suitable tame Banach/Sobolev spaces, no
   KIDs imply split-surjectivity of the linearized vacuum constraint map.
   Carlotto (2021), §4.1 and Theorem 4.6, together with the Fischer--Marsden
   linearization-stability theorem, then identifies the relevant constraint
   tangent directions with integrable curves of exact data. The Lorentzian
   Einstein-map version is equivalent for consistent function spaces,
   locally near a Cauchy surface.
2. **Orbit tangency.** On (M=\mathbb R\times\Sigma) with compact
   (Sigma), the GR audit proves a cutoff-flow lemma: for any smooth vector
   field (V), the family (V_s=\chi(st)V) has compact spacetime support
   for (s\ne0), and (f_s=\operatorname{Fl}^{V_s}_s), (f_0=\mathrm{id}),
   is jointly smooth in ((s,x)) with (dot f_0=V). Thus, if (G_0)
   contains the allowed compactly supported isotopies, (\mathcal L_V\phi)
   is tangent to an actual (G_0)-orbit. The construction is not formalized
   in Lean.

The group topology still matters for H5. In the standard convenient
manifold model for diffeomorphisms of a noncompact manifold, the Lie algebra
is the compactly supported vector fields (Michor, 1980), while the cutoff
path above is smooth in the compact-open (C^\infty) sense but its supports
expand as (s\to0). With the compact-open functional diffeology, the full
diffeomorphism group is nonregular (Magnot, 2018), so one cannot assume that
arbitrary Lie-algebra paths integrate. This does not obstruct the specific
cutoff-flow construction; it means that the group model used for H5 must be
matched to the jointly smooth isotopies used here.

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
- Petersen (arXiv:1802.06028): linearized Einstein Cauchy uniqueness up to gauge, gauge-producing initial-data directions, and the quotient-level Cauchy map.
- Michor, *Manifolds of smooth maps, II* (1980): the standard convenient Lie-group model for diffeomorphisms of a noncompact manifold and its compactly supported Lie algebra.
- Magnot, *Demonstratio Mathematica* **51** (2018), 8--16, arXiv:1101.2370: nonregularity of the full noncompact diffeomorphism group with compact-open functional diffeology.
- Carlotto (Living Rev. Relativ. 24 (2021) 2): KIDs, surjectivity of the linearized constraint map, and linearization stability.
- A. E. Fischer and J. E. Marsden, “Linearization stability of nonlinear partial differential equations,” *Proc. Sympos. Pure Math.* **27** (1975), 219--263.
- Arms--Marsden--Moncrief: linearization stability and conical singularities at
  symmetric compact-Cauchy vacuum solutions.
- Isenberg--Marsden: spacetime-diffeomorphism slice theorem for spatially
  compact globally hyperbolic Einstein solutions with CMC foliations.
- Choquet-Bruhat--Geroch: uniqueness of maximal globally hyperbolic
  developments up to data-fixing isometry.
- Mounoud: nonproperness phenomena for diffeomorphism actions on spaces of
  Lorentzian metrics.

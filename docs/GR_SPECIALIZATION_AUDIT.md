# GR specialization audit of the covariant presymplectic-reduction argument

This document checks the abstract hypotheses against vacuum general relativity
in the spatially compact, globally hyperbolic setting. It is deliberately
conditional: the cited theorems have specific Sobolev/CMC hypotheses, and
they do not establish the abstract result for every diffeomorphism-invariant
field theory.

## Reference setting

Let \(V^4\) be globally hyperbolic with a compact spacelike Cauchy surface
\(\Sigma^3\), and let \(g\) be a vacuum Einstein solution. Work on a background with no spacetime Killing fields and, for the ordinary
smooth quotient in H5, trivial stabilizer under the chosen identity-component
diffeomorphism group. No Killing fields remove continuous isotropy but do not
by themselves exclude residual discrete stabilizers. For the slice/quotient
results, also assume the existence of a constant-mean-curvature (CMC)
foliation, as in the Isenberg--Marsden construction.

Use \(K_{ij}=-\frac12\mathcal L_n h_{ij}\) and the momentum convention
\[
\pi^{ij}=\sqrt h\,(K h^{ij}-K^{ij}).
\]
The canonical potential and symplectic form are
\[
\Theta_{\rm ADM}=\int_\Sigma \pi^{ij}\,\delta h_{ij},
\qquad
\Omega_{\rm ADM}=\delta\Theta_{\rm ADM}
=\int_\Sigma \delta\pi^{ij}\wedge\delta h_{ij},
\]
which matches the work-note convention \(\Omega=\int\delta p\wedge\delta q\).
The ADM initial data are \((h_{ij},\pi^{ij})\), subject to the Hamiltonian and
momentum constraints
\[
\mathcal H=
\frac{1}{\sqrt h}\left(\pi_{ij}\pi^{ij}-\frac12\pi^2\right)
-\sqrt h\,{}^{(3)}R,
\qquad
\mathcal H_i=-2h_{ij}D_k\pi^{jk}.
\]
The constraint map is
\[
\Phi(h,\pi)=(\mathcal H(h,\pi),\mathcal H_i(h,\pi))=0.
\]
The multipliers are a lapse-shift pair \((N,X^i)\).

## D1: why spacetime diffeomorphisms are null on a closed Cauchy slice

For a diffeomorphism-covariant Lagrangian, the on-shell covariant
presymplectic current satisfies \(d\omega=0\) when both variations solve the
linearized equations. This is the Lee--Wald/Iyer--Wald identity; Harlow--Wu
give a boundary-aware derivation.

Fix a Cauchy surface \(\Sigma_0\) and a spacetime vector field \(\xi\). Choose
a smooth time cutoff \(\chi\) such that \(\chi=1\) in a neighborhood of
\(\Sigma_0\) and \(\chi=0\) near an earlier Cauchy surface \(\Sigma_-\).
Set \(\widehat\xi=\chi\xi\). Diffeomorphism covariance implies
\(\mathcal L_{\widehat\xi}g\) is a linearized solution. Conservation of
\(\omega\) gives
\[
\int_{\Sigma_0}\omega(\delta g,\mathcal L_{\widehat\xi}g)
=
\int_{\Sigma_-}\omega(\delta g,\mathcal L_{\widehat\xi}g)=0,
\]
because \(\mathcal L_{\widehat\xi}g\) vanishes near \(\Sigma_-\).
Since \(\widehat\xi=\xi\) near \(\Sigma_0\), locality of the symplectic
current gives
\[
\Omega_{\Sigma_0}(\delta g,\mathcal L_\xi g)=0.
\]
Compactness and absence of a spatial boundary remove side-boundary terms.
This proves the inclusion of diffeomorphism directions in the presymplectic
kernel without introducing a Noether charge.

The proof requires the allowed diffeomorphism flows to preserve the solution
space and boundary conditions. If the Cauchy surface has a boundary or
asymptotic boundary conditions are imposed, boundary charges can make these
transformations non-null.

## D3A: literature cross-check of higher-order momenta

Margalef-Bentabol and Villaseñor, arXiv:2204.06383, Section VI,
Eqs. (22)--(24), derive the higher-order canonical momenta by a backward
recursion and prove equivalence of the canonical and covariant symplectic
forms for higher-order theories, including boundary terms. Their momentum
formula has the same finite alternating-derivative structure as
\[
p_j=\sum_{m=j+1}^{k}(-D)^{m-j-1}F_m,
\qquad
p_j=F_{j+1}-Dp_{j+1}.
\]
The exact index and boundary-density dictionary must be written when
specializing their notation to the work note, but the recursion and the
canonical/covariant symplectic equivalence are independently present in the
literature. This is an important check that the D3A algebra is not an
invented Ostrogradsky convention.

## Hypothesis-by-hypothesis status

| Abstract condition | GR realization | Status and limitation |
|---|---|---|
| H0: diffeomorphism-covariant local action, no fixed background | Einstein--Hilbert action, with boundary terms treated consistently; compact \(\Sigma\) has no spatial boundary | Standard. Boundary conventions must be fixed before comparing symplectic potentials. |
| H1: canonical flat map injective; constraint annihilator is conormal image | ADM phase space \(T^*\mathrm{Riem}(\Sigma)\) with canonical symplectic form; \(\Phi\) is the ADM constraint map | The canonical pairing is weakly nondegenerate. For compact-Cauchy vacuum data, Moncrief identifies \(\ker D\Phi^*\) with the space of Killing initial data (KIDs), which correspond to spacetime Killing fields in the maximal development. Thus no KIDs imply injectivity of the formal adjoint. To infer surjectivity of \(D\Phi\), one must also work in specified Sobolev spaces where the underdetermined-elliptic operator has closed range/split image; this is the analytic step behind the regular constraint-manifold statement. Once \(D\Phi\) is a bounded surjection between Banach spaces, the open mapping theorem shows that every continuous functional annihilating \(\ker D\Phi\) factors continuously through \(D\Phi\). In the work-note notation \(D\chi:V\to\Lambda^*\), the resulting multiplier lies in \(\Lambda^{**}\), which is identified with \(\Lambda\) for a reflexive Hilbert choice by Riesz. However, this proves the exact work-note statement only if the selected admissible cotangent pairing \(\mathrm{Ann}_{\rm adm}\) is the continuous dual used in the Banach argument, or if one separately proves that the factorizing multiplier belongs to the allowed \(\Lambda\). Riesz identification alone does not identify an arbitrary restricted admissible dual with the full continuous dual. Lean currently proves only the algebraic-dual factorization; it does not formalize the Sobolev closed-range estimate or open mapping theorem. |
| H2: solution-to-initial-data map is a local submersion/product | Cauchy data satisfying \(\Phi=0\) determine a maximal globally hyperbolic development up to isometry; the regular solution space is smooth near a no-Killing background | Margalef-Bentabol--Villaseñor (2022) prove equivalence of the covariant and canonical symplectic forms, with a separate higher-order discussion in Sec. VI. For Einstein--Hilbert gravity on a closed Cauchy surface, this supports the pullback compatibility \(\Omega_{\rm CPS}=r_\Sigma^*\Omega_{\rm ADM}\) once the boundary potential, orientation, and normalization are matched. Petersen (2018), Theorem 4.18, proves that the *linearized* Cauchy solution map from initial data modulo gauge-producing data to solutions modulo gauge solutions is an isomorphism of locally convex topological vector spaces; for compact \(\Sigma\), Corollary 4.22 gives the quotient a Hilbert structure at finite Sobolev order and a Fréchet structure in the smooth case. This verifies the linearized quotient-level Cauchy map. It does not prove that the nonlinear map \(r_\Sigma\) is a smooth submersion with a local product structure. That nonlinear map-level part of H2 remains open in the chosen function-space setting. |
| H3 / CP: each constraint-generated initial-data direction is induced by a spacetime diffeomorphism | A lapse-shift \((N,X)\) is the normal/tangential deformation of the Cauchy embedding, \(\xi=Nn+X\) | Petersen (2018), Lemma 4.13 and Eqs. (23)--(24), identifies the gauge-producing initial-data directions with the induced data \(\pi_\Sigma(\mathcal L_V g)\) of spacetime gauge variations, explicitly in lapse-shift variables. This gives the CP identification in vacuum GR, after translating the sign convention for the second fundamental form. The ADM Hamiltonian calculation below independently checks the sign used in this note. |
| H4 / PU: a smooth family of solutions with identical initial data is a smooth diffeomorphism family | Uniqueness of maximal globally hyperbolic developments up to a data-fixing isometry | The work note's H4 is a nonlinear, parameterized same-data uniqueness statement and is stronger than D3B needs. The exact tangent-level condition required by D3B is instead proved for vacuum GR by Petersen (2018), Theorem 4.7: a solution \(h\) of the linearized Einstein equation whose induced first and second fundamental-form variations vanish is a pure gauge perturbation \(h=\mathcal L_V g\). The theorem constructs \(V\) by solving a normally hyperbolic vector equation and uses Cauchy uniqueness. Thus the tangent-level PU hypothesis of the Lean bridge is literature-supported in the stated globally hyperbolic vacuum setting. The nonlinear H4 itself remains unproved and appears unnecessary for the kernel-equality theorem; a revised statement could replace H4 by this weaker linearized condition. |
| H5: regular quotient by spacetime diffeomorphisms has local slices | Isenberg--Marsden spacetime-diffeomorphism slice theorem for spatially compact globally hyperbolic Einstein solutions, using CMC foliations | The quotient is stratified symplectic. The ordinary smooth quotient applies on a stratum with trivial stabilizer. Killing fields give continuous isotropy and conical singularities; residual discrete isotropy can instead give orbifold/stratified points and must not be silently treated as a free quotient. |

## The ADM check for CP

For a spacelike embedding \(i:\Sigma\hookrightarrow V\), decompose a deformation
field along the embedding as
\[
\xi=Nn+X,
\]
where \(n\) is the future unit normal, \(N\) is the lapse, and \(X\) is tangent
to \(\Sigma\) (the shift). The induced data are \(h=i^*g\) and the second
fundamental form \(K\), with \(\pi\) its ADM momentum density.

With the standard ADM convention \(K_{ij}=-\frac12\mathcal L_n h_{ij}\)
and in vacuum (\(\Lambda=0\)), the induced hypersurface-deformation formulas
are
\[
\delta_{(N,X)}h_{ij}=-2N K_{ij}+\mathcal L_X h_{ij},
\]
\[
\delta_{(N,X)}K_{ij}
=-D_iD_jN
+N\bigl(R_{ij}+K K_{ij}-2K_{ik}K^k{}_j\bigr)
+\mathcal L_XK_{ij}.
\]
These are the ADM evolution equations read as deformations of the Cauchy
embedding. Other sign conventions for \(K_{ij}\) change the corresponding
signs and must be translated consistently.

With \(\Omega_{\rm ADM}=\int_\Sigma\delta\pi^{ij}\wedge\delta h_{ij}\)
and \(\iota_{X_H}\Omega_{\rm ADM}=-\delta H\), the Hamiltonian vector field
of the smeared constraint satisfies
\[
X_{H[N,X]}h_{ij}
=\frac{2N}{\sqrt h}\left(\pi_{ij}-\frac12\pi h_{ij}\right)
+\mathcal L_Xh_{ij}
=-2NK_{ij}+\mathcal L_Xh_{ij}.
\]
This is exactly the first hypersurface-deformation formula above, with the
declared sign convention for \(K_{ij}\).

The smeared constraint functional is
\[
H[N,X]=\int_\Sigma (N\mathcal H+X^i\mathcal H_i).
\]
In the ADM/embedding formulation, the deformation of the embedding induces
the same Hamiltonian vector field on \((h,\pi)\) as the constraint generator.
Marsden's Theorem 9.3 expresses this schematically as
\[
\frac{d}{d\lambda}(h(\lambda),\pi(\lambda))
=-\,\mathbb J\circ D\Phi(h(\lambda),\pi(\lambda))^*(N(\lambda),X(\lambda)),
\]
where \(\mathbb J\) is the canonical complex structure associated with the
ADM symplectic form and the chosen \(L^2\) pairing. This is the precise
constraint/embedding statement needed for CP. The embedding deformation is
the restriction of the spacetime diffeomorphism generated by \(\xi\).

The deformation vector \(Nn+X\) is initially defined only along the
embedding. Extend it smoothly to a neighborhood of \(\Sigma\), then multiply
by a time cutoff equal to one near \(\Sigma\); this gives an allowed
spacetime-diffeomorphism generator with the same induced initial-data
variation. The lapse-shift and the corresponding \(\xi\) are
embedding/background dependent. The space of embeddings is not itself a
group, so the hypersurface-deformation algebra should not be treated as a
fixed Lie algebra of spacetime vector fields away from the constraint surface.

This formula is not yet Lean-formalized in the repository; the Lean theorem
D3B assumes CP abstractly.

## Linearized Cauchy uniqueness: direct verification of tangent-level PU and CP

A stronger and more direct reference than the nonlinear H4 route is Petersen,
*On the Cauchy problem for the linearised Einstein equation* (2018).

1. **Tangent-level PU is a theorem, not an extra conjecture in vacuum GR.**
   Petersen's Theorem 4.7 states that if \(h_{\mu\nu}\) solves the linearized
   vacuum Einstein equation and its induced first and second fundamental-form
   variations on a Cauchy surface vanish, then there exists a vector field
   \(V\) such that
   \[
   h_{\mu\nu}=\mathcal L_V g_{\mu\nu}.
   \]
   The proof solves a normally hyperbolic vector equation for \(V\), then
   applies uniqueness for a linear wave equation to the gauge-adjusted
   perturbation with zero Cauchy data. This is precisely
   \(\ker D r_\Sigma\subseteq\operatorname{im}R_g\), the tangent-level PU
   hypothesis used by Lean D3B. The theorem is stated for globally hyperbolic
   vacuum spacetimes in finite-energy Sobolev regularity spaces, including
   the smooth case.

2. **CP is also explicit in the same paper.**
   Petersen's Lemma 4.13 and Eqs. (23)--(24) identify the space of
   gauge-producing initial-data variations with the image of the spacetime
   gauge variations \(\mathcal L_Vg\) under the linearized initial-data map.
   Decomposing \(V|_\Sigma=N\nu+\beta\) gives the lapse-shift formulas for
   the induced variations of the first and second fundamental forms. This
   matches the geometric content of CP, subject to translating the sign
   convention for the second fundamental form.

3. **The quotient-level linearized Cauchy map is an isomorphism.**
   Petersen's Theorem 4.18 proves that the linear solution map
   \[
   \frac{\{\text{linearized solutions}\}}{\{\text{spacetime gauge solutions}\}}
   \longleftrightarrow
   \frac{\{\text{linearized constraint data}\}}{\{\text{gauge-producing data}\}}
   \]
   is an isomorphism of locally convex topological vector spaces. For compact
   \(\Sigma\), Corollary 4.22 gives the quotient a Hilbert structure at finite
   Sobolev order and a Fréchet structure in the smooth case. This is a
   linearized quotient statement, not the nonlinear split-submersion claim
   H2 in the work note.

Consequently, the nonlinear H4 assumption is stronger than needed for D3B:
the weaker tangent-level PU follows from Petersen's theorem in vacuum GR.
The remaining nonlinear gap is H2, namely a smooth local product structure
for the nonlinear solution-to-initial-data map. Isenberg--Marsden slices
control the diffeomorphism quotient, but the construction must still show
that the development and slice charts combine into the required local
submersion in a common topology.

## Killing fields and the regular stratum

For vacuum spacetimes with compact Cauchy surfaces, Moncrief identifies the
kernel of the adjoint linearized constraint map with spacetime Killing fields.
Consequently, absence of Killing fields gives the regularity/surjectivity
condition needed for linearization stability in the standard functional
setting. If Killing fields are present, the linearized constraint equations
admit spurious directions unless the Taub quadratic charges vanish. The
solution space can have a conical singularity.

Thus, in GR, the regular solution-space theorem requires no Killing fields.
For the stronger free-action hypothesis in H5, also check that the stabilizer
inside the selected identity-component diffeomorphism group is actually
trivial; no Killing fields only show that its Lie algebra vanishes. If a
residual discrete stabilizer remains, use the orbifold/stratified quotient
rather than an ordinary smooth manifold. At backgrounds with Killing fields,
linearization stability itself also requires the Taub-charge conditions.

## What remains open in this specialization

1. Write the precise Sobolev spaces and prove the split-surjectivity and
   continuous-dual annihilator identity for \(D\Phi\) in those spaces.
2. Give the explicit ADM sign/normalization conversion to the work-note
   convention \(\iota_{X_H}\Omega=-\delta H\).
3. Prove the parameterized smooth PU statement using a fixed hyperbolic gauge
   and smooth dependence on the external parameter.
4. Specialize the general covariant/canonical symplectic-equivalence theorem
   to the chosen Einstein--Hilbert boundary potential and verify the exact
   16πG normalization and sign convention used in the note.
5. Restrict H5 to the CMC setting of the slice theorem, or separately justify
   a different regular quotient construction.

## Prior covariant-phase-space criterion to compare against

Khavkine (2014) is a close prior result, not an optional background citation.
The exact statements are Definitions 3.2 (global parametrizability of
constraints) and 3.3 (global recognizability of gauge transformations);
Lemma 3.5 proves nondegeneracy of the formal gauge-invariant solution
tangent/cotangent pairing under these hypotheses; Lemma 3.11 establishes
Cauchy-surface independence and formal closedness; Corollary 3.1 descends
the presymplectic form to the formal gauge quotient; and Theorem 3.2 proves
that the Peierls formula is its two-sided inverse. These hypotheses overlap
substantially with the purpose of H1 and the D2--D4 conclusion, but they are
not literally H1's ADM annihilator factorization or H4's nonlinear
parameterized same-data uniqueness. Khavkine works with formal tangent and
cotangent quotients of the linearized constrained hyperbolic system; the
present note additionally asks for a smooth geometric quotient with local
sections and a local-product/submersion property. A novelty claim therefore
requires a theorem-by-theorem comparison showing that the latter is a
genuinely new result in a specified function-space category, not just an ADM
rephrasing of the formal reduction.

## Primary references

- I. Khavkine, “Covariant phase space, constraints, gauge and the Peierls formula,” *Int. J. Mod. Phys. A* **29** (2014), 1430009, DOI: 10.1142/S0217751X14300099, arXiv:1402.1282.
- T. J. R. Hughes, T. Kato and J. E. Marsden, “Well-posed quasi-linear second-order hyperbolic systems with applications to nonlinear elastodynamics and general relativity,” *Arch. Rational Mech. Anal.* **63** (1977), 273--294, DOI: 10.1007/BF00251584.
- A. Carlotto, “The general relativistic constraint equations,” *Living Reviews in Relativity* **24** (2021), article 2, DOI: 10.1007/s41114-020-00030-z; see the discussion of KIDs and Theorem 4.6.
- O. L. Petersen, “On the Cauchy problem for the linearised Einstein equation,” arXiv:1802.06028 (2018), especially Theorems 4.7 and 4.18, Lemma 4.13, and Corollary 4.22.
- J. Isenberg and J. E. Marsden, “A Slice Theorem for the Space of Solutions of Einstein's Equations,” *Physics Reports* **89** (1982), 179--222, DOI: 10.1016/0370-1573(82)90066-7.
- J. Margalef-Bentabol and E. J. S. Villaseñor, “Proof of the equivalence of the symplectic forms derived from the canonical and the covariant phase space formalisms,” arXiv:2204.06383 (2022).
- J. Isenberg and J. E. Marsden, “A Slice Theorem for the Space of Solutions
  of Einstein's Equations,” *Physics Reports* **89** (1982), 179--222,
  DOI: 10.1016/0370-1573(82)90066-7.
- J. E. Marsden, *Lectures on Geometric Methods in Mathematical Physics*,
  Lectures 9--10: Theorem 9.1 (regular points), Theorem 9.3 (ADM/embedding
  evolution), and Theorem 10.1 (conical singularities at symmetric points).
- V. Moncrief, “Space-Time Symmetries and Linearization Stability of the
  Einstein Equations. I,” *J. Math. Phys.* **16** (1975), 493--498,
  DOI: 10.1063/1.522572; and part II, *J. Math. Phys.* **17** (1976),
  1893--1902, DOI: 10.1063/1.522814.
- A. E. Fischer, J. E. Marsden and V. Moncrief, “The Structure of the Space
  of Solutions of Einstein's Equations. I. One Killing Field,” *Ann. Inst.
  H. Poincaré A* **33** (1980), 147--194.
- J. Isenberg, “Parametrization of the Space of Solutions of Einstein's
  Equations,” *Phys. Rev. Lett.* **59** (1987), 2389.
- Y. Choquet-Bruhat and R. Geroch, “Global Aspects of the Cauchy Problem in
  General Relativity,” *Commun. Math. Phys.* **14** (1969), 329--335,
  DOI: 10.1007/BF01645389.

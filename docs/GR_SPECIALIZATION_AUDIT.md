# GR specialization audit of the covariant presymplectic-reduction argument

This document checks the abstract hypotheses against vacuum general relativity
in the spatially compact, globally hyperbolic setting. It is deliberately
conditional: the cited theorems have specific Sobolev/CMC hypotheses, and
they do not establish the abstract result for every diffeomorphism-invariant
field theory.

## Reference setting

Let \(V^4\) be globally hyperbolic with a compact spacelike Cauchy surface
\(\Sigma^3\), and let \(g\) be a vacuum Einstein solution. Work on a regular
background with no spacetime Killing fields. For the slice/quotient results,
also assume the existence of a constant-mean-curvature (CMC) foliation, as in
the Isenberg--Marsden construction.

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

## Hypothesis-by-hypothesis status

| Abstract condition | GR realization | Status and limitation |
|---|---|---|
| H0: diffeomorphism-covariant local action, no fixed background | Einstein--Hilbert action, with boundary terms treated consistently; compact \(\Sigma\) has no spatial boundary | Standard. Boundary conventions must be fixed before comparing symplectic potentials. |
| H1: canonical flat map injective; constraint annihilator is conormal image | ADM phase space \(T^*\mathrm{Riem}(\Sigma)\) with canonical symplectic form; \(\Phi\) is the ADM constraint map | The canonical pairing is weakly nondegenerate. At a compact-Cauchy vacuum background, \(\ker D\Phi^*\) corresponds to spacetime Killing fields. With no Killing fields, the constraint map is a submersion in the standard split Sobolev setting; the elliptic/splitting result supplies the relevant annihilator factorization. To identify the multiplier space with the dual of the constraint-value space in the work-note notation, choose compatible Hilbert Sobolev spaces and use the Riesz/reflexivity identification. This is not a theorem about arbitrary Fréchet spaces without specifying function spaces. |
| H2: solution-to-initial-data map is a local submersion/product | Cauchy data satisfying \(\Phi=0\) determine a maximal globally hyperbolic development up to isometry; the regular solution space is smooth near a no-Killing background | The equivalence of covariant and canonical symplectic forms is established in general by Margalef-Bentabol--Villaseñor (2022), including higher-order theories and boundaries, subject to a good variational principle. For Einstein--Hilbert gravity on a closed Cauchy surface, this supports the pullback compatibility Ω_CPS = r_Σ^* Ω_ADM once the boundary potential and normalization are matched. The separate map-level part of H2 still requires a smooth gauge-fixed development section and a local product proof using Cauchy uniqueness and the slice theorem. |
| H3 / CP: each constraint-generated initial-data direction is induced by a spacetime diffeomorphism | A lapse-shift \((N,X)\) is the normal/tangential deformation of the Cauchy embedding, \(\xi=Nn+X\) | Supported by the ADM/embedding formulation. The Hamiltonian flow of the smeared constraints is the induced deformation of \((h,\pi)\); see the formula below. Sign conventions must match the chosen \(\iota_{X_H}\Omega=-\delta H\). |
| H4 / PU: a smooth family of solutions with identical initial data is a smooth diffeomorphism family | Uniqueness of maximal globally hyperbolic developments up to a data-fixing isometry | Choquet-Bruhat--Geroch gives an isometry for each member of a same-data family. On the no-Killing regular stratum, the Isenberg--Marsden slice theorem supplies local smooth orbit coordinates; together these should yield a smoothly parameterized family of diffeomorphisms. The proof must explicitly identify the data-fixing isometries with the local identity-component action and use the slice coordinate to establish smooth dependence. Pointwise uniqueness alone does not prove parameterized PU. |
| H5: regular quotient by spacetime diffeomorphisms has local slices | Isenberg--Marsden spacetime-diffeomorphism slice theorem for spatially compact globally hyperbolic Einstein solutions, using CMC foliations | The quotient is stratified symplectic. The ordinary smooth quotient applies on a regular symmetry stratum; symmetric solutions have conical singularities and must be treated by singular/stratified reduction. |

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

## How Cauchy uniqueness and the slice theorem can supply H2/PU

There is a concrete route to the two remaining map-level conditions:

1. In a fixed hyperbolic gauge, the local Einstein Cauchy problem assigns to
   each regular constrained initial datum \(c\in\mathcal C\) a development
   \(\operatorname{Dev}(c)\). Smooth dependence on \(c\) gives a candidate
   smooth local section of \(r_\Sigma\).
2. Choquet-Bruhat--Geroch uniqueness says that any other maximal globally
   hyperbolic development with the same initial data is isometric to
   \(\operatorname{Dev}(c)\), with the isometry identifying the initial
   hypersurface and its data.
3. On a no-Killing regular stratum, the Isenberg--Marsden slice theorem gives
   local smooth orbit coordinates with trivial isotropy. Therefore, for a
   smooth curve of solutions in one \(r_\Sigma\)-fiber, the diffeomorphism
   coordinate relating it to \(\operatorname{Dev}(c)\) is smooth in the
   curve parameter.

If the gauge-fixed development section and the slice coordinates are
constructed in the same Sobolev topology, this yields the local product
structure in H2 and the parameterized PU condition in H4. This is the
intended GR proof route, not yet a completed proof in the work note. The
remaining technical work is to specify the function spaces, the
identity-component diffeomorphism subgroup, the data-fixing isometries, and
the smoothness of the development/slice maps.

## Killing fields and the regular stratum

For vacuum spacetimes with compact Cauchy surfaces, Moncrief identifies the
kernel of the adjoint linearized constraint map with spacetime Killing fields.
Consequently, absence of Killing fields gives the regularity/surjectivity
condition needed for linearization stability in the standard functional
setting. If Killing fields are present, the linearized constraint equations
admit spurious directions unless the Taub quadratic charges vanish. The
solution space can have a conical singularity.

Thus, in GR, the smooth-manifold theorem should be stated on the no-Killing
regular stratum. At symmetric backgrounds, use the singular/stratified
version instead.

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

## Primary references

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

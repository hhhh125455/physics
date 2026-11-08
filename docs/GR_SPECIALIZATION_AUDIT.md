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

Fix the Einstein--Hilbert normalization
\[
S_{\rm EH}=\frac{1}{\kappa}\int_M R[g]\,\boldsymbol\epsilon,
\qquad \kappa:=16\pi G,
\]
and use \(K_{ij}=-\frac12\mathcal L_n h_{ij}\). After the standard temporal
boundary term in the ADM decomposition, the canonical momentum is
\[
\pi^{ij}=\frac{\sqrt h}{\kappa}\,(K h^{ij}-K^{ij}).
\]
The canonical potential and symplectic form are
\[
\Theta_{\rm ADM}=\int_\Sigma \pi^{ij}\,\delta h_{ij},
\qquad
\Omega_{\rm ADM}=\delta\Theta_{\rm ADM}
=\int_\Sigma \delta\pi^{ij}\wedge\delta h_{ij},
\]
which matches the work-note convention \(\Omega=\int\delta p\wedge\delta q\)
and the Harlow--Wu convention (their Eq. (16)). The ADM initial data are
\((h_{ij},\pi^{ij})\), subject to
\[
\mathcal H=
\frac{\kappa}{\sqrt h}
\left(\pi_{ij}\pi^{ij}-\frac12\pi^2\right)
-\frac{\sqrt h}{\kappa}\,{}^{(3)}R,
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
| H2: solution-to-initial-data map is a local submersion/product | Cauchy data satisfying \(\Phi=0\) determine a maximal globally hyperbolic development up to isometry; the regular solution space is smooth near a no-Killing background | Margalef-Bentabol--Villaseñor (2022) prove equivalence of the covariant and canonical symplectic forms, with a separate higher-order discussion in Sec. VI. For Einstein--Hilbert gravity on a closed Cauchy surface, this supports the pullback compatibility \(\Omega_{\rm CPS}=r_\Sigma^*\Omega_{\rm ADM}\) once the boundary potential, orientation, and normalization are matched. Petersen (2018), Theorem 4.18, proves that the *linearized* Cauchy solution map between initial data modulo gauge-producing data and solutions modulo infinitesimal gauge solutions is an isomorphism of locally convex topological vector spaces; for compact \(\Sigma\), Corollary 4.22 gives the quotient a Hilbert structure at finite Sobolev order and a Fréchet structure in the smooth case. Together with CP, its algebraic content is enough for the surjectivity of the unquotiented linearized initial-data map used in D3B.

The actual-solution tangent issue has a separate standard route. Carlotto (2021), §4.1, Definitions 4.1--4.2 and Theorem 4.6, explains that in the appropriate tame Banach/Sobolev setting the vacuum constraint map is linearisation stable precisely when its derivative is surjective; away from KIDs, injectivity of the formal adjoint (with its injective elliptic symbol) gives the required split-surjectivity. The Lorentzian Einstein-map version is equivalent to the constraint-level version for consistent choices of function spaces, locally in a tubular neighbourhood of the Cauchy surface. Thus, on a compact no-KID regular stratum, the linearized solution directions are integrable to \(C^1\) curves of actual solutions locally in time. This is enough to identify the actual tangent space with the linearized solution space in that local solution-space model. It does not by itself prove that the nonlinear map \(r_\Sigma\) is a smooth submersion with a local product structure over an entire global solution space. That stronger nonlinear part of H2 remains open, although it is stronger than what the pointwise D3B kernel argument itself uses. |
| H3 / CP: each constraint-generated initial-data direction is induced by a spacetime diffeomorphism | A lapse-shift \((N,X)\) is the normal/tangential deformation of the Cauchy embedding, \(\xi=Nn+X\) | Petersen (2018), Lemma 4.13 and Eqs. (23)--(24), identifies the gauge-producing initial-data directions with the induced data \(\pi_\Sigma(\mathcal L_V g)\) of spacetime infinitesimal gauge variations, explicitly in lapse-shift variables. The separate ADM Hamiltonian calculation below matches the Hamiltonian vector fields of the smeared constraints to these lapse-shift deformations, after translating the sign convention for the second fundamental form. This combined comparison is the CP check; Lemma 4.13 alone does not identify an arbitrary constraint generator with a spacetime diffeomorphism. |
| H4 / PU: a smooth family of solutions with identical initial data is a smooth diffeomorphism family | Uniqueness of maximal globally hyperbolic developments up to a data-fixing isometry | The work note's H4 is a nonlinear, parameterized same-data uniqueness statement and is stronger than the infinitesimal condition used by the algebraic D3B bridge. Petersen (2018), Theorem 4.7, proves that a linearized vacuum Einstein solution \(h\) whose induced first and second fundamental-form variations vanish has the form \(h=\mathcal L_V g\), with \(V\) constructed by solving a normally hyperbolic vector equation and using Cauchy uniqueness. This proves infinitesimal PU at the level of the linearized PDE solution space.

The remaining identification with an actual \(\mathcal G_0\)-orbit tangent can be supplied by a cutoff-flow lemma under the work note's product and compactness assumptions. Let \(M=\mathbb R\times\Sigma\), with \(\Sigma\) compact, let \(t\) be the product time coordinate, and choose \(\chi\in C_c^\infty(\mathbb R)\) equal to one near zero. For an arbitrary smooth vector field \(V\) on \(M\), set
\[
V_s=\chi(st)V\quad(s\ne0),\qquad V_0=V,
\qquad f_s=\operatorname{Fl}^{V_s}_s\quad(s\ne0),\qquad f_0=\mathrm{id}.
\]
For each \(s\ne0\), \(V_s\) has compact spacetime support because \(\Sigma\) is compact, hence is complete and has a globally defined flow. For every compact \(K\subset M\), the local flow of \(V\) exists uniformly for sufficiently small parameter on a compact neighbourhood of \(K\); for sufficiently small \(s\), \(\chi(st)=1\) throughout that neighbourhood. Consequently \(f_s\) agrees there with the local flow of \(V\). This proves that \((s,x)\mapsto f_s(x)\) is smooth in the compact-open \(C^\infty\) sense and
\[
\left.\frac{d}{ds}f_s^*g\right|_{s=0}=\mathcal L_Vg.
\]
Each \(f_s\) is a compactly supported diffeomorphism isotopic to the identity. Thus, if \(\mathcal G_0\) contains the allowed compactly supported isotopies as in H0, every smooth infinitesimal gauge direction is tangent to an actual smooth \(\mathcal G_0\)-orbit. This construction does not require \(V\) itself to be complete.

The cutoff-flow lemma is a local-in-parameter construction; it does not make the full diffeomorphism group regular. Magnot's functional diffeology declares a parameterized family of diffeomorphisms smooth precisely when its evaluation map \((s,x)\mapsto f_s(x)\) is smooth. Thus the construction above is a specific smooth curve in \(\mathrm{Diff}(M)\) with that functional diffeology, and it places the arbitrary smooth \(V\) in the corresponding tangent space. Magnot's nonregularity theorem says that not every smooth path in the Lie algebra integrates to a group path; it does not obstruct this particular curve, which is constructed directly.

In contrast, if one equips \(\mathrm{Diff}_c(M)\) with its usual strict-LF Lie-group topology, a smooth curve must have locally uniformly bounded support. For a general \(V\) with noncompact time support, the supports of \(f_s\) expand as \(s\to0\), so this particular curve need not be smooth in that topology. The group topology used for H5 must therefore be compatible with the functional-diffeology/compact-open isotopies in H4. Isenberg--Marsden's CMC slice theorem is a candidate source of the required spacetime-diffeomorphism orbit geometry, but its precise group/function-space model must be matched to this compact-open cutoff construction.

Combining (a) linearization stability on the no-KID regular stratum, (b) Petersen's infinitesimal PU theorem, and (c) the cutoff-flow lemma gives a concrete replacement for nonlinear H4 in the local solution-space setting. The remaining issue is not parameterized Cauchy uniqueness itself; it is the compatibility of the chosen \(\mathcal G_0\) topology/action with the H5 slice theorem. |
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
=\frac{2\kappa N}{\sqrt h}\left(\pi_{ij}-\frac12\pi h_{ij}\right)
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

## Actual solution-space tangent: the no-Killing theorem

There is a direct theorem for the actual spacetime solution space, not merely
for the constraint map. Marsden, *Lectures on Geometric Methods in
Mathematical Physics*, Lecture 9, Theorem 9.1, states for a globally
hyperbolic vacuum spacetime with a compact spacelike Cauchy hypersurface that
the space \(\mathcal E\) of globally hyperbolic vacuum solutions is a smooth
manifold near \(g\), with tangent space equal to the solutions of the
linearized Einstein equation, if and only if \(g\) has no Killing fields.
The lecture specifies the topology as \(H^s\)-convergence on compact subsets
of spacetime and explains that the compact-Cauchy initial-value formulation
reduces the local analysis to a compact neighbourhood and Banach spaces.
The proof lineage is Fischer--Marsden and Moncrief.

This is exactly the linearization-stability input needed to interpret
Petersen's linearized solution space as the tangent space of actual
solutions on the no-Killing regular stratum. Carlotto's constraint-map
criterion gives the initial-data mechanism: no KIDs, together with the
injective-symbol/closed-range splitting condition, makes the constraint
map a submersion. The two statements are compatible but should not be
conflated: Marsden's Theorem 9.1 is the spacetime solution-manifold
statement; Carlotto's Theorem 4.6 is the constraint-map linearization-
stability statement.

Marsden's Lecture 9, Theorem 9.3, also formulates the ADM evolution in terms
of spacelike embeddings and the adjoint linearized constraint map. It
explains why lapse and shift are the infinitesimal deformation data and why
the embedding space acts analogously to a symmetry group, while explicitly
warning that the embedding space is not itself a group. This is useful
background for CP, but it is not a substitute for the separate
lapse-shift/ADM-generator calculation in this audit.

## Tangent-level GR kernel theorem: replace nonlinear H2/H4 by linearized inputs

The preceding results give a cleaner GR-specific route than the general
H2/H4 hypotheses in the work note. Let \((M,g)\) be a globally hyperbolic
vacuum spacetime with compact Cauchy surface \(\Sigma\), and suppose:

1. \(g\) has no spacetime Killing fields, so the actual solution space
   \(\mathcal E\) is smooth near \(g\) and
   \(T_g\mathcal E=\mathrm{Sol}_{\mathrm{lin}}(g)\) (Marsden, Lecture 9,
   Theorem 9.1).
2. The vacuum constraint map is realized in compatible Sobolev Hilbert
   spaces, its formal adjoint has the injective mixed-order symbol above,
   and there are no KIDs. Then \(D\Phi\) is split-surjective and
   \(\operatorname{Ann}(T_z\mathcal C)=\operatorname{im}D\Phi_z^*\);
   with the weak ADM symplectic form this gives
   \[
   \ker\big(\Omega_{\mathrm{ADM}}|_{T_z\mathcal C}\big)
   =\operatorname{im}X_z.
   \]
3. The linearized Cauchy map induces the quotient isomorphism
   \[
   \mathrm{Sol}_{\mathrm{lin}}(g)/\operatorname{im}R_g
   \ \xrightarrow{\;\simeq\;}\
   T_z\mathcal C/\operatorname{im}X_z,
   \]
   as in Petersen, Theorem 4.18, and the ADM/spacetime gauge directions
   are identified by CP (Petersen, Lemma 4.13 plus the lapse-shift
   constraint-generator calculation).
4. The covariant form and the ADM form obey the pullback identity
   \[
   \Omega_{\mathrm{CPS},g}
   =D r_\Sigma^*
     \big(\Omega_{\mathrm{ADM}}|_{T_z\mathcal C}\big),
   \]
   with the Einstein--Hilbert potential, orientation, and normalization
   translated consistently.
5. The selected identity-component diffeomorphism group has a smooth
   action compatible with the compact-open cutoff paths, and its local
   solution-space quotient has a slice at \(g\). The CMC
   Isenberg--Marsden theorem supplies the relevant slice result; the
   precise group-topology match remains an explicit hypothesis until
   checked against its function-space model.

Then the tangent-level kernel identity follows:
\[
\boxed{\quad
\ker\Omega_{\mathrm{CPS},g}
=\operatorname{im}R_g
=T_g(\mathcal G_0\!\cdot g).
\quad}
\]
Indeed, the quotient Cauchy isomorphism together with CP gives the
unquotiented linearized initial-data surjectivity and the infinitesimal
zero-data uniqueness inclusion. These are precisely the algebraic
hypotheses extracted by Lean theorem
\`full_kernel_eq_from_quotient_cauchy_map_properties\`. If
\(u\in\ker\Omega_{\mathrm{CPS},g}\), surjectivity of \(D r_\Sigma\) and
the pullback identity imply that \(D r_\Sigma u\) lies in the kernel of
the restricted ADM form. By item 2 it is a constraint-generated
direction; CP lifts that direction to \(R_g\xi\). The difference
\(u-R_g\xi\) has zero linearized Cauchy data, so quotient injectivity
(or Petersen's Theorem 4.7) makes it infinitesimally gauge. This proves
\(\ker\Omega_{\mathrm{CPS},g}\subseteq\operatorname{im}R_g\).
The reverse inclusion is the diffeomorphism-degeneracy statement D1.
The cutoff-flow lemma identifies these infinitesimal gauge vectors with
actual orbit tangents in the chosen compact-open smooth group model.

On a regular CMC slice with trivial \(\mathcal G_0\)-stabilizer, the
Isenberg--Marsden slice gives a local smooth quotient. The descended
two-form is closed and weakly nondegenerate: if a quotient tangent class
pairs to zero with all classes, any lift lies in
\(\ker\Omega_{\mathrm{CPS},g}\), hence is vertical and represents zero.
Thus the local quotient carries the unique weak symplectic form whose
pullback is \(\Omega_{\mathrm{CPS}}\).

**Scope.** This tangent-level GR theorem does not prove the full nonlinear
initial-data map is a submersion with a local product structure, nor the
general nonlinear parameterized H4 statement. Those stronger hypotheses
are unnecessary for this pointwise kernel identity once the actual
solution tangent is identified by the no-Killing theorem and the
linearized Cauchy quotient isomorphism is used. The group-topology
compatibility in item 5 and the exact Einstein--Hilbert sign/normalization
translation in item 4 remain to be completed. The theorem is at present a
literature-backed synthesis, not yet a novelty claim.

## Linearized Cauchy uniqueness: what Petersen proves and what it does not

Petersen, *On the Cauchy problem for the linearised Einstein equation*
(arXiv:1802.06028), supplies a strong linearized result in globally
hyperbolic vacuum GR (spacetime dimension at least three).

1. **Theorem 4.7: infinitesimal PU for the linearized PDE.**
   If \(h_{\mu\nu}\) solves the linearized vacuum Einstein equation and its
   induced first and second fundamental-form variations on a Cauchy surface
   vanish, then there is a vector field \(V\) such that
   \[
   h_{\mu\nu}=\mathcal L_Vg_{\mu\nu}.
   \]
   The proof solves a normally hyperbolic vector equation for \(V\), then
   applies uniqueness for a linear wave equation to the gauge-adjusted
   perturbation with zero Cauchy data. This proves
   \[
   \ker(\pi_\Sigma|_{\mathrm{Sol}_{\rm lin}})
   \subseteq \operatorname{im}(\mathcal L_g)
   \]
   for the linearized solution space and the paper's finite-energy
   regularity classes.

   **Important distinction:** this is equality with the image of the
   infinitesimal gauge operator. It is not, without further work, equality
   with the tangent space to the orbit of the particular nonlinear group
   \(\mathcal G_0\) used in the work note. To make that identification one
   must (a) identify the tangent space of the actual nonlinear solution
   manifold with the linearized solution space (linearization stability),
   and (b) prove that every vector field \(V\) produced in the theorem is
   an admissible Lie-algebra element of the chosen diffeomorphism group and
   integrates to a smooth path in \(\mathcal G_0\). The latter is not
   automatic on \(M\simeq\mathbb R\times\Sigma\): when \(\Sigma\) is compact,
   spatially compact support places no restriction in time, and an arbitrary
   smooth vector field need not be complete.

   This is a genuine function-space issue, not just a technicality. In the
   standard convenient-manifold model of diffeomorphisms of a noncompact
   manifold, the Lie algebra is the space of compactly supported vector
   fields (Michor, 1980); Petersen's \(V\) is only spatially compact and need
   not be compactly supported in spacetime. If instead one equips the full
   noncompact diffeomorphism group with the compact-open \(C^\infty\)
   functional diffeology, Magnot (2018) proves nonregularity: not every
   smooth path in the Lie algebra integrates to a group path. Thus the
   topology and smooth structure on \(\mathcal G_0\) must be specified, and
   Petersen's \(V\) must be shown to belong to its actual infinitesimal
   orbit image. Isenberg--Marsden's slice theorem supplies a candidate
   spacetime-diffeomorphism group action on spatially compact globally
   hyperbolic Einstein solutions in the CMC setting, but its group model and
   Lie algebra must still be matched explicitly to the function spaces used
   in Petersen's theorem.

2. **Lemma 4.13 and Eqs. (23)--(24): gauge-producing initial data.**
   Petersen decomposes \(V|_\Sigma=N\nu+\beta\) and computes the induced
   first and second fundamental-form variations. This identifies the
   initial-data image of spacetime infinitesimal gauge transformations.
   To obtain the work note's CP, one must additionally match these lapse-shift
   formulas with the Hamiltonian vector fields of the ADM smeared
   constraints. The ADM calculation below performs this comparison; the
   second fundamental-form convention is translated by
   \(K=-\tilde k\).

3. **Theorem 4.18: quotient-level linearized Cauchy isomorphism.**
   The linear solution map between solutions modulo infinitesimal gauge
   solutions and linearized constraint data modulo gauge-producing data is
   an isomorphism of locally convex topological vector spaces. For compact
   \(\Sigma\), Corollary 4.22 gives the quotient a Hilbert structure at finite
   Sobolev order and a Fréchet structure in the smooth case. Lean formalizes
   only the underlying algebraic well-definedness and bijectivity needed to
   derive surjectivity of the unquotiented linearized initial-data map and
   the infinitesimal PU inclusion; it does not formalize the topology or
   the theorem's continuity estimates.

Consequently, the nonlinear local-product portion of H2 and the nonlinear
parameterized H4 are stronger than the pointwise linearized D3B argument
requires. For the actual nonlinear theorem, however, one still needs
linearization stability and the group-integrability identification above.
The remaining smooth nonlinear quotient/local-slice construction is a
separate H5 issue; Isenberg--Marsden's slice theorem is relevant only in its
stated CMC and stratified setting.

## Reduced GR criterion: the hypotheses actually needed for the kernel theorem

The preceding results suggest replacing the original H2/H4 package by a
smaller set of tangent-level inputs. This is a conditional synthesis of
existing theorems, not yet a novelty claim.

Let \(M=I\times\Sigma\), with \(\Sigma\) a compact Cauchy surface, and let
\(\phi\) be a smooth vacuum Einstein solution in a CMC regular stratum. Fix
compatible Sobolev spaces and a precise identity-component diffeomorphism
group \(\mathcal G_0\). Suppose:

1. **Regular constraint surface (H1).** The ADM constraint map
   \(\Phi\) has surjective derivative with split kernel. In the tame
   compact-Cauchy setting, no KIDs imply this submersion property because
   \(D\Phi^*\) is injective and has injective symbol. Carlotto's Theorem 4.6
   then gives linearisation stability. The continuous-dual annihilator
   factorization follows from the Banach open mapping theorem, provided the
   work note's admissible dual is chosen to be the corresponding continuous
   dual (or the multiplier is proved to lie in the permitted space).
2. **Covariant/canonical compatibility (the pullback part of H2).**
   \[
   \Omega_{\rm CPS}=r_\Sigma^*\Omega_{\rm ADM}
   \]
   with boundary potential, orientation, and normalization matched.
   Margalef-Bentabol--Villaseñor supply the general equivalence theorem;
   the Einstein--Hilbert specialization must still be written in the exact
   conventions of the note.
3. **ADM constraint generators (H3/CP).** The Hamiltonian vector fields of
   the smeared Hamiltonian and momentum constraints agree with the
   lapse-shift-induced data variations of spacetime infinitesimal gauge
   transformations. Petersen's Lemma 4.13 gives the latter; the ADM
   hypersurface-deformation calculation performs the comparison.
4. **Linearized Cauchy quotient theorem (Petersen).** Theorem 4.18 gives
   the quotient-level linearized Cauchy isomorphism; Theorem 4.7 gives
   infinitesimal gauge exactness for zero linearized initial data. Combined
   with CP, these imply the two pointwise properties needed by D3B:
   surjectivity of \(D r_\Sigma\) and
   \(\ker D r_\Sigma\subseteq\operatorname{im}\mathcal L_\phi\).
5. **Actual solution tangent and orbit tangent.** No-KID linearisation
   stability identifies the relevant local solution tangent with the
   linearized solution space. The cutoff-flow lemma above identifies
   \(\operatorname{im}\mathcal L_\phi\) with the tangent to the
   \(\mathcal G_0\)-orbit, provided \(\mathcal G_0\) contains the compactly
   supported isotopies constructed there.
6. **Smooth quotient (H5).** A compatible CMC slice theorem and trivial
   full stabilizer give a local smooth quotient. No Killing fields remove
   continuous isotropy, but residual discrete stabilizers must also be
   excluded if the quotient is to be an ordinary manifold rather than an
   orbifold/stratified space.

Under these assumptions, D1--D4 yield
\[
\ker\Omega_{\rm CPS,\phi}
   =T_\phi(\mathcal G_0\cdot\phi),
\]
and the form descends to a unique nondegenerate two-form on the local
quotient. The proof is the three-step D3B argument: use surjectivity of
\(D r_\Sigma\) and pullback compatibility to show that a vector in
\(\ker\Omega_{\rm CPS}\) maps into the ADM constraint radical; use H1/D2
to identify that radical with the constraint-generator image; then use CP
to subtract a spacetime gauge direction and the infinitesimal PU result
to show the remainder is vertical gauge. D1 gives the reverse inclusion.

**What has been removed:** the full nonlinear local-product assertion for
\(r_\Sigma\) in H2 is not needed for this pointwise kernel identity, once
the linearized Cauchy theorem supplies \(D r_\Sigma\)-surjectivity.
The nonlinear, parameterized same-data uniqueness statement H4 is also
not needed; it is replaced by linearization stability, Petersen's
linearized theorem, and the cutoff-flow lemma. The pullback identity in H2
and the smooth quotient/slice requirement H5 remain essential.

This is a useful simplification of the work note, but it is not yet a new
GR theorem: Khavkine's formal reduction and Isenberg--Marsden's CMC
stratified symplectic quotient are close prior results. A publication-level
contribution must show that the precise function-space formulation,
admissible-dual criterion, or a new higher-derivative application goes
beyond those results.

## A concrete regular background: compact Milne quotient

The no-KID regular stratum is nonempty. Let \((\Sigma,h_{-1})\) be a closed
hyperbolic three-manifold, with sectional curvature \(-1\), and set
\[
M=(0,\infty)\times\Sigma,\qquad
g=-dt^2+t^2h_{-1}.
\]
This is the compact-Cauchy Milne quotient. In the warped-product Ricci
formulas, with scale factor \(a(t)=t\) and spatial curvature \(k=-1\),
\[
\operatorname{Ric}_{tt}=-3\frac{\ddot a}{a}=0,\qquad
\operatorname{Ric}_{ij}
=\big(a\ddot a+2\dot a^2+2k\big)(h_{-1})_{ij}=0.
\]
Thus \(g\) is vacuum. Each \(t=\mathrm{const}\) slice is compact, has
\(\tilde g=t^2h_{-1}\), and has pure-trace second fundamental form
\(\tilde k=\pm t h_{-1}=\pm t^{-1}\tilde g\), so its mean curvature is
\(\pm3/t\): the foliation is CMC. The metric is globally hyperbolic because
\(g=t^2(-d(\log t)^2+h_{-1})\) is conformal to the static product metric on
\(\mathbb R\times\Sigma\).

With the audit convention \(K_{ij}=-\frac12\mathcal L_n\tilde g_{ij}\) and
\(n=\partial_t\), the initial data at \(t=t_0\) are
\[
\gamma_{ij}=t_0^2(h_{-1})_{ij},\qquad
K_{ij}=-t_0(h_{-1})_{ij}=-t_0^{-1}\gamma_{ij}.
\]
Consequently
\[
R[\gamma]=-\frac6{t_0^2},\qquad
K=-\frac3{t_0},\qquad
K_{ij}K^{ij}=\frac3{t_0^2}.
\]
The vacuum Hamiltonian constraint is therefore
\(R[\gamma]+K^2-K_{ij}K^{ij}=0\). The momentum constraint also vanishes:
\(K_{ij}-K\gamma_{ij}=(2/t_0)\gamma_{ij}\), whose spatial divergence is zero.
This checks directly that the example lies on the ADM constraint surface,
rather than relying only on the spacetime Ricci calculation.

There are no spacetime Killing fields. The universal cover is the future
Minkowski cone, and its deck group is a torsion-free cocompact lattice
\(\Gamma<SO^+(3,1)\). A Killing field on the cone is the restriction of a
Minkowski Killing field \(X(x)=a+Bx\), with \(a\in\mathbb R^{3,1}\) and
\(B\in\mathfrak{so}(3,1)\). To descend to the quotient it must be
\(\Gamma\)-invariant, hence \(a=\gamma a\) and \(B\gamma=\gamma B\) for
every \(\gamma\in\Gamma\). By the Borel density theorem, \(\Gamma\) is
Zariski dense in \(SO^+(3,1)\); the standard representation has no
nonzero invariant vector and the Lie algebra \(\mathfrak{so}(3,1)\) has
zero centre. Therefore \(a=B=0\). Moncrief's KID theorem then gives
\(\ker D\Phi^*=0\) on every compact Cauchy slice.

The stabilizer in the identity component of the spacetime diffeomorphism
group is also trivial. A time-orientation-preserving spacetime isometry
preserves the CMC value \(\pm3/t\), hence preserves each \(t\)-slice.
Write it as \(F(t,x)=(t,\varphi_t(x))\). The vanishing of the pulled-back
\(dt\,dx\) term forces \(\partial_t\varphi_t=0\), so the same spatial
isometry \(\varphi\in\operatorname{Isom}(\Sigma,h_{-1})\) acts on every
slice. If the spacetime isometry is isotopic to the identity, projection
of that isotopy to \(\Sigma\) shows that \(\varphi\) is homotopic to the
identity; Mostow rigidity forces \(\varphi=\mathrm{id}\). Thus there is no
residual discrete stabilizer inside \(\mathcal G_0\), even though the full
isometry group of \(\Sigma\) need not be trivial.

This gives a concrete background on which the analytic regularity and
stabilizer conditions are simultaneously satisfied. The remaining
qualification is the same as above: the smooth structure/topology on the
spacetime diffeomorphism group used by the CMC slice theorem must be checked
against the compact-open jointly smooth cutoff isotopies used to represent
arbitrary infinitesimal gauge fields.

## Principal-symbol check for the vacuum constraint adjoint

For the vacuum constraints on a compact \(n\)-dimensional Cauchy surface,
\[
\mathcal H(\gamma,K)=R[\gamma]+K^2-K_{ij}K^{ij},\qquad
\mathcal M_i(\gamma,K)=\nabla^j(K_{ij}-K\gamma_{ij}),
\]
the formal adjoint \(D\Phi^*(N,X)\) is a mixed-order
(Douglis--Nirenberg) overdetermined elliptic system: the lapse enters at
order two and the shift at order one. Its mixed principal symbol is
triangular in \(N\) and \(X\). Up to an overall sign and nonzero numerical
factors, the lapse symbol in the metric component is
\[
\sigma_\zeta(D_\gamma\mathcal H)^*N
=N(\zeta_i\zeta_j-|\zeta|_\gamma^2\gamma_{ij}),
\]
and the shift symbol in the \(K\)-component is
\[
\sigma_\zeta(D_K\mathcal M)^*X
=\zeta_{(i}X_{j)}-\gamma_{ij}\zeta^kX_k .
\]
For \(\zeta\ne0\), if the latter vanishes, taking its trace gives
\((1-n)\zeta\cdot X=0\). For \(n\ge2\), this implies
\(\zeta\cdot X=0\); contracting the remaining equation with \(\zeta^i\)
then gives \(|\zeta|^2X_j=0\), hence \(X=0\). With \(X=0\), vanishing of
the lapse symbol forces \(N=0\), because
\(\zeta_i\zeta_j-|\zeta|^2\gamma_{ij}\ne0\) for \(n\ge2\).
Thus the principal symbol of the coupled overdetermined operator
\(D\Phi^*\) is injective.

On closed \(\Sigma\), this injective-symbol ellipticity gives the standard
Sobolev elliptic estimate and closed range for \(D\Phi^*\) in compatible
Sobolev scales. If there are no KIDs, then \(\ker D\Phi^*=0\). In a
compatible Hilbert realization, the closed-range theorem gives
\(\operatorname{ran}D\Phi\) closed, while
\((\operatorname{ran}D\Phi)^\perp=\ker D\Phi^*=0\) makes it dense.
Therefore \(D\Phi\) is surjective; the corresponding elliptic splitting
gives a split kernel. This is the analytic mechanism behind H1 and the
constraint-map linearization-stability criterion. The precise Sobolev
indices and dual identifications are still to be fixed for the chosen
canonical phase space; the symbol calculation alone does not choose them.

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

1. Fix the precise Sobolev spaces for ((\gamma,K)), the constraint values,
   and the admissible dual; complete the elliptic closed-range argument in
   those spaces and prove the continuous-dual annihilator identity.
2. Finish the ADM sign/normalization conversion to the work-note convention
   \(\iota_{X_H}\Omega=-\delta H\), including the exact lapse-shift map.
3. The full nonlinear H2 submersion/local-product statement and nonlinear
   parameterized PU remain unproved. They are not needed for the
   pointwise tangent-level D3B identity once Marsden's no-Killing theorem,
   Petersen's quotient Cauchy theorem, CP, and the cutoff-flow lemma are
   combined.
4. Specialize the general covariant/canonical symplectic-equivalence theorem
   to the chosen Einstein--Hilbert potential and verify the exact \(16\pi G\)
   normalization and sign convention used in the note.
5. For H5, identify the precise smooth structure on the spacetime
   diffeomorphism group in Isenberg--Marsden with the compact-open
   jointly-smooth cutoff isotopies. The CMC slice theorem is the right
   solution-space result, but this group-topology match must be stated rather
   than assumed.

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
- A. E. Fischer and J. E. Marsden, “Linearization stability of nonlinear partial differential equations,” *Proc. Sympos. Pure Math.* **27** (1975), 219--263.
- G. D. Mostow, *Strong Rigidity of Locally Symmetric Spaces*, Annals of Mathematics Studies **78**, Princeton University Press (1973).
- A. Borel, “Density properties for certain subgroups of semisimple groups without compact components,” *Annals of Mathematics* **72** (1960), 179--188.
- J. E. Marsden, *Lectures on Geometric Methods in Mathematical Physics*, Lecture 9, Theorems 9.1 and 9.3 (original lectures 1979; online version modified 22 July 2009), https://www.cds.caltech.edu/~marsden/volume/LGMMP/lgmmp.pdf.
- O. L. Petersen, “On the Cauchy problem for the linearised Einstein equation,” arXiv:1802.06028 (2018), especially Theorems 4.7 and 4.18, Lemma 4.13, and Corollary 4.22.
- P. W. Michor, “Manifolds of smooth maps, II: The Lie group of diffeomorphisms of a non-compact smooth manifold,” *Cahiers de topologie et géométrie différentielle catégoriques* **21** (1980), 63--86.
- J.-P. Magnot, “The group of diffeomorphisms of a non-compact manifold is not regular,” *Demonstratio Mathematica* **51** (2018), 8--16, DOI: 10.1515/dema-2018-0001; arXiv:1101.2370.
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

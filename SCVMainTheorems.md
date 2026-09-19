# Several Complex Variables: mathematical coverage and proof status

This project develops classical analysis on open subsets of finite-dimensional complex
spaces, with Banach-space targets wherever the statements allow. In the order of the
catalogue below, it covers: Cauchy and Taylor theory on polydiscs, the Cauchy–Riemann
equations, the identity and maximum principles, and the Cauchy–Pompeiu identity with the
Cauchy transform (A); locally uniform convergence, Montel's and Vitali's theorems, and
holomorphic function spaces (B); the inverse and implicit mapping theorems (C); Reinhardt
geometry, logarithmic convexity, power series, Laurent expansion, and continuation from
Reinhardt and circular domains (D); the Hartogs phenomena, namely Hartogs–Taylor and
Hartogs–Laurent expansion, extension from Hartogs figures, Hartogs' unrestricted
separate-holomorphy theorem, removable singularities, and the compact-hole extension
theorem (E); elementary analytic sets and the two Riemann extension theorems (F); analytic
germs, Weierstrass division and preparation, Noetherianity, and unique factorization (G);
zero-set geometry, injective holomorphic maps, Cartan uniqueness, and circular rigidity (H);
common extension domains, holomorphic convexity, Thullen's lemma, the Cartan–Thullen
equivalences, and Bochner's tube theorem (I); subharmonic and plurisubharmonic functions,
the Levi form, pseudoconvexity, and Levi's theorem with peak functions (J); Runge pairs,
Runge domains, and polynomial hulls (K).

The catalogue contains **65 principal results or closely related theorem groups**, and
every one of them is **proved**: each stated theorem has a checked proof relying only on the
project and on the existing mathematical library, with no admitted statements. The catalogue
follows the main mathematical dependencies: local analysis precedes convergence and extension;
local mapping theory precedes regular zero sets; division and preparation precede factorization
and the later geometric results; holomorphic convexity precedes pseudoconvexity. Independent
branches are grouped by subject. This is a mathematical overview, not an inventory of all
supporting lemmas.

Named theorems outside the present scope are the Oka–Weil approximation theorem and the
one-variable Runge theorem for rational approximation; see the closing section.

## Definitions and mathematical conventions

Conventions follow Mathlib where applicable, while the choice of mathematical
material draws on the project's several reference texts.

### Ambient spaces, holomorphy, and domains

Unless specified otherwise, the source is a finite-dimensional complex normed
space $E$, often written as $\mathbb C^n$ in coordinate formulas below, and the target
$F$ is a complex Banach space. Scalar-valued statements are marked explicitly.
Finite coordinate sets need not be ordered. Dimension zero is included whenever
the assertion makes sense; lower dimension bounds are stated when essential.

**Holomorphic** means complex Fréchet-differentiable at every point of an open
set. **Analytic** means locally representable by a convergent power series of
continuous homogeneous polynomials. In the finite-dimensional-source,
Banach-target setting used here, their equivalence is proved. Coordinate Taylor
series use multi-indices $\alpha$, with

$$
z^\alpha=\prod_{j=1}^n z_j^{\alpha_j},\qquad
\lvert\alpha\rvert=\sum_j\alpha_j,\qquad
\alpha!=\prod_j\alpha_j!.
$$

A **domain**, in this document, is a nonempty connected open set. The underlying
results impose openness, connectedness, and nonemptiness separately. Many local
or extension statements apply to arbitrary open sets, including disconnected
or empty ones.

The default coordinate norm is the **supremum norm**. Its balls are equal-radius
polydiscs. A polydisc with separate positive radii is

$$
P(a;r)=\lbrace z:\lvert z_j-a_j\rvert<{r_j}\text{ for every }j\rbrace.
$$

Its distinguished boundary is the product torus
$T(a;r)=\lbrace z:\lvert z_j-a_j\rvert=r_j\text{ for every }j\rbrace$, rather than the entire
topological boundary. Euclidean balls are treated using a Hermitian norm and
are explicitly identified as such. The Hermitian inner product is conjugate-linear
in its first argument and linear in its second.

### Reinhardt, Hartogs, and circular geometry

The geometric properties below do **not** by themselves assert openness or
connectedness.

- A set $U\subseteq\mathbb C^n$ is **Reinhardt** if membership is unchanged by
  independent rotations of the coordinates, equivalently by replacing a point
  with another having the same coordinate moduli.
- It is **complete Reinhardt** if $z\in U$ and $\lvert w_j\rvert\le \lvert z_j\rvert$ for every
  $j$ imply $w\in U$. This implies Reinhardt symmetry. A nonempty such set
  contains the origin.
- Its **logarithmic image** is
  $\lbrace (\log\lvert z_1\rvert,\ldots,\log\lvert z_n\rvert):z\in U,\ z_j\ne0\text{ for all }j\rbrace$.
  Classical logarithmic convexity means convexity of this image.
- To include zero coordinates, the project also uses the **modulus trace**
  $M(U)=\lbrace (\lvert z_1\rvert,\ldots,\lvert z_n\rvert):z\in U\rbrace\subseteq[0,\infty)^n$.
  Its geometric convexity means closure under
  $(r,s)\mapsto(r_j^t s_j^{1-t})_j$, for $0\le t\le1$.
  The endpoint convention $0^0=1$ gives the expected endpoints; for interior
  weights a zero in either input produces a zero in that coordinate. This
  property is equivalent to classical logarithmic convexity for open complete
  Reinhardt sets, but the two definitions are kept distinct in general.
- The **complete Reinhardt hull** is the smallest complete Reinhardt set
  containing $U$. The **logarithmic Reinhardt hull** is the smallest Reinhardt
  set containing $U$ whose modulus trace is geometrically convex. A **partial
  Reinhardt hull** allows coordinatewise shrinking only in selected coordinates.
- A **Hartogs set** in $E\times\mathbb C$ is invariant under rotations of the
  last coordinate: $(z,w)\in U\Rightarrow(z,e^{i\theta}w)\in U$. Its base is
  the projection to $E$, and its fiber at $z$ is $U_z=\lbrace w:(z,w)\in U\rbrace$.
  It is **complete Hartogs** if each fiber is closed under decreasing modulus.
  **Connectedness of the nonempty fibers is a separate property**, not part of
  the definition of a Hartogs set. Open nonempty complete fibers are centered
  discs, possibly the whole plane. Open connected rotationally invariant fibers
  can also be annuli or punctured discs.
- A set is **circular** if it is invariant under simultaneous rotation
  $z\mapsto e^{i\theta}z$. It is **balanced** if $\lambda U\subseteq U$
  for every $`\lvert\lambda\rvert\le1`$. These are different from independent-coordinate
  Reinhardt symmetry. The balanced hull is the smallest balanced containing set.

### Holomorphic hulls and local continuation

For $K\subset U$, its **holomorphic hull relative to $U$** is

$$
{\hat{K}_U}=\lbrace z\in U: \lvert f(z)\rvert\leq{\sup_K\lvert f\rvert}\text{ for all }f\in\mathcal O(U)\rbrace.
$$

The definition uses all real upper bounds instead of a real supremum, so it
also handles empty sets and unbounded functions. In particular,
$`{\hat{\varnothing}_U=\varnothing}`$. A compact set is holomorphically convex
relative to $U$ when its hull equals itself. An open set $U$ is holomorphically
convex when every compact $K\subset U$ has compact hull. These notions differ
from the logarithmic Reinhardt hull used earlier.

The **domain-of-holomorphy property** excludes connected open continuation sets
$V\not\subset U$ with a fixed nonempty open overlap $W\subset U\cap V$ to which
every function in $\mathcal O(U)$ can continue. Agreement is required on $W$,
not on all components of $U\cap V$. A **domain of existence** for a specified
function excludes the same local continuations for that one function.
Connectedness of $U$ is not built into either predicate; their theorems cover
disconnected open sets as well.

Boundary distance is distance to the complement, with values in $[0,\infty]$.
This treats the whole ambient space and empty compact sets without exceptions.
In coordinate spaces its metric is the supremum metric, giving polydisc radii.
The **tube over $\Omega\subset\mathbb R^n$** is
$T_\Omega=\lbrace z\in\mathbb C^n:\mathrm{Re}z\in\Omega\rbrace$.

### Maps, germs, and analytic sets

A **biholomorphic map** is a bijection between open sets whose map and inverse
are holomorphic. Connectedness is not built into this notion.

The **ring of scalar analytic germs** at $a$, denoted $\mathcal O_{E,a}$, identifies
functions that agree on some neighborhood of $a$. Its maximal ideal consists
of germs vanishing at $a$. The **total order** of a germ is the least total
degree of a nonzero Taylor coefficient, with order $\infty$ for the zero
series. This differs from its order on a specified coordinate axis.

Writing the coordinates as $(z,w)\in\mathbb C^{n-1}\times\mathbb C$, a germ
is **regular of order $d$ in $w$** if the one-variable germ $w\mapsto f(0,w)$
has finite order $d$. A **distinguished polynomial** has the form

$$
W(z,w)=w^d+a_{d-1}(z)w^{d-1}+\cdots+a_0(z),\qquad a_j(0)=0,
$$

with holomorphic coefficient germs. Degree zero is permitted and gives $W=1$.
For germs, **relatively prime** means that every common divisor is a unit.
It does not mean that the two germs generate the unit ideal.

An **analytic subset of an open set $U$** is a subset $A\subseteq U$ that,
near every point of $U$, is the common zero set of finitely many scalar
holomorphic functions. Relative closedness is a consequence. A **regular point
of codimension $q$** is a point at which a local biholomorphic change of
coordinates takes the set to a complex linear subspace of codimension $q$.
The regular locus allows any such codimension; the singular locus is its
complement in $A$.

For the extension theory, the project uses an explicit **slice condition for
codimension at least $q$**: through every $a\in A$ there is an injectively
parametrized affine complex $q$-plane whose intersection with $A$ is locally
just $a$. This is kept separate from analyticity. It is the precise hypothesis
of the general codimension-two theorem below; a general theory of local analytic
dimension has not been developed.

### Plurisubharmonic functions, Levi geometry, and approximation

A real function $u$ on an open set $U\subset\mathbb C$ is **subharmonic** if it is upper
semicontinuous on $U$ and has the local submean property at every point: for all sufficiently
small $r>0$, $u$ is integrable on the circle of radius $r$ around the point and $u(a)$ is at
most its average over that circle. A real function on an open subset of $E$ is
**plurisubharmonic** if it is upper semicontinuous and its restriction to every complex line
$t\mapsto a+tw$ is subharmonic on the corresponding open parameter set. No smoothness is
assumed; the $C^2$ criteria by the Laplacian and by the Levi form are theorems.

The **Levi form** of a real $C^2$ function $\rho$ at $a$ in the direction $w$ is

$$
L_\rho(a;w)=\tfrac14\bigl(D^2\rho(a)(w,w)+D^2\rho(a)(iw,iw)\bigr),
$$

which in coordinates is the complex Hessian
$`{\sum_{j,k}\frac{\partial^2\rho}{\partial z_j\thinspace\partial\bar{z}_k}\thinspace
w_j\bar{w}_k}`$.
A **local defining function** for an open set $U$ at a boundary point $p$ is a real $C^2$
function $\rho$ on an open neighborhood $V$ of $p$ with $\rho(p)=0$, $D\rho(p)\ne0$ and
$U\cap V=\lbrace \rho<0\rbrace\cap V$; the set $U$ has **$C^2$ boundary** if every boundary point has one.
The **complex tangent space** at $p$ consists of the $w$ with $D\rho(p)w=D\rho(p)(iw)=0$. The
set $U$ is **Levi pseudoconvex at $p$** if for every local defining function the Levi form is
positive semidefinite on the complex tangent space, **strictly** so if it is positive definite
there, and **Levi pseudoconvex** if it is Levi pseudoconvex at every boundary point.
Quantifying over all defining functions makes the definition independent of the choice by
fiat; that one defining function suffices is then a theorem.

An open set is **pseudoconvex** if it carries a continuous plurisubharmonic exhaustion
function, one whose sublevel sets within the set are compact. The **continuity principle** for
affine analytic discs asserts that along a continuous family of closed affine discs whose
boundary circles stay in the set, with the initial disc in the set, every disc of the family
lies in the set. **Hartogs convexity** of an open subset of $E'\times\mathbb C$ asserts that
whenever a Hartogs cylinder over an open preconnected base, with full disc fibers over a
nonempty open part of the base, lies in the set, so does the filled cylinder.

The **polynomial hull** of $K\subset\mathbb C^n$ consists of the points at which every
polynomial is bounded by each of its bounds on $K$, in the same real-bound form as the
holomorphic hull, and $K$ is **polynomially convex** if it equals its hull. A pair of sets
$U\subseteq V$ is a **Runge pair** if every holomorphic function on $U$ is approximated within
any $\varepsilon>0$ on every compact subset of $U$ by a holomorphic function on $V$; an open
$U\subset\mathbb C^n$ is a **Runge domain** if the approximants may be taken to be polynomials.
The domain-of-holomorphy property is not part of these definitions.

For a real-linear map $L$ from a complex normed space to a complex Banach space and a
direction $v$, the **antiholomorphic part** of $L$ along $v$ is
$`{{\tfrac12}\bigl(Lv+i\thinspace L(iv)\bigr)}`$.
A real-linear map is complex-linear exactly when all its antiholomorphic parts vanish.

## A. Local analysis and differential calculus

### 1. Cauchy's integral formula on a polydisc

For $f$ holomorphic on a neighborhood of a closed polydisc and $z\in P(a;r)$,

$$
f(z)=\frac{1}{(2\pi i)^n}\int_{T(a;r)}
\frac{f(\zeta)}{\prod_j(\zeta_j-z_j)}\thinspace d\zeta_1\cdots d\zeta_n.
$$

The proved version requires only continuity on the closed polydisc and
analyticity of each coordinate slice at its points. The iterated integrals and
the formula are Banach-valued. Expansion of the Cauchy kernel supplies local
power-series representations.

### 2. Joint analyticity with continuity or local bounds

A separately analytic function on an open subset of $\mathbb C^n$ is jointly
analytic if it is continuous, or if it is locally bounded. The bounded version
includes quantitative local Lipschitz estimates obtained from one-variable
Cauchy estimates. Both assertions allow Banach targets. The unrestricted
separate-analyticity theorem is distinguished in item 27.

### 3. Holomorphic and analytic are equivalent

For an open subset of a finite-dimensional complex normed space and a complex
Banach target, complex Fréchet differentiability throughout the set is equivalent
to local convergent power-series representation. The result is available both
in coordinates and independently of a chosen basis.

### 4. Cauchy–Riemann equations, derivatives, and chain rule

On an open coordinate set, holomorphy is equivalent to real Fréchet
differentiability together with the coordinate Cauchy–Riemann equations. The
antiholomorphic Wirtinger derivatives vanish, and the holomorphic Wirtinger
derivatives agree with complex coordinate derivatives. For holomorphic maps,
mixed derivatives commute, remain holomorphic, and determine the Fréchet
derivative. Composition satisfies

$$
D(g\circ f)(z)=Dg(f(z))\circ Df(z),\qquad
J(g\circ f)(z)=Jg(f(z))Jf(z).
$$

### 5. Multi-index Taylor expansion and Cauchy estimates

On a polydisc, the Taylor coefficients equal the torus Cauchy coefficients:

$$
c_\alpha=\frac{\partial^\alpha f(a)}{\alpha!},\qquad
\lVert\partial^\alpha f(a)\rVert\le
\alpha!\thinspace M\prod_j r_j^{-\alpha_j}
$$

when $f$ is holomorphic near the closed polydisc and bounded there by $M$.
The Taylor series represents $f$ in the interior, converges absolutely there
and uniformly on every strictly smaller closed polydisc, and admits explicit
geometric bounds for finite remainders. Coefficients are independent of the
admissible radii.

### 6. Identity and real-parameter uniqueness theorems

Two Banach-valued holomorphic maps on a domain that agree on a nonempty open
subset agree everywhere. Agreement as germs at one interior point also suffices.
There is additionally an entire-function theorem with values in any complex normed space,
without completeness: agreement on all vectors
of strictly positive real coordinates determines the function on $\mathbb C^n$.
The general several-variable identity theorem does not use mere accumulation
of agreement points as its hypothesis.

### 7. Maximum modulus principle

A scalar holomorphic function on a domain is constant if its modulus has a local
maximum at an interior point. The norm version is also proved for maps into
strictly convex complex Banach spaces, with strict convexity understood over
the reals. This target restriction matters: constant norm alone does not force
a holomorphic map into an arbitrary Banach space to be constant.

### 8. Holomorphic dependence of integrals

An integral depending on finitely many complex parameters is holomorphic under
local integrable domination of its parameter derivatives, together with the
appropriate measurability and integrability hypotheses. Differentiation passes
under the integral. Compact integration sets with jointly continuous integrands
and derivatives provide a useful special case. A Banach-valued version instead assumes
local integrable domination of the holomorphic integrand, retaining the stated
derivative-measurability hypothesis.

### 9. The Cauchy–Pompeiu identity and the Cauchy transform

For a compactly supported $C^1$ function $\varphi:\mathbb C\to F$,

$$
\int_{\mathbb C}\frac{1}{w}\thinspace \frac{\partial\varphi}{\partial\bar w}(w)\thinspace dA(w)=-\pi\thinspace \varphi(0).
$$

The antiholomorphic part along a direction $v$ of a real-linear map $L$ is
$\tfrac12(Lv+i\thinspace L(iv))$, and it vanishes for all $v$ exactly when $L$ is complex-linear;
for the real derivative of a function of one complex variable and $v=1$ it is
$\partial/\partial\bar w$. The identity is proved in polar coordinates: along each ray the
integrand is the radial derivative, whose integral is $-\varphi(0)$, and around each circle it
is the angular derivative divided by the radius, whose integral vanishes by periodicity. No
Green or Stokes theorem is used.

The **Cauchy transform** in the first variable of a compactly supported $C^1$ function $g$ on
$\mathbb C\times G$ is $u(z,y)=\pi^{-1}\int w^{-1}g(z-w,y)\thinspace dA(w)$. It is real-differentiable,
its derivative is the transform of the derivative of $g$, by differentiation under the integral
with the locally integrable kernel $w^{-1}$, and it satisfies $`{\partial u/\partial\bar z}=g`$;
the antiholomorphic parameter derivatives pass through the transform, and $u$ vanishes on
every slice on which $g$ vanishes. These are the one-variable ingredients of Ehrenpreis' proof
of the compact-hole theorem in item 31.

## B. Convergence and spaces of holomorphic functions

### 10. Weierstrass convergence theorem and convergence of derivatives

A locally uniform limit of Banach-valued holomorphic functions on an open set
is holomorphic. All fixed mixed coordinate derivatives converge locally
uniformly to the corresponding derivatives of the limit. The results also
support locally uniform sums of holomorphic series. Applied to Taylor sums,
they give termwise mixed differentiation, with locally uniform convergence
of the differentiated expansion.

### 11. Compact-open holomorphic function spaces

For open subsets of arbitrary complex normed spaces, $\mathcal O(U,F)$ is defined as a
complex linear subspace of $C(U,F)$. On finite-dimensional source spaces it is closed, with
the compact-open topology, and is complete for Banach $F$. Evaluation,
restriction, and coordinate differentiation are continuous. Restriction to a
nonempty open subset of a domain is injective; restriction to a dense open
subset is injective without connectedness assumptions.

Surjective restriction under the identity-theorem hypotheses is a continuous
complex-linear equivalence, including Banach-valued targets. The proof uses
Baire’s theorem and successive approximations in the complete compact-open
spaces to establish the Fréchet open-mapping theorem. For scalar functions,
multiplication and restriction give the corresponding algebra structures,
and the restriction algebra isomorphism is continuous in both directions.

### 12. Montel's theorem

A family of holomorphic maps bounded uniformly on every compact subset is
equicontinuous. When the target is finite-dimensional, the family has compact
closure in the compact-open topology. The equicontinuity assertion allows Banach
targets; the compactness assertion retains the finite-dimensional restriction.

### 13. Vitali's theorem

Let $(f_k)$ be holomorphic on a domain, with finite-dimensional target, and
bounded uniformly on every compact subset. If $f_k(z)$ converges for every
$z$ in a nonempty open subset, then the sequence converges locally uniformly
on the whole domain to a holomorphic map. This is the precise convergence-set
hypothesis currently provided, rather than a general formulation for arbitrary
uniqueness sets.

### 14. Holomorphic $L^p$ spaces

For $1\le p\le\infty$, let $A^p(U,F)$ be the subspace of Lebesgue $L^p(U,F)$
whose classes admit holomorphic representatives. Such representatives are
unique everywhere on $U$, a **proved** fact. The local estimate

$$
\sup_{z\in K}\lVert f(z)\rVert\le C_{K,U,p}\lVert f\rVert_{L^p(U)},\qquad K\Subset U,
$$

is **proved** by the polydisc volume mean-value formula and Hölder's inequality.
The volume formula follows by averaging common complex rotations and applying
Fubini. Closedness in $L^p$, Banach completeness, and locally uniform convergence
of representatives under $L^p$ convergence are therefore proved as well.
At $p=2$, a Hilbert target gives a Hilbert space with the integral inner product.
No boundedness, connectedness, or finite-volume assumption is imposed on $U$;
empty coordinate types are included.

## C. Local holomorphic mappings

### 15. Holomorphic inverse mapping theorem

If $f$ is holomorphic near $a$ and $Df(a)$ is an invertible complex-linear
map, then $f$ restricts to a biholomorphism between neighborhoods of $a$
and $f(a)$. Its inverse satisfies

$$
D(f^{-1})(f(a))=Df(a)^{-1}.
$$

Coordinate Jacobian criteria are included. An injective derivative also gives
local injectivity when the finite-dimensional target may have larger dimension.
A biholomorphism with nonempty source forces equality of source and target
complex dimensions.

### 16. Holomorphic implicit mapping theorem and graphs

If $f(z,w)$ is holomorphic near $(a,b)$ and $D_wf(a,b)$ is invertible,
then the nearby level set $f(z,w)=f(a,b)$ is exactly the graph $w=g(z)$
of a unique local holomorphic solution. The derivative is

$$
Dg(a)=-D_wf(a,b)^{-1}\circ D_zf(a,b).
$$

The project includes the zero-set version, a nonvanishing-minor criterion,
and the local graph parametrization. The analytic version also allows suitable
Banach parameter and unknown spaces.

## D. Reinhardt geometry, power series, and continuation from Reinhardt and circular domains

### 17. Complete Reinhardt geometry and hulls

Complete Reinhardt sets have Reinhardt symmetry, and nonempty ones are
path-connected by radial contraction to the origin. Centered polydiscs give
basic examples. Complete and partial Reinhardt hulls have their expected
containment and minimality properties; completion of an open Reinhardt set
preserves openness. These are geometric results independent of extension
theorems for functions.

### 18. Logarithmic convexity including zero coordinates

For an open complete Reinhardt set, convexity of its positive logarithmic image
is equivalent to geometric convexity of its full modulus trace. The latter
includes coordinate hyperplanes and behaves correctly at the interpolation
endpoints. Geometric and logarithmic Reinhardt hulls satisfy minimality,
monotonicity, and idempotence. The logarithmic hull of an arbitrary open Reinhardt
set is open. The proof includes zero coordinates: positive weighted geometric
interpolation is an open map on nonnegative radius vectors, interiors preserve
geometric convexity, and geometric convex hulls preserve openness.

If an open Reinhardt set contains the origin, its logarithmic hull contains its
complete Reinhardt hull. This geometric inclusion is also **proved**, independently
of the analytic extension theorems.

### 19. Geometry and analyticity of power-series convergence

For coefficients $c_\alpha\in F$, define

$$
A_c=\left\lbrace z:\sum_\alpha\lVert c_\alpha\rVert\thinspace \lvert z^\alpha\rvert<\infty\right\rbrace,
\qquad D_c=\mathrm{int}A_c.
$$

Both the absolute-convergence set and its interior are complete Reinhardt and
have geometrically convex moduli. On $D_c$, the series converges locally
uniformly and its sum is holomorphic. The definition of $D_c$ excludes merely
boundary convergence and permits an empty convergence domain. No convergence
hypothesis on the original coefficient family is needed to state these results.

### 20. Taylor representation and logarithmic extension on complete Reinhardt sets

Every Banach-valued holomorphic function on an open complete Reinhardt set is
represented there by its Taylor series at the origin, with absolute convergence
and with the set contained in the interior of the series' absolute-convergence
set. The sum is analytic at every point of the logarithmic Reinhardt hull and
agrees with the original function. This proof does not require the
Laurent theorem or the general hull-openness theorem in item 18.

### 21. Characterization of power-series convergence domains: converse

Every nonempty open complete logarithmically convex Reinhardt set is the exact
convergence domain $D_c$ of a scalar power series. Bounded and unbounded sets
are included, as are empty coordinate types. Together with item 19 this proves
the classical characterization often attributed to Hartogs. Monomial separation
first proves holomorphic convexity of the prescribed domain. Cartan–Thullen
then supplies a nonextendable function, whose Taylor series at zero has exactly
that convergence domain.

### 22. Multivariable Laurent expansion and approximation

On a Reinhardt domain, every Banach-valued holomorphic function has a unique
Laurent expansion indexed by $\mathbb Z^n$, converging absolutely and locally
uniformly. Torus integrals give its coefficients independently of the admissible
torus. If the domain meets $z_j=0$, coefficients with negative $j$-th exponent
vanish. The proof combines successive one-variable annular expansions with
summable geometric bounds from finitely many coefficient tori. It includes
coordinate hyperplanes and dimension zero.

Approximation on compact subsets by finite Laurent sums is **proved**, as are
continuity and linearity of the fixed-torus coefficient functionals. The continuous
holomorphic projection operators, their idempotence and mutual annihilation, and
convergence of finite partial sums are also **proved**. These are Laurent
approximation results on Reinhardt sets.

### 23. Continuation from more general Reinhardt domains

If a Reinhardt domain meets every coordinate hyperplane, its holomorphic
functions extend by a power series to its logarithmic hull. The intersection
points with the different hyperplanes need not coincide.

If the domain contains the origin, its holomorphic functions extend to its
complete Reinhardt hull. When only selected coordinate hyperplanes are met,
they extend to the associated partial Reinhardt hull. These results now follow
from the completed Laurent theorem and the geometric hull results in item 18.
The supporting local uniform convergence and analyticity theorems for coefficient
series use a finite box of radii in the original domain to provide a common
summable bound. Forbidden negative coefficients vanish, so shrinking the selected
coordinates introduces no singularities.

### 24. Homogeneous expansion and continuation from circular domains

For a circular domain containing the origin, the homogeneous Taylor expansion
of a Banach-valued holomorphic function converges locally uniformly
on the domain and on its balanced hull, defining an analytic extension there.
Cauchy projections under simultaneous rotation identify the homogeneous terms;
compact bounds and strict radial contractions give geometric majorants on the
balanced hull. The identity theorem identifies the sum with the original function
and proves uniqueness of the extension. Zero-dimensional source spaces are included.

## E. Hartogs phenomena and removable singularities

### 25. Hartogs–Taylor and Hartogs–Laurent expansions

On an open complete Hartogs set, a holomorphic $f(z,w)$ has the expansion

$$
f(z,w)=\sum_{k\ge0}a_k(z)w^k,\qquad
a_k(z)=\frac{1}{k!}\frac{\partial^k f}{\partial w^k}(z,0),
$$

with coefficients holomorphic on the projected base. This Taylor expansion is
**proved**, including pointwise summation and uniform convergence on compact
subsets. Joint holomorphy of fiber derivatives and Cauchy estimates on local
product neighborhoods give a summable geometric bound.

On an open Hartogs set whose nonempty fibers are connected, the analogous
integer-indexed Laurent expansion, with coefficients holomorphic on the whole
base, is **proved** using the independent one-variable Laurent theory.
Cauchy's formula on an annulus gives the one-variable expansion and independence
of radius. Negative coefficients vanish on fibers containing zero. Fixed-circle
integrals give holomorphic dependence on the base; inner and outer circles give
geometric majorants for the negative and nonnegative terms, establishing local
uniform convergence. Both formulations allow Banach targets, disconnected bases,
zero-dimensional parameter spaces, and the empty set.

### 26. Extension from a Hartogs cylinder or figure

Let $D$ be a domain, let $D_0\subseteq D$ be nonempty and open, and let
$0\le\rho<R$. Every Banach-valued holomorphic function on

$$
`\bigl(D\times\lbrace w:\rho<\lvert w\rvert<R\rbrace\bigr)
\thickspace\cup\thickspace
\bigl(D_0\times\lbrace w:\lvert w\rvert<R\rbrace\bigr)`
$$

extends holomorphically to $D\times\lbrace \lvert w\rvert<R\rbrace$. No boundedness assumption on
the function is needed. The standard Hartogs-figure theorem and uniqueness of
its extension are proved consequences. These results do not depend on the
fiber-expansion theorems in item 25.

### 27. Hartogs' unrestricted separate-holomorphy theorem

A Banach-valued function on an open subset of $\mathbb C^n$, analytic in each
coordinate separately, is jointly analytic without any continuity or local
boundedness hypothesis. The statement holds for arbitrary finite coordinate
sets, including the empty and singleton cases. The versions with continuity or
local boundedness in item 2 are used in the proof.

The proof is by induction on the number of coordinates, splitting off one fiber
coordinate. Its ingredients are proved independently:

- Baire's theorem gives a uniformly bounded open cylinder from separate continuity
  and a compact second factor. Joint analyticity on a thin cylinder whose fiber
  disc lies close to the given point then follows from the locally bounded Osgood
  theorem, since the base slices are jointly analytic by the induction hypothesis.
- Every positive power of a holomorphic norm satisfies circle and ball submean
  inequalities, including powers below one and arbitrary complex normed targets.
  The ball inequality holds on closed balls of any finite-dimensional complex
  normed space with an additive Haar volume, by averaging unit complex rotations.
- Hartogs' growth lemma turns pointwise eventual upper bounds for these powers
  into bounds uniform near the center, assuming a common bound on a closed ball
  of such a space. The exponents may vary, as required for roots of Taylor
  coefficients.
- Hartogs' fiber extension lemma: a function jointly analytic on a thin cylinder
  over an open base, whose fiber slices are analytic on a larger disc, is locally
  bounded on the larger cylinder. The fiber Taylor coefficients are analytic in the
  base variable by Cauchy's formula on a small circle, their roots are bounded
  pointwise by Cauchy's estimates on the large disc, and Hartogs' lemma makes the
  bound uniform, so the fiber Taylor series has a geometric majorant.

The induction is organized with Mathlib's empty-option induction on finite types;
reindexing along a bijection of coordinate types is proved separately.

### 28. Removal of isolated singularities in dimension at least two

If $\dim_{\mathbb C}E\ge2$, $U\subseteq E$ is open, and $a\in U$, every
Banach-valued holomorphic function on $U\mathbin{\backslash}\lbrace a\rbrace$ extends
holomorphically across $a$. Neither boundedness nor connectedness of $U$
is assumed. The proof uses concrete Hartogs continuation, independently of
the general compact-hole theorem below.

### 29. Scalar zero sets have no isolated points in dimension at least two

If a scalar function is holomorphic near $a$, vanishes at $a$, and the
source dimension is at least two, then every punctured neighborhood of $a$
contains another zero. The proof applies isolated-singularity removal to a
putative reciprocal. This is a statement about one scalar equation; several
simultaneous equations can have isolated common zeros.

### 30. First Riemann extension theorem and continuous removal

Let $g$ be scalar holomorphic on an open set $U$, with nonzero germ at
every point. A Banach-valued holomorphic function on $U\mathbin{\backslash} Z(g)$
that is locally bounded near $Z(g)$ extends uniquely to $U$. In a domain,
it suffices that $g$ is not identically zero. Singular zero sets are allowed.
The local theorem also extends to relatively closed exceptional sets locally
contained in such zero sets.

A separate proved result says that a continuous function on an open set,
holomorphic off a countable subset, is holomorphic everywhere. That countable
exceptional set need not be closed or discrete.

### 31. Hartogs' compact-hole extension theorem

In complex dimension at least two, let $U$ be open and $K\subseteq U$ compact, with
$U\mathbin{\backslash} K$ connected. Every Banach-valued holomorphic function on $U\mathbin{\backslash} K$
extends holomorphically to $U$. Connectedness of $U$ itself is not assumed. Stated extensions from spherical shells and exteriors of
closed balls are consequently proved as well.

The proof is Ehrenpreis' argument, using the Cauchy–Pompeiu identity and the Cauchy transform
of item 9. After a linear change of coordinates $E\cong\mathbb C\times G$, a smooth cutoff
$\varphi$ equal to one near $K$ with compact support in $U$ gives $F_0=(1-\varphi)f$, extended
by zero across $K$.
Its antiholomorphic derivatives along all directions are compactly supported and commute,
by symmetry of the second derivative, so $F_0-u$ with $u$ the Cauchy transform of
$`{\partial F}_0/{\partial\bar z}_1`$ has complex-linear real derivative and is holomorphic
on $U$.
On the open set of points whose $G$-coordinate lies outside the projection of the support of
$\varphi$, nonempty because a nonempty open subset of $G$ is not compact, both $F_0=f$ and
$u=0$; the identity principle on $U\mathbin{\backslash} K$ concludes. No Bochner–Martinelli
kernel is used.

## F. Elementary analytic sets

### 32. Basic operations, thinness, and removal for analytic sets

Analytic subsets are relatively closed and are stable under finite unions,
finite intersections, products, holomorphic inverse images, restriction, and
biholomorphic changes of coordinates. A proper analytic subset of a domain
has empty interior and dense connected complement.

More generally, on any open $U$, an analytic subset with empty interior
locally lies in a scalar zero set with nonzero defining germ. Consequently,
locally bounded Banach-valued holomorphic functions on its complement extend
uniquely across it, by item 30.

### 33. Regular points and full-rank defining equations

A point $a\in A$ is regular of codimension $q$ precisely when, locally,

$$
A=\lbrace f_1=\cdots=f_q=0\rbrace,\qquad
\mathrm{rank}D(f_1,\ldots,f_q)(a)=q
$$

for some choice of holomorphic defining equations. The inverse mapping theorem
gives the flattening coordinates. The regular locus is relatively open, and
the singular locus is relatively closed. The rank criterion is existential:
an arbitrary redundant or nonreduced presentation need not have full rank at
a regular point of the underlying set.

### 34. Removal across a coordinate plane of codimension two

For an arbitrary open subset of $P\times\mathbb C\times\mathbb C$, a
Banach-valued holomorphic function off the plane $w_1=w_2=0$ extends across
that plane. The plane is verified to be analytic and to satisfy the
two-dimensional slice condition. The removal proof uses the proved Hartogs
cylinder theorem directly.

### 35. Second Riemann extension theorem

Let $A$ be an analytic subset of an open $U$ satisfying the slice condition
for codimension at least two. Every Banach-valued holomorphic function on
$U\mathbin{\backslash} A$ extends uniquely to $U$, with no boundedness assumption.
Around an isolated two-dimensional slice, compactness supplies nearby Hartogs
figures avoiding $A$. Hartogs continuation and connectedness of the complement
of a proper analytic subset give a local holomorphic extension. Its continuity
proves automatic local boundedness, so global existence follows from item 32.
Uniqueness follows by density. The scalar restriction-algebra isomorphism across
$A$ is therefore also proved. Connectedness of $U$ is unnecessary.

## G. Germs, Weierstrass theory, and elementary local algebra

### 36. The local integral domain of analytic germs

The scalar germ ring $\mathcal O_{E,a}$ is a local integral domain. A germ is a
unit exactly when its value at $a$ is nonzero; the unique maximal ideal is
the kernel of evaluation, and the residue field is $\mathbb C$. Analytic maps
induce pullbacks on germs. In dimension zero, the germ ring itself is $\mathbb C$.
These facts do not rely on Noetherianity or Weierstrass preparation.

### 37. Coordinate normalization and roots of units

Translation and invertible complex-linear changes of coordinates identify the
corresponding germ rings; analytic homeomorphisms analytic in both directions
give the analogous pullback isomorphisms. A nonzero scalar germ in positive
dimension can be made regular in the last coordinate by an invertible linear
change. One change works simultaneously for any finite family of nonzero
germs. Every unit germ has a $k$-th root for each positive integer $k$.

### 38. Taylor determination and order of germs

The Taylor-series map on scalar germs is injective and preserves addition and
multiplication. Analytic coordinate differentiation agrees with formal partial
differentiation of the Taylor series. In particular,

$$
\mathrm{ord}(f)=\infty\iff f=0,\qquad
\mathrm{ord}(f)=0\iff f\text{ is a unit}.
$$

The sum inequality
$\mathrm{ord}(f+g)\ge\min(\mathrm{ord}(f),\mathrm{ord}(g))$,
equality for unequal orders, and the product formula

$$
\mathrm{ord}(fg)=\mathrm{ord}(f)+\mathrm{ord}(g)
$$

are **proved**, including zero germs and zero-dimensional coordinate spaces.
Analytic pullback cannot lower total order, including maps between different
dimensions. Applying this to a coordinate map and its analytic inverse proves
invariance under analytic coordinate changes. In positive dimension, an
invertible linear change makes the order on the last axis equal to total
order, strengthening item 37's finite-order normalization. This includes units
and follows by evaluating the first nonzero homogeneous Taylor polynomial
in a suitable direction. Polynomial evaluation has the expected Taylor series,
and total order in one coordinate agrees with scalar analytic order.

### 39. Division by a coordinate power

On a product polydisc, a scalar holomorphic $g$ has a unique decomposition

$$
`g(z,w)=w^d q(z,w)+\sum_{j<d}a_j(z)w^j.`
$$

The quotient and coefficients are holomorphic. If $\lvert g\rvert\le M$ and the fiber
radius is $R$, the proved estimate is $\lvert q\rvert\le(d+1)M/R^d$ throughout the
product polydisc. Existence does not require boundedness of the numerator;
boundedness is used for the estimate. Uniqueness, $d=0$, and the case of no
parameter variables are included.

### 40. Weierstrass division

If $f(z,w)$ is regular of order $d$ in $w$ at the origin, every scalar
analytic numerator germ $g$ has a unique decomposition

$$
`g=qf+r,\qquad r(z,w)=\sum_{j<d}a_j(z)w^j.`
$$

The proved main theorem chooses a fixed product polydisc depending on the
divisor and permits every bounded holomorphic numerator there, with a quotient
bound $\lVert q\rVert_\infty\le C\lVert g\rVert_\infty$ uniform in the numerator.
Local existence and uniqueness for arbitrary analytic numerator germs follow
by shrinking representatives. The ring-theoretic formulation with a polynomial
remainder over the parameter germ ring is also proved. Division by a
nonvanishing germ includes the order-zero case.

### 41. Weierstrass preparation and uniqueness

A scalar germ regular of order $d$ in $w$ has a unique factorization $f=uW$,
where $u$ is a unit and $W$ is distinguished of degree $d$. The factors
have representatives on a sufficiently small product polydisc, with $u$
nowhere zero there. Existence and uniqueness follow from the proved division
theorem in item 40, both for function representatives and in the germ ring.
Simultaneous preparation of a finite family after one linear coordinate change
is included.

### 42. Distinguished polynomial factors

A monic divisor of a distinguished polynomial over the parameter germ ring is
distinguished. More generally, if $pq$ is distinguished, the factors $p,q$
can be rescaled by reciprocal coefficient units so that both become
distinguished. The proof uses reduction modulo the maximal ideal and does not
depend on division, Noetherianity, or unique factorization.

### 43. Comparison between polynomials and analytic germs

The project maps $\mathcal O_{\mathbb C^{n-1},0}[w]$ into $\mathcal O_{\mathbb C^n,0}$ by evaluating
the last-coordinate polynomial. Injectivity is **proved**, by restriction to the
zero section and polynomial induction, independently of Weierstrass division.
Preservation of polynomial quotients under division by a distinguished polynomial
and comparison of irreducibility are **proved**. In particular, a distinguished
polynomial is irreducible exactly when its analytic germ is. The ring-theoretic
existence-and-uniqueness formulations of germ division and preparation are also
proved.

### 44. Noetherianity of the analytic germ ring

Every ideal of $\mathcal O_{\mathbb C^n,a}$ is finitely generated. The proof
proceeds by dimension induction, starting with the zero-dimensional germ ring
$\mathbb C$. The analytic induction step normalizes a nonzero ideal element,
divides by it, and reduces to a finite module of remainder coefficients over
the lower-dimensional germ ring. Transport gives the result at every base point
of any finite-dimensional complex normed space.

### 45. Unique factorization and persistence of relative primality

Every nonzero scalar analytic germ has a finite factorization into irreducibles,
unique up to units and order. This is **proved**: Noetherianity gives
factorization into irreducibles, and the polynomial comparison and Weierstrass
theory prove that irreducible germs are prime. The unique-factorization
instance is consequently complete.

Two relatively prime germs of fixed holomorphic representatives remain relatively
prime at all nearby points. Consequently the locus of relative primality is open.
Weierstrass preparation and division give a nonzero resultant in the parameter
germ ring and express it as a combination of the two original germs. Nonvanishing
on a scalar fiber excludes common nonunit factors nearby. Coordinate changes
reduce the general finite-dimensional case to this argument. Zero germs and
dimension zero are included without adding assumptions.

The distinction from generating the unit ideal is already proved: two germs
vanishing at the base point cannot generate $1$, even when they have no
nonunit common divisor.

Total germ order is also available intrinsically on arbitrary finite-dimensional complex
normed spaces. It agrees with the coordinate order in every continuous linear coordinate
system, and a Taylor-series interface accepts arbitrary finite coordinate index types.

## H. Further zero-set geometry and biholomorphic rigidity

### 46. Existence of a regular point on a hypersurface

The zero set of a scalar holomorphic function on a domain contains a regular
point of codimension one provided that the zero set is **nonempty and proper**.
Both conditions are explicit. Regularity concerns the set, not necessarily
the differential of the originally supplied defining function; for example,
a repeated factor can make that differential vanish.

The proof chooses an iterated derivative of minimal order that is nonzero
somewhere on the zero set. A preceding scalar derivative vanishes on the whole
zero set and has nonzero differential at the selected point. Biholomorphic
coordinates straighten its zero set to a hyperplane. Persistence of zeros in
nearby one-variable slices, proved using the maximum modulus principle for
reciprocals, identifies the two zero sets locally. No unfinished theorem is used.

### 47. Injective holomorphic maps in equal dimensions

An injective holomorphic map between open subsets of equal-dimensional complex
spaces has invertible derivative everywhere and is biholomorphic onto its open
image. Its coordinate Jacobian determinant never vanishes. Connectedness and
nonemptiness are unnecessary, and dimension zero is included.

The one-variable argument makes the inverse analytic by removing an isolated
singularity. An implicit level curve then proves nonsingularity wherever the
derivative is injective on a hyperplane. Dimension induction shows that any
injective holomorphic map has immersion points in every nonempty open restriction,
even with a larger target dimension. Restricting to a regular hypersurface in the
critical set would supply an invertible hyperplane minor and hence a contradiction.
The regular-point theorem for scalar zero sets therefore forces the Jacobian's zero
set to be empty. The original equal-dimension hypothesis is unchanged.

### 48. Cartan uniqueness and determination by a first derivative

If $U$ is a bounded domain and $f:U\to U$ is holomorphic with
$f(a)=a$ and $Df(a)=I$, then $f$ is the identity. No injectivity or
surjectivity of $f$ is assumed. This theorem is **proved** using averages of
bounded iterates, a locally uniformly convergent Montel subsequence, derivative
convergence, local injectivity, and the identity principle. The consequence
that two biholomorphisms with the same bounded connected source and the same
target are equal if their values and derivatives agree at one point is
also **proved**; boundedness of the target is not required for this
consequence.

### 49. Linearity of origin-preserving maps between circular domains with bounded source

A biholomorphism between circular domains with bounded source that sends the origin to
the origin is the restriction of an invertible complex-linear map. Both
domains contain the origin. The deduction from Cartan uniqueness is complete:
conjugating rotations gives rotation equivariance, and Cauchy's derivative formula
identifies the map with its derivative at zero. This last analytic argument is
independently proved, also for Banach-valued holomorphic maps.

### 50. Euclidean ball automorphisms and the ball–polydisc distinction

For $a$ in the Euclidean unit ball, the project defines the standard map

$$
\phi_a(z)=\frac{a-P_a z-\sqrt{1-\lVert a\rVert^2}\thinspace (z-P_a z)}
{1-\langle a,z\rangle},
$$

where $P_a$ is orthogonal projection onto $\mathbb C a$, with $P_0=0$.
Its holomorphy, nonvanishing denominator on the ball, exchange of $0$ and $a$,
preservation of the ball, and involutivity are **proved**. The metric calculation gives

$$
(1-\lVert\phi_a(z)\rVert^2)\lvert1-\langle a,z\rangle\rvert^2
=(1-\lVert a\rVert^2)(1-\lVert z\rVert^2).
$$

Its biholomorphic automorphism property and transitivity of the ball automorphism
group are therefore also **proved**, independently of Cartan uniqueness.
The nonexistence of a biholomorphism between the Euclidean unit ball and the unit polydisc in
dimension at least two is also **proved**, independently of Cartan uniqueness.
After normalization at zero, Schwarz's lemma applied to the map and its inverse
forces the derivative to preserve norms. The supremum norm fails the parallelogram
identity satisfied by the Euclidean norm, giving a contradiction.

## I. Common extensions, holomorphic convexity, Cartan–Thullen, and Bochner's tube theorem

The explicit involution and transitivity hold in arbitrary complex inner-product spaces;
finite dimensionality is retained for the separate ball–polydisc distinction.

### 51. Restrictions on common extension domains

Suppose $U\subseteq V$ are domains and every scalar holomorphic function
on $U$ extends to $V$. For every holomorphic $g$ on $V$,

$$
g(V)=g(U),\qquad V\subseteq\mathrm{conv}_{\mathbb R}(U).
$$

Thus a common extension preserves the range of each scalar function, including
its omitted values, and stays within the real convex hull of the original
domain. These results concern concrete subsets of the same ambient space.

### 52. Relative holomorphic hulls

Holomorphic hulls are extensive for subsets of the ambient set, monotone,
idempotent, relatively closed, and bounded when the original set is bounded.
Enlarging the ambient open set enlarges the hull. The empty hull is empty,
and a singleton has no additional hull points, including in dimension zero.

A point outside the hull can be separated by a holomorphic function arbitrarily
small on the original set and arbitrarily large at the point. Holomorphic maps
carry hulls into hulls; biholomorphic maps transport them exactly. Holomorphic
convexity is preserved by products, finite intersections, and biholomorphic
equivalence. These proofs are independent of Cartan–Thullen.

Every open complete logarithmically convex Reinhardt set is also holomorphically
convex. A monomial separates any exterior point from a compact subset, including
when the exterior point lies on coordinate hyperplanes. The entire holomorphic
hull therefore remains inside the domain. This proof includes unbounded and
empty domains and is independent of Cartan–Thullen.

### 53. Local continuation and elementary continuation obstructions

The project distinguishes obstruction to common local continuation from the
strong nonextendability of one function. `IsDomainOfHolomorphy` is a generalized
continuation-obstruction predicate for arbitrary sets: openness, connectedness,
and nonemptiness are separate hypotheses. It agrees with the classical
notion of a domain of holomorphy when applied to a nonempty connected open set.
A domain of existence of a single function satisfies this predicate. An open
nonempty set satisfying it cannot have a proper connected common extension
containing it.

Every planar open set, every finite product of planar open sets, and every
real-convex open subset of a finite-dimensional complex normed space satisfies
this continuation property. The formal product assertion also permits arbitrary
plane factors. When the product has empty interior, the predicate holds
vacuously because there is no nonempty open overlap on which to test
continuation. For nonempty connected open plane factors, the assertion recovers
the classical theorem that their product is a domain of holomorphy.

The proofs use reciprocals of separating entire functions and the identity
principle. These examples are independent of the Cartan–Thullen implications.

### 54. Convex compact exhaustions and escaping sequences

Every holomorphically convex open set has a compact exhaustion by compact sets
fixed by their relative holomorphic hulls. Successive sets contain their
predecessors in their relative interiors. This construction is **proved**.

The characterization by escaping sequences is **proved**: holomorphic convexity
is equivalent to the assertion that every sequence eventually leaving each
compact subset admits a scalar holomorphic function unbounded on that sequence.
The forward implication uses Baire's theorem in the complete compact-open space
of holomorphic functions, together with separators tending to zero locally
uniformly. The converse extracts an escaping sequence from a noncompact hull.
Empty open sets, disconnected open sets, and empty coordinate types are included.

### 55. Thullen's lemma and hull boundary distance

Mixed derivative bounds transfer from a set to its holomorphic hull; this is
**proved**, also for Banach-valued functions, by norming functionals.
The Taylor continuation lemma is also **proved**, for Banach-valued $f$:
if $q\in\mathcal O(U)$ is scalar, $f$ is holomorphic on $U$ with values in a Banach space,
$K\subset U$ is compact, and the polydisc of radius $\lvert q(w)\rvert$ centered at $w$ lies in $U$ for
each $w\in K$, then the Taylor series of $f$ at any $`a\in{\widehat K}_U`$ continues its germ
to the polydisc of radius $\lvert q(a)\rvert$.
The statement includes locally uniform convergence there and permits zeros of
$q$. The proof obtains uniform Cauchy bounds on compact families of smaller balls,
transfers coefficients weighted by powers of $q$ to the hull, and compares the
resulting Taylor terms with a product of geometric series.

From this lemma, the deductions that a domain of holomorphy preserves these
radius bounds, preserves compact-hull boundary distance exactly, and is
holomorphically convex are **proved**. In particular, real-convex open coordinate
sets are now proved holomorphically convex. The separate implication from
uniform positive hull-radius bounds to compactness of hulls is **proved**.

### 56. Cartan–Thullen equivalences

For an open subset $U\subset\mathbb C^n$, the project proves the equivalence of:

1. the domain-of-holomorphy property;
2. holomorphic convexity;
3. exact preservation of boundary distance under compact holomorphic hulls;
4. existence of one scalar function having $U$ as its domain of existence.

Thullen's lemma proves the implications from the domain-of-holomorphy property
to preservation of hull boundary distance and to holomorphic convexity. For
the reverse direction, a countable basis of balls and overlap components
supplies escaping sequences that detect every local continuation patch.
Baire's theorem gives one holomorphic function unbounded on all of them,
contradicting any proposed continuation. The uniform polydisc-radius
characterization is proved as well. The statements allow disconnected open
sets, the whole space, the empty set, and dimension zero. The function-theoretic equivalence
of items 1, 2, and 4 is also exported for arbitrary finite-dimensional complex normed spaces;
the numerical boundary-distance and polydisc-radius statements retain their coordinate norm.

### 57. Bochner's tube theorem

For a preconnected open base $\Omega\subset\mathbb R^n$, every Banach-valued
holomorphic function on $T_\Omega$ extends to $T_{\mathrm{conv}\Omega}$,
agreeing with the original function on $T_\Omega$. Uniqueness of the extension,
elementary openness and convexity of tubes, and the equivalence between convexity of
the base and the domain-of-holomorphy property of the tube are proved as well. The
formulation stays inside $\mathbb C^n$ and does not construct an abstract envelope of
holomorphy.

The proof follows Hörmander (Theorem 2.5.10). Fix a Banach space, the base and a point
$p$ of it, and consider the open star-convex sets with respect to $p$ to whose tubes every
holomorphic function on $T_\Omega$ extends, agreeing with it near $p$. Their union
$\tilde\Omega$ again has this property, since two such sets meet in a star-convex set
whose tube is connected. The union is convex: for $t_1,t_2\in\tilde\Omega$ the scaled
triangles with vertex $p$ lie in $\tilde\Omega$ by an induction on the scale. On a slightly
smaller triangle every point lies on a parabolic analytic disc
$\zeta\mapsto p+\zeta v_1+(c\zeta^2+1-c)v_2$ whose boundary lies over the two sides through
$p$; by the planar maximum principle the disc lies in the holomorphic hull of its boundary,
and Thullen's lemma, proved here for Banach-valued functions by norming functionals, gives
Taylor continuation to balls of a uniform radius. These local continuations glue along the
convex triangle, the enlarged star-convex tube is absorbed by maximality, and the scale
advances by a fixed amount. No change of coordinates is used, and the two points may be
linearly dependent. For a connected base, a path from $p$ leaves $\tilde\Omega$ at a first
point $x_1$; local agreement propagates along the path, so the extension and the original
function define a holomorphic function on the tube over $\tilde\Omega\cup B(x_1,r)$, which is
star-convex with respect to $x_1$, and the star-convex case extends it to the convex hull,
contradicting maximality. Hence $\Omega\subseteq\tilde\Omega$. The general finite index type
is reached by reindexing from $\mathbb R^{\lbrace 1,\dots,n\rbrace}$.

## J. Plurisubharmonic functions, the Levi form, and pseudoconvexity

### 58. Subharmonic functions of one variable

A real function on an open subset of $\mathbb C$ is subharmonic if it is upper
semicontinuous and satisfies the local submean inequality: at each point and for all
small radii, the function is integrable on the circle and its center value is at most its
circle average (Ransford's definition). Only real values are admitted. Sums, nonnegative
multiples and maxima of subharmonic functions are subharmonic; real parts of holomorphic
functions, positive powers of holomorphic norms and logarithms of nonvanishing holomorphic
moduli are subharmonic. The maximum principle holds in two forms: a subharmonic function
on a preconnected open set attaining its supremum is constant, and on a disc a function
subharmonic inside and upper semicontinuous on the closure is bounded by its supremum on
the boundary circle.

Real parts of complex polynomials in the normalized circle variable approximate every
continuous function on a circle uniformly, by density of trigonometric polynomials.
Consequently a continuous function whose center value lies below the center value of
every such harmonic polynomial majorant satisfies the submean inequality, and continuous
subharmonic functions satisfy the submean inequality on every closed disc in their domain.

### 59. The Laplacian criterion

For a `C²` function of one complex variable, the circle average of radius $r$ differs
from the center value by $r^2/4$ times the Laplacian up to $o(r^2)$, uniformly through a
second-order Taylor bound obtained from the mean value inequality. Hence a positive
Laplacian gives the strict submean inequality on small circles, a negative Laplacian the
reverse inequality, a subharmonic `C²` function has nonnegative Laplacian, and a `C²`
function with nonnegative Laplacian on an open set is subharmonic. The last step perturbs
by a small multiple of the squared distance, whose Laplacian is $4$, and uses the submean
inequality on closed discs. The Laplacian is Mathlib's Laplacian on $\mathbb C$.

### 60. Plurisubharmonic functions and the Levi form

A real function on an open subset of a complex normed space is plurisubharmonic if it is
upper semicontinuous and its restriction to every complex line is subharmonic. Sums,
nonnegative multiples, maxima and complex affine substitutions preserve
plurisubharmonicity; continuous convex functions, in particular the norm, are
plurisubharmonic; real parts, positive powers of norms and logarithms of nonvanishing
moduli of holomorphic maps are plurisubharmonic.

The Levi form of a real `C²` function at $a$ in direction $w$ is defined in
coordinate-free form as one quarter of the real Hessian on $(w,w)$ plus the real Hessian
on $(iw,iw)$; it is one quarter of the Laplacian of the slice $t\mapsto f(a+tw)$ at
$t=0$. A `C²` function on an open set is plurisubharmonic exactly when its Levi form is
positive semidefinite at every point.

### 61. Pseudoconvexity of domains of holomorphy

On a domain of holomorphy in $\mathbb C^n$ with the sup norm, $-\log\delta$ is
plurisubharmonic, where $\delta$ is the distance to the complement (Hörmander 2.6.5). The
proof uses harmonic polynomial majorants along complex lines and the weighted hull-radius
bound of Thullen's lemma. An open set is called pseudoconvex if it carries a continuous
plurisubharmonic exhaustion function; domains of holomorphy are pseudoconvex, with
exhaustion $\max(-\log\delta,\lVert z\rVert)$. Pseudoconvexity and the two continuity principles
below are transported from $\mathbb C^n$ to domains of holomorphy in any finite-dimensional
complex normed space, since both notions and the domain-of-holomorphy property are invariant
under continuous linear equivalences; the boundary-distance statement itself is tied to the
sup norm.

Pseudoconvex sets satisfy the continuity principle for continuous families of affine
analytic discs, by the disc maximum principle for plurisubharmonic functions. In a product
$E\times\mathbb C$, the continuity principle implies Hartogs convexity for cylinder figures:
a Hartogs cylinder over an open preconnected base contained in the set has its filled
cylinder contained in the set. The converse implications, from pseudoconvexity back to
the domain-of-holomorphy property, form the Levi problem and are outside the present scope.

### 62. Levi convex boundaries and Levi's theorem

A local `C²` defining function for an open set $U$ at a boundary point $p$ is a `C²`
function $\rho$ on an open neighborhood $V$ of $p$ with $\rho(p)=0$, $d\rho(p)\neq0$, and
$U\cap V=\lbrace \rho<0\rbrace\cap V$. The complex tangent space at $p$ is the kernel of the
complex-linear part of $d\rho(p)$. The set $U$ satisfies the Levi condition at $p$ if the Levi
form of every local defining function is positive semidefinite on the complex tangent space,
and it is Levi pseudoconvex if this holds at every boundary point. Quantifying over all
defining functions gives an intrinsic condition. The independence theorem and the
criterion using one defining function are proved; see item 64.

Convex open sets are Levi pseudoconvex: a negative second derivative along a real tangent
direction would put two symmetric points of the tangent line into $U$, hence the boundary
point itself.

**Levi's theorem.** A domain of holomorphy in a finite-dimensional complex normed space is
Levi pseudoconvex at every boundary point that admits a local `C²` defining function (Range,
Theorem 2.11). The proof is given in $\mathbb C^n$ with the sup norm and transported by a
linear equivalence, using the invariance of the Levi condition under pullback; within
$\mathbb C^n$ it avoids holomorphic coordinate changes. Near $p$ the defining function is
comparable to the boundary distance: $c\thinspace \lvert\rho\rvert\le\delta\le C\thinspace \lvert\rho\rvert$
on $U$, by the mean value inequality and by moving inward along a direction on which $d\rho$
is positive. If the Levi form were negative in a complex tangent direction $w$, the Levi
polynomial gives a quadratic analytic disc $\zeta\mapsto p+\zeta w+\zeta^2c+\kappa r^2\nu$
on which $\rho=-\kappa r^2+\lvert\zeta\rvert^2L+O(\eta r^2)$ with $L<0$, uniformly for $\lvert\zeta\rvert\le r$
and small $r$, by the uniform second-order Taylor bound and the decomposition of a symmetric
bilinear form along a complex line. The boundary circle is then deeper inside $U$ than the
center by a fixed multiple of $r^2$, while the center lies in the holomorphic hull of the
circle by the maximum modulus principle; Thullen's weighted radius bound contradicts this.

### 63. Levi form under holomorphic maps and the Kontinuitätssatz

For a `C²` function $g$ and a holomorphic map $\Phi$, the Levi form obeys the chain rule
$\mathrm{Lev}(g\circ\Phi)(a,w)=\mathrm{Lev}(g)(\Phi(a),\Phi'(a)w)$. The
second-derivative term of $\Phi$ cancels because the real second derivative of a holomorphic
map is complex bilinear (it is the restriction of scalars of the complex second derivative).
Consequently `C²` plurisubharmonic functions compose with holomorphic maps to `C²`
plurisubharmonic functions.

A local defining function pulls back along a holomorphic map with surjective derivative to a
local defining function of the preimage, complex tangent vectors correspond under the
derivative, and for a holomorphic map with invertible derivative the Levi condition of a
defining function at $\Phi(p)$ is equivalent to that of its pullback at $p$.

A domain of holomorphy in $\mathbb C^n$ satisfies the continuity principle for continuous
families of holomorphic discs: if every boundary circle and the initial disc lie in the
domain, so does every disc. Every point of a holomorphic disc lies in the holomorphic hull of
its boundary circle, and Thullen's radius bound keeps the discs at least as far from the
complement as the compact set of boundary circles. The affine continuity principle of item 61
follows.

### 64. Independence of the defining function and local peak functions

Two local `C²` defining functions of an open set at the same boundary point have positively
proportional derivatives, and on tangent vectors their second derivatives are proportional
with the same factor. The first-order statement compares one-sided difference quotients
along lines entering the set; the second-order statement compares second-order expansions
along parabolic curves $t\mapsto p+tv+\beta t^2\nu$, whose sign is controlled by the defining
property, and uses a linear-algebra lemma on half-space containment. No implicit function
theorem and no positive-factor lemma is used. Consequently the complex tangent space is
independent of the defining function, the Levi forms of two defining functions are positively
proportional on it, and the Levi condition, strict or not, can be verified on one defining
function.

At a strictly Levi convex boundary point, adding a large multiple of the square of the defining
function makes the Levi form positive definite on the whole space; the constant comes from a
sequential compactness argument on the unit sphere. The complex bilinear part of the real
Hessian is a bounded complex bilinear map, so the Levi polynomial
$F(z)=\partial\rho(p)(z-p)+Q(z-p)$ is entire, vanishes at $p$, and by the second-order Taylor
expansion satisfies $`\mathrm{Re}F(z)\le{\tilde\rho}(z)-\tfrac c2\lVert z-p\rVert^2`$ near $p$
(Range, Proposition 2.16). Hence $\mathrm{Re}F<0$ on the set near $p$, and $1/F$ is a
holomorphic function on the set near $p$ whose modulus tends to infinity at $p$. The
normalized local peak function is $\exp F$: its value at $p$ is one and its modulus is
strictly less than one at every other nearby point on the closed side $\rho\le0$. The step from peak functions to the domain-of-holomorphy property of a local piece
is not taken; it is the non-elementary comparison of weak and strong domains of holomorphy.

## K. Runge pairs, Runge domains, and polynomial hulls

### 65. Runge pairs, Runge domains, and the polynomial hull

A pair of sets $U\subseteq V$ is a Runge pair if every holomorphic function on $U$ is
approximated within $\varepsilon$ on every compact subset of $U$ by a holomorphic function on
$V$; an open subset of $\mathbb C^n$ is a Runge domain if the approximants are polynomials.
Runge pairs are reflexive and transitive, and on an open set the compact-set formulation is
equivalent to locally uniform convergence of a sequence of approximants, using a compact
exhaustion $\overline B(0,k)\cap\lbrace \mathrm{dist}(\cdot,U^c)\ge 1/(k+1)\rbrace$.

Entire functions on $\mathbb C^n$ are uniform limits on compact sets of partial sums of their
Taylor series, which are polynomials. Hence the polynomial hull of a compact set, defined by
the bounds of all polynomials, coincides with its hull relative to all entire functions; it is
closed and contained in the closed ball spanned by the coordinate polynomials, hence compact.
A set is a Runge domain exactly when it forms a Runge pair with the whole space. For a Runge
domain $U$ and a compact $K\subseteq U$ the polynomial hull of $K$ meets $U$ in the holomorphic
hull of $K$ relative to $U$, and for a Runge domain of holomorphy this set is compact by
Cartan–Thullen (Hörmander, Theorem 2.7.3; Jakóbczak–Jarnicki, Theorem 4.3.3, the elementary
implications). The converse implications, and the approximation theorem for polynomially
convex compact sets, form the Oka–Weil theorem and are not included; the one-variable Runge
theorem for rational approximation is also not included.

Complete Reinhardt open sets are Runge domains, since holomorphic functions on them are
represented by their Taylor series at the origin with locally uniform convergence; polydiscs
and balls centered at the origin and the whole space are examples. Circular connected open sets
containing the origin are Runge domains, since the homogeneous expansion converges locally
uniformly and each homogeneous term, the diagonal restriction of a continuous multilinear map,
is a polynomial. Runge domains are transported by holomorphic maps with polynomial inverses,
in particular by polynomial automorphisms with polynomial inverses and by translations
(Jakóbczak–Jarnicki, Proposition 4.3.2).

## Extent of the present theory

The completed extension results include phenomena that are often proved later
in textbooks: locally bounded removal across singular zero sets, isolated-point
removal in dimension at least two, and removal across analytic sets of slice
codimension at least two. Their proofs use direct analysis and are independent of the
general compact-hole theorem, which is proved as well. Weierstrass division and
preparation, Noetherianity, unique factorization, and persistence of relative primality
are also complete.
Total order is invariant under analytic coordinate changes and can be realized
along an axis after a linear change.

The scope remains classical function theory. General Riemann domains and abstract
envelopes of holomorphy are deferred. There is no independent development of
manifolds, sheaves, cohomology, or general complex analytic spaces. For analytic
sets, the current coverage also stops short of a systematic irreducible-component
theory, analyticity of the singular locus, and general local dimension theory.
The catalogue does not assert the Oka–Weil theorem or a general Runge theory beyond the
elementary implications of item 65, nor a Levi theory beyond items 62–64.

The statements draw on several sources, especially the introductory treatments
by Boas, Fritzsche–Grauert, Jakóbczak–Jarnicki, Korevaar–Wiegerinck, Lebl, Range,
Scheidemann, Shabat, and Suwa. No single source fixes the conventions. The
formulations above record the project's actual hypotheses and current proof
status, with the existing mathematical library guiding choices of generality
and terminology.

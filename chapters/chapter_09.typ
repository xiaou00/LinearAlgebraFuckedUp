#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Free Algebras

We have already introduced the notion of $cal(O)$-algebra objects of a symmetric $cal(O)$-monoidal $oo$-category $cal(C)$, which is defined by a map of $oo$-operads $cal(O)^times.o->cal(C)^times.o$, and the $oo$-category of algebras $Alg_cal(O)(cal(C))$. The aim of this part is to study this notion in more detail.

== From Symmetric Powers to Free Algebras

Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category. Restriction along
the inclusion of operads

$ cat("Triv")^times.o arrow.r.hook Comm^times.o $

is the forgetful functor

$ theta:CAlg(cal(C))->cal(C) $

In an ordinary cocomplete symmetric monoidal category, if tensor product
preserves colimits separately in each variable, the left adjoint is the
symmetric algebra functor

$
  "Sym"^ast (c)=coprod_(n>=0) c^(times.o n)\/Sigma_n
$

In the $oo$-categorical setting the quotient is replaced by homotopy orbits,
so the expected formula is

$
  "Sym"^ ast(c)=coprod_(n>=0) (c^(times.o n))_(h Sigma_n)
$

This formula is the model example, but the natural problem is more general.
A map of $oo$-operads

$ f:cal(O)'^times.o->cal(O)^times.o $

induces restriction of algebra structures

$
  f^ast:Alg_cal(O) (cal(C))->Alg_(cal(O)') (cal(C))
$

We want to construct its left adjoint $f_!$. The correct construction is an
#emph[operadic left Kan extension]. Its local building blocks are operadic colimit
diagrams.

#remark(title:[Why Ordinary Colimits Are Insufficient])[
  A colimit of underlying objects need not inherit an algebra structure. The
  obstruction is that every multimorphism must remain compatible with the
  colimit. For example, if $a=colim_i a_i$, then the multiplication on $a$
  requires the comparison

  $
    (colim_i a_i) times.o (colim_j a_j)
    ->colim_(i,j) (a_i times.o a_j)
  $

  to be an equivalence. Operadic colimits encode exactly this compatibility,
  and do so one tensor variable at a time.
]

== Operadic Colimit Diagrams

Let

$ q:cal(C)^times.o->cal(O)^times.o $

be a fibration of $oo$-operads. Write $cal(C)^times.o_"act"$ and
$cal(O)^times.o_"act"$ for the subcategories containing all objects and only
active morphisms.

=== Weak and Genuine Operadic Colimits

Let $overline(p):k^▹->cal(C)^times.o_"act"$ be a cone and let
$p=overline(p)|_k$.

#definition(title:[The Active Cocone Category])[
  For a diagram $d:s->cal(C)^times.o_"act"$, define

  $
    cat("Cocone")_cal(C)^"act" (d)
    :=Fun(s^▹,cal(C)^times.o_"act")
      times_(Fun(s,cal(C)^times.o_"act")) {d}
  $

  Thus $cat("Cocone")_cal(C)^"act" (d)$ is the homotopy fiber over $d$ of
  the restriction functor from $s^▹$-diagrams to $s$-diagrams.

  + An object is an extension

    $ overline(d):s^▹->cal(C)^times.o_"act" $

    together with an identification $overline(d)|_s tilde.eq d$.

  + A morphism is a homotopy-coherent natural transformation between two
    such extensions which is fixed on $s$.

  The superscript $"act"$ restricts only the morphisms: all objects of
  $cal(C)^times.o$ remain, but every arrow in the cocone is required to be
  active. Equivalently,

  $
    cat("Cocone")_cal(C)^"act" (d)
    tilde.eq (cal(C)^times.o_"act")_(d slash)
  $
]

#remark(title:[A Two-Object Cocone])[
  If $s={0,1}$ is discrete and $d(0)=x_0$, $d(1)=x_1$, an object of the active
  cocone category has the form

  #align(center, diagram({
    node((0, 0), [$x_0$], name: <x0>)
    node((2, 0), [$x_1$], name: <x1>)
    node((1, 1), [$c$], name: <c>)
    edge(<x0>, <c>, [active], label-side: right, "->")
    edge(<x1>, <c>, [active], label-side: left, "->")
  }))

  If the $x_i$ are tuples of colors and $c$ lies over
  $chevron.l 1 chevron.r$, these arrows are multimorphisms with common output
  $c$.
]

There is now a canonical comparison map

$
  psi_(overline(p)):
  cat("Cocone")_cal(C)^"act" (overline(p))
  ->cat("Cocone")_cal(C)^"act" (p)
    times_(cat("Cocone")_cal(O)^"act" (q p))
    cat("Cocone")_cal(O)^"act" (q overline(p))
$

#remark(title:[Meaning of the Comparison Map])[
  The left-hand side is the category of further active cocones on the already
  chosen cone $overline(p)$. A point on the right consists of an active cocone on
  $p$ in $cal(C)^times.o$ and a compatible further cocone on $q overline(p)$ in
  the base. The map $psi_(overline(p))$ forgets the actual active lift from the
  cone point of $overline(p)$. Hence it is a trivial Kan fibration precisely when
  every compatible base cocone has a contractibly unique lift.
]

#definition(title:[Weak Operadic Colimit])[
  The cone $overline(p)$ is a #emph[weak operadic $q$-colimit diagram] if
  $psi_(overline(p))$ is a trivial Kan fibration.

  Equivalently, every active cocone compatible with the prescribed cocone in
  $cal(O)^times.o$ lifts through $q$, and the space of such lifts is
  contractible.
]

#definition(title:[Operadic Colimit])[
  An active cone $overline(p):k^▹->cal(C)^times.o_"act"$ is an
  #emph[operadic $q$-colimit diagram] if, for every object $c in cal(C)$, the cone obtained by
  adjoining $c$

  $ overline(p) ⊕ c:k^▹->cal(C)^times.o_"act" $

  is a weak operadic $q$-colimit diagram.
]

Here $⊕$ denotes concatenation of operadic inputs. The second definition is
stronger because it asks the universal property to survive after an arbitrary
extra input is inserted.

#remark(title:[Warning])[
  An ordinary $q$-colimit need not be an operadic $q$-colimit, and an
  operadic $q$-colimit need not be an ordinary $q$-colimit. They coincide only
  under additional compatibility hypotheses.
]

#remark(title:[The Lifting Picture])[
  Weak operadic universality can be tested by filling the dotted arrow in
  every diagram of the following form, with the cone point landing in the
  underlying category of colors.

  #align(center, diagram({
    node((0, 0), [$k star partial Delta^n$], name: <boundary>)
    node((1, 0), [$cal(C)^times.o_"act"$], name: <total>)
    node((0, 1), [$k star Delta^n$], name: <simplex>)
    node((1, 1), [$cal(O)^times.o_"act"$], name: <base>)
    edge(<boundary>, <total>, [], "->")
    edge(<boundary>, <simplex>, [], "->")
    edge(<total>, <base>, [$q$], label-side: left, "->")
    edge(<simplex>, <base>, [], "->")
    edge(<simplex>, <total>, [], "-->")
  }))
]

=== Formal Properties

#proposition(title:[Basic Stability Properties])[
  Operadic colimit diagrams satisfy the following rules.

  + A weak operadic colimit remains one after left-cofinal reindexing.

  + A finite product of operadic $q$-colimit diagrams is again an operadic
    $q$-colimit diagram.

  + If the indexing simplicial sets in such a finite product are weakly
    contractible, the resulting cone is also an ordinary $q$-colimit.

  + Suppose $overline(p)_0$ and $overline(p)_1$ are joined by a natural transformation
    whose components on the original diagram are $q$-coCartesian and whose
    component at the cone point is an equivalence. Then one is an operadic
    $q$-colimit if and only if the other is.
]

#proofsketch[
  The comparison maps defining weak operadic colimits are left fibrations, so
  it suffices to prove that their fibers are contractible. Cofinal changes do
  not alter these fibers. Finite products are handled one variable at a time,
  using the contractible choice of extensions over a coCartesian cone. The
  natural-transformation statement follows by comparing the corresponding
  active cocone categories and applying two-out-of-three.
]

#proposition(title:[Detecting coCartesian Fibrations])[
  The fibration $q$ is a coCartesian fibration of $oo$-operads if and only if
  every active arrow in $cal(O)^times.o$ admits a lift which, regarded as a
  cone on one object, is an operadic $q$-colimit diagram.
]

Thus a coCartesian lift is precisely a unary operadic colimit. This is the
first indication that operadic colimits are the correct relative analogue of
ordinary colimits.

=== The Fiberwise Criterion

Assume now that $q$ is a coCartesian fibration. An active operation

$ m:x ⊕ y->z $

in $cal(O)^times.o$ induces a pushforward functor between the corresponding
fibers. If $overline(p):k^▹->cal(C)_x$ is a cone, then adjoining an object
$d in cal(C)_y$ and pushing forward along $m$ gives

$
  k^▹->^(overline(p)) cal(C)_x
  ->^(- ⊕ d) cal(C)_(x ⊕ y)
  ->^(m_!) cal(C)_z
$

#theorem(title:[Fiberwise Criterion])[
  The cone $overline(p)$ is an operadic $q$-colimit diagram if and only if every
  composite above is an ordinary colimit diagram in $cal(C)_z$, for every
  choice of $y,z,d$, and active operation $m:x ⊕ y->z$.
]

#remark(title:[Symmetric Monoidal Case])[
  If $cal(C)^times.o->Ner(Fin_*)$ is a symmetric monoidal $oo$-category, the
  criterion reduces to a familiar statement: a cone

  $ overline(p):k^▹->cal(C) $

  is an operadic colimit exactly when, for every $c in cal(C)$,

  $ k^▹->^(overline(p)) cal(C)->^(c times.o -) cal(C) $

  is an ordinary colimit diagram. In short,

  #quote[An operadic colimit is a colimit preserved by tensoring with every object.]
]

#proofsketch[
  The Segal equivalence decomposes an object over a finite pointed set into
  its input components. The fibers of the comparison map
  $psi_(overline(p))$ are therefore the fibers of the ordinary colimit comparison
  maps obtained after adjoining the remaining inputs and applying an active
  operation. Contractibility of all these fibers is exactly the stated
  fiberwise condition.
]

=== Existence from Compatible Colimits

#definition(title:[Compatibility with Indexed Colimits])[
  Let $k$ be a simplicial set. A coCartesian fibration of $oo$-operads

  $ q:cal(C)^times.o->cal(O)^times.o $

  is #emph[compatible with $k$-indexed colimits] if

  + every fiber $cal(C)_x$ admits $k$-indexed colimits

  + every operadic tensor functor

    $
      times.o_phi:product_(1<=i<=n) cal(C)_(x_i)->cal(C)_y
    $

    preserves $k$-indexed colimits separately in each variable
]

#theorem(title:[Existence of Operadic Colimits])[
  If $q$ is compatible with $k$-indexed colimits, then every
  $k$-diagram in $cal(C)^times.o_"act"$, together with a prescribed cone over
  its image in $cal(O)^times.o_"act"$, extends to an operadic $q$-colimit
  diagram.
]

#proofsketch[
  First form the required ordinary colimit in the fiber containing the cone
  point. The preservation hypothesis implies that adjoining any other inputs
  and applying any active operation still produces a colimit cone. The
  fiberwise criterion upgrades this ordinary cone to an operadic one, while
  coCartesian lifting supplies the required coherent map over the prescribed
  base cone.
]

#corollary(title:[Small-Colimit Criterion])[
  For a regular cardinal $kappa$, the map $q$ is a coCartesian fibration
  compatible with $kappa$-small colimits if and only if every
  $kappa$-small diagram equipped with a cone in the base admits an operadic
  $q$-colimit lift.
]

#remark(title:[Role in the Construction of Free Algebras])[
  Under the compatibility hypotheses, operadic left Kan extension along $f$
  is left adjoint to restriction. The free algebra functor is the special
  case which freely adds the operations encoded by $cal(O)$.
]

== Operadic Left Kan Extensions

For an ordinary functor $u:cal(A)->cal(B)$, the value of a left Kan extension
at $b in cal(B)$ is computed from all arrows $u(a)->b$. The operadic version
has the same shape, except that one must allow an arbitrary finite tuple of
inputs and use active morphisms in place of ordinary arrows.

=== Correspondences of Operads

#definition(title:[Correspondence of Operads])[
  A #emph[correspondence of $oo$-operads] is a $Delta^1$-family of
  $oo$-operads

  $
    r:cal(M)^times.o->Ner(Fin_*) times Delta^1
  $

  Its fibers over $0$ and $1$ will be denoted by $cal(A)^times.o$ and
  $cal(B)^times.o$. Thus $cal(M)^times.o$ interpolates from
  $cal(A)^times.o$ to $cal(B)^times.o$ and records the operations which may
  carry inputs from the first fiber to outputs in the second.

  #align(center, diagram({
    node((0, 0), [$cal(A)^times.o$], name: <a>)
    node((1, 0), [$cal(M)^times.o$], name: <m>)
    node((2, 0), [$cal(B)^times.o$], name: <b>)
    node((0, 1), [${0}$], name: <zero>)
    node((1, 1), [$Delta^1$], name: <interval>)
    node((2, 1), [${1}$], name: <one>)
    edge(<a>, <m>, [], "hook->")
    edge(<b>, <m>, [], "hook->")
    edge(<zero>, <interval>, [], "hook->")
    edge(<one>, <interval>, [], "hook->")
    edge(<a>, <zero>, [], "->")
    edge(<m>, <interval>, [], "->")
    edge(<b>, <one>, [], "->")
  }))
]

Let $q:cal(C)^times.o->cal(O)^times.o$ be a fibration of $oo$-operads and
let $F:cal(M)^times.o->cal(C)^times.o$ be a map of generalized
$oo$-operads. For $b in cal(B)^times.o$, define the active indexing category

$
  cal(K)_b
  :=(cal(M)^times.o_"act")_(\/b)
    times_(cal(M)^times.o) cal(A)^times.o
$

Here the map from the active slice to $cal(M)^times.o$ remembers the source.
Consequently, an object of $cal(K)_b$ is an active operation $a->b$ whose
input object $a$ lies in the initial fiber $cal(A)^times.o$. The identity of
$b$ supplies a canonical cone

$
  cal(K)_b^▹->(cal(M)^times.o)_(\/b)
    ->cal(M)^times.o->^F cal(C)^times.o
$

#definition(title:[Operadic Left Kan Extension])[
  The map $F$ is an #emph[operadic $q$-left Kan extension] of
  $F|_(cal(A)^times.o)$ if the cone above is an operadic $q$-colimit diagram
  for every $b in cal(B)^times.o$.
]

#remark(title:[What the Definition Says])[
  The restriction of $F$ to $cal(A)^times.o$ supplies the input data. For an
  output $b$, the category $cal(K)_b$ lists every active way of feeding that
  data into $b$. The operadic colimit condition says that $F(b)$ is universal
  among objects receiving all these operations, and that this universality
  survives after any further operadic input is adjoined. In particular,
  $F(b)$ is determined up to a contractible space of choices.
]

=== Existence and Coherent Extension

#theorem(title:[Local-to-Global Extension Principle])[
  Consider a lifting problem of $Delta^n$-families of operads over the
  fibration $q$.

  + If $n=1$, an operadic left Kan extension exists if and only if, for every
    object $b$ in the terminal fiber, the diagram indexed by $cal(K)_b$ can
    be completed to an operadic $q$-colimit cone lifting the prescribed cone
    in $cal(O)^times.o$.

  + If $n>1$ and the restriction to the edge ${0,1}$ is already an operadic
    left Kan extension, then the compatible partial family extends over the
    whole $n$-simplex.
]

#proofsketch[
  Factor morphisms in $Ner(Fin_*)$ into inert and active parts and attach the
  missing simplices dimension by dimension. At a new vertex, the required
  filler is exactly an operadic colimit cone. Higher-dimensional attachments
  are inner-horn lifting problems and are solved by the fibration $q$. The
  active--inert factorization makes these attachments compatible with the
  operadic Segal condition. Thus the only genuinely new choices occur at
  objects, and their spaces are contractible by the operadic colimit
  property.
]

#remark(title:[Why the Higher-Simplex Statement Matters])[
  Pointwise existence alone would not produce a functor. The second part of
  the theorem supplies all naturality and higher coherence simultaneously.
  It is the operadic counterpart of the fact that pointwise ordinary Kan
  extensions assemble into a homotopy-coherent functor.
]

=== The Pointwise Formula

Suppose now that

$ f:cal(O)'^times.o->cal(O)^times.o $

is a map of $oo$-operads, $a$ is an $cal(O)'$-algebra in
$cal(C)^times.o$, and the relevant operadic colimits exist. For a color
$y in cal(O)$, set

$
  cal(I)_y
  :=(cal(O)^times.o_"act")_(\/y)
    times_(cal(O)^times.o) cal(O)'^times.o
$

An object of $cal(I)_y$ is a tuple of colors $x_1,dots,x_n$ of $cal(O)'$
together with an active operation

$ alpha:f(x_1) ⊕ dots ⊕ f(x_n)->y $

Let $times.o_alpha$ denote the pushforward functor classified by this
operation. The value of the operadic left Kan extension is

$
  (f_!a)(y)
  tilde.eq
  colim_((x_1,dots,x_n;alpha) in cal(I)_y)
  times.o_(alpha) (a(x_1),dots,a(x_n))
$

#remark(title:[Symmetric Monoidal Form])[
  In a symmetric monoidal $oo$-category there is a single ambient fiber, and
  $times.o_alpha$ is the corresponding iterated tensor product. Hence the
  formula becomes

  $
    (f_!a)(y)
    tilde.eq
    colim_((x_1,dots,x_n;alpha) in cal(I)_y)
    a(x_1) times.o dots times.o a(x_n)
  $

  The indexing category retains the operation $alpha$ and all of its
  homotopies; replacing it by a mere set of operations would lose the
  required coherent symmetry.
]

#remark(title:[Free Algebras])[
  Take $f:cat("Triv")^times.o->cal(O)^times.o$. For a one-colored operad and
  an object $c$, the preceding formula specializes to

  $
    "Free"_cal(O)(c)
    tilde.eq
    coprod_(n>=0)
    (cal(O)(n) times.o c^(times.o n))_(h Sigma_n)
  $

  The $n=0$ term inserts the constants of $cal(O)$. For
  $cal(O)=Comm$, every $cal(O)(n)$ is contractible and this recovers

  $
    "Sym"^ast (c)
    tilde.eq coprod_(n>=0) (c^(times.o n))_(h Sigma_n)
  $
]

=== Computational Summary

#quote[
  Operadic left Kan extension is a colimit over active operations, computed
  in the output fiber and tested after adjoining every extra input.
]

The comparison with the ordinary pointwise formula is

$
  (Lan_u F)(b)
  tilde.eq colim_((a,u(a)->b)) F(a)
$

$
  (f_!a)(y)
  tilde.eq colim_((x_1,dots,x_n;alpha:f(x_1)⊕dots⊕f(x_n)->y))
  times.o_(alpha) (a(x_1),dots,a(x_n))
$

The practical procedure is therefore:

+ form the active slice $cal(I)_y$ of all operations with output $y$

+ evaluate the input algebra and apply the operation-specific tensor functor
  $times.o_alpha$

+ take the ordinary colimit in the fiber $cal(C)_y$

+ verify, using the fiberwise criterion, that every operadic tensor functor
  preserves this colimit separately in each additional variable

Under compatibility with the required indexed colimits, the final condition
is automatic. The resulting objects assemble coherently by the
local-to-global extension theorem and define the left adjoint

$
  f_!:Alg_(cal(O)') (cal(C))->Alg_cal(O) (cal(C))
$

#remark(title:[Colimits, Not a Formal Duality])[
  The construction in this section is the operadic #emph[colimit] and left
  Kan extension theory. Its pointwise formulas resemble ordinary colimits,
  but the active-operation index and the stability under extra inputs are
  essential. A formal dual theory is not obtained merely by reversing every
  arrow, because the definition of an operad is intrinsically asymmetric in
  its many inputs and single output.
]

=== The Adjunction $f_! ⊣ f^ast$

#definition(title:[Restriction of Algebra Structures])[
  Let $q:cal(C)^times.o->cal(O)^times.o$ be an $cal(O)$-monoidal
  $oo$-category and let

  $ f:cal(O)'^times.o->cal(O)^times.o $

  be a map of $oo$-operads. Its base change is the $cal(O)'$-monoidal
  $oo$-category

  $
    cal(C)_f^times.o
    :=cal(C)^times.o
      times_(cal(O)^times.o) cal(O)'^times.o
    ->cal(O)'^times.o
  $

  By convention, $Alg_(cal(O)') (cal(C))$ below means
  $Alg_(cal(O)') (cal(C)_f)$. An $cal(O)$-algebra is an inert-preserving
  section

  $ b:cal(O)^times.o->cal(C)^times.o $

  Restriction along $f$ is precomposition:

  $
    f^ast b:=b compose f:
    cal(O)'^times.o->cal(C)^times.o
  $

  Since $q compose b compose f=f$, this map is equivalently a section of
  $cal(C)_f^times.o->cal(O)'^times.o$, and hence an $cal(O)'$-algebra.
  On a morphism $theta:b->b'$, the functor is defined by the same
  precomposition rule $f^ast(theta)=theta compose f$.
]

#remark(title:[Meaning of the Two Sides])[
  The two algebra categories record different amounts of operadic structure.

  + $Alg_(cal(O)') (cal(C))$ consists of objects carrying the operations and
    coherences prescribed by $cal(O)'$.

  + $Alg_cal(O) (cal(C))$ consists of objects carrying the operations and
    coherences prescribed by $cal(O)$.

  The functor $f^ast$ views an $cal(O)$-algebra only through the operations
  coming from $cal(O)'$. If $f$ is an inclusion, it literally forgets the
  operations not lying in its image; for a general $f$, it reindexes colors
  and operations along $f$. In the opposite direction, $f_!$ freely
  supplies the missing $cal(O)$-operations by the operadic colimits of the
  preceding subsection, subject only to the original $cal(O)'$-relations.
]

#theorem(title:[Operadic Kan Extension Adjunction])[
  Let

  $ f:cal(O)'^times.o->cal(O)^times.o $

  be a map of $oo$-operads, and let $cal(C)^times.o$ be an
  $cal(O)$-monoidal $oo$-category compatible with all operadic colimits
  required by the pointwise formula. Restriction along $f$ admits the
  operadic left Kan extension as a left adjoint:

  $
    f_!:Alg_(cal(O)') (cal(C))
    arrows.lr
    Alg_cal(O) (cal(C)):f^ast
  $

  In other words, $f_! ⊣ f^ast$, where $f^ast$ is restriction of the
  algebra structure and $f_!$ is computed by the operadic left Kan extension
  formula above.

  For $a in Alg_(cal(O)') (cal(C))$ and
  $b in Alg_cal(O) (cal(C))$, the adjunction is characterized by a natural
  equivalence of mapping anima

  $
    Map_(Alg_cal(O) (cal(C))) (f_!a,b)
    tilde.eq
    Map_(Alg_(cal(O)') (cal(C))) (a,f^ast b)
  $
]

The unit and counit are natural transformations

$
  eta:id_(Alg_(cal(O)') (cal(C)))->f^ast f_!,
  quad
  epsilon:f_! f^ast->id_(Alg_cal(O) (cal(C)))
$

Their components are induced by the canonical inclusions into, and
evaluation maps out of, the active-operation colimits. They satisfy the
triangle identities

$
  epsilon_(f_!a) compose f_!(eta_a) tilde.eq id_(f_!a),
  quad
  f^ast(epsilon_b) compose eta_(f^ast b) tilde.eq id_(f^ast b)
$

#proofsketch[
  An $cal(O)$-algebra map $f_!a->b$ is determined by compatible maps from
  every term

  $ times.o_(alpha) (a(x_1),dots,a(x_n)) $

  in the active-operation colimit defining $f_!a$. By the universal property
  of this operadic colimit, such a compatible family is exactly an
  $cal(O)'$-algebra map $a->f^ast b$. The equivalence is natural in both
  variables, so it determines the adjunction together with its unit,
  counit, and triangle identities.
]

== Construction of Free Algebras

#definition(title:[Relative Free Algebra])[
  Let $f:cal(O)'^times.o->cal(O)^times.o$ be a map of $oo$-operads and
  suppose that $f_! ⊣ f^ast$ exists. For
  $a in Alg_(cal(O)') (cal(C))$, the #emph[relative free $cal(O)$-algebra
  generated by $a$] is simply $f_!a$; equivalently, its unit
  $a->f^ast f_!a$ induces, naturally in every
  $b in Alg_cal(O) (cal(C))$, the equivalence

  $
    Map_(Alg_cal(O) (cal(C))) (f_!a,b)
    tilde.eq
    Map_(Alg_(cal(O)') (cal(C))) (a,f^ast b)
  $
]

We now express the preceding adjunction directly in terms of generators and
operations. Let $q:cal(C)^times.o->cal(O)^times.o$ be a fibration of
$oo$-operads and suppose that we are given maps

$
  cal(A)^times.o ->^i cal(B)^times.o ->^j cal(O)^times.o
$

Restriction along $i$ gives

$
  theta=i^ast:
  Alg_(cal(B)\/cal(O)) (cal(C))
  ->Alg_(cal(A)\/cal(O)) (cal(C))
$

=== Free Relative Algebras

Let $a in Alg_(cal(A)\/cal(O)) (cal(C))$. For a color
$y in cal(B)$, define

$
  cal(K)_y
  :=cal(A)^times.o
    times_(cal(B)^times.o)
    (cal(B)^times.o_"act")_(\/y)
$

Thus $cal(K)_y$ parametrizes active operations in $cal(B)$ with output $y$
and with every input supplied by $cal(A)$. Evaluation of $a$ produces a
diagram $cal(K)_y->cal(C)^times.o_"act"$ over the corresponding diagram in
$cal(O)^times.o_"act"$.

#definition(title:[Free Algebra Generated by a Relative Algebra])[
  Let

  $
    b in Alg_(cal(B)\/cal(O)) (cal(C)),
    quad eta:a->i^ast b
  $

  The map $eta$ #emph[exhibits $b$ as a $q$-free $cal(B)$-algebra generated
  by $a$] if, for every $y in cal(B)$, the induced cone

  $ cal(K)_y^▹->cal(C)^times.o_"act" $

  is an operadic $q$-colimit diagram.
]

#proposition(title:[Universal Property of a Free Algebra])[
  If $eta:a->i^ast b$ exhibits $b$ as a $q$-free algebra generated by $a$,
  then for every $b' in Alg_(cal(B)\/cal(O)) (cal(C))$, composition with
  $eta$ induces a natural equivalence

  $
    Map_(Alg_(cal(B)\/cal(O)) (cal(C))) (b,b')
    tilde.eq
    Map_(Alg_(cal(A)\/cal(O)) (cal(C))) (a,i^ast b')
  $

  Consequently, $b$ is unique up to a contractible space of choices and is
  the value $i_!a$ whenever the left adjoint $i_!$ exists.
]

#proofsketch[
  A map $b->b'$ is determined at each output $y$ by a compatible cocone from
  the active-operation diagram indexed by $cal(K)_y$. The operadic colimit
  property identifies such cocones with maps from the original
  $cal(A)$-algebra $a$ to $i^ast b'$. Compatibility with inert morphisms
  assembles these pointwise equivalences into the stated equivalence of
  mapping anima.
]

=== Existence

#theorem(title:[Pointwise Existence Criterion])[
  For $a in Alg_(cal(A)\/cal(O)) (cal(C))$, the following conditions are
  equivalent.

  + There exist a $cal(B)$-algebra $b$ and a map $a->i^ast b$ which exhibit
    $b$ as a $q$-free algebra generated by $a$.

  + For every color $y in cal(B)$, the diagram indexed by $cal(K)_y$ extends
    to an operadic $q$-colimit cone lifting the canonical cone in
    $cal(O)^times.o_"act"$.
]

#corollary(title:[Existence under Small-Colimit Hypotheses])[
  Let $kappa$ be an uncountable regular cardinal. Suppose that
  $cal(A)^times.o$ and $cal(B)^times.o$ are essentially $kappa$-small and
  that $q$ is a coCartesian fibration compatible with $kappa$-small
  colimits. Then restriction admits a left adjoint

  $
    i_!:Alg_(cal(A)\/cal(O)) (cal(C))
    arrows.lr
    Alg_(cal(B)\/cal(O)) (cal(C)):i^ast
  $

  and $i_!a$ is the $q$-free $cal(B)$-algebra generated by $a$.
]

#proofsketch[
  The active indexing categories $cal(K)_y$ are $kappa$-small. Compatibility
  supplies the required operadic colimits, so the pointwise existence
  criterion constructs $i_!a$. The universal property above then identifies
  the resulting functor as the left adjoint of restriction.
]

#remark(title:[The Unital Improvement])[
  If the operads are unital, the relevant active indexing categories are
  weakly contractible. It is then enough to assume the existence and
  separate preservation of weakly contractible $kappa$-small colimits. This
  weaker form is often the useful one in practice.
]

#remark(title:[Naturality])[
  Let $T:cal(C)^times.o->cal(D)^times.o$ be an $cal(O)$-monoidal functor
  which preserves the colimits appearing above. Then $T$ preserves free
  algebras:

  $ T(i_!a) tilde.eq i_!(T(a)) $
]

=== Operadic Symmetric Powers

We specialize to the inclusion

$ cat("Triv")^times.o->cal(O)^times.o $

which selects a color $x in cal(O)$. Let $c in cal(C)_x$ and let
$y in cal(O)$. For $n>=0$, denote by $cal(P)_(x,y) (n)$ the anima of active
operations with $n$ inputs of color $x$ and output $y$, including their
permutations and higher homotopies. Its fiber over a chosen ordering is

$ Mul_cal(O) ({x}_(1<=i<=n);y) $

CoCartesian transport along an operation $alpha in cal(P)_(x,y) (n)$ gives
an object

$ times.o_(alpha) (c,dots,c) in cal(C)_y $

#definition(title:[Operadic Symmetric Power])[
  The $n$th operadic symmetric power of $c$ from $x$ to $y$ is

  $
    "Sym"_(cal(O);x,y)^(n) (c)
    :=colim_(alpha in cal(P)_(x,y) (n))
      times.o_(alpha) (c,dots,c)
  $
]

#theorem(title:[Explicit Free-Algebra Formula])[
  Under the small-colimit hypotheses above, the free $cal(O)$-algebra on
  $c in cal(C)_x$ exists. Its value at a color $y$ is

  $
    "Free"_cal(O)(c)(y)
    tilde.eq
    coprod_(n>=0) "Sym"_(cal(O);x,y)^(n) (c)
  $

  A map $c->a(x)$ exhibits an $cal(O)$-algebra $a$ as free on $c$ if and
  only if these canonical maps are equivalences for every $y$.
]

#proofsketch[
  Decompose the active indexing category $cal(I)_y$ by the number $n$ of
  inputs. Its $n$th component is $cal(P)_(x,y) (n)$, so the pointwise
  operadic Kan-extension formula becomes the coproduct of the corresponding
  colimits. The universal property follows from the adjunction
  $"Free"_cal(O) ⊣ U$.
]

#example(title:[Commutative Algebras])[
  For $cal(O)=Comm$ there is one color and
  $cal(P)_(x,x) (n) tilde.eq B Sigma_n$. Therefore

  $
    "Sym"^ast (c)
    tilde.eq
    coprod_(n>=0) (c^(times.o n))_(h Sigma_n)
  $

  which is the homotopy-coherent version of the classical symmetric algebra.
]

#remark(title:[Relation with Operadic Left Kan Extension])[
  Free-algebra construction introduces no new mechanism: it is precisely the
  operadic left Kan extension along $i$. The factorization through a
  correspondence of operads is used only to organize its coherent
  construction. The long technical proof attaches simplices one at a time;
  active faces impose the universal colimit condition, while inert faces
  impose the operadic Segal compatibility.
]

== Transitivity of Operadic Left Kan Extensions

Suppose that we have composable maps of $oo$-operads

$
  cal(O)_0^times.o ->^f cal(O)_1^times.o
  ->^g cal(O)_2^times.o
$

and an $cal(O)_2$-monoidal $oo$-category $cal(C)^times.o$. Assume that the
operadic left Kan extensions below exist; it is enough, for example, that
the relevant active indexing categories are small and that the operadic
tensor products in $cal(C)$ preserve their colimits separately in each
variable.

#theorem(title:[Transitivity])[
  For every $a in Alg_(cal(O)_0) (cal(C))$, there is a canonical natural
  equivalence

  $
    (g compose f)_!a
    tilde.eq g_!(f_!a)
  $

  Thus extending an algebra structure from $cal(O)_0$ directly to
  $cal(O)_2$ agrees with first extending it to $cal(O)_1$ and then to
  $cal(O)_2$.
]

#align(center)[
  #diagram(
    node-stroke: none,
    edge-stroke: .7pt,
    node((0, 0), [$Alg_(cal(O)_0) (cal(C))$], name: <a0>),
    node((4, 0), [$Alg_(cal(O)_1) (cal(C))$], name: <a1>),
    node((2, 1.4), [$Alg_(cal(O)_2) (cal(C))$], name: <a2>),
    edge(<a0>, <a1>, [$f_!$], "->"),
    edge(<a1>, <a2>, [$g_!$], label-side: left, "->"),
    edge(<a0>, <a2>, [$(g compose f)_!$], label-side: right, "->"),
  )
]

#remark(title:[Pointwise Meaning])[
  Let $cal(K)_f(y)$ denote the active operations from $cal(O)_0$ whose
  image under $f$ has output $y in cal(O)_1$, and define
  $cal(K)_g(z)$ similarly. The iterated construction of $g_!f_!a$ is indexed
  by

  $
    integral_(beta in cal(K)_g(z))
    product_i cal(K)_f(y_i)
  $

  where the inputs of $beta$ are $y_1,dots,y_n$. Operadic substitution
  composes these operations and gives the active indexing category for
  $(g compose f)_!a$.
]

#proofsketch[
  Substitute the colimit formula for each value $(f_!a)(y_i)$ into the
  pointwise formula for $g_!$. The Fubini rule for colimits rewrites the
  resulting iterated colimit as a single colimit over the displayed
  Grothendieck construction. Operadic composition identifies this index
  cofinally with the active slice defining $(g compose f)_!a$, producing
  the claimed equivalence. Equivalently, once the adjunctions exist,

  $
    (g compose f)^ast=f^ast compose g^ast
  $

  and both $(g compose f)_!$ and $g_! compose f_!$ are left adjoint to this
  restriction functor, hence are canonically equivalent.
]

#remark(title:[Why a Flatness Hypothesis Appears])[
  In the family-valued formulation, one assumes that the family over
  $Delta^2$ is flat. Its role is exactly to ensure that the two-stage active
  indexing category above computes the direct one without introducing extra
  homotopy. For ordinary composable operad maps under the preceding
  colimit-compatibility assumptions, the practical conclusion is simply the
  transitivity formula above.
]

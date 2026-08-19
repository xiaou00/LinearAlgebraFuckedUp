#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= (co)Limits of Algebras

Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category and let
$cal(O)^times.o$ be an $oo$-operad. This chapter studies limits and colimits
in $Alg_cal(O) (cal(C))$.

#quote[
  Limits of algebras are usually detected on the underlying objects;
  colimits must also be compatible with every operadic multiplication.
]

More precisely, limits are generally computed in the underlying fibers
whenever the required limits exist there; no tensor-preservation hypothesis
is needed. Colimits are subtler. Sifted colimits are often still computed underneath
when tensor products preserve them separately in each variable, whereas
arbitrary coproducts usually are not. The free-algebra construction of the
preceding chapter provides the standard method: resolve a diagram by free
algebras, compute there, and then recover its colimit geometrically.

#remark(title:[Two Important Extremes])[
  For commutative algebras, finite coproducts are tensor products in the
  underlying symmetric monoidal category. At the opposite extreme, the
  empty coproduct is the initial algebra. We begin with the latter because
  it is controlled entirely by nullary operations and unit objects.
]

== Unit Objects and Trivial Algebras

Let

$ p:cal(C)^times.o->cal(O)^times.o $

be a fibration of $oo$-operads, and suppose that $cal(O)^times.o$ is unital.
Write $cal(C)$ and $cal(O)$ for the fibers over
$chevron.l 1 chevron.r$. The fiber over $chevron.l 0 chevron.r$ records the
nullary input.

=== Relative Unit Objects

#definition(title:[$x$-Unit Object])[
  Let $x in cal(O)^times.o$ and let $1_x in cal(C)^times.o_x$. A morphism

  $ u:c_0->1_x $

  #emph[exhibits $1_x$ as an $x$-unit object] if
  $c_0 in cal(C)^times.o_(chevron.l 0 chevron.r)$ and the edge $u$, regarded
  as a cone $Delta^1 tilde.eq (Delta^0)^▹->cal(C)^times.o$, is
  an operadic $p$-colimit diagram.
]

Thus $1_x$ is not merely a chosen object: it is the universal value of the
empty tensor product in the fiber over $x$. Its universal property makes it
unique up to a contractible space of choices.

#remark(title:[A Unit Relative to a Color])[
  The object $1_x$ is the unit #emph[relative to the color $x$] of the base
  operad. Different colors may therefore have units in different fibers
  $cal(C)_x$; for a one-colored operad this reduces to the usual tensor unit
  $1 in cal(C)$.
]

#definition(title:[Unit Object in a Tuple])[
  A morphism $u:c_0->c$ in $cal(C)^times.o$ #emph[exhibits $c$ as a unit
  object] if, for every inert projection $c->c_i$ to a component over
  $chevron.l 1 chevron.r$, the composite

  $ c_0->c->c_i $

  exhibits $c_i$ as a $p(c_i)$-unit object.

  We say that $p$ #emph[has unit objects] if such a lift exists for every
  object of $cal(O)^times.o$.
]

#remark(title:[How to Recognize Them])[
  Every morphism exhibiting a unit is $p$-coCartesian. Conversely, a
  $p$-coCartesian lift out of a nullary object exhibits a unit as soon as
  each unary component does. Consequently it is enough to construct units
  one color at a time; units for tuples are obtained by concatenating the
  corresponding unary units.
]

#proposition(title:[Units in a Monoidal Family])[
  If $p$ is a coCartesian fibration of $oo$-operads and
  $cal(O)^times.o$ is unital, then $p$ has unit objects. Equivalently, for
  every color $x in cal(O)$, the fiber $cal(C)_x$ contains an essentially
  unique object $1_x$ representing the empty tensor product.
]

#proofsketch[
  The unique nullary operation of the unital operad $cal(O)^times.o$ has a
  coCartesian lift. The operadic colimit criterion shows that its target is
  an $x$-unit. CoCartesian composition constructs the units of arbitrary
  tuples, and the same universal property makes all choices contractible.
]

=== Trivial Algebras

#definition(title:[Trivial Algebra])[
  An algebra $a in Alg_(cal(O)\/cal(O)) (cal(C))$ is #emph[trivial] if, for
  every $x in cal(O)^times.o$, the canonical morphism

  $ a(0)->a(x) $

  exhibits $a(x)$ as a unit object. Here $0$ denotes the nullary object of
  $cal(O)^times.o$.
]

In other words, a trivial algebra interprets every color by its corresponding
unit and every operation by the uniquely induced map between units. It has
no algebraic data beyond the units forced by the operad.

#theorem(title:[Initial Algebra Criterion])[
  Assume that $p$ has unit objects. For
  $a in Alg_(cal(O)\/cal(O)) (cal(C))$, the following conditions are
  equivalent.

  + The algebra $a$ is initial in $Alg_(cal(O)\/cal(O)) (cal(C))$.

  + The section $a$ is the operadic $p$-left Kan extension of its restriction
    to the nullary fiber
    $cal(O)^times.o_(chevron.l 0 chevron.r)$.

  + The algebra $a$ is trivial.
]

#proofsketch[
  Extending from the nullary fiber forces every value of $a$ to be the
  appropriate unit object, so the second and third conditions agree. A map
  from units into the values of any algebra is determined by the unit maps
  of that algebra and has a contractible space of coherent choices. Hence a
  trivial algebra admits an essentially unique map to every algebra and is
  initial. Conversely, an initial algebra agrees with the nullary left Kan
  extension, which exists because $p$ has unit objects.
]

#proposition(title:[Existence])[
  For a fibration of $oo$-operads over a unital $cal(O)^times.o$, the
  following conditions are equivalent.

  + The fibration $p$ has unit objects.

  + The $oo$-category $Alg_(cal(O)\/cal(O)) (cal(C))$ contains a trivial
    algebra.

  Whenever they hold, the trivial algebra is the initial algebra.
]

#corollary(title:[The Initial Commutative Algebra])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category. Then
  $CAlg(cal(C))$ has an initial object. A commutative algebra $a$ is initial
  if and only if its unit map

  $ 1->a $

  is an equivalence in $cal(C)$. Thus the initial commutative algebra is the
  tensor unit equipped with its canonical commutative multiplication.
]

== Limits of Algebras

The basic phenomenon already appears for ordinary commutative algebras. Let
$a,b in CAlg(cal(C))$ and suppose that the product $a times b$ exists in
$cal(C)$. Its multiplication is the composite

$
  (a times b) times.o (a times b)
  ->(a times.o a) times (b times.o b)
  ->a times b
$

obtained from the projections and the multiplications of $a$ and $b$.
Hence the product in $CAlg(cal(C))$ is the product of the underlying
objects. The same argument works for arbitrary operads, arbitrary diagram
shapes, and relative limits.

=== Relative Limits

Let $cal(O)^times.o$ be an $oo$-operad and let

$ p:cal(C)^times.o->cal(D)^times.o $

be a fibration of $oo$-operads over $cal(O)^times.o$. It induces a functor

$
  q:Alg_(cal(O)\/cal(O)) (cal(C))
  ->Alg_(cal(O)\/cal(O)) (cal(D))
$

For each color $x in cal(O)$, write
$p_x:cal(C)_x->cal(D)_x$ for the induced functor between fibers.

#definition(title:[Relative Limit])[
  A cone in $cal(C)_x$ lying over a fixed cone in $cal(D)_x$ is a
  #emph[$p_x$-limit cone] if it is terminal among the cones with that fixed
  image in $cal(D)_x$. Thus a relative limit is computed while the cone in
  the base is held fixed.
]

#theorem(title:[Fiberwise Criterion for Relative Limits])[
  Let $k$ be a simplicial set, let

  $ d:k->Alg_(cal(O)\/cal(O)) (cal(C)) $

  be a diagram, and fix a cone

  $ e:k^◃->Alg_(cal(O)\/cal(O)) (cal(D)) $

  extending $q compose d$. Suppose that, for every color $x in cal(O)$, the
  evaluated diagram $d_x:k->cal(C)_x$ admits a $p_x$-limit cone lying over
  $e_x$. Then:

  + these fiberwise cones assemble into a cone
    $overline(d):k^◃->Alg_(cal(O)\/cal(O)) (cal(C))$ lying over $e$

  + a cone over $d$ is a $q$-limit cone if and only if its evaluation at
    every color $x$ is a $p_x$-limit cone
]

#remark(title:[Relative versus Ordinary Limits])[
  A $p_x$-limit is generally stronger than an ordinary limit in
  $cal(C)_x$: its universal property is relative to the prescribed cone in
  $cal(D)_x$. The two notions coincide when the base is terminal, which is
  the absolute situation below.
]

#proofsketch[
  Choose the relative limit object separately in each fiber. For an
  operation $alpha:(x_1,dots,x_n)->y$, the projections of the cones give
  compatible maps from the tuple of limit objects to every stage of the
  diagram in $cal(C)_y$. The universal property of the $p_y$-limit produces
  the required structure map at $y$. Its coherence is forced because it can
  be checked after all cone projections. The same argument shows that the
  global cone is universal precisely when each evaluated cone is universal.
]

=== Absolute Limits Are Computed Fiberwise

Now let

$ r:cal(C)^times.o->cal(O)^times.o $

be a coCartesian fibration of $oo$-operads. For every color $x$, evaluation
defines a functor

$ "ev"_x:Alg_(cal(O)\/cal(O)) (cal(C))->cal(C)_x $

#corollary(title:[Limits of Algebras])[
  Let $k$ be a simplicial set and suppose that every fiber $cal(C)_x$ admits
  $k$-indexed limits. Then $Alg_(cal(O)\/cal(O)) (cal(C))$ admits
  $k$-indexed limits, and a cone of algebras is a limit cone if and only if
  its evaluation in every $cal(C)_x$ is a limit cone. In particular, every
  evaluation functor $"ev"_x$ preserves these limits.
]

#remark(title:[No Tensor-Preservation Hypothesis])[
  Unlike colimits, this statement does not require the operadic tensor
  products to preserve limits. To define an operation on a limit, one maps
  from the tensor product of the limit objects to every stage and then uses
  the universal property of the target limit. For colimits the arrows point
  in the opposite direction, which is exactly why separate preservation by
  tensor products becomes necessary there.
]

#corollary(title:[Equivalences Are Detected Colorwise])[
  A morphism $eta:a->b$ of $cal(O)$-algebras is an equivalence if and only
  if

  $ eta_x:a(x)->b(x) $

  is an equivalence in $cal(C)_x$ for every color $x in cal(O)$.
]

#quote[
  To compute a limit of operadic algebras, forget to every color, take the
  limit in the corresponding fiber, and recover all operations from the
  universal property of those limits.
]

== Colimits of Algebras

For colimits the preceding argument cannot simply be reversed: an operation
must carry the colimits of its inputs to the colimit of its outputs. We first
treat sifted diagrams, where this compatibility gives a pointwise answer,
and then obtain general colimits from free-algebra resolutions.

=== Sifted Colimits Are Computed Fiberwise

Let

$ p:cal(C)^times.o->cal(O)^times.o $

be a coCartesian fibration of $oo$-operads, let $k$ be a sifted simplicial
set, and assume that $p$ is compatible with $k$-indexed colimits: every
fiber $cal(C)_x$ admits them and every operadic tensor functor preserves them
separately in each variable.

#theorem(title:[Pointwise Sifted Colimits])[
  The $oo$-category $Alg_(cal(O)\/cal(O)) (cal(C))$ admits $k$-indexed
  colimits. A cocone

  $ overline(d):k^▹->Alg_(cal(O)\/cal(O)) (cal(C)) $

  is a colimit cocone if and only if, for every color $x in cal(O)$, its
  evaluation

  $ overline(d)_x:k^▹->cal(C)_x $

  is a colimit cocone. Consequently the evaluation functors create these
  colimits.
]

#remark(title:[Why Siftedness Is the Right Hypothesis])[
  For an $n$-ary operation, separate preservation gives colimits in one
  input at a time. Siftedness says that the diagonal $k->k^n$ is cofinal, so
  these iterated colimits agree with the colimit of the original single
  $k$-diagram. This is precisely what lets the pointwise colimit inherit all
  $n$-ary operations.
]

#proofsketch[
  Form $c_x:=colim_(i in k)d_i (x)$ in every fiber. For an operation
  $alpha:(x_1,dots,x_n)->y$, compatibility with colimits and cofinality of
  the diagonal give

  $
    times.o_(alpha) (c_(x_1),dots,c_(x_n))
    tilde.eq
    colim_(i in k)
    times.o_(alpha) (d_i (x_1),dots,d_i (x_n))
  $

  The algebra structures of the $d_i$ therefore induce a structure map to
  $c_y$. Operadic coherence is inherited stagewise, and the same calculation
  identifies maps out of $c$ with compatible cocones, proving universality.
]

#corollary(title:[Sifted Colimits of Commutative Algebras])[
  Let $cal(C)^times.o$ be symmetric monoidal and compatible with
  $k$-indexed sifted colimits. Then $CAlg(cal(C))$ admits these colimits, and
  the forgetful functor

  $ U:CAlg(cal(C))->cal(C) $

  creates them.
]

#remark(title:[A Unital Improvement])[
  Suppose that the structure map

  $ cal(O)^times.o->Comm^times.o $

  factors through $EE_0^times.o$. Then every operation has arity at most
  one. In this case the same pointwise theorem holds for any weakly
  contractible indexing simplicial set $k$, provided the fiber transports
  preserve the relevant $k$-colimits. There are no genuinely multivariable
  operations, so siftedness is no longer needed; weak contractibility deals
  with the nullary operation.
]

=== General Colimits from Free Algebras

#theorem(title:[Existence of Small Colimits])[
  Let $kappa$ be an uncountable regular cardinal. Suppose that
  $cal(O)^times.o$ is essentially $kappa$-small and that
  $p:cal(C)^times.o->cal(O)^times.o$ is compatible with $kappa$-small
  colimits. Then $Alg_(cal(O)\/cal(O)) (cal(C))$ admits all
  $kappa$-small colimits.
]

#proofsketch[
  The forgetful functor from algebras with only their underlying colored
  objects has the free-algebra functor as a left adjoint. Every algebra is
  the geometric realization of its simplicial free-algebra resolution.
  Sifted colimits and geometric realizations are computed fiberwise by the
  preceding theorem, while coproducts of free algebras exist because the
  free functor preserves colimits. Combining geometric realizations, sifted
  colimits, and finite coproducts constructs every $kappa$-small colimit.
]

#remark(title:[Why the General Formula Is Less Explicit])[
  The theorem gives existence but usually not a short pointwise formula for
  an arbitrary coproduct of algebras. The free resolution replaces the
  original diagram by one whose coproduct is easy, then imposes the algebraic
  relations through a geometric realization.
]

=== Accessibility and Presentability

#theorem(title:[Presentability Criterion])[
  Assume that $cal(O)^times.o$ is essentially small.

  + If every fiber $cal(C)_x$ is accessible and all transport functors
    induced by morphisms of $cal(O)^times.o$ are accessible, then
    $Alg_(cal(O)\/cal(O)) (cal(C))$ is accessible.

  + If every fiber $cal(C)_x$ is presentable and $p$ is compatible with all
    small colimits, then $Alg_(cal(O)\/cal(O)) (cal(C))$ is presentable.
]

#corollary(title:[The Standard Symmetric Monoidal Case])[
  If $cal(C)$ is a presentable $oo$-category and its symmetric monoidal
  tensor product preserves small colimits separately in each variable, then
  $CAlg(cal(C))$ is presentable. More generally, the same holds for
  $cal(O)$-algebras whenever $cal(O)^times.o$ is essentially small.
]

#quote[
  Sifted colimits of algebras are computed colorwise; arbitrary colimits are
  built by resolving into free algebras; presentability follows when these
  constructions are accessible.
]

== Tensor Products of Commutative Algebras

The preceding existence theorem constructs coproducts indirectly. This is
unavoidable for associative algebras: their coproduct is a free product and
has no simple formula in terms of the underlying objects. For commutative
algebras, however, the tensor product already has the coproduct universal
property. We first record the operadic construction which produces this
tensor product.

=== A Family of Algebra Categories

Let

$
  f:cal(O)^times.o times cal(P)^times.o->cal(Q)^times.o
$

be an operadic bifunctor and let

$ q:cal(C)^times.o->cal(Q)^times.o $

be a fibration of $oo$-operads. For a color $y in cal(P)$, write
$f_y:cal(O)^times.o->cal(Q)^times.o$ for the restriction of $f$ to
$cal(O)^times.o times {y}$.

#definition(title:[The Parametrized Algebra Operad])[
  The $oo$-operad

  $ Alg_f (cal(C))^times.o->cal(P)^times.o $

  is the family whose fiber over $y$ is the $oo$-category of lifts $a$ in
  the diagram

  #align(center, diagram({
    node((0, 0), [$cal(O)^times.o$])
    node((1, 0), [$cal(C)^times.o$])
    node((0, 1), [$cal(Q)^times.o$])
    node((1, 1), [$cal(Q)^times.o$])
    edge((0, 0), (1, 0), [$a$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f_y$], label-side: right, "->")
    edge((1, 0), (1, 1), [$q$], label-side: left, "->")
    edge((0, 1), (1, 1), [$id$], label-side: left, "->")
  }))

  Thus its objects over $y$ are $cal(O)$-algebra objects in $cal(C)$ whose
  structural map to $cal(Q)^times.o$ is prescribed by $f_y$. Transport in
  the $cal(P)$-direction varies this algebra structure functorially.
]

#proposition(title:[Operadic Structure of the Family])[
  The projection $Alg_f (cal(C))^times.o->cal(P)^times.o$ is a fibration of
  $oo$-operads. Moreover:

  + a morphism is inert precisely when its image in $cal(P)^times.o$ is
    inert and its value at every color of $cal(O)$ is inert in
    $cal(C)^times.o$;

  + if $q$ is a coCartesian fibration, then so is
    $Alg_f (cal(C))^times.o->cal(P)^times.o$;

  + in that case, a morphism is coCartesian precisely when it is
    $q$-coCartesian after evaluation at every color of $cal(O)$.
]

#proofsketch[
  The Segal decomposition reduces an object and a morphism over
  $chevron.l n chevron.r$ to their values at the $n$ inert projections.
  Consequently inertness and the coCartesian mapping-space criterion can be
  tested color by color. CoCartesian lifts are obtained by lifting the
  corresponding component maps in $cal(C)^times.o$ and then reassembling
  them by the same Segal equivalence.
]

=== Pointwise Tensor Products of Algebras

There is a unique operadic bifunctor

$ Comm^times.o times cal(O)^times.o->Comm^times.o $

for every $oo$-operad $cal(O)^times.o$. Applying the preceding construction
to a symmetric monoidal $oo$-category $cal(C)^times.o$ gives an
$cal(O)$-monoidal structure on $Alg_cal(O) (cal(C))$.

#proposition(title:[Pointwise Tensor Product])[
  The induced tensor product is evaluated colorwise. For
  $a,b in Alg_cal(O) (cal(C))$ and every color $x in cal(O)$,

  $ (a times.o b)(x) tilde.eq a(x) times.o b(x) $

  The unit is the constant algebra determined by $1_cal(C)$, and every
  evaluation functor

  $ "ev"_x:Alg_cal(O) (cal(C))->cal(C) $

  is symmetric monoidal.
]

#remark(title:[Why Commutativity Matters])[
  Pointwise multiplication uses the interchange map which lets an
  $cal(O)$-operation pass through the tensor product. For associative
  algebras, two maps into a target need not commute, so their coproduct is a
  free product. In a commutative target the required interchange is
  automatic; this is what turns the pointwise tensor product into a
  coproduct.
]

=== Tensor Product Is Coproduct

#theorem(title:[Tensor Products of Commutative Algebras])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category. The pointwise
  symmetric monoidal structure on $CAlg(cal(C))$ is coCartesian. Hence
  $CAlg(cal(C))$ admits finite coproducts, its initial object is the unit
  algebra $1_cal(C)$, and

  $ a coprod_(CAlg(cal(C))) b tilde.eq a times.o b $

  for all commutative algebra objects $a,b$.
]

#proofsketch[
  The multiplication of a commutative algebra $a$ gives a natural fold map

  $ delta_a:a times.o a->a $

  and its unit gives $1_cal(C)->a$. The exponential law

  $ CAlg(CAlg(cal(C))) tilde.eq CAlg(cal(C)) $

  makes these fold maps coherent. Commutativity, associativity, and
  unitality then verify the intrinsic criterion for a coCartesian symmetric
  monoidal structure. Consequently

  $
    Map_(CAlg(cal(C))) (a times.o b,c)
    tilde.eq
    Map_(CAlg(cal(C))) (a,c) times Map_(CAlg(cal(C))) (b,c)
  $

  which is exactly the coproduct universal property.
]

#corollary(title:[A Concrete Coproduct Formula])[
  Whenever the underlying tensor product is familiar, it directly computes
  coproducts of commutative algebras. For example, for commutative rings,

  $ a coprod b tilde.eq a times.o_ZZ b $

  while for commutative algebra spectra it is the smash product
  $a smash_(SS) b$ over the sphere spectrum.
]

#remark(title:[Maps out of a coCartesian Monoidal Category])[
  Let $cal(B)$ admit finite coproducts. A functor $g:cal(B)->cal(D)$ defines
  a symmetric monoidal functor from $cal(B)^coprod$ precisely when it
  preserves finite coproducts. Thus, once $CAlg(cal(C))$ is equipped with the
  tensor product above, a symmetric monoidal functor out of it is the same
  thing as a functor preserving its initial object and binary coproducts.
]

#quote[
  In commutative algebra, tensor product is not merely compatible with
  coproducts: it is the coproduct.
]

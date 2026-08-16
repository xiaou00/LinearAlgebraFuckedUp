#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= $oo$-Operads: Constructions

We now study how categorical constructions interact with
$cal(O)$-monoidal structures. Recall that a symmetric monoidal
$oo$-category is the special case of an $oo$-operad
$cal(C)^times.o->Ner(Fin_*)$ whose structure map is a coCartesian fibration.

== Subcategories of $cal(O)$-Monoidal $oo$-Categories

=== Tensor-Closed Subcategories

Let $p:cal(C)^times.o->cal(O)^times.o$ be an $cal(O)$-monoidal
$oo$-category. If $cal(D) subset cal(C)$ is a full subcategory stable under
equivalence, let $cal(D)^times.o subset cal(C)^times.o$ be the full
subcategory consisting of tuples whose components all belong to $cal(D)$.
For a color $x in cal(O)$, write

$ cal(D)_x:=cal(D) inter cal(C)_x $

#proposition(title:[Inheritance by a Tensor-Closed Subcategory])[
  Suppose that, for every operation

  $ f in Mul_cal(O) ({x_i}_(1<=i<=n);y) $

  the associated tensor functor satisfies

  $
    times.o_f
    (product_(i=1)^n cal(D)_(x_i))
    subset cal(D)_y
  $

  Then the restriction

  $ p|_(cal(D)^times.o):cal(D)^times.o->cal(O)^times.o $

  is a coCartesian fibration of $oo$-operads. Hence $cal(D)$ inherits an
  $cal(O)$-monoidal structure, and the inclusion
  $cal(D)^times.o->cal(C)^times.o$ is $cal(O)$-monoidal.
]

#proofsketch[
  The Segal equivalence identifies the fiber of $cal(D)^times.o$ over a tuple
  with the product of the corresponding fibers $cal(D)_(x_i)$. The closure
  hypothesis says exactly that coCartesian transport along every active map
  stays inside $cal(D)^times.o$; inert transport merely selects components
  and does so automatically. Thus the restricted projection is coCartesian
  and still satisfies the operadic Segal condition.
]

#remark(title:[The Symmetric Monoidal Criterion])[
  If $cal(C)$ is symmetric monoidal, a full replete subcategory
  $cal(D) subset cal(C)$ inherits the restricted symmetric monoidal structure
  if and only if it contains the unit and is closed under the binary tensor
  product

  $ 1 in cal(D), quad d times.o d' in cal(D) $

  The nullary operation detects the unit, while iteration of the binary
  operation gives all finite tensor products.
]

=== Colocalizations and Algebra Objects

#proposition(title:[Fiberwise Colocalization])[
  In the situation above, suppose moreover that every inclusion
  $i_x:cal(D)_x->cal(C)_x$ admits a right adjoint $r_x$. Then the functors
  ${r_x}_(x in cal(O))$ assemble into a map of $oo$-operads

  $ r^times.o:cal(C)^times.o->cal(D)^times.o $

  which is right adjoint to the inclusion. There is a counit
  $i^times.o compose r^times.o->id$ lying over the identity of
  $cal(O)^times.o$.
]

#proofsketch[
  Apply $r_x$ componentwise in every Segal fiber. Closure under all tensor
  operations ensures that the universal colocalizing arrows are preserved by
  operadic transport. Their spaces of choices are contractible, so the
  fiberwise right adjoints assemble coherently and preserve inert morphisms.
]

#corollary(title:[Colocalization of Algebra Objects])[
  For every map $alpha:cal(P)^times.o->cal(O)^times.o$, the inclusion induces
  a fully faithful functor

  $
    Alg_(cal(P)\/cal(O))(cal(D))
    ->Alg_(cal(P)\/cal(O))(cal(C))
  $

  and postcomposition with $r^times.o$ is its right adjoint. Thus an algebra
  object colocalizes by applying $r_x$ to its underlying objects and then
  using the induced operadic structure.
]

=== Compatible Monoidal Localizations

#remark(title:[Recall: Localization and Colocalization])[
  A #emph[localization] of an $oo$-category $cal(C)$ consists of a full
  subcategory $i:cal(D) arrow.r.hook cal(C)$ for which the inclusion admits
  a left adjoint

  $ ell:cal(C) arrows.lr cal(D):i $

  We usually regard $ell$ as the endofunctor $i compose ell$ of $cal(C)$. Its
  unit $eta:id->ell$ is idempotent: both $ell eta_c$ and $eta_(ell c)$ are
  equivalences. An object $d$ is #emph[local] if $eta_d$ is an equivalence,
  equivalently if $d$ belongs to the essential image of $ell$. The adjunction
  is characterized by

  $ Map_cal(C) (ell c,d) tilde.eq Map_cal(C) (c,d) $

  for every local object $d$. A morphism $g$ is an
  #emph[$ell$-equivalence] if $ell(g)$ is an equivalence; equivalently,
  precomposition with $g$ induces an equivalence of mapping spaces into every
  local object.

  Dually, a #emph[colocalization] is a full subcategory whose inclusion admits
  a right adjoint $r$, with counit $r->id$. Thus localization reflects objects
  into a subcategory, while colocalization coreflects them.
]

#definition(title:[Compatibility with an $cal(O)$-Monoidal Structure])[
  Suppose that for every color $x in cal(O)$ we have a localization
  $ell_x:cal(C)_x->cal(C)_x$. A morphism $g$ in $cal(C)_x$ is an
  #emph[$ell_x$-equivalence] if $ell_x(g)$ is an equivalence. The family
  ${ell_x}_(x in cal(O))$ is #emph[compatible with the $cal(O)$-monoidal
  structure] if, for every operation

  $ f in Mul_cal(O) ({x_i}_(1<=i<=n);y) $

  and every family of $ell_(x_i)$-equivalences $g_i$, the morphism

  $ times.o_f ({g_i}_(1<=i<=n)) $

  is an $ell_y$-equivalence.
]

#remark(title:[One-Colored Test])[
  For a localization $ell:cal(C)->cal(C)$ of a symmetric monoidal
  $oo$-category, compatibility is equivalent to the elementary condition

  $ g " is an " ell"-equivalence"
    ==> g times.o id_z " is an " ell"-equivalence" $

  for every object $z$. By symmetry and iteration, this tests all variables
  and all arities.
]

#lemma(title:[Fiberwise Localization Lemma])[
  Let $q:cal(E)->cal(B)$ be a coCartesian fibration, and let $ell_E,ell_B$ be
  localizations whose essential images are $cal(E)'$ and $cal(B)'$. Suppose
  that $q$ restricts to $q':cal(E)'->cal(B)'$ and carries
  $ell_E$-equivalences to $ell_B$-equivalences. Then $ell_E$ carries
  $q$-coCartesian morphisms to $q'$-coCartesian morphisms, and $q'$ is a
  coCartesian fibration.
]

#proofsketch[
  The coCartesian property is detected by the usual homotopy-Cartesian square
  of mapping spaces. Mapping into a local object identifies the localized and
  unlocalized mapping spaces, while compatibility identifies their bases.
  The defining square therefore remains homotopy Cartesian after applying the
  localizations.
]

#proposition(title:[Monoidal Localization])[
  Let ${ell_x}_(x in cal(O))$ be a compatible family of localizations, and let
  $cal(D)_x$ be the essential image of $ell_x$. Then:

  1. the fiberwise functors assemble into a localization
     $ell^times.o:cal(C)^times.o->cal(D)^times.o$ over
     $cal(O)^times.o$

  2. the projection $cal(D)^times.o->cal(O)^times.o$ is a coCartesian
     fibration of $oo$-operads

  3. the inclusion is a map of $oo$-operads and $ell^times.o$ is an
     $cal(O)$-monoidal functor

  The induced operation on local objects is characterized by

  $
    times.o_f^cal(D)(d_1,dots,d_n)
    tilde.eq
    ell_y (times.o_f^cal(C)(d_1,dots,d_n))
  $
]

#proofsketch[
  Compatibility says that each tensor functor descends through the
  localizations. The fiberwise localization lemma shows that the descended
  transport is coCartesian. Applying the Segal equivalence fiberwise then
  constructs $cal(D)^times.o$ and shows that $ell^times.o$ preserves the
  required coCartesian morphisms. The unit maps
  $id->ell_x$ assemble because their spaces of extensions are contractible.
]

#remark(title:[Restriction versus Localization])[
  If local objects are already closed under the tensor products of
  $cal(C)$, the inherited tensor is simply the restriction considered above.
  In general they need not be tensor-closed: the localized category still
  becomes monoidal, but one must tensor in $cal(C)$ and then apply $ell$.
]

=== Compatible $t$-Structures

#definition(title:[Monoidal Compatibility of $t$-Structures])[
  Suppose every fiber $cal(C)_x$ is stable, every operation $times.o_f$ is
  exact in each variable, and each fiber carries a $t$-structure. The family
  is #emph[compatible with the $cal(O)$-monoidal structure] if

  $
    times.o_f
    (product_(i=1)^n (cal(C)_(x_i))_(>=0))
    subset (cal(C)_y)_(>=0)
  $

  for every operation $f$ of $cal(O)$.
]

#proposition(title:[Connective and Truncated Objects])[
  For a compatible family of $t$-structures:

  1. the connective objects $cal(C)_(>=0)$ inherit an
     $cal(O)$-monoidal structure

  2. exactness gives the degree estimate

     $
       times.o_f
       (product_(i=1)^n (cal(C)_(x_i))_(>=m_i))
       subset (cal(C)_y)_(>=sum_i m_i)
     $

  3. for every $k>=0$, the truncation localizations
     $tau_(<=k):(cal(C)_x)_(>=0)->(cal(C)_x)_(>=0)$ form a compatible family
     and hence the subcategories
     $(cal(C)_x)_(>=0) inter (cal(C)_x)_(<=k)$ inherit the induced
     $cal(O)$-monoidal structure
]

#proofsketch[
  The first statement is the tensor-closed subcategory criterion. For the
  third, it is enough to vary one input. If $g:c->c'$ is a
  $tau_(<=k)$-equivalence between connective objects, then its fiber belongs
  to degree $>=k+1$. Exactness in that variable and the degree estimate put
  the fiber of $times.o_f (g)$ in degree $>=k+1$, so applying $tau_(<=k)$
  makes $times.o_f (g)$ an equivalence. This is precisely compatibility of the
  truncation localizations.
]

#corollary(title:[The Heart Inherits the Tensor Product])[
  Taking $k=0$, the hearts of a compatible family of $t$-structures inherit
  the corresponding monoidal operations. In particular, the heart of a
  symmetric monoidal stable $oo$-category with compatible $t$-structure is
  an ordinary symmetric monoidal category.
]

== Slicing $oo$-Operads

=== Relative Slice Constructions

Let $q:x->s$ be a map of simplicial sets and let
$p:s times k->x$ be a map over $s$, so that the triangle

#align(center, diagram({
  node((0, 1), [$s times k$])
  node((1, 0), [$x$])
  node((2, 1), [$s$])
  edge((0, 1), (1, 0), [$p$], label-side: left, "->")
  edge((1, 0), (2, 1), [$q$], label-side: left, "->")
  edge((0, 1), (2, 1), [$pr_1$], label-side: right, "->")
}))

commutes.

#definition(title:[Relative Slices])[
  The #emph[relative undercategory] $x_(p\/)->s$ is characterized by the
  following universal property: for every $u:y->s$, maps
  $y->x_(p\/)$ over $s$ are naturally identified with maps

  $ F:y times k^triangle.r->x $

  over $s$ whose restriction to $y times k$ is
  $p compose (u times id_k)$. Dually, the #emph[relative overcategory]
  $x_(\/p)->s$ is defined by replacing the right cone $k^"▹"$ with the left
  cone $k^"◃"$.
]

When $s=Delta^0$, these are the usual undercategory and overcategory. More
generally, slicing is computed fiberwise: for every vertex $a in s$,

$ (x_(p\/))_a tilde.eq (x_a)_(p_a\/), quad
  (x_(\/p))_a tilde.eq (x_a)_(\/p_a) $

where $x_a=x times_s {a}$ and $p_a:k->x_a$ is the induced diagram.

=== Slices of $oo$-Operads

Let $q:cal(C)^times.o->cal(O)^times.o$ be a fibration of $oo$-operads and let

$ p:k->Alg_cal(O)(cal(C)) $

be a diagram of $cal(O)$-algebra objects. Evaluation gives a map

$ tilde(p):cal(O)^times.o times k->cal(C)^times.o $

over $cal(O)^times.o$. Define

$
  cal(C)_(p\/cal(O))^times.o
    :=(cal(C)^times.o)_(tilde(p)\/),
  quad
  cal(C)_(\/p\/cal(O))^times.o
    :=(cal(C)^times.o)_(\/tilde(p))
$

If $k=Delta^0$ and $p$ selects an algebra object $a$, we abbreviate these to
$cal(C)_(a\/cal(O))^times.o$ and
$cal(C)_(\/a\/cal(O))^times.o$. Their fibers over $chevron.l 1 chevron.r$ are
the ordinary slices $cal(C)_(a\/)$ and $cal(C)_(\/a)$, respectively.

#theorem(title:[Operadic Slice Theorem])[
  With the notation above:

  1. the induced maps

     $
       q':cal(C)_(p\/cal(O))^times.o->cal(O)^times.o,
       quad
       q'':cal(C)_(\/p\/cal(O))^times.o->cal(O)^times.o
     $

     are fibrations of $oo$-operads

  2. a morphism in either sliced operad is inert if and only if its image in
     $cal(C)^times.o$ is inert

  3. if $q$ is a coCartesian fibration, then the map $q''$ is a coCartesian
     fibration, so the relative overcategory inherits an
     $cal(O)$-monoidal structure

  4. the map $q'$ is also coCartesian provided every section
     $p(t):cal(O)^times.o->cal(C)^times.o$, for $t in k_0$, preserves all
     coCartesian morphisms
]

#proofsketch[
  The universal property of relative slices translates inner-horn lifting in
  the sliced objects into inner-horn lifting for $q$. Fiberwise, the slices
  are ordinary undercategories or overcategories, and the Segal product
  decomposition is therefore inherited from $cal(C)^times.o$. The same cone
  description identifies inert morphisms and coCartesian transport. For the
  undercategory, transport must also move the chosen source diagram $p$;
  this is why the additional coCartesian-preservation hypothesis on every
  section $p(t)$ is necessary.
]

#remark(title:[The Asymmetry])[
  For an $cal(O)$-monoidal category, slicing #emph[over] an algebra object is
  automatically $cal(O)$-monoidal. Slicing #emph[under] it generally is not:
  the algebra section must itself be $cal(O)$-monoidal, meaning that it
  preserves every coCartesian morphism rather than only the inert ones
  required of an algebra object.
]

=== Slicing over a Commutative Algebra

#corollary(title:[The Monoidal Overcategory])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category and let
  $a in cat("CAlg")(cal(C))$. Then the ordinary slice $cal(C)_(\/a)$ is the
  underlying $oo$-category of a symmetric monoidal $oo$-category. For objects
  $u:x->a$ and $v:y->a$, their tensor product is the composite

  $ x times.o y -->^(u times.o v) a times.o a -->^m a $

  where $m:a times.o a->a$ is the multiplication. The unit is the unit map
  $1->a$.
]

#proofsketch[
  Apply the operadic slice theorem with
  $cal(O)^times.o=Comm^times.o$ and $k=Delta^0$. The formula is simply
  coCartesian transport in the sliced operad. Associativity, the unit law,
  and symmetry follow coherently from the corresponding structure maps of
  the commutative algebra $a$.
]

#remark(title:[The Undercategory])[
  The undercategory $cal(C)_(a\/)$ inherits the analogous symmetric monoidal
  structure only when the section
  $a:Comm^times.o->cal(C)^times.o$ is symmetric monoidal. This is the
  “trivial algebra” case: its structural maps, including
  $1->a$ and $a times.o a->a$, are equivalences. Without this hypothesis,
  there is no canonical way to tensor two arrows whose common source is $a$.
]

== Coproducts of $oo$-Operads

The $oo$-category $Op_oo$ is presentable, so coproducts of $oo$-operads
exist abstractly. Their total $oo$-categories cannot simply be joined over
$Ner(Fin_*)$: the arities contributed by the two factors must first be
combined. The following construction makes this bookkeeping explicit.

=== Splitting a Finite Set of Inputs

For a subset $s subset chevron.l n chevron.r$ containing the basepoint, write
$[s]$ for the pointed finite set obtained from $s$ by its induced order.

#definition(title:[The Category $cat("Sub")$])[
  An object of $cat("Sub")$ is a triple

  $ (chevron.l n chevron.r,s,t) $

  where $s$ and $t$ contain the basepoint and partition the non-basepoint
  elements:

  $ s union t=chevron.l n chevron.r, quad s inter t={ast} $

  A morphism to $(chevron.l n' chevron.r,s',t')$ is a pointed map
  $f:chevron.l n chevron.r->chevron.l n' chevron.r$ satisfying
  $f(s) subset s'$ and $f(t) subset t'$. There are three evident functors

  $
    pi_- (chevron.l n chevron.r,s,t)=[s], quad
    pi (chevron.l n chevron.r,s,t)=chevron.l n chevron.r, quad
    pi_+ (chevron.l n chevron.r,s,t)=[t]
  $
]

The pair $(pi_-,pi_+)$ is an equivalence

$ cat("Sub") tilde.eq Fin_* times Fin_* $

The extra projection $pi$ remembers how the two ordered lists of inputs are
interleaved inside one list. This is the only additional information needed
to combine two operads.

=== The Box Product

#definition(title:[Box Product of $oo$-Operads])[
  Let $cal(C)^times.o->Ner(Fin_*)$ and
  $cal(D)^times.o->Ner(Fin_*)$ be $oo$-operads. Define
  $cal(C)^times.o plus.square cal(D)^times.o$ by the pullback square

  #align(center, diagram({
    node((0, 0), [$cal(C)^times.o plus.square cal(D)^times.o$])
    node((1, 0), [$cal(C)^times.o times cal(D)^times.o$])
    node((0, 1), [$Ner(cat("Sub"))$])
    node((1, 1), [$Ner(Fin_*) times Ner(Fin_*)$])
    edge((0, 0), (1, 0), "->")
    edge((0, 0), (0, 1), "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 1), (1, 1), [$Ner(pi_- times pi_+)$], label-side: right, "->")
  }))

  Its structure map to $Ner(Fin_*)$ is induced by
  $pi:cat("Sub")->Fin_*$. We call it the #emph[box product] of
  $cal(C)^times.o$ and $cal(D)^times.o$.
]

As an $oo$-category, the box product is equivalent to
$cal(C)^times.o times cal(D)^times.o$. Its operadic projection is different,
however: $pi$ merges the two input lists. In particular, the colors of the
box product form the disjoint union of the colors of $cal(C)$ and $cal(D)$,
not their Cartesian product.

#theorem(title:[Coproduct of $oo$-Operads])[
  The box product $cal(C)^times.o plus.square cal(D)^times.o$ is an
  $oo$-operad. Moreover, for every $oo$-operad $cal(E)^times.o$, restriction
  induces an equivalence

  $
    Alg_(cal(C) plus.square cal(D)) (cal(E))
    tilde.eq
    Alg_cal(C) (cal(E)) times Alg_cal(D) (cal(E))
  $

  Passing to maximal subgroupoids gives

  $
    Map_(Op_oo) (cal(C) plus.square cal(D),cal(E))
    tilde.eq
    Map_(Op_oo) (cal(C),cal(E))
      times Map_(Op_oo) (cal(D),cal(E))
  $

  Hence the box product represents the coproduct of $cal(C)$ and $cal(D)$
  in $Op_oo$.
]

Equivalently, an algebra over $cal(C) plus.square cal(D)$ is a pair
consisting of a $cal(C)$-algebra and a $cal(D)$-algebra on the same target;
the coproduct imposes no further compatibility law between them.

#proofsketch[
  Split every input according to $s$ and $t$, then apply the Segal
  decompositions in $cal(C)^times.o$ and $cal(D)^times.o$ separately. The
  extreme suboperads $t={ast}$ and $s={ast}$ are operadically equivalent to
  $cal(C)$ and $cal(D)$. A map out of the box product is therefore determined,
  up to a contractible choice, by one map from each factor.
]

== Monoidal Envelopes

The monoidal envelope is the universal construction which turns an
$oo$-operad into a monoidal $oo$-category. It keeps the original operations
but freely supplies tensor products and their coCartesian transport.

=== Construction by Active Morphisms

Let $cal(O)^times.o$ be an $oo$-operad. Denote by

$ Act(cal(O)^times.o) subset Fun(Delta^1,cal(O)^times.o) $

the full subcategory spanned by the active morphisms, and write
$ev_0,ev_1$ for evaluation at the source and target.

#definition(title:[Relative Monoidal Envelope])[
  Let

  $ p:cal(C)^times.o->cal(O)^times.o $

  be a fibration of $oo$-operads. Its #emph[$cal(O)$-monoidal envelope] is
  the pullback

  $
    Env_cal(O)(cal(C))^times.o
    :=cal(C)^times.o times_(cal(O)^times.o) Act(cal(O)^times.o)
  $

  where the two maps to $cal(O)^times.o$ are $p$ and $ev_0$. Its projection
  to $cal(O)^times.o$ is induced by $ev_1$. When $cal(O)=Comm$, we simply
  write $Env(cal(C))^times.o$.
]

i.e. defined by the pullback square

#align(center, diagram({
	node((-1, 0), [$cal(C)^times.o$])
	node((-1, 1), [$cal(O)^times.o$])
	node((-2, 1), [$bold(sans("Act"))(cal(O)^times.o)$])
	node((-2, 0), [$bold(sans("Env"))_(cal(O))(cal(C))^times.o$])
	edge((-1, 0), (-1, 1), [$p$], label-side: left, "->")
	edge((-2, 1), (-1, 1), [$"ev"_1$], label-side: right, "->")
	edge((-2, 0), (-1, 0), "->")
	edge((-2, 0), (-2, 1), "->")
}))

Thus an object of $Env_cal(O)(cal(C))^times.o$ is a pair $(c,alpha)$, where
$c in cal(C)^times.o$ and

$ alpha:p(c)->x $

is active in $cal(O)^times.o$. A morphism is a commutative square between
such active arrows together with a compatible morphism in
$cal(C)^times.o$.

The diagonal choice $alpha=id_(p(c))$ defines a canonical map of
$oo$-operads

$ i:cal(C)^times.o->Env_cal(O)(cal(C))^times.o $

This map is fully faithful: the envelope adds formal tensor transport but
does not identify or discard any operation already present in $cal(C)$.

=== The Induced Monoidal Structure

#theorem(title:[The Envelope is $cal(O)$-Monoidal])[
  Evaluation at the target induces a coCartesian fibration of $oo$-operads

  $
    q:Env_cal(O)(cal(C))^times.o->cal(O)^times.o
  $

  A morphism in the envelope is $q$-coCartesian if and only if its projection
  to $cal(C)^times.o$ is inert.
]

#proofsketch[
  Factor morphisms in $cal(O)^times.o$ into active and inert parts. The
  operadic lifting axioms supply the inert part, while composition of active
  arrows supplies the active part. This constructs the required coCartesian
  lifts. The Segal equivalence is inherited by applying the same factorization
  separately to every output slot.
]

#corollary(title:[Symmetric Monoidal Envelope])[
  Every $oo$-operad $cal(C)^times.o->Comm^times.o$ has a canonical symmetric
  monoidal envelope $Env(cal(C))^times.o$.
]

Its underlying $oo$-category has a particularly concrete description:

$ Env(cal(C)) tilde.eq cal(C)_"act"^times.o $

The right-hand side has all objects of $cal(C)^times.o$ but only active
morphisms. Equivalently, its objects are finite lists
$(c_1,dots,c_n)$ of colors of $cal(C)$, its unit is the empty list, and its
tensor product is concatenation

$
  (c_1,dots,c_m) times.o (d_1,dots,d_n)
  =(c_1,dots,c_m,d_1,dots,d_n)
$

In this structure, tensor products of active coCartesian morphisms are again
active and coCartesian.

=== Universal Property

#theorem(title:[Universal Property of the Monoidal Envelope])[
  Let $cal(D)^times.o->cal(O)^times.o$ be an $cal(O)$-monoidal
  $oo$-category. Restriction along $i$ induces an equivalence

  $
    i^*:Fun_cal(O)^times.o (Env_cal(O)(cal(C)),cal(D))
    tilde.eq Alg_(cal(C)\/cal(O)) (cal(D))
  $

  In words, an operad map from $cal(C)$ to an $cal(O)$-monoidal category
  extends uniquely up to a contractible space of choices to an
  $cal(O)$-monoidal functor from its envelope.
]

#proofsketch[
  Restriction gives the forward map. Conversely, for an operad map
  $f:cal(C)^times.o->cal(D)^times.o$, send $(c,alpha)$ to the coCartesian
  transport of $f(c)$ along $alpha$. CoCartesian lifts are unique up to a
  contractible space of choices and compose coherently, so this construction
  gives the inverse equivalence.
]

#corollary(title:[The Envelope Adjunction])[
  The forgetful functor

  $ U:Cat_oo^times.o->Op_oo $

  admits the monoidal-envelope functor as a left adjoint

  $ Env:Op_oo->Cat_oo^times.o $

  Equivalently, for every symmetric monoidal $oo$-category $cal(D)^times.o$,

  $
    Fun_Comm^times.o (Env(cal(C)),cal(D))
    tilde.eq Alg_cal(C) (cal(D))
  $
]

== Tensor Products of $oo$-Operads

The tensor product of operads is different from both the coproduct above and
the Cartesian product of their total $oo$-categories. It is characterized by
the principle that an algebra over $cal(O) times.o cal(P)$ is an
$cal(O)$-algebra internal to $cal(P)$-algebras.

=== Multiplying Arities

Define the smash-product functor

$ smash:Fin_* times Fin_*->Fin_* $

by

$ chevron.l m chevron.r smash chevron.l n chevron.r
  =chevron.l m n chevron.r $

Its non-basepoint elements are pairs $(a,b)$, ordered lexicographically. For
pointed maps $f$ and $g$,

$
  (f smash g)(a,b)=cases(
    ast & "if " f(a)=ast " or " g(b)=ast,
    (f(a),g(b)) & "otherwise"
  )
$

The functor $smash$ is associative and preserves coproducts separately in
each variable.

#remark(title:[Why Symmetry is Subtle])[
  The chosen lexicographic order makes associativity strict, but the
  symmetry

  $ chevron.l m chevron.r smash chevron.l n chevron.r
    tilde.eq chevron.l n chevron.r smash chevron.l m chevron.r $

  is not literally the identity. Hence this single functor does not by itself
  give a strict symmetric structure. The space of all smash-product functors
  $Fin_*^i->Fin_*$ is nevertheless contractible; using this whole space
  supplies the required coherent symmetries.
]

=== Operadic Bifunctors

#definition(title:[Bifunctor of $oo$-Operads])[
  Let $cal(O)^times.o$, $cal(P)^times.o$, and $cal(Q)^times.o$ be
  $oo$-operads. An #emph[operadic bifunctor] is a functor

  $ f:cal(O)^times.o times cal(P)^times.o->cal(Q)^times.o $

  fitting into the commutative square

  #align(center, diagram({
    node((0, 0), [$cal(O)^times.o times cal(P)^times.o$])
    node((1, 0), [$cal(Q)^times.o$])
    node((0, 1), [$Ner(Fin_*) times Ner(Fin_*)$])
    node((1, 1), [$Ner(Fin_*)$])
    edge((0, 0), (1, 0), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 1), (1, 1), [$Ner(- smash -)$], label-side: left, "->")
  }))

  and such that $f(alpha,beta)$ is inert whenever both $alpha$ and $beta$
  are inert. Denote the resulting $oo$-category by

  $ BiFun(cal(O),cal(P);cal(Q)) $
]

#remark(title:[The Concrete Construction of $BiFun$])[
  Give $cal(O)^times.o times cal(P)^times.o$ its map to $Ner(Fin_*)$ by
  composing the two projections with $Ner(- smash -)$. Formally,
  $BiFun(cal(O),cal(P);cal(Q))$ is the full subcategory of

  $
    Fun_(\/Ner(Fin_*))
      (cal(O)^times.o times cal(P)^times.o,cal(Q)^times.o)
  $

  spanned by the functors which carry every pair of inert morphisms to an
  inert morphism. Since it is a full subcategory, a morphism $f->g$ in
  $BiFun$ is simply a natural transformation over $Ner(Fin_*)$; no extra
  condition is imposed on the transformation.

  Concretely, choose colors $x_1,dots,x_m,x$ of $cal(O)$ and
  $y_1,dots,y_n,y$ of $cal(P)$, together with operations

  $
    alpha in Mul_cal(O) ({x_i}_(1<=i<=m);x), quad
    beta in Mul_cal(P) ({y_j}_(1<=j<=n);y)
  $

  A bifunctor produces the $m n$-ary operation

  $
    f(alpha,beta) in
    Mul_cal(Q)
      ({f(x_i,y_j)}_(1<=i<=m, 1<=j<=n);f(x,y))
  $

  The inert condition guarantees that these $m n$ inputs really are the
  matrix of pairs $(x_i,y_j)$. Functoriality says that first composing along
  the rows and then along the columns agrees coherently with composing in the
  opposite order. This is the #emph[interchange law]. Equivalently, $f$ is
  operadic in each variable separately, with the two operadic actions made
  coherently compatible.
]

#definition(title:[Tensor Product of $oo$-Operads])[
  A bifunctor

  $ cal(O)^times.o times cal(P)^times.o->(cal(O) times.o cal(P))^times.o $

  exhibits $cal(O) times.o cal(P)$ as the #emph[tensor product] if, for every
  $oo$-operad $cal(Q)$, composition induces an equivalence

  $
    Alg_(cal(O) times.o cal(P)) (cal(Q))
    tilde.eq BiFun(cal(O),cal(P);cal(Q))
  $
]

#theorem(title:[Existence of the Operadic Tensor Product])[
  Every pair of small $oo$-operads admits a tensor product, unique up to a
  canonical equivalence.
]

#remark(title:[Model-Categorical Construction])[
  This existence statement is the technically difficult part. For marked
  preoperads $overline(x)=(x,m)$ and $overline(y)=(y,n)$, first form

  $ overline(x) odot overline(y):=(x times y,m times n) $

  over $Ner(Fin_*)$ using the smash-product map $Ner(smash)$. The functor
  $odot:POp_oo times POp_oo->POp_oo$ is left Quillen in each variable, making
  $POp_oo$ a monoidal model category. A fibrant replacement of this external product represents
  $cal(O) times.o cal(P)$. Thus the tensor product is derived rather than the
  naive product of the underlying simplicial sets.
]

=== Universal Consequences

#corollary(title:[Algebraic Exponential Law])[
  If $cal(C)^times.o$ is symmetric monoidal, then there is a canonical
  equivalence

  $
    Alg_(cal(O) times.o cal(P)) (cal(C))
    tilde.eq Alg_cal(O) (Alg_cal(P) (cal(C)))
  $

  Consequently, $Alg_cal(O) (cal(C))$ inherits a symmetric monoidal
  structure whose tensor product is computed pointwise in $cal(C)$.
]

#remark(title:[Interchange, Not Mere Coexistence])[
  Compare this with the coproduct $cal(O) plus.square cal(P)$. An algebra over
  the coproduct merely carries independent $cal(O)$- and $cal(P)$-structures.
  An algebra over $cal(O) times.o cal(P)$ carries both structures together
  with coherent interchange: every $cal(O)$-operation is a morphism of
  $cal(P)$-algebras, and conversely.
]

#theorem(title:[The Symmetric Monoidal $oo$-Category of Operads])[
  Operadic tensor products assemble into a symmetric monoidal $oo$-category

  $ Op_oo^times.o->Ner(Fin_*) $

  whose underlying $oo$-category is $Op_oo$. Its tensor unit is the trivial
  operad $cat("Triv")^times.o$, and its multimorphism spaces classify
  multilinear operad maps.
]

#proofsketch[
  The contractible groupoids of smash-product functors provide all coherent
  choices of parenthesization and permutation. Their operadic nerves assemble
  the derived external products of preoperads into a symmetric monoidal
  structure. The universal property above identifies its binary operation
  with $cal(O) times.o cal(P)$, while the one-color unary operad
  $cat("Triv")$ supplies the unit.
]

#corollary(title:[Unary Operads Recover Cartesian Products])[
  Under the fully faithful embedding $Cat_oo->Op_oo$ by unary operads, the
  operadic tensor product restricts to the Cartesian product:

  $ cal(C) times.o cal(D) tilde.eq cal(C) times cal(D) $

  Equivalently, the symmetric monoidal subcategory of unary operads is
  symmetric monoidally equivalent to $Cat_oo^times$.
]

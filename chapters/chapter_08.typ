#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= (co)Cartesian Symmetric Monoidal Categories

== Cartesian Monoidal Categories

Let $cal(C)$ be an $oo$-category with finite products. The ordinary product
already suggests a symmetric monoidal operation: its unit is the final object,
and its structural maps are the projections. The point of this section is that
these elementary facts determine all higher coherence automatically.

=== Intrinsic Characterization

#definition(title:[Cartesian Symmetric Monoidal Structure])[
  Let $cal(C)^times.o->Ner(Fin_*)$ be a symmetric monoidal $oo$-category, with
  underlying $oo$-category $cal(C)$. Its monoidal structure is
  #emph[Cartesian] if

  + the unit $1_cal(C)$ is final in $cal(C)$

  + for every $c,d in cal(C)$, the canonical projections

    $ c times.o d -> c, quad c times.o d -> d $

    exhibit $c times.o d$ as $c times d$
]

#remark(title:[The Defining Picture])[
  The tensor product is not merely equivalent to a product as an object: the
  equivalence is detected by the two inert projections.

  #align(center, diagram({
    node((1, 0), [$c times.o d$])
    node((0, 1), [$c$])
    node((2, 1), [$d$])
    edge((1, 0), (0, 1), [$pr_1$], label-side: right, "->")
    edge((1, 0), (2, 1), [$pr_2$], label-side: left, "->")
  }))

  Thus maps into the tensor product split as

  $ Map_cal(C) (x,c times.o d) tilde.eq
    Map_cal(C) (x,c) times Map_cal(C) (x,d) $
]

#definition(title:[Lax Cartesian Structure])[
  Let $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad and let $cal(D)$ admit
  finite products. A functor $pi:cal(O)^times.o->cal(D)$ is a
  #emph[lax Cartesian structure] if, whenever
  $x in cal(O)^times.o_(chevron.l n chevron.r)$ has inert components
  $x_i$, the canonical maps exhibit

  $ pi(x) tilde.eq product_(i=1)^n pi(x_i) $

  If $cal(O)^times.o$ is symmetric monoidal, the structure is #emph[weak
  Cartesian] when $pi$ also carries every coCartesian arrow over an active
  map to an equivalence. A weak Cartesian structure is #emph[Cartesian] when
  its restriction $cal(O)->cal(D)$ is an equivalence.
]

The first condition says that a list of inputs is evaluated componentwise.
The second says that an active tensor operation introduces no information
beyond the product already present in $cal(D)$.

=== The Canonical Construction

The bookkeeping category behind the construction is $Gamma^times$. Its
objects are pairs $(chevron.l n chevron.r,S)$ with
$S subset.eq chevron.l n chevron.r^circle$, and a morphism

$ (chevron.l n chevron.r,S)->^(alpha)
  (chevron.l m chevron.r,T) $

is a pointed map $alpha:chevron.l n chevron.r->chevron.l m chevron.r$ such
that $alpha^(-1)(T) subset.eq S$. The subset $S$ records which inputs remain
visible. In particular, singleton subsets recover the individual factors.

#remark(title:[Why Subsets Appear])[
  Over $chevron.l 3 chevron.r$, the relevant part of a product diagram has the
  form

  #align(center, diagram({
    node((1, 0), [$c_1 times c_2 times c_3$])
    node((0, 1), [$c_1 times c_2$])
    node((1, 1), [$c_1 times c_3$])
    node((2, 1), [$c_2 times c_3$])
    node((0, 2), [$c_1$])
    node((1, 2), [$c_2$])
    node((2, 2), [$c_3$])
    edge((1, 0), (0, 1), "->")
    edge((1, 0), (1, 1), "->")
    edge((1, 0), (2, 1), "->")
    edge((0, 1), (0, 2), "->")
    edge((0, 1), (1, 2), "->")
    edge((1, 1), (0, 2), "->")
    edge((1, 1), (2, 2), "->")
    edge((2, 1), (1, 2), "->")
    edge((2, 1), (2, 2), "->")
  }))

  The arrows forget entries. The entire diagram is forced by the three
  singleton values: each value at $S$ is their product over $i in S$.
]

For an $oo$-category $cal(C)$, one first forms an $oo$-category over
$Ner(Fin_*)$ whose fiber over $chevron.l n chevron.r$ consists of diagrams

$ F:cal(P)(chevron.l n chevron.r^circle)^op->cal(C) $

Here $cal(P)$ denotes the poset of subsets. Let $cal(C)^times$ be the full
subcategory on the diagrams satisfying

$ F(S) tilde.eq product_(i in S) F({i}) $

Equivalently, $F$ is the right Kan extension of its values on the singleton
subsets. This is precisely the condition that turns the formal list
$(c_1,dots,c_n)$ into its coherent system of partial products.

#proposition(title:[Structure of $cal(C)^times$])[
  The projection $cal(C)^times->Ner(Fin_*)$ has the following properties.

  + Evaluation on singleton subsets induces an equivalence

    $ cal(C)^times_(chevron.l n chevron.r) tilde.eq cal(C)^n $

  + The value at the empty subset is the terminal object, while the value at
    $S$ is the product of the entries indexed by $S$.

  + A morphism of subset diagrams over
    $alpha:chevron.l n chevron.r->chevron.l m chevron.r$ is coCartesian
    exactly when, for every $T subset.eq chevron.l m chevron.r^circle$, its
    comparison map

    $ F(alpha^(-1)(T))->F'(T) $

    is an equivalence.

  + If $cal(C)$ admits finite products, the active fold
    $chevron.l n chevron.r->chevron.l 1 chevron.r$ induces the ordinary
    $n$-fold product functor $cal(C)^n->cal(C)$.
]

#remark(title:[Nullary and Binary Cases])[
  For $n=0$, the construction selects the empty product $1_cal(C)$. For
  $n=2$, the inert projections select $c$ and $d$, while the active fold
  selects $c times d$. Thus the unit, projections, and multiplication of the
  monoidal structure all come from the same subset diagram.
]

#theorem(title:[Existence and Uniqueness of the Cartesian Structure])[
  An $oo$-category $cal(C)$ admits a Cartesian symmetric monoidal structure if
  and only if it admits finite products. In that case

  $ cal(C)^times->Ner(Fin_*) $

  is a Cartesian symmetric monoidal $oo$-category, and every other Cartesian
  symmetric monoidal structure on $cal(C)$ is symmetrically monoidally
  equivalent to it through an equivalence homotopic to the identity on
  $cal(C)$.
]

#proofsketch[
  Finite products extend every tuple of objects uniquely, up to contractible
  choice, to the subset diagram above. Reindexing subsets supplies the
  coCartesian transport over $Fin_*$, while the singleton decomposition gives
  the operadic Segal equivalences. Conversely, the unit and the two inert
  projections in any Cartesian structure recover the final object and binary
  products. Since every higher product is their iterated universal product,
  no additional coherent choices remain.
]

#example(title:[Spaces and Additive Categories])[
  The $oo$-category $Ani$ carries its Cartesian monoidal structure by ordinary
  products of spaces. A commutative algebra object in $Ani^times$ is therefore
  an $E_oo$-space and is genuine additional structure.

  In an additive $oo$-category, finite products and finite coproducts agree as
  biproducts. Its Cartesian and coCartesian monoidal structures therefore have
  the same underlying tensor object, although their universal descriptions
  use projections and inclusions respectively.
]

=== Universal Property

Write $Fun^"fp" (cal(C),cal(D))$ for the $oo$-category of finite-product-
preserving functors.

#theorem(title:[Functorial Characterization])[
  If $cal(C)$ and $cal(D)$ admit finite products, restriction to the underlying
  $oo$-categories induces an equivalence

  $ Fun^times.o (cal(C)^times,cal(D)^times)
    tilde.eq Fun^"fp" (cal(C),cal(D)) $

  Consequently, the $oo$-category of Cartesian symmetric monoidal
  $oo$-categories and symmetric monoidal functors is equivalent to the
  $oo$-category of $oo$-categories with finite products and functors which
  preserve them.
]

#proofsketch[
  A symmetric monoidal functor preserves the tensor unit and the tensors
  encoded by active fold maps; in the Cartesian models these are precisely
  the final object and finite products. Conversely, a product-preserving
  functor can be applied pointwise to every subset diagram. It preserves the
  right Kan extension condition and hence defines a symmetric monoidal
  functor $cal(C)^times->cal(D)^times$. The space of such extensions is
  contractible, which gives full faithfulness as well as essential
  surjectivity.
]

#remark(title:[Coherence Is a Consequence of Products])[
  A product-preserving functor automatically preserves the unit, every
  $n$-fold tensor product, permutations, and all associativity coherences.
  Thus “symmetric monoidal” is not extra structure in the Cartesian setting;
  it is a property of the underlying functor.
]

#proposition(title:[Algebras as Cartesian Structures])[
  Let $cal(O)^times.o$ be an $oo$-operad and let $cal(D)$ admit finite
  products. Composition with the Cartesian structure
  $pi:cal(D)^times->cal(D)$ induces a trivial Kan fibration

  $ Alg_cal(O) (cal(D))
    -> Fun^"lax-Cart" (cal(O)^times.o,cal(D)) $

  Hence a lax Cartesian structure lifts, through a contractible space of
  choices, to an $cal(O)$-algebra in $cal(D)^times$. If
  $cal(O)^times.o$ is symmetric monoidal, symmetric monoidal functors into
  $cal(D)^times$ correspond in the same way to weak Cartesian structures.
]

#proofsketch[
  A map of $oo$-operads into $cal(D)^times$ is determined by its singleton
  components. After composing with $pi$, the operadic Segal condition becomes
  exactly the assertion that the value of a tuple is the product of those
  components. Thus lax Cartesian structures are precisely the diagrams which
  admit the required lift. Since products are universal, the space of lifts
  and of all their coherences is contractible.
]

#remark(title:[What Is Being Lifted])[
  The product diagram in $cal(D)$ already contains all target-side coherence.
  An algebra structure is therefore the unique operadic lift of the lower
  functor in the triangle

  #align(center, diagram({
    node((0, 0), [$cal(O)^times.o$])
    node((2, 0), [$cal(D)^times$])
    node((1, 1), [$cal(D)$])
    edge((0, 0), (2, 0), [$a^times.o$], label-side: left, "->")
    edge((0, 0), (1, 1), [$pi compose a^times.o$], label-side: right, "->")
    edge((2, 0), (1, 1), [$pi$], label-side: left, "->")
  }))
]

== Monoid Objects

For an ordinary category with finite products, a commutative monoid is an
object equipped with a unit and a multiplication. In an $oo$-category the
same description hides infinitely many coherences. A more robust definition
packages all powers of the object into a single product-preserving functor.

#definition(title:[$cal(O)$-Monoid])[
  Let $cal(C)$ be an $oo$-category with finite products and let
  $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad. An
  #emph[$cal(O)$-monoid] in $cal(C)$ is a functor

  $ m:cal(O)^times.o->cal(C) $

  such that, for every
  $x in cal(O)^times.o_(chevron.l n chevron.r)$ with inert components
  $x_1,dots,x_n$, the canonical map

  $ m(x)->product_(i=1)^n m(x_i) $

  is an equivalence. Write $Mon_cal(O) (cal(C))$ for the full subcategory of
  $Fun(cal(O)^times.o,cal(C))$ spanned by these functors. When
  $cal(O)^times.o=Comm^times.o$, write

  $ CMon(cal(C)):=Mon_Comm (cal(C)) $
]

#remark(title:[Recovering the Classical Operations])[
  Let $m in CMon(cal(C))$ and put
  $a=m(chevron.l 1 chevron.r)$. The Segal equivalences give

  $ m(chevron.l n chevron.r) tilde.eq a^n $

  The unique active fold $mu_2:chevron.l 2 chevron.r->chevron.l 1 chevron.r$
  and the nullary active map therefore give

  $ a times a tilde.eq m(chevron.l 2 chevron.r)->a,
    quad 1_cal(C) tilde.eq m(chevron.l 0 chevron.r)->a $

  Functoriality of $m$ packages commutativity, associativity, unitality, and
  every higher homotopy between them. Thus a commutative monoid object is the
  coherent version of the familiar data $(a,1->a,a times a->a)$.
]

#proposition(title:[Monoids versus Algebras])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category and let
  $pi:cal(C)^times.o->cal(D)$ be a Cartesian structure. For every
  $oo$-operad $cal(O)^times.o$, composition with $pi$ induces an equivalence

  $ Alg_cal(O) (cal(C)) tilde.eq Mon_cal(O) (cal(D)) $

  In particular, for the canonical Cartesian structure on an $oo$-category
  with finite products,

  $ Alg_cal(O) (cal(C)) tilde.eq Mon_cal(O) (cal(C)) $
]

#proofsketch[
  This is the preceding lifting theorem with the terminology changed. The
  Segal condition for an algebra map into $cal(C)^times$ says exactly that its
  composite with $pi$ carries an $n$-tuple to the product of its singleton
  values. Conversely, those product diagrams have a unique coherent lift to
  $cal(C)^times$.
]

#example(title:[Monoidal $oo$-Categories as Monoid Objects])[
  Taking $cal(C)=Cat_oo$, a commutative monoid object is the same thing as a
  symmetric monoidal $oo$-category. More generally,
  $Mon_cal(O) (Cat_oo)$ is the $oo$-category of $cal(O)$-monoidal
  $oo$-categories and $cal(O)$-monoidal functors.
]

#proposition(title:[Approximation Invariance])[
  Let $f:cal(E)^times.o->cal(O)^times.o$ be a weak approximation which is an
  equivalence on colors. If $cal(C)$ has finite products, restriction induces

  $ Mon_cal(O) (cal(C)) tilde.eq Mon_cal(E) (cal(C)) $
]

#proofsketch[
  Extend an $cal(E)$-monoid by right Kan extension. Approximation makes every
  indexing category of active lifts contractible, while the product condition
  supplies the inert extensions. Hence the extension exists and is unique up
  to contractible choice.
]

#remark(title:[Passing to Opposites])[
  Although a symmetric monoidal structure is not manifestly self-dual, the
  involution $cal(C) mapsto cal(C)^op$ on $Cat_oo$ carries commutative monoid
  objects to commutative monoid objects. Consequently a symmetric monoidal
  structure on $cal(C)$ canonically determines one on $cal(C)^op$, up to a
  contractible space of choices. This is the formal bridge from Cartesian to
  coCartesian structures.
]

== coCartesian Monoidal Categories

The dual theory starts from finite coproducts.

#definition(title:[coCartesian Symmetric Monoidal Structure])[
  A symmetric monoidal structure on $cal(C)$ is #emph[coCartesian] if its unit
  $0_cal(C)$ is initial and the canonical inclusions

  $ c->c times.o d <-d $

  exhibit $c times.o d$ as the coproduct $c coprod d$.
]

#remark(title:[Product versus Coproduct])[
  The two universal cones point in opposite directions.

  #align(center, diagram({
    node((1, 0), [$c times.o d$])
    node((0, 1), [$c$])
    node((2, 1), [$d$])
    edge((1, 0), (0, 1), [$pr_1$], label-side: right, "->")
    edge((1, 0), (2, 1), [$pr_2$], label-side: left, "->")

    node((4, 0), [$c$])
    node((6, 0), [$d$])
    node((5, 1), [$c times.o d$])
    edge((4, 0), (5, 1), [$i_1$], label-side: right, "->")
    edge((6, 0), (5, 1), [$i_2$], label-side: left, "->")
  }))

  The left cone is Cartesian; the right cone is coCartesian. Formally the
  latter is obtained by applying the Cartesian construction to
  $cal(C)^op$ and then taking opposites.
]

=== An Explicit coCartesian Operad

The duality argument proves existence, but a direct model makes the
multimorphisms transparent.

#definition(title:[The Category $Gamma^coprod$])[
  An object of $Gamma^coprod$ is a pair
  $(chevron.l n chevron.r,i)$ with
  $i in chevron.l n chevron.r^circle$. A morphism

  $ (chevron.l m chevron.r,i)->^(alpha)
    (chevron.l n chevron.r,j) $

  is a pointed map
  $alpha:chevron.l m chevron.r->chevron.l n chevron.r$ satisfying
  $alpha(i)=j$.
]

For any $oo$-category $cal(C)$, define $cal(C)^coprod$ over $Ner(Fin_*)$ as
follows. An object over $chevron.l n chevron.r$ is a tuple
$(c_1,dots,c_n)$. A morphism from $(c_1,dots,c_m)$ to
$(d_1,dots,d_n)$ over $alpha:chevron.l m chevron.r->chevron.l n chevron.r$
is a collection

$ {f_i:c_i->d_(alpha(i))}_(alpha(i)!=ast) $

No map is required from an input which $alpha$ sends to the base point.

#remark(title:[The Wiring Encoded by a Morphism])[
  If $alpha(1)=alpha(2)=1$ and $alpha(3)=2$, a morphism over $alpha$ is
  exactly the displayed collection of ordinary arrows.

  #align(center, diagram({
    node((0, 0), [$c_1$])
    node((1, 0), [$c_2$])
    node((2, 0), [$c_3$])
    node((0, 1), [$d_1$])
    node((2, 1), [$d_2$])
    edge((0, 0), (0, 1), [$f_1$], label-side: right, "->")
    edge((1, 0), (0, 1), [$f_2$], label-side: left, "->")
    edge((2, 0), (2, 1), [$f_3$], label-side: left, "->")
  }))

  The coCartesian lift replaces all inputs in each fiber
  $alpha^(-1)({j})$ by their coproduct.
]

#proposition(title:[Structure of $cal(C)^coprod$])[
  The projection $p:cal(C)^coprod->Ner(Fin_*)$ has the following properties.

  + It is an $oo$-operad for every $oo$-category $cal(C)$.

  + Its fiber over $chevron.l n chevron.r$ is canonically equivalent to
    $cal(C)^n$.

  + A morphism over $alpha:chevron.l m chevron.r->chevron.l n chevron.r$
    is $p$-coCartesian exactly when, for every $1<=j<=n$, its component maps

    $ {c_i->d_j}_(i in alpha^(-1)({j})) $

    exhibit $d_j$ as $coprod_(i in alpha^(-1)({j})) c_i$.

  + The projection $p$ is a coCartesian fibration, hence a symmetric
    monoidal $oo$-category, if and only if $cal(C)$ admits finite coproducts.
]

#proofsketch[
  The fiber decomposition is immediate from the description by tuples. The
  mapping-space criterion for coCartesian arrows reduces independently at
  every output $j$ to the universal property of a coproduct. Such lifts exist
  for all pointed maps precisely when all finite coproducts exist; the empty
  fiber produces the initial object.
]

#remark(title:[Multimorphisms])[
  The active fold gives

  $
    Mul_(cal(C)^coprod) ({c_i}_(1<=i<=n),d)
    tilde.eq product_(i=1)^n Map_cal(C) (c_i,d)
  $

  If $cal(C)$ has finite coproducts, this is

  $ Map_cal(C) (coprod_(i=1)^n c_i,d) $

  Thus the higher operadic composition law contains no new operation: it is
  composition of ordinary arrows after applying the coproduct universal
  property.
]

#definition(title:[coCartesian $oo$-Operad])[
  An $oo$-operad is #emph[coCartesian] if it is equivalent, as an
  $oo$-operad, to $cal(C)^coprod$ for some $oo$-category $cal(C)$. A symmetric
  monoidal $oo$-category is coCartesian in this sense if and only if it is
  coCartesian according to the intrinsic definition above.
]

=== Universal Properties

#corollary(title:[The coCartesian Dual])[
  If $cal(C)$ admits finite coproducts, it carries an essentially unique
  coCartesian symmetric monoidal structure $cal(C)^coprod$. Symmetric
  monoidal functors

  $ cal(C)^coprod->cal(D)^coprod $

  are exactly the functors $cal(C)->cal(D)$ which preserve finite coproducts.
]

#example(title:[Disjoint Union])[
  The category of sets, or the $oo$-category of spaces, is coCartesian
  symmetric monoidal under disjoint union. For a space $x$, the fold map

  $ x coprod x->x $

  is the multiplication of its canonical commutative algebra structure. This
  should not be confused with a commutative monoid structure on $x$ under the
  Cartesian product.
]

#remark(title:[Canonical Algebra and Coalgebra Structures])[
  In a coCartesian monoidal $oo$-category every object has a canonical,
  essentially unique commutative algebra structure: its multiplication and
  unit are the fold maps

  $ c coprod c->c, quad 0_cal(C)->c $

  Dually, in a Cartesian monoidal $oo$-category every object has a canonical
  cocommutative coalgebra structure given by the diagonal and terminal map

  $ c->c times c, quad c->1_cal(C) $

  This is why algebra theory in a coCartesian monoidal category is formally
  trivial, whereas commutative monoid objects in a Cartesian category can
  carry genuine extra structure.
]

#corollary(title:[Triviality of coCartesian Algebra Theory])[
  Evaluation on the underlying object is an equivalence

  $ CAlg(cal(C)) tilde.eq cal(C) $

  Its inverse equips $c$ with all iterated fold maps
  $coprod_(i=1)^n c->c$. The commutative algebra axioms follow from the
  universal property of coproducts, so the entire coherent structure is
  unique up to contractible choice.
]

#theorem(title:[Algebras in a coCartesian Target])[
  Let $cal(P)^times.o$ be a unital $oo$-operad and let
  $cal(C)^coprod$ be coCartesian. Restriction to colors induces an equivalence

  $ Alg_cal(P) (cal(C)) tilde.eq Fun(cal(P),cal(C)) $

  More generally, maps between coCartesian $oo$-operads are determined by
  their underlying functors. In particular, the forgetful functor from
  coCartesian symmetric monoidal $oo$-categories to $oo$-categories with
  finite coproducts is an equivalence onto the subcategory of
  finite-coproduct-preserving functors.
]

#proofsketch[
  Unitality determines all nullary operations. Every higher operation in the
  target is a coproduct followed by an ordinary morphism, so a functor on
  colors forces the images of all operations. The coproduct universal
  property makes the space of coherent extensions contractible.
]

#theorem(title:[The Universal Family Property])[
  Let $cal(B)$ be an $oo$-category and let $cal(O)^times.o$ and
  $cal(D)^times.o$ be $oo$-operads. Put

  $
    cal(P)^times.o
    :=cal(B)^coprod times_(Ner(Fin_*)) cal(O)^times.o
  $

  Then restriction induces an equivalence

  $
    Alg_cal(P) (cal(D))
    tilde.eq
    Fun(cal(B),Alg_cal(O) (cal(D)))
  $

  Taking $cal(O)^times.o=Comm^times.o$ gives

  $
    Alg_(cal(B)^coprod) (cal(D))
    tilde.eq
    Fun(cal(B),CAlg(cal(D)))
  $
]

#remark(title:[Meaning of the Family Property])[
  A map of operads out of $cal(B)^coprod$ is a coherently $cal(B)$-indexed
  family of commutative algebra objects. Notice that maps of operads preserve
  inert morphisms but need not preserve every coCartesian morphism; the result
  concerns lax monoidal data, not only strong symmetric monoidal functors.
]

=== Recognition by Fold Maps

#proposition(title:[Recognition Criterion])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category. The following
  conditions are equivalent.

  + The symmetric monoidal structure on $cal(C)$ is coCartesian.

  + The induced symmetric monoidal structure on $h cal(C)$ is coCartesian.

  + The unit $1_cal(C)$ is initial and there is a natural family of fold maps
    $delta_c:c times.o c->c$ satisfying

    $ delta_c compose (id_c times.o u_c) tilde.eq id_c $

    $ f compose delta_c tilde.eq
      delta_d compose (f times.o f) $

    and

    $ delta_(c times.o d) compose beta_(c,d)
      tilde.eq delta_c times.o delta_d $

    Here $u_c:1_cal(C)->c$ is the unique map and
    $beta_(c,d):(c times.o c) times.o (d times.o d)
    tilde.eq (c times.o d) times.o (c times.o d)$ is the canonical symmetry.
]

#remark(title:[Naturality of the Fold])[
  The middle identity is the homotopy commutativity of

  #align(center, diagram({
    node((0, 0), [$c times.o c$])
    node((1, 0), [$d times.o d$])
    node((0, 1), [$c$])
    node((1, 1), [$d$])
    edge((0, 0), (1, 0), [$f times.o f$], label-side: left, "->")
    edge((0, 0), (0, 1), [$delta_c$], label-side: right, "->")
    edge((1, 0), (1, 1), [$delta_d$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
  }))
]

#proofsketch[
  Only the last implication needs proof. The canonical maps
  $c->c times.o d<-d$ are induced by the initial unit. For every $a$, define

  $
    Map_cal(C) (c,a) times Map_cal(C) (d,a)
    ->Map_cal(C) (c times.o d,a)
  $

  by sending $(f,g)$ to

  $ c times.o d->^(f times.o g) a times.o a->^(delta_a) a $

  Unitality, naturality, and multiplicativity of $delta$ show that this map is
  inverse to restriction along the two inclusions. Hence $c times.o d$ is a
  coproduct. The same argument at the unit proves that the entire symmetric
  monoidal structure is coCartesian.
]

== Wreath Products

The tensor product of two $oo$-operads is characterized by a universal
property, but the marked preoperad used to construct it must usually be
replaced by a fibrant object. The #emph[wreath product] is a more explicit
intermediate model: it records one operad acting on blocks and a second
operad acting inside each block. It is generally not itself an
$oo$-operad, but after marking its inert arrows it represents the same
derived object as the operadic tensor product.

=== Flattening Lists of Arities

For an $oo$-category $cal(J)$, let $cal(J)^coprod$ denote the simplicial set
whose objects are finite lists

$ (j_1,dots,j_m) $

and whose morphisms from $(j_1,dots,j_m)$ to
$(j'_1,dots,j'_n)$ consist of a pointed map
$alpha:⟨m⟩->⟨n⟩$ together with maps

$ j_i->j'_(alpha(i)) quad (alpha(i)!=*) $

When $cal(J)=Ner(cal(I))$, this is the nerve of the ordinary category with
exactly this description. Applying the construction to $Ner(Fin_*)$ gives
a canonical #emph[flattening functor]

$
  Phi:Ner(Fin_*)^coprod->Ner(Fin_*)
$

which concatenates a list of pointed finite sets. On objects,

$
  Phi(⟨k_1⟩,dots,⟨k_m⟩)
  =⟨k_1+dots+k_m⟩
$

#remark(title:[Two Levels of Arity])[
  The outer arity counts blocks, while the inner arities count inputs inside
  those blocks. Flattening forgets the subdivision and retains the total
  collection of inputs.

  #align(center, diagram({
    node((0, 0), [$⟨m⟩$], name: <outer>)
    node((0, 1),
      [$(⟨k_1⟩,dots,⟨k_m⟩)$],
      name: <blocks>)
    node((0, 2), [$⟨k_1+dots+k_m⟩$], name: <total>)
    edge(<outer>, <blocks>, [block arities], label-side: left, "->")
    edge(<blocks>, <total>, [$Phi$], label-side: left, "->")
  }))
]

=== The Explicit Model

#definition(title:[Wreath Product])[
  Let $cal(C)^times.o$ and $cal(D)^times.o$ be $oo$-operads. Their wreath
  product is the $oo$-category

  $
    cal(C)^times.o wr cal(D)^times.o
    :=cal(C)^times.o times_(Ner(Fin_*)) (cal(D)^times.o)^coprod
  $

  equipped with the structure map to $Ner(Fin_*)$ obtained from $Phi$.
]

Thus an object can be written

$ (c;d_1,dots,d_m) $

where $c$ lies over $⟨m⟩$ and $d_i$ lies over
$⟨k_i⟩$. Its total arity is
$⟨k_1+dots+k_m⟩$. A morphism has two layers: a morphism in
$cal(C)^times.o$ rearranges and combines the blocks, while compatible
morphisms in $cal(D)^times.o$ act inside the blocks.

#remark(title:[The Inert Marking])[
  Let $cal(M)$ be the class of morphisms in
  $cal(C)^times.o wr cal(D)^times.o$ for which the outer morphism in
  $cal(C)^times.o$ is inert and every induced inner morphism in
  $cal(D)^times.o$ is inert. The pair

  $ (cal(C)^times.o wr cal(D)^times.o,cal(M)) $

  is an $oo$-preoperad. The marking is essential: without it the wreath
  product remembers the two-level combinatorics but not which arrows play
  the role of inert projections.
]

There is a canonical monomorphism

$
  i:cal(C)^times.o times cal(D)^times.o
  ->cal(C)^times.o wr cal(D)^times.o
$

It sends a pair $(c,d)$, of arities $m$ and $n$, to
$(c;d,dots,d)$ with $m$ copies of $d$. Its total arity is $m n$, in agreement
with the smash-product arity used in the operadic tensor product.

=== Comparison with the Operadic Tensor Product

#lemma(title:[Extension over a Finite coCartesian Cone])[
  Let $s$ be a finite discrete simplicial set and suppose
  $x->s^◁$ and $y->s^◁$ are coCartesian fibrations whose
  fibers at the cone point are products of the fibers over $s$. Restriction
  from functors preserving coCartesian morphisms to their values over $s$ is
  a trivial Kan fibration.
]

#proofsketch[
  A value at the cone point must be the product of the prescribed values over
  $s$, so it exists and is unique up to a contractible space of choices. The
  coCartesian universal property then supplies the structure maps and all
  higher coherences. This is the extension principle used repeatedly in the
  comparison theorem.
]

#theorem(title:[Wreath Product Comparison])[
  The canonical inclusion induces a weak equivalence of $oo$-preoperads

  $
    cal(C)^(times.o,natural) odot cal(D)^(times.o,natural)
    ->(cal(C)^times.o wr cal(D)^times.o,cal(M))
  $

  Consequently, every fibrant replacement of the marked wreath product
  represents the operadic tensor product
  $cal(C)^times.o times.o cal(D)^times.o$.
]

#proofsketch[
  Restriction along $i$ is a trivial Kan fibration on mapping spaces into
  every fibrant $oo$-preoperad. The extension lemma handles the choices over
  each finite family of blocks. To pass from boundary data to arbitrary
  simplices, filter the missing simplices by dimension and combinatorial
  complexity. Each new simplex is attached together with a distinguished
  quasi-degenerate face, so the required extension reduces to an inner-horn
  lifting problem or to the finite-cone lemma. Hence $i$ induces the same
  derived mapping spaces against all fibrant targets.
]

#remark(title:[Three Models of the Same Tensor Product])[
  The comparison may be summarized by

  #align(center, diagram({
    node((0, 0),
      [$cal(C)^(times.o,natural) odot cal(D)^(times.o,natural)$],
      name: <raw>)
    node((0, 1),
      [$(cal(C)^times.o wr cal(D)^times.o,cal(M))$],
      name: <wreath>)
    node((0, 2),
      [$cal(C)^times.o times.o cal(D)^times.o$],
      name: <tensor>)
    edge(<raw>, <wreath>, [weak equivalence], label-side: left, "->")
    edge(<wreath>, <tensor>, [fibrant replacement], label-side: left, "->")
  }))

  The first line is convenient for the model structure, the second exposes
  the two-level operadic combinatorics, and the last is the intrinsic
  $oo$-operadic tensor product. The long simplex filtration in the complete
  proof establishes only the first arrow; it adds no further structure to
  the final object.
]

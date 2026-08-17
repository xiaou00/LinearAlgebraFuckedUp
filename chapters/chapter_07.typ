#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Disintegration and Assembly

Let $A$ be an associative ring. An #emph[involution] on $A$ is a map
$sigma:A->A$ such that

$
  (a+b)^sigma=a^sigma+b^sigma,
  quad (a b)^sigma=b^sigma a^sigma,
  quad (a^sigma)^sigma=a
$

Write $Ring$ for the category of associative rings and $Ring^sigma$ for the
category of rings with involution. The functor

$ A mapsto A^op $

defines a $Sigma_2$-action on $Ring$, and an involution is a coherent
identification $A tilde.eq A^op$ whose square is the identity. Hence
$Ring^sigma$ is the category of homotopy fixed points of this action.

This admits an operadic reformulation. The category $Ring$ is the category of
algebras over the associative operad $cal(O)$ in $Ab$, while $Ring^sigma$ is
the category of algebras over an enlarged operad $cal(O)'$. The reversal of
the order of the inputs defines a $Sigma_2$-action on $cal(O)$, and, up to the
appropriate coherent interpretation,

$ cal(O)' tilde.eq cal(O) semidirect Sigma_2 $

Here $cal(O)$ contains only the associative operations, while $cal(O)'$ also
remembers the involution. Disintegration separates these two layers;
assembly reconstructs the enlarged operad from the operadic fibers and their
symmetry.

We shall extend this idea using unitalization, reduced $oo$-operads, and
generalized $oo$-operads. The main principle is that a unital $oo$-operad
whose underlying $oo$-category is a Kan complex can be disintegrated into a
parametrized family of reduced $oo$-operads and then assembled back.

#remark(title:[Assembly and Semidirect Products])[
  In the example above, assembly recovers the familiar semidirect-product
  operad $cal(O) semidirect Sigma_2$. The general assembly construction should be
  viewed as its homotopy-coherent and parametrized analogue.
]

== Unital $oo$-Operads

For objects ${x_i}_(1<=i<=n)$ and $y$ of an $oo$-operad $cal(O)^times.o$, the
space

$ Mul_cal(O) ({x_i}_(1<=i<=n);y) $

classifies $n$-ary operations with the indicated input and output colors.
For $n=1$ these are the ordinary mapping spaces of the underlying
$oo$-category. The case $n=0$ instead records #emph[constants], so it is here
that the presence of units becomes visible.

#definition(title:[Unital $oo$-Operad])[
  An $oo$-operad $cal(O)^times.o$ is #emph[unital] if, for every color $x$,

  $ Mul_cal(O) (emptyset;x) $

  is contractible. Thus there is an essentially unique nullary operation with
  output $x$.
]

#remark(title:[Two Uses of “Unital”])[
  Classically, “unital operad” may mean either that a distinguished unary
  identity has been chosen or that there is a unique nullary operation. The
  first condition is already built into the definition of an $oo$-operad;
  here #emph[unital] always refers to the second.
]

Both $Comm^times.o$ and $EE_0^times.o$ are unital. The trivial operad
$cat("Triv")^times.o$ is not, since it contains no nullary operation.

#proposition(title:[Categorical Criterion])[
  An $oo$-operad $cal(O)^times.o$ is unital if and only if its total
  $oo$-category $cal(O)^times.o$ is pointed.
]

#proofsketch[
  The fiber over $chevron.l 0 chevron.r$ contains a canonical final object
  $0$. If $x$ lies over $chevron.l n chevron.r$ and has components
  $x_1,dots,x_n$, the operadic Segal condition gives

  $
    Map_(cal(O)^times.o) (0,x)
    tilde.eq product_(1<=i<=n) Mul_cal(O) (emptyset;x_i)
  $

  Hence $0$ is also initial exactly when all nullary operation spaces are
  contractible.
]

=== Localization at Nullary Operations

#proposition(title:[Unital Operads as Local Objects])[
  The operad $EE_0^times.o$ is idempotent for the operadic tensor product:

  $ EE_0 times.o EE_0 tilde.eq EE_0 $

  Consequently

  $ U(cal(O)):=cal(O) times.o EE_0 $

  defines an idempotent localization of $Op_oo$ whose essential image is the
  full subcategory $Op_oo^"un"$ of unital $oo$-operads. Equivalently,
  $cal(O)$ is unital if and only if the canonical map

  $ cal(O)->U(cal(O)) $

  is an equivalence.
]

#proofsketch[
  The tensor product with $EE_0$ freely makes the nullary operation spaces
  contractible. The equivalence $EE_0 times.o EE_0 tilde.eq EE_0$ makes $U$
  idempotent, and the universal property of the operadic tensor product then
  identifies its local objects with the unital operads.
]

=== Unitalization by Pointed Objects

#definition(title:[Unitalization])[
  A map $u:cal(O)^u->cal(O)$ #emph[exhibits $cal(O)^u$ as a unitalization] if
  $cal(O)^u$ is unital and, for every unital $oo$-operad $cal(E)$,
  restriction along $u$ induces an equivalence

  $ Alg_cal(E) (cal(O)^u) tilde.eq Alg_cal(E) (cal(O)) $

  Such an object is unique up to equivalence.
]

#proposition(title:[Explicit Unitalization])[
  Let $cal(O)_*^times.o$ be the $oo$-category of pointed objects of
  $cal(O)^times.o$. Then the forgetful map

  $ p:cal(O)_*^times.o->cal(O)^times.o $

  is a fibration of $oo$-operads, $cal(O)_*^times.o$ is unital, and $p$
  exhibits it as a unitalization of $cal(O)^times.o$.
]

#proofsketch[
  Pointing is compatible with the operadic product decomposition, so the
  pointed objects again form an $oo$-operad. Its zero object supplies the
  unique nullary operations. If $cal(E)$ is unital, then
  $cal(E)^times.o$ is pointed by the categorical criterion; a map from it to
  $cal(O)^times.o$ therefore lifts to pointed objects through a contractible
  space of choices. This is exactly the stated universal property.
]

Thus unital operads form both a localization and a colocalization of
$Op_oo$: tensoring with $EE_0$ gives the former, while pointed objects give
the latter.

=== Unitality in Monoidal Families

#proposition(title:[Fiberwise Criterion])[
  Let

  $ p:cal(C)^times.o->cal(O)^times.o $

  be a coCartesian fibration of $oo$-operads, where $cal(O)$ is unital. Then
  $cal(C)^times.o$ is unital if and only if, for every color $x in cal(O)$,
  the unit object $1_x$ is initial in the fiber $cal(C)_x$.
]

#proofsketch[
  A nullary operation in the total operad is a choice of a nullary operation
  in the base together with a map from the corresponding fiberwise unit.
  Since the nullary operation in $cal(O)$ is unique, contractibility reduces
  exactly to the initiality of each $1_x$.
]

#corollary(title:[Compatibility with Algebra Objects])[
  If $q:cal(C)^u->cal(C)$ is a unitalization over a unital operad $cal(O)$,
  then the composite $cal(C)^u->cal(O)$ is again a coCartesian fibration of
  $oo$-operads. Moreover, for every map of unital operads
  $cal(E)->cal(O)$, restriction induces an equivalence

  $
    Alg_(cal(E)\/cal(O)) (cal(C)^u)
    tilde.eq Alg_(cal(E)\/cal(O)) (cal(C))
  $

  Thus unitalization changes the ambient operad without changing algebra
  objects whose acting operad is already unital.
]

== Generalized $oo$-Operads

For an ordinary $oo$-operad, the Segal equivalence gives

$ cal(O)_(chevron.l n chevron.r)^times.o tilde.eq cal(O)^n $

and the fiber over $chevron.l 0 chevron.r$ is contractible. A generalized
$oo$-operad keeps the same active–inert calculus but allows this fiber to be
an arbitrary $oo$-category. Absolute powers are consequently replaced by
fiber products over the zero-input fiber.

#definition(title:[Generalized $oo$-Operad])[
  A #emph[generalized $oo$-operad] is an $oo$-category

  $ q:cal(O)^times.o->Ner(Fin_*) $

  satisfying the following relative Segal conditions.

  + Every inert morphism in $Ner(Fin_*)$ admits a $q$-coCartesian lift.

  + An inert square in $Fin_*$ is called #emph[exact] when the corresponding
    square of nonbasepoint sets is a pushout. Every exact inert square induces
    a pullback square between the fibers of $q$.

  + A square of $q$-coCartesian lifts of an exact inert square is a
    $q$-limit diagram.

  In particular, if $cal(B):=cal(O)_(chevron.l 0 chevron.r)^times.o$ and
  $cal(A):=cal(O)_(chevron.l 1 chevron.r)^times.o$, then

  $
    cal(O)_(chevron.l n chevron.r)^times.o
    tilde.eq
    cal(A) times_cal(B) dots times_cal(B) cal(A)
  $

  where the right-hand side has $n$ factors.
]

#remark(title:[What Was Relaxed?])[
  For an ordinary $oo$-operad, $cal(B)$ is contractible, so the relative
  product above reduces to $cal(A)^n$. A generalized $oo$-operad therefore
  has the same operations and substitution laws, but its colors may vary
  over the parameter $oo$-category $cal(B)$.

  For $n=2$, the relative Segal equivalence is the pullback square

  #align(center, diagram({
    node((0, 0), [$cal(O)_(chevron.l 2 chevron.r)^times.o$])
    node((1, 0), [$cal(A)$])
    node((0, 1), [$cal(A)$])
    node((1, 1), [$cal(B)$])
    edge((0, 0), (1, 0), [$rho^1$], label-side: left, "->")
    edge((0, 0), (0, 1), [$rho^2$], label-side: right, "->")
    edge((1, 0), (1, 1), [$epsilon$], label-side: left, "->")
    edge((0, 1), (1, 1), [$epsilon$], label-side: right, "->")
  }))

  Thus $cal(O)_(chevron.l 2 chevron.r)^times.o tilde.eq
  cal(A) times_cal(B) cal(A)$. When $cal(B) tilde.eq ast$, this becomes the
  ordinary product $cal(A) times cal(A)$.
]

#definition(title:[Maps])[
  A map of generalized $oo$-operads is a functor over $Ner(Fin_*)$ which
  carries inert morphisms to inert morphisms. It is a #emph[fibration of
  generalized $oo$-operads] when its underlying functor is an isofibration.
  We denote the resulting $oo$-category by $Op_oo^"gn"$.
]

#proposition(title:[Recovering Ordinary $oo$-Operads])[
  A generalized $oo$-operad $cal(O)^times.o$ is an ordinary $oo$-operad if
  and only if

  $ cal(O)_(chevron.l 0 chevron.r)^times.o $

  is a contractible Kan complex.
]

#proofsketch[
  This is exactly the missing ordinary Segal condition. Once the zero-input
  fiber is contractible, every relative fiber product over it becomes the
  corresponding absolute product. The converse is part of the usual
  definition of an $oo$-operad.
]

#remark(title:[Generalized Operadic Model Structure])[
  Marked preoperads admit a model structure whose cofibrations are
  monomorphisms and whose fibrant objects are generalized $oo$-operads. The
  ordinary operadic model structure is a further localization of it. Hence
  there is a fully faithful inclusion

  $ Op_oo subset Op_oo^"gn" $

  and ordinary operads are precisely the generalized operads satisfying the
  contractibility condition above.
]

=== The Parameter Category

Taking the zero-input fiber defines a forgetful functor

$ F:Op_oo^"gn"->Cat_oo, quad F(cal(O))=cal(O)_(chevron.l 0 chevron.r)^times.o $

#proposition(title:[The Trivial Generalized Operad])[
  The functor $F$ has a fully faithful right adjoint

  $ G:Cat_oo->Op_oo^"gn", quad G(cal(C))=cal(C) times Ner(Fin_*) $

  In particular, every $oo$-category occurs as the parameter category of a
  generalized $oo$-operad.
]

#proofsketch[
  A map from a generalized operad to
  $cal(C) times Ner(Fin_*)$ is forced along inert morphisms and is therefore
  determined by its restriction to the zero-input fiber. Conversely, every
  functor from that fiber to $cal(C)$ extends by right Kan extension. The
  space of extensions is contractible.
]

#remark(title:[The Adjunction at a Glance])[
  The two functors fit into

  $ Cat_oo -->^G Op^"gn"_oo -->^F Cat_oo $

  with $F compose G tilde.eq id_(Cat_oo)$. The middle term remembers all
  operadic fibers; $F$ keeps only their parameter category, while $G$ inserts
  the constant family over it.
]

=== Families of $oo$-Operads

#definition(title:[$cal(C)$-Family of $oo$-Operads])[
  Let $cal(C)$ be an $oo$-category. A #emph[$cal(C)$-family of
  $oo$-operads] is an isofibration

  $ p:cal(P)^times.o->cal(C) times Ner(Fin_*) $

  such that:

  + inert morphisms admit $p$-coCartesian lifts;

  + the component maps over
    $rho^i:chevron.l n chevron.r->chevron.l 1 chevron.r$ exhibit an object as
    the corresponding $p$-limit of its $n$ components;

  + for every $c in cal(C)$, the fiber
    $cal(P)_c^times.o->Ner(Fin_*)$ is an ordinary $oo$-operad.
]

#remark(title:[Reading a Family Fiberwise])[
  For every $c in cal(C)$, the ordinary operad over $c$ is obtained from the
  pullback square

  #align(center, diagram({
    node((0, 0), [$cal(P)_c^times.o$])
    node((1, 0), [$cal(P)^times.o$])
    node((0, 1), [$brace.l c brace.r times Ner(Fin_*)$])
    node((1, 1), [$cal(C) times Ner(Fin_*)$])
    edge((0, 0), (1, 0), "->")
    edge((0, 0), (0, 1), "->")
    edge((1, 0), (1, 1), [$p$], label-side: left, "->")
    edge((0, 1), (1, 1), "->")
  }))

  A morphism $c->d$ in $cal(C)$ supplies coherent transport from the operad
  $cal(P)_c^times.o$ to $cal(P)_d^times.o$. The generalized operad is the
  total object obtained by assembling all these fibers.
]

#theorem(title:[Generalized Operads Are Families])[
  Let

  $ p:cal(P)^times.o->cal(C) times Ner(Fin_*) $

  be an isofibration. The following are equivalent:

  + $cal(P)^times.o$ is a generalized $oo$-operad and the induced map
    $cal(P)_(chevron.l 0 chevron.r)^times.o->cal(C)$ is a trivial Kan
    fibration;

  + $p$ exhibits $cal(P)^times.o$ as a $cal(C)$-family of ordinary
    $oo$-operads.

  Consequently a generalized $oo$-operad is equivalently a pair
  $(cal(C),cal(P)^times.o)$ consisting of an $oo$-category $cal(C)$ and a
  $cal(C)$-family of $oo$-operads. Canonically one may take

  $ cal(C)=cal(P)_(chevron.l 0 chevron.r)^times.o $
]

#proofsketch[
  The relative Segal conditions are exactly the ordinary Segal conditions in
  each fiber together with coherent transport along $cal(C)$. The trivial Kan
  condition identifies $cal(C)$ with the zero-input fiber, and the converse
  construction glues the transported fibers.
]

== Assembly and Approximations to $oo$-Operads

The inclusion $i:Op_oo arrow.r.hook Op_oo^"gn"$ is reflective: every
generalized operad has a universal ordinary replacement.

#definition(title:[Assembly])[
  A map from a generalized $oo$-operad to an ordinary one

  $ gamma:cal(O)^times.o->cal(P)^times.o $

  #emph[assembles] $cal(O)^times.o$ into $cal(P)^times.o$ if, for every
  ordinary $oo$-operad $cal(Q)^times.o$, precomposition with $gamma$ induces
  an equivalence

  $
    Alg_cal(P) (cal(Q))
    tilde.eq
    Alg_cal(O) (cal(Q))
  $
]

#proposition(title:[The Assembly Reflection])[
  The inclusion $i:Op_oo arrow.r.hook Op_oo^"gn"$ has a left adjoint
  $Assem:Op_oo^"gn"->Op_oo$. Its unit
  $cal(O)^times.o->Assem(cal(O))^times.o$ is an assembly, unique up to a
  contractible space of choices. Equivalently, $Op_oo$ is a localization of
  $Op_oo^"gn"$.
]

#remark(title:[Assembly as a Colimit])[
  If $cal(O)^times.o$ is presented by a $cal(C)$-family
  ${cal(O)_c^times.o}_(c in cal(C))$, then its assembly behaves as the
  operadic colimit of that family. Schematically,

  #align(center, diagram({
    node((0, 0), [$cal(O)^times.o$])
    node((2, 0), [$cal(Q)^times.o$])
    node((1, 1), [$Assem(cal(O))^times.o$])
    edge((0, 0), (2, 0), [$g$], label-side: left, "->")
    edge((0, 0), (1, 1), [$eta$], label-side: right, "->")
    edge((1, 1), (2, 0), [$tilde(g)$], label-side: right, "->")
  }))

  Every map $g$ from $cal(O)^times.o$ to an ordinary operad factors through
  the unit $eta$, and the factor $tilde(g)$ is unique up to contractible
  choice. This is the precise sense in which assembly forgets only the
  varying parameter category.
]

=== Approximation and Weak Approximation

Assembly is an abstract localization. An approximation gives a concrete
category of operations from which the same operad can be reconstructed.

#definition(title:[Approximation])[
  Let $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad and let
  $f:cal(E)->cal(O)^times.o$ be an isofibration. We call $f$ an
  #emph[approximation] if:

  + for every $e in cal(E)$ over $chevron.l n chevron.r$ and every inert
    projection $rho^i:chevron.l n chevron.r->chevron.l 1 chevron.r$, there is
    a locally $f$-coCartesian lift $e->e_i$ whose image is inert;

  + every active morphism $alpha:x->f(e)$ admits an $f$-Cartesian lift
    $overline(alpha):overline(x)->e$.

  More generally, $f$ is a #emph[weak approximation] if the first condition
  holds and, for every morphism $alpha:x->f(e)$, the $oo$-category of
  factorizations

  $ x -->^gamma f(e') -->^(f(beta)) f(e) $

  with $gamma$ inert is weakly contractible. An arbitrary functor is called a
  (weak) approximation when it becomes one after factoring it as an
  equivalence followed by an isofibration.
]

#remark(title:[The Two Lifting Rules])[
  The definition separates the two roles of morphisms in an operad:

  #align(center, diagram({
    node((0, 0), [$overline(x)$])
    node((1, 0), [$e$])
    node((0, 1), [$x$])
    node((1, 1), [$f(e)$])
    edge((0, 0), (1, 0), [$overline(alpha)$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f$], label-side: right, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), [$alpha$ #text[ active]], label-side: right, "->")
  }))

  Inert arrows decompose an object into its inputs and lift coCartesianly;
  active arrows encode operations and lift Cartesianly. A weak approximation
  replaces the chosen Cartesian lift by a contractible space of inert--active
  factorizations.
]

#proposition(title:[Active-Fiber Criterion])[
  Suppose the inert lifting condition above holds. Then $f$ is a weak
  approximation if and only if, for every $e in cal(E)$ and every active
  $alpha:x->f(e)$, the $oo$-category

  $
    cal(E)_(\/ e) times_(cal(O)^times.o_(\/ f(e))) {alpha}
  $

  of lifts of $alpha$ is weakly contractible. Hence only active arrows need
  to be tested.
]

#proofsketch[
  Factor an arbitrary arrow into an inert arrow followed by an active arrow.
  The inert lift is already supplied by hypothesis, so the remaining choice
  is precisely a point of the displayed active lifting category. The
  active--inert factorization system and cofinality identify its
  contractibility with the definition above.
]

#proposition(title:[Formal Properties])[
  Approximations satisfy the following useful rules.

  + Every approximation is a weak approximation.

  + If $f$ is a map of generalized $oo$-operads, then $f$ is an approximation
    exactly when its restrictions to the ordinary operadic parameter fibers
    are approximations.

  + Given composable maps of $oo$-operads
    $cal(O)^times.o->^f cal(P)^times.o->^g cal(Q)^times.o$ whose underlying
    color categories are Kan complexes, if $g$ is an approximation, then $f$
    is an approximation if and only if $g compose f$ is.

  + For a map of $oo$-operads whose underlying categories are Kan complexes,
    approximation and weak approximation are equivalent; equivalently, the
    induced map on active subcategories is an equivalence followed by a right
    fibration.
]

=== The Approximation Theorem

To formulate the central conclusion, let $f:cal(E)->cal(O)^times.o$ be a weak
approximation. An $cal(E)$-algebra in an $oo$-operad
$cal(P)^times.o$ is a functor $a:cal(E)->cal(P)^times.o$ over $Ner(Fin_*)$
which sends the chosen inert lifts in $cal(E)$ to inert morphisms. It is
#emph[locally constant] if it sends every arrow over
$id_(chevron.l 1 chevron.r)$ to an equivalence. Write
$Alg_cal(E) (cal(P))$ and $Alg_cal(E)^"loc" (cal(P))$ for the resulting
$oo$-categories.

#theorem(title:[Approximation Theorem])[
  Let $f:cal(E)->cal(O)^times.o$ be a weak approximation and let
  $cal(P)^times.o$ be any $oo$-operad. Precomposition defines

  $ theta:Alg_cal(O) (cal(P))->Alg_cal(E) (cal(P)) $

  + If $f$ induces an equivalence
    $cal(E)_(chevron.l 1 chevron.r)->cal(O)$ on colors, then $theta$ is an
    equivalence.

  + If $cal(O)$ is a Kan complex and the map on colors is only a weak homotopy
    equivalence, then $theta$ induces an equivalence

    $
      Alg_cal(O) (cal(P))
      tilde.eq
      Alg_cal(E)^"loc" (cal(P))
    $
]

#proofsketch[
  Replace $f$ by an equivalent isofibration and extend an
  $cal(E)$-algebra by right Kan extension. The inert lifting condition makes
  the extension preserve input decompositions, while the active-fiber
  criterion says that every indexing category used to define an operation is
  contractible. The extension therefore exists and is unique up to
  contractible choice. If the color map is only a weak equivalence, precisely
  the locally constant algebras descend.
]

#remark(title:[What the Theorem Says])[
  An approximation may contain many more objects and morphisms than
  $cal(O)^times.o$, but it contains exactly one coherent way to represent
  each operation. Thus it presents the same algebra theory:

  #align(center, diagram({
    node((0, 0), [$cal(E)$])
    node((2, 0), [$cal(P)^times.o$])
    node((1, 1), [$cal(O)^times.o$])
    node((1, 2), [$Alg_cal(E) (cal(P)) tilde.eq Alg_cal(O) (cal(P))$])
    edge((0, 0), (2, 0), [$a compose f$], label-side: left, "->")
    edge((0, 0), (1, 1), [$f$], label-side: right, "->")
    edge((1, 1), (2, 0), [$a$], label-side: right, "->")
    edge((1, 1), (1, 2), "--")
  }))

  The upper triangle is the concrete presentation; the lower node records
  that restriction along $f$ loses no algebraic structure.
]

#corollary(title:[Detecting Equivalences of Operads])[
  Let $f:cal(E)^times.o->cal(O)^times.o$ be a weak approximation of ordinary
  $oo$-operads. If $f$ induces an equivalence on their underlying color
  $oo$-categories, then $f$ is an equivalence of $oo$-operads.
]

#remark(title:[Model-Categorical Form])[
  Under the same color-equivalence hypothesis, an approximation induces a
  left Quillen equivalence between the corresponding slice model categories
  of $oo$-preoperads. The technical fibrization construction in the full
  proof replaces an arbitrary approximation by a fibration with the same
  homotopy type; the contractibility criteria above guarantee that this
  replacement does not change the represented operad.
]

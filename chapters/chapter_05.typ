#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= $oo$-Operads

== Motivations

=== From Binary Products to Many Inputs

A commutative monoid is usually presented by a binary multiplication and a
unit, subject to strict identities. A symmetric monoidal category
$cal(C)$ has analogous data

$ 1 in cal(C), quad times.o:cal(C) times cal(C) -> cal(C) $

but associativity, symmetry, and the unit laws now hold only through coherent
isomorphisms. Trying to repeat this definition in an $oo$-category would lead
to isomorphisms between isomorphisms, then homotopies between those
isomorphisms, and so on. Listing this infinite hierarchy explicitly is not a
workable definition.

The useful change of viewpoint is to regard an $n$-fold tensor product as a
single $n$-ary operation. Its meaning is captured by multimorphisms

$
  Hom_cal(C) (c_1 times.o dots times.o c_n,d)
  tilde.eq "Mul"_cal(C) (c_1,dots,c_n;d)
$

For example, a linear map $u times.o v -> w$ is the same thing as a bilinear
map $u times v -> w$. Both parenthesizations of $u times.o v times.o w$ therefore
represent trilinear maps, which explains why the associator is canonical.
Operads turn this observation into a definition: all finite-arity operations
and their substitutions are recorded at once.

=== Pointed Finite Sets as Bookkeeping

Let $Fin_*$ be the category of finite pointed sets, and write

$ chevron.l n chevron.r = {ast,1,dots,n} $

A pointed map $alpha:chevron.l n chevron.r -> chevron.l m chevron.r$ may be viewed as a
partially defined map from the $n$ inputs to the $m$ outputs: an input sent to
$ast$ is simply unused. Two kinds of maps will be especially important.

- The inert map $rho^i:chevron.l n chevron.r -> chevron.l 1 chevron.r$ selects the
  $i$th input and sends every other input to $ast$

- The active fold map $mu_n:chevron.l n chevron.r -> chevron.l 1 chevron.r$ sends every
  non-basepoint to $1$

#figure(
  align(center, cetz.canvas(length: 0.82cm, {
    import cetz.draw: *

    let selected = 1.25pt + c-thm
    let forgotten = (
      paint: c-rem,
      thickness: 0.85pt,
      dash: "dashed",
    )
    let selected-arrow = (
      end: ">",
      scale: 0.64,
      fill: c-thm,
      stroke: c-thm,
    )
    let forgotten-arrow = (
      end: ">",
      scale: 0.57,
      fill: c-rem,
      stroke: c-rem,
    )
    let ordinary-node(p) = circle(
      p,
      radius: 0.085,
      fill: white,
      stroke: 1pt + c-thm,
    )
    let chosen-node(p) = circle(
      p,
      radius: 0.105,
      fill: c-thm,
      stroke: 1pt + c-thm,
    )
    let base-node(p) = circle(
      p,
      radius: 0.105,
      fill: c-rem,
      stroke: 1pt + c-rem,
    )

    // rho^3 keeps input 3 and sends every other input to the basepoint.
    line((0.85, 3.75), (4.65, 0.20), stroke: forgotten, mark: forgotten-arrow)
    line((0.85, 3.00), (4.65, 0.20), stroke: forgotten, mark: forgotten-arrow)
    line((0.85, 2.25), (4.65, 2.72), stroke: selected, mark: selected-arrow)
    line((0.85, 1.50), (4.65, 0.20), stroke: forgotten, mark: forgotten-arrow)
    line((0.85, 0.75), (4.65, 0.20), stroke: forgotten, mark: forgotten-arrow)
    line((0.85, 0.20), (4.65, 0.20), stroke: forgotten, mark: forgotten-arrow)

    for p in ((0.85, 3.75), (0.85, 3.00), (0.85, 1.50), (0.85, 0.75)) {
      ordinary-node(p)
    }
    chosen-node((0.85, 2.25))
    base-node((0.85, 0.20))
    chosen-node((4.65, 2.72))
    base-node((4.65, 0.20))

    content((2.75, 4.55), text(size: 9.5pt, weight: "semibold", fill: ink)[$rho^3:chevron.l 5 chevron.r->chevron.l 1 chevron.r$])
    content((0.85, 4.18), text(size: 7.5pt, fill: muted)[inputs])
    content((4.65, 3.18), text(size: 7.5pt, fill: muted)[output])
    content((0.50, 3.75), text(size: 8pt, fill: muted)[$1$])
    content((0.50, 3.00), text(size: 8pt, fill: muted)[$2$])
    content((0.50, 2.25), text(size: 8pt, fill: c-thm)[$3$])
    content((0.50, 1.50), text(size: 8pt, fill: muted)[$4$])
    content((0.50, 0.75), text(size: 8pt, fill: muted)[$5$])
    content((0.50, 0.20), text(size: 8pt, fill: c-rem)[$ast$])
    content((5.00, 2.72), text(size: 8pt, fill: c-thm)[$1$])
    content((5.00, 0.20), text(size: 8pt, fill: c-rem)[$ast$])

    content((6.65, 2.42), text(size: 8pt, fill: ink)[$rho^i (i)=1$])
    content((6.65, 1.88), text(size: 8pt, fill: muted)[$rho^i (j)=ast$ for $j!=i$])
  })),
  caption: [The inert projection $rho^i$ retains the $i$th input and sends every other input to the basepoint.],
)

#remark(title:[Why the Pointed Set $chevron.l n chevron.r$ Is So Effective])[
  The elements $1,dots,n$ represent input slots; the basepoint $ast$ is not an
  additional input or output, but a place for unused data. Consequently, one
  pointed map

  $ alpha:chevron.l n chevron.r->chevron.l m chevron.r $

  records three pieces of information at once.

  - The fiber $alpha^(-1)(j)$ specifies which inputs are grouped together to
    produce the $j$th output

  - The fiber $alpha^(-1)(ast)$ records the inputs which are discarded

  - If $alpha^(-1)(j)$ is empty, the $j$th output is produced by a nullary
    operation, hence by a constant or unit map

  In particular, $chevron.l 0 chevron.r={ast}$ represents zero inputs. The
  unique active map $chevron.l 0 chevron.r->chevron.l 1 chevron.r$ therefore
  encodes nullary operations.

  More generally, an active map sends no non-basepoint to $ast$, while an
  inert map selects exactly one input for every output. Every pointed map
  factors, essentially uniquely, as

  $
    chevron.l n chevron.r
    ->^i chevron.l k chevron.r
    ->^a chevron.l m chevron.r,
    quad alpha=a compose i
  $

  with $i$ inert and $a$ active. The inert part selects and forgets inputs;
  the active part groups the remaining inputs into genuine operations. This
  active--inert separation is the central reason that $Fin_*$ can encode
  units, tensor products, projections, and all finite substitutions in one
  small category.
]

Given a symmetric monoidal category $cal(C)$, package its tensor product into
a category $cal(C)^times.o$ over $Fin_*$

$ p:cal(C)^times.o -> Fin_* $

An object over $chevron.l n chevron.r$ is a finite list
$[c_1,dots,c_n]$. A morphism over
$alpha:chevron.l n chevron.r -> chevron.l m chevron.r$ is a family of maps

$
  times.o_(i in alpha^(-1)(j)) c_i -> d_j
  quad (1 <= j <= m)
$

The tensor over an empty fiber is interpreted as the unit. Composition is
substitution: first tensor together the inputs belonging to each intermediate
output, then tensor those blocks according to the next pointed map.

This projection contains the entire monoidal structure. Classically it has
the following two properties.

1. The functor $p$ is an opfibration, so maps in $Fin_*$ admit coherent
   pushforward along cocartesian lifts

2. The inert projections induce equivalences

   $
     cal(C)^times.o_(chevron.l n chevron.r)
     tilde.eq product_(i=1)^n cal(C)^times.o_(chevron.l 1 chevron.r)
     tilde.eq cal(C)^n
   $

#remark(title:[How the Usual Structure Is Recovered])[
  Put $cal(C)=cal(C)^times.o_(chevron.l 1 chevron.r)$. The fiber over
  $chevron.l 0 chevron.r$ determines the unit, pushforward along $mu_2$ gives
  $c times.o d$, and permutations of $chevron.l n chevron.r$ give the symmetry.
  Different composites in $Fin_*$ encode different parenthesizations. Their
  functorial compatibility supplies the associator, the unit constraints, and
  the Mac Lane coherence diagrams automatically.

  Thus the logical process is

  $
    "finite inputs"
    -> "a map in " Fin_*
    -> "cocartesian transport"
    -> "tensor and all its coherences"
  $
]

=== The Higher-Categorical Form

The same description survives unchanged after replacing categories by
$oo$-categories. A symmetric monoidal $oo$-category is encoded by a
coCartesian fibration

$ p:cal(C)^times.o -> Ner(Fin_*) $

for which the inert maps $rho^i$ induce the Segal equivalence

$
  cal(C)^times.o_(chevron.l n chevron.r)
  tilde.eq product_(i=1)^n cal(C)^times.o_(chevron.l 1 chevron.r)
$

The fiber over $chevron.l 1 chevron.r$ is the underlying $oo$-category
$cal(C)$. Since composition of cocartesian transport is coherent by
construction, the infinitely many higher associativity and symmetry
homotopies no longer have to be specified one at a time.

The classical theory below isolates the many-input structure which will later
be transferred to the $oo$-categorical setting.

== Operads

=== Colored Operads

An ordinary category organizes unary maps $x->y$. A colored operad instead
allows a finite collection of inputs and a single output, with every input and
output carrying a type, or #emph[color].

#definition(title:[Colored Operad])[
  A #emph[colored operad] $cal(O)$ consists of the following data.

  1. A collection of objects, called the #emph[colors] of $cal(O)$

  2. For every finite set $I$, colors ${x_i}_(i in I)$, and a color $y$, a
     set of multimorphisms

     $ Mul_cal(O) ({x_i}_(i in I);y) $

  3. For every map $alpha:I->J$, with $I_j=alpha^(-1)(j)$, substitution maps

     $
       product_(j in J) Mul_cal(O) ({x_i}_(i in I_j);y_j)
       times Mul_cal(O) ({y_j}_(j in J);z)
       -> Mul_cal(O) ({x_i}_(i in I);z)
     $

  4. Identity operations

     $ "id"_x in Mul_cal(O) ({x};x) $

  Substitution is associative and the identity operations are left and right
  units. Reindexing the finite set $I$ by a bijection gives the symmetric
  action on the inputs.
]

#remark(title:[Meaning of Substitution])[
  The map $alpha:I->J$ groups the original inputs into the fibers
  $I_j=alpha^(-1)(j)$. Choose an inner operation for every group and one outer
  operation

  $
    phi_j in Mul_cal(O) ({x_i}_(i in I_j);y_j),
    quad
    psi in Mul_cal(O) ({y_j}_(j in J);z)
  $

  Substitution first applies each $phi_j$ to the inputs in $I_j$, producing
  one intermediate output of color $y_j$, and then feeds all these outputs
  into $psi$. The resulting operation is

  $
    psi compose ({phi_j}_(j in J))
    in Mul_cal(O) ({x_i}_(i in I);z)
  $

  For example, take $J={1,2}$, $I_1={1}$, and $I_2={2,3,4}$. A unary
  operation $g$, a ternary operation $h$, and a binary operation $f$ then
  compose as

  $
    (f compose (g,h))(a_1,a_2,a_3,a_4)
    =f(g(a_1),h(a_2,a_3,a_4))
  $

  Thus operadic composition is simply simultaneous insertion into all input
  slots. Associativity says that a multilevel insertion gives the same result
  whether it is performed one level at a time or all at once.
]

The use of a finite indexing set, rather than a chosen ordering, is the form
most compatible with $Fin_*$. Every colored operad has an underlying category
with

$ Hom_cal(O) (x,y)=Mul_cal(O) ({x};y) $

An ordinary category is therefore the special colored operad whose
multimorphism sets are empty unless there is exactly one input.

#remark(title:[Simplicial Variant])[
  Replacing every set $Mul_cal(O) ({x_i}_(i in I);y)$ by a simplicial set,
  with simplicial substitution maps, gives a #emph[simplicial colored
  operad]. We will return to this enrichment only after the classical theory
  has been packaged categorically.
]

=== Operads: The Single-Color Case

#definition(title:[Operad])[
  An #emph[operad] is a colored operad $cal(O)$ having only one color, denoted
  by $1$. For every $n>=0$, put

  $
    cal(O)_n
    =Mul_cal(O) ({1}_(1<=i<=n);1)
  $

  We call $cal(O)_n$ the set of $n$-ary operations. The operad is equivalently
  determined by the collection ${cal(O)_n}_(n>=0)$, the actions of the
  symmetric groups $Sigma_n$, the identity $"id" in cal(O)_1$, and the
  substitution maps

  $
    cal(O)_m times product_(1<=i<=m) cal(O)_(n_i)
    -> cal(O)_(n_1+dots+n_m)
  $

  These data are unital, associative, and equivariant under the symmetric
  group actions.
]

Here $cal(O)_0$, $cal(O)_1$, and $cal(O)_2$ are the nullary, unary, and binary
operations. One may picture substitution by grafting rooted trees;
associativity says that the result does not depend on the order of grafting.

#remark(title:[Nullary Operations Are Constants])[
  A nullary operation has no inputs. For a colored operad, an operation with
  output color $y$ is an element of

  $ Mul_cal(O) (emptyset;y) $

  so it behaves as a constant of color $y$. In the colored operad associated
  to a symmetric monoidal category $cal(C)$, such a constant is represented
  by a morphism from the unit object

  $ 1_cal(C)->y $

  Thus, in the one-colored case, the elements of $cal(O)_0$ are precisely the
  constant operations.
]

=== A Basic Example

#example(title:[A Symmetric Monoidal Category as a Colored Operad])[
  Every symmetric monoidal category $cal(C)$ determines a colored operad with
  colors $"Ob"(cal(C))$ and

  $
    Mul_cal(C) ({x_i}_(i in I);y)
    =Hom_cal(C) (times.o_(i in I)x_i,y)
  $

  Composition is composition of maps after tensoring. This example has an
  additional representability property: the functor

  $ y |-> Mul_cal(C) ({x_i}_(i in I);y) $

  is represented by $times.o_(i in I)x_i$. A general colored operad supplies the
  multimorphism sets but need not supply an object representing them. This is
  the precise reason that symmetric monoidal categories form a special class
  of operads.
]

=== Packaging a Colored Operad over $Fin_*$

The definition of a colored operad is asymmetric: a morphism has a finite
collection of inputs but only one output. Following Higher Algebra, we correct
this asymmetry by packaging the data into an ordinary category over $Fin_*$.

#example(title:[The Category $cal(O)^times.o$])[
  Let $cal(O)$ be a colored operad. Define a category $cal(O)^times.o$ as follows.

  1. Its objects are finite, possibly empty, sequences of colors

     $ [x_1,dots,x_m] $

  2. A morphism from $[x_1,dots,x_m]$ to $[y_1,dots,y_n]$ consists of a
     pointed map

     $ alpha:chevron.l m chevron.r->chevron.l n chevron.r $

     and, for every $1<=j<=n$, an operation

     $
       phi_j in
       Mul_cal(O) ({x_i}_(i in alpha^(-1)(j));y_j)
     $

     Inputs sent by $alpha$ to $ast$ are discarded. An empty fiber
     $alpha^(-1)(j)$ is allowed and is governed by a nullary operation.

  3. The identity of $[x_1,dots,x_m]$ lies over the identity of
     $chevron.l m chevron.r$ and is given by the unary operations
     ${"id"_(x_i)}_(1<=i<=m)$

  4. Suppose $(alpha,{phi_j}_(1<=j<=n))$ is followed by
     $(beta,{psi_k}_(1<=k<=r))$. Their composite lies over

     $ beta compose alpha:chevron.l m chevron.r->chevron.l r chevron.r $

     and its $k$th component is the operadic substitution

     $
       theta_k
       =psi_k compose ({phi_j}_(j in beta^(-1)(k)))
       in Mul_cal(O)
       ({x_i}_(i in (beta compose alpha)^(-1)(k));z_k)
     $

  The unit and associativity axioms of $cal(O)$ imply the corresponding
  category axioms for $cal(O)^times.o$.
]

#remark(title:[Meaning of a Morphism in $cal(O)^times.o$])[
  A morphism in $cal(O)^times.o$ has two layers.

  1. The pointed map $alpha:chevron.l m chevron.r->chevron.l n chevron.r$ is
     a #emph[wiring diagram]. If $alpha(i)=j$, the input wire $x_i$ is routed
     to the $j$th output; if $alpha(i)=ast$, that wire is discarded

  2. For every output $j$, the decoration

     $
       phi_j in
       Mul_cal(O) ({x_i}_(i in alpha^(-1)(j));y_j)
     $

     combines exactly the wires routed to $j$ and produces an output of color
     $y_j$

  Thus a many-output morphism is not a new primitive operation: it is a family
  of ordinary one-output operadic operations performed in parallel.

  For example, consider $alpha:chevron.l 4 chevron.r->chevron.l 2 chevron.r$
  given by

  $
    alpha(1)=alpha(3)=1,
    quad alpha(2)=2,
    quad alpha(4)=ast
  $

  A morphism over $alpha$ from $[x_1,x_2,x_3,x_4]$ to $[y_1,y_2]$ is precisely
  a pair

  $
    phi_1 in Mul_cal(O) ({x_1,x_3};y_1),
    quad
    phi_2 in Mul_cal(O) ({x_2};y_2)
  $

  The input $x_4$ plays no role. If $cal(O)$ comes from a symmetric monoidal
  category, the same data are maps

  $ x_1 times.o x_3->y_1, quad x_2->y_2 $

  Composition now has a transparent meaning: connect the output wires of the
  first diagram to the input wires of the second and substitute the vertex
  labels. The pointed maps compose, while the operations compose by operadic
  substitution.
]

There is a canonical projection

$ pi:cal(O)^times.o->Fin_* $

On objects it sends $[x_1,dots,x_m]$ to $chevron.l m chevron.r$. On morphisms
it sends $(alpha,{phi_j})$ to $alpha$. Thus $pi$ remembers the assignment of
inputs to outputs and forgets the operations decorating that assignment.

#definition(title:[Inert Morphism])[
  A morphism $f:chevron.l m chevron.r->chevron.l n chevron.r$ in $Fin_*$ is
  #emph[inert] if every $i in {1,dots,n}$ has exactly one preimage under $f$.
  In particular, $rho^i:chevron.l n chevron.r->chevron.l 1 chevron.r$ is
  inert.
]

#remark[
  Write $chevron.l n chevron.r^circle={1,dots,n}$ for the non-basepoint part.
  Every inert morphism

  $ f:chevron.l m chevron.r->chevron.l n chevron.r $

  determines an injective map

  $ alpha:chevron.l n chevron.r^circle->chevron.l m chevron.r^circle $

  characterized by

  $ f^(-1)({i})={alpha(i)} $

  Thus an inert map chooses one input for every output; all inputs outside the
  image of $alpha$ are sent to the basepoint. Conversely, every such injection
  determines a unique inert map.
]

#remark(title:[What the Packaging Remembers])[
  The fiber over $chevron.l 1 chevron.r$ is the underlying category of
  $cal(O)$, while the inert maps $rho^i$ identify the fiber over
  $chevron.l n chevron.r$ with $cal(O)^n$. Morphisms over the active fold
  $mu_n$ recover the sets $Mul_cal(O) ({x_i}_(1<=i<=n);y)$. Consequently,
  both multimorphisms and their substitution law can be reconstructed from

  $ pi:cal(O)^times.o->Fin_* $
]

== Toward $oo$-Operads

=== Definition of an $oo$-Operad

Let

$ p:cal(O)^times.o->Ner(Fin_*) $

be a functor between $oo$-categories. Write
$cal(O)^times.o_(chevron.l n chevron.r)$ for its fiber over
$chevron.l n chevron.r$. If $x$ and $y$ lie over $chevron.l m chevron.r$ and
$chevron.l n chevron.r$, respectively, and
$f:chevron.l m chevron.r->chevron.l n chevron.r$, let

$ Map_(cal(O)^times.o)^f (x,y) $

denote the union of those components of $Map_(cal(O)^times.o) (x,y)$ which lie over
$f$.

#definition(title:[$oo$-Operad])[
  An #emph[$oo$-operad] is a functor

  $ p:cal(O)^times.o->Ner(Fin_*) $

  satisfying the following conditions.

  1. #emph[Inert lifts.] For every inert
     $f:chevron.l m chevron.r->chevron.l n chevron.r$ and every
     $x in cal(O)^times.o_(chevron.l m chevron.r)$, there is a $p$-coCartesian
     morphism

     $ x->f_! x $

     lying over $f$

  2. #emph[Decomposition of targets.] Let
     $x in cal(O)^times.o_(chevron.l m chevron.r)$ and
     $y in cal(O)^times.o_(chevron.l n chevron.r)$. Choose $p$-coCartesian
     morphisms $y->y_i$ over
     $rho^i:chevron.l n chevron.r->chevron.l 1 chevron.r$. Then every
     $f:chevron.l m chevron.r->chevron.l n chevron.r$ induces an equivalence

     $
       Map_(cal(O)^times.o)^f (x,y)
       tilde.eq
       product_(i=1)^n
       Map_(cal(O)^times.o)^(rho^i compose f) (x,y_i)
     $

  3. #emph[Existence of tuples.] For every finite collection
     $x_1,dots,x_n in cal(O)^times.o_(chevron.l 1 chevron.r)$, there is an object
     $x in cal(O)^times.o_(chevron.l n chevron.r)$ and $p$-coCartesian morphisms
     $x->x_i$ over the maps $rho^i$
]

Condition (1) says that an $n$-tuple can be projected to selected entries.
Condition (2) says that a morphism with $n$ outputs is exactly a collection of
$n$ independent one-output morphisms. Condition (3) says that every finite
list of colors really occurs as an object over $chevron.l n chevron.r$.

#remark(title:[The Segal Form])[
  Let

  $ cal(O)=cal(O)^times.o_(chevron.l 1 chevron.r) $

  be the #emph[underlying $oo$-category]. Conditions (2) and (3) together say
  that the inert projections induce an equivalence

  $
    cal(O)^times.o_(chevron.l n chevron.r)
    tilde.eq cal(O)^n
  $

  Thus objects over $chevron.l n chevron.r$ may be written as formal tuples
  $x_1 ⊕ dots ⊕ x_n$. The symbol $⊕$ here means
  concatenation of colors, not a coproduct in $cal(O)$.
]

Strictly speaking, this definition generalizes #emph[colored] operads. To
obtain the single-colored analogue, one additionally chooses an essentially
surjective functor $Delta^0->cal(O)$.

=== Multimorphism Spaces

Let $x_1,dots,x_n,y in cal(O)$ and let

$ mu_n:chevron.l n chevron.r->chevron.l 1 chevron.r $

be the active fold map. Using the Segal equivalence, choose the object
$x_1 ⊕ dots ⊕ x_n$ over $chevron.l n chevron.r$.

#definition(title:[Multimorphism Space])[
  The space of operations with inputs $x_1,dots,x_n$ and output $y$ is

  $
    Mul_cal(O) ({x_i}_(1<=i<=n);y)
    :=Map_(cal(O)^times.o)^(mu_n)
    (x_1 ⊕ dots ⊕ x_n,y)
  $
]

For $n=1$ this is the ordinary mapping space of the underlying
$oo$-category. In general, the three axioms above equip these spaces with
substitution maps which are associative up to coherent homotopy. This is the
precise higher-categorical replacement of a classical colored operad.

=== Fundamental Examples

#definition(title:[The Commutative $oo$-Operad])[
  The #emph[commutative $oo$-operad] is the identity functor

  $ Ner(Fin_*)->Ner(Fin_*) $

  regarded as an $oo$-operad. We denote it by

  $ Comm^times.o $
]

#remark(title:[Meaning of $Comm^times.o$])[
  Its underlying $oo$-category has a single color $x$. For every $n>=0$, the
  active fold $mu_n$ is the unique $n$-ary operation, so

  $
    Mul_Comm ({x}_(1<=i<=n);x)
    tilde.eq Delta^0
  $

  Thus $Comm^times.o$ is not itself a commutative algebra object. It is the
  #emph[theory] of commutative algebra objects: a map of $oo$-operads

  $ Comm^times.o->cal(C)^times.o $

  chooses an object of $cal(C)$ together with multiplication, unit, symmetry,
  and all higher coherences. Moreover, $Comm^times.o$ is terminal among
  $oo$-operads, since every $p:cal(O)^times.o->Ner(Fin_*)$ has a unique map to it,
  namely $p$ itself. A $Comm$-monoidal $oo$-category is therefore exactly a
  symmetric monoidal $oo$-category.
]

#definition(title:[The Trivial $oo$-Operad])[
  Let $cat("Triv") subset Fin_*$ be the subcategory containing every object
  and only the inert morphisms. The #emph[trivial $oo$-operad] is the
  inclusion

  $ Ner(cat("Triv"))->Ner(Fin_*) $

  We denote its source by

  $ cat("Triv")^times.o:=Ner(cat("Triv")) $
]

#remark(title:[Meaning of $cat("Triv")^times.o$])[
  This is the minimal one-colored $oo$-operad. If $x$ denotes its unique
  color, then

  $
    Mul_(cat("Triv")) ({x}_(1<=i<=n);x)
    tilde.eq cases(
      Delta^0 & "if " n=1,
      emptyset & "if " n!=1,
    )
  $

  Hence it contains the required unary identity but no constants and no
  genuine multi-input operations. A map

  $ cat("Triv")^times.o->cal(O)^times.o $

  is determined by the image of $x$, so it merely chooses a color of
  $cal(O)$. In particular, a $cat("Triv")$-algebra in a monoidal
  $oo$-category is just an object with no additional algebraic structure.
]

#remark(title:[The Two Extremes])[
  There is a canonical inclusion of $oo$-operads

  $ cat("Triv")^times.o->Comm^times.o $

  The source retains only the structural inert maps; the target supplies one
  operation in every arity. Restriction along this inclusion sends a
  commutative algebra object to its underlying object. Thus
  $cat("Triv")^times.o$ and $Comm^times.o$ have two extremal universal roles: the former
  remembers only an object, while the latter specifies one coherently
  commutative operation in every arity.
]

#proposition(title:[Classical Operads Give Discrete $oo$-Operads])[
  If $cal(O)$ is a classical colored operad, then

  $ Ner(cal(O)^times.o)->Ner(Fin_*) $

  is an $oo$-operad.
]

#proof[
  Inert maps lift by selecting the corresponding colors and decorating the
  lift with identity operations. The definition of morphisms in
  $cal(O)^times.o$ gives the product decomposition in condition (2), while the list
  $[x_1,dots,x_n]$ supplies condition (3). All operation spaces are discrete,
  so no additional homotopy coherence is introduced.
]

#definition(title:[Operadic Nerve])[
  Let $cal(O)$ be a simplicial colored operad and let $cal(O)^times.o$ be its
  simplicial category constructed above. Its #emph[operadic nerve] is the
  homotopy coherent nerve

  $ Ner^times.o (cal(O)):=Ner(cal(O)^times.o) $

  together with the canonical map

  $ Ner^times.o (cal(O))->Ner(Fin_*) $

  We call $cal(O)$ #emph[fibrant] if every simplicial set
  $Mul_cal(O) ({x_i}_(i in I);y)$ is a Kan complex.
]

#proposition(title:[Operadic Nerve Theorem])[
  If $cal(O)$ is a fibrant simplicial colored operad, then its operadic nerve
  $Ner^times.o(cal(O))$ is an $oo$-operad. Its underlying $oo$-category is the
  homotopy coherent nerve of the underlying simplicial category of colors.
]

#proof[
  The mapping simplicial sets of $cal(O)^times.o$ are coproducts of finite products
  of Kan complexes, hence are Kan. Its homotopy coherent nerve is therefore an
  $oo$-category. Inert lifts are induced by identity operations, the mapping
  space decomposition in condition (2) is already an isomorphism of
  simplicial sets, and the fiber over $chevron.l n chevron.r$ is the
  $n$-fold product of the fiber over $chevron.l 1 chevron.r$.
]

=== Reading the Definition: Objects and Operations

The definition becomes more transparent once we separate #emph[colors],
#emph[wiring], and #emph[operations]. The map

$ p:cal(O)^times.o->Ner(Fin_*) $

records only the arity and wiring of a construction; the fiberwise data record
the colors and the operations decorating that wiring.

#remark(title:[What Are the Objects?])[
  The genuine colors form the $oo$-category

  $ cal(O)=cal(O)^times.o_(chevron.l 1 chevron.r) $

  An object $x in cal(O)$ is therefore one color. More generally, the Segal
  equivalence identifies

  $
    cal(O)^times.o_(chevron.l n chevron.r)
    tilde.eq cal(O)^n
  $

  so an object over $chevron.l n chevron.r$ is merely a formal tuple
  $x_1 ⊕ dots ⊕ x_n$. It is not a tensor product and need not define an object
  of $cal(O)$. The inert maps $rho^i$ extract its entries. Their coCartesian
  lifts make this extraction canonical up to a contractible space of choices.
]

#remark(title:[What Are the Operations?])[
  A morphism of the underlying $oo$-category $cal(O)$ is only a #emph[unary]
  operation. An $n$-ary operation is instead a morphism in the total
  $oo$-category $cal(O)^times.o$ lying over the active fold map

  $ mu_n:chevron.l n chevron.r->chevron.l 1 chevron.r $

  Thus its space is

  $
    Mul_cal(O) ({x_i}_(1<=i<=n);y)
    =Map_(cal(O)^times.o)^(mu_n) (x_1 ⊕ dots ⊕ x_n,y)
  $

  A point of this space is an operation, a path is a homotopy between
  operations, and its higher simplices encode higher homotopies. This is the
  precise difference from a classical operad, whose operation spaces are
  discrete sets.
]

#remark(title:[How to Read a General Morphism])[
  Consider a morphism over

  $ f:chevron.l m chevron.r->chevron.l n chevron.r $

  from $x_1 ⊕ dots ⊕ x_m$ to $y_1 ⊕ dots ⊕ y_n$. The map $f$ is its wiring
  diagram. For each output $j$, the fiber $f^(-1)(j)$ specifies the inputs
  entering that output. Condition (2) says that the entire mapping space is

  $
    product_(j=1)^n
    Mul_cal(O) ({x_i}_(i in f^(-1)(j));y_j)
  $

  Consequently, a general morphism is exactly one operation for every output,
  performed in parallel. Inputs mapped to $ast$ are discarded. An empty fiber
  gives a nullary operation, hence a constant of the corresponding output
  color.
]

The three axioms can now be read as follows.

1. Inert lifts provide the structural operations which select and rearrange
   entries of a tuple
2. The mapping-space decomposition says that distinct outputs carry
   independent one-output operations
3. The existence axiom says that every finite tuple of colors is available

Finally, composition in the $oo$-category $cal(O)^times.o$ substitutes the output
operations of one wiring diagram into the input slots of the next. Because
this is composition in an $oo$-category, associativity, units, and all higher
compatibilities are supplied coherently rather than imposed by an infinite
list of equations. In short, an $oo$-operad is a system of colors and spaces
of many-input, one-output operations, together with coherently associative
substitution; the map to $Ner(Fin_*)$ is the device which keeps the combinatorics
of the inputs separate from the homotopy theory of the operations.

== Active–Inert Structure

=== Active and Inert Morphisms

#definition(title:[Active Morphism])[
  A pointed map

  $ f:chevron.l m chevron.r->chevron.l n chevron.r $

  in $Fin_*$ is #emph[active] if

  $ f^(-1)(ast)={ast} $

  Thus an active map uses every input. In contrast, an inert map selects
  exactly one input for every output and may discard the remaining inputs.
]

#figure(
  align(center, cetz.canvas(length: 0.90cm, {
    import cetz.draw: *

    let wire = 1.05pt + c-thm
    let discarded = (
      paint: c-rem,
      thickness: 0.9pt,
      dash: "dashed",
    )
    let divider = 0.7pt + rule-c
    let arrow = (
      end: ">",
      scale: 0.62,
      fill: c-thm,
      stroke: c-thm,
    )
    let discard-arrow = (
      end: ">",
      scale: 0.58,
      fill: c-rem,
      stroke: c-rem,
    )
    let input-node(p) = circle(
      p,
      radius: 0.085,
      fill: white,
      stroke: 1pt + c-thm,
    )
    let output-node(p) = circle(
      p,
      radius: 0.105,
      fill: c-thm.transparentize(82%),
      stroke: 1.1pt + c-thm,
    )
    let base-node(p) = circle(
      p,
      radius: 0.105,
      fill: c-rem,
      stroke: 1pt + c-rem,
    )

    // Inert: keep one input for each output and discard the rest.
    line((0.72, 3.20), (4.25, 2.85), stroke: wire, mark: arrow)
    line((0.72, 2.40), (4.25, 1.55), stroke: wire, mark: arrow)
    bezier(
      (0.72, 1.60), (4.25, 0.20),
      (2.10, 1.48), (3.15, 0.28),
      stroke: discarded,
      mark: discard-arrow,
    )
    bezier(
      (0.72, 0.80), (4.25, 0.20),
      (2.05, 0.68), (3.25, 0.24),
      stroke: discarded,
      mark: discard-arrow,
    )
    line((0.72, 0.20), (4.25, 0.20), stroke: discarded, mark: discard-arrow)

    for p in ((0.72, 3.20), (0.72, 2.40), (0.72, 1.60), (0.72, 0.80)) {
      input-node(p)
    }
    output-node((4.25, 2.85))
    output-node((4.25, 1.55))
    base-node((0.72, 0.20))
    base-node((4.25, 0.20))

    content((2.48, 5.05), text(size: 10pt, weight: "semibold", fill: ink)[inert])
    content((2.48, 4.55), text(size: 7.8pt, fill: muted)[select / forget])
    content((0.72, 3.88), text(size: 7.5pt, fill: muted)[inputs $chevron.l 4 chevron.r$])
    content((4.25, 3.88), text(size: 7.5pt, fill: muted)[outputs $chevron.l 2 chevron.r$])
    content((0.38, 3.20), text(size: 8pt, fill: muted)[$1$])
    content((0.38, 2.40), text(size: 8pt, fill: muted)[$2$])
    content((0.38, 1.60), text(size: 8pt, fill: muted)[$3$])
    content((0.38, 0.80), text(size: 8pt, fill: muted)[$4$])
    content((0.38, 0.20), text(size: 8pt, fill: c-rem)[$ast$])
    content((4.60, 2.85), text(size: 8pt, fill: muted)[$1$])
    content((4.60, 1.55), text(size: 8pt, fill: muted)[$2$])
    content((4.60, 0.20), text(size: 8pt, fill: c-rem)[$ast$])

    // Visual separator.
    line((5.55, -0.10), (5.55, 5.18), stroke: divider)

    // Active: no input is discarded; fibers group inputs at outputs.
    line((6.65, 3.20), (10.18, 2.85), stroke: wire, mark: arrow)
    line((6.65, 2.40), (10.18, 2.85), stroke: wire, mark: arrow)
    line((6.65, 1.60), (10.18, 1.15), stroke: wire, mark: arrow)
    line((6.65, 0.80), (10.18, 1.15), stroke: wire, mark: arrow)
    line((6.65, 0.20), (10.18, 0.20), stroke: discarded, mark: discard-arrow)

    for p in ((6.65, 3.20), (6.65, 2.40), (6.65, 1.60), (6.65, 0.80)) {
      input-node(p)
    }
    output-node((10.18, 2.85))
    output-node((10.18, 1.15))
    base-node((6.65, 0.20))
    base-node((10.18, 0.20))

    content((8.42, 5.05), text(size: 10pt, weight: "semibold", fill: ink)[active])
    content((8.42, 4.55), text(size: 7.8pt, fill: muted)[group / operate])
    content((6.65, 3.88), text(size: 7.5pt, fill: muted)[inputs $chevron.l 4 chevron.r$])
    content((10.18, 3.88), text(size: 7.5pt, fill: muted)[outputs $chevron.l 2 chevron.r$])
    content((6.31, 3.20), text(size: 8pt, fill: muted)[$1$])
    content((6.31, 2.40), text(size: 8pt, fill: muted)[$2$])
    content((6.31, 1.60), text(size: 8pt, fill: muted)[$3$])
    content((6.31, 0.80), text(size: 8pt, fill: muted)[$4$])
    content((6.31, 0.20), text(size: 8pt, fill: c-rem)[$ast$])
    content((10.55, 2.85), text(size: 8pt, fill: muted)[$1, phi_1$])
    content((10.55, 1.15), text(size: 8pt, fill: muted)[$2, phi_2$])
    content((10.55, 0.20), text(size: 8pt, fill: c-rem)[$ast$])
  })),
  caption: [An inert map selects one wire for every output and may discard the others. An active map sends no ordinary input to the basepoint and groups all inputs into output operations.],
)

#remark(title:[How to Read the Wires])[
  For a pointed map $f:chevron.l m chevron.r->chevron.l n chevron.r$, a wire
  ending at $j$ says that its input lies in $f^(-1)(j)$. These are precisely
  the inputs of the operation producing the $j$th output. A wire ending at
  $ast$ is unused.

  In the left panel,

  $ i(1)=1, quad i(2)=2, quad i(3)=i(4)=ast $

  so each output retains exactly one input. In the right panel,

  $ a(1)=a(2)=1, quad a(3)=a(4)=2 $

  so all inputs are used and the two fibers label the operations

  $
    phi_1 in Mul_cal(O) ({x_1,x_2};y_1),
    quad
    phi_2 in Mul_cal(O) ({x_3,x_4};y_2)
  $
]

#proposition(title:[Active–Inert Factorization])[
  Every morphism $f$ in $Fin_*$ factors, uniquely up to a unique isomorphism,
  as

  $ f=a compose i $

  where $i$ is inert and $a$ is active. Hence the inert and active morphisms
  form a factorization system on $Fin_*$.
]

#proof[
  Let $S subset.eq {1,dots,m}$ be the set of inputs not sent to $ast$, and
  choose an identification $S tilde.eq {1,dots,k}$. First define an inert map
  $i:chevron.l m chevron.r->chevron.l k chevron.r$ which keeps precisely the
  elements of $S$. The restriction of $f$ to $S$ then defines an active map
  $a:chevron.l k chevron.r->chevron.l n chevron.r$, and $f=a compose i$.
  Another choice differs only by a permutation of $chevron.l k chevron.r$.
  Finally, a square with inert left edge and active right edge has a unique
  filler: each output of the inert map has one specified preimage, while the
  active map discards none. This gives the factorization system.
]

The inert part performs bookkeeping: it selects, permutes, or forgets inputs.
The active part then groups the surviving inputs into genuine many-input
operations. This factorization lifts to every $oo$-operad.

#definition(title:[Active and Inert Morphisms in an $oo$-Operad])[
  Let $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad. A morphism $u$ of
  $cal(O)^times.o$ is

  - #emph[inert] if $p(u)$ is inert and $u$ is $p$-coCartesian

  - #emph[active] if $p(u)$ is active
]

#proposition(title:[Lifted Active–Inert Factorization])[
  The inert and active morphisms form a factorization system on
  $cal(O)^times.o$. In particular, every morphism factors, through a contractible
  space of choices, as an inert morphism followed by an active morphism.
]

#proof[
  Given $u:x->z$, factor its image as $p(u)=a compose i$. Choose the
  $p$-coCartesian lift $tilde(i):x->y$ supplied by the inert-lift axiom. The
  universal property of $tilde(i)$ produces a morphism $tilde(a):y->z$ over $a$
  and a homotopy

  $ u tilde.eq tilde(a) compose tilde(i) $

  The space of such choices is contractible. Orthogonality follows from the
  corresponding factorization system on $Fin_*$ and the mapping-space
  universal property of coCartesian morphisms.
]

Thus inert morphisms contain only structural bookkeeping, while active
morphisms contain the operadic operations and their composites.

== Maps of $oo$-Operads

#definition(title:[Map of $oo$-Operads])[
  A map from $p:cal(O)^times.o->Ner(Fin_*)$ to
  $q:cal(P)^times.o->Ner(Fin_*)$ is a functor

  $ F:cal(O)^times.o->cal(P)^times.o $

  such that $q compose F=p$ and $F$ preserves inert morphisms. We denote the
  $oo$-category of such maps by

  $ Alg_cal(O) (cal(P)) $

  where morphisms are natural transformations over $Ner(Fin_*)$, which can be viewed as a full subcategory of $Fun_(\/Ner(Fin_*)) (cal(O)^times.o,cal(P)^times.o)$.
]

Commuting with the projection means that $F$ preserves arities and wiring.
Preservation of inert morphisms means that it also respects the decomposition
of tuples into colors. Consequently, $F$ is precisely a map on colors together
with compatible maps on all multimorphism spaces which preserve identities
and operadic substitution.

#proposition(title:[Detecting Maps of $oo$-Operads])[
  Let $F:cal(O)^times.o->cal(P)^times.o$ be a functor over $Ner(Fin_*)$. It is enough to
  check that $F$ preserves inert morphisms lying over the elementary
  projections

  $ rho^i:chevron.l n chevron.r->chevron.l 1 chevron.r $

  If it does, then it preserves every inert morphism and hence is a map of
  $oo$-operads.
]

#proof[
  Under the Segal equivalences, an object over $chevron.l n chevron.r$ is
  determined by its $n$ projections. An inert morphism is likewise determined
  by the corresponding elementary projections and equivalences between their
  targets. Since the family ${rho^i}_(1<=i<=n)$ jointly detects these data,
  preservation of their coCartesian lifts implies preservation of every inert
  morphism.
]

=== The $oo$-Category of $oo$-Operads

Maps of $oo$-operads are closed under composition and contain all identity
maps. Together with their coherent homotopies, they therefore form an
$oo$-category.

#definition(title:[The $oo$-Category $Op_oo$])[
  Let $Op_oo^Delta$ be the simplicial category whose objects are small
  $oo$-operads $cal(O)^times.o->Ner(Fin_*)$ and whose mapping Kan complexes
  are

  $
    Map_(Op_oo^Delta) (cal(O),cal(P))
    :=Alg_cal(O) (cal(P))^(tilde.eq)
  $

  Here the right-hand side is the maximal Kan complex of
  $Alg_cal(O) (cal(P))$: its vertices are maps of $oo$-operads, and its paths
  are equivalences between such maps. Define

  $ Op_oo:=Ner(Op_oo^Delta) $

  and call it the #emph[$oo$-category of $oo$-operads].
]

The final section gives a marked-simplicial-set model for $Op_oo$. Besides
making the preceding construction concrete, that model proves that $Op_oo$
is presentable and therefore admits all small limits and colimits.

#remark(title:[Mapping Category versus Mapping Space])[
  The $oo$-category $Alg_cal(O) (cal(P))$ also contains noninvertible natural
  transformations between operad maps. The mapping object of $Op_oo$ must be
  a space, so only its maximal subgroupoid
  $Alg_cal(O) (cal(P))^(tilde.eq)$ appears in the definition of $Op_oo$.
]

#proposition(title:[Detecting Equivalences of $oo$-Operads])[
  A map $F:cal(O)^times.o->cal(P)^times.o$ is an equivalence in $Op_oo$ if and only if
  both of the following hold.

  1. The underlying functor on colors $cal(O)->cal(P)$ is essentially
     surjective

  2. For every $x_1,dots,x_n,y in cal(O)$, the induced map

     $
       Mul_cal(O) ({x_i}_(1<=i<=n);y)
       ->
       Mul_cal(P) ({F(x_i)}_(1<=i<=n);F(y))
     $

     is a homotopy equivalence
]

#proofsketch[
  The second condition is operadic full faithfulness. The Segal decomposition
  reconstructs every mapping space in $cal(O)^times.o$ from the multimorphism
  spaces and the wiring maps in $Fin_*$. The first condition gives essential
  surjectivity over $chevron.l 1 chevron.r$, and hence, by the Segal
  equivalence, over every $chevron.l n chevron.r$. Thus $F$ is an equivalence
  of the total $oo$-categories over $Ner(Fin_*)$. The converse follows by
  restricting such an equivalence to colors and to the fibers over the active
  fold maps.
]

#remark(title:[The Two Universal Examples])[
  The earlier examples have the following meaning inside $Op_oo$:

  $
    Map_(Op_oo) (cal(O),Comm) tilde.eq Delta^0,
    quad
    Map_(Op_oo) (cat("Triv"),cal(O)) tilde.eq cal(O)^(tilde.eq)
  $

  Hence $Comm^times.o$ is terminal in $Op_oo$, while a map out of
  $cat("Triv")^times.o$ is exactly the choice of a color, up to equivalence.
]

Let's recall the definition of an isofibration, which is a special kind of inner fibration.

#definition(title:[Isofibration])[
  A functor $F:cal(C)->cal(D)$ between $oo$-categories is an
  #emph[isofibration] if it is an inner fibration and equivalences lift: for
  every $x in cal(C)$ and every equivalence $u:F(x)->y$ in $cal(D)$, there is
  an object $tilde(y) in cal(C)$ and an equivalence
  $tilde(u):x->tilde(y)$ satisfying

  $ F(tilde(y))=y, quad F(tilde(u))=u $
]

#definition(title:[Fibration of $oo$-Operads])[
  A map of $oo$-operads

  $ F:cal(O)^times.o->cal(P)^times.o $

  is a #emph[fibration of $oo$-operads] if its underlying functor of
  $oo$-categories is an isofibration.
]

This notion allows colors and operations to vary in families. For an inner
fibration of $oo$-operads, it can be detected using only inert morphisms.

#proposition(title:[Detecting Fibrations of $oo$-Operads])[
  Let $F:cal(O)^times.o->cal(P)^times.o$ be a map of $oo$-operads which is an inner
  fibration. Then $F$ is a fibration of $oo$-operads if and only if every
  inert morphism $F(x)->y$ in $cal(P)^times.o$ admits an inert lift with source $x$.
  In this case, the inert morphisms of $cal(O)^times.o$ are exactly the
  $F$-coCartesian morphisms whose images in $cal(P)^times.o$ are inert.
]

#proof[
  Suppose first that inert morphisms admit inert lifts. Every equivalence in
  $cal(P)^times.o$ is inert, so an equivalence $F(x)->y$ lifts to an inert morphism
  over an isomorphism of pointed finite sets. Such a lift is itself an
  equivalence. Hence $F$ is an isofibration.

  Conversely, suppose that $F$ is an isofibration and let $u:F(x)->y$ be
  inert. First choose in $cal(O)^times.o$ an inert morphism $v:x->x'$ over the same
  pointed map as $u$. The morphisms $F(v)$ and $u$ are two coCartesian lifts
  of that pointed map, so their targets are related by an equivalence
  $e:F(x')->y$, together with a homotopy $u tilde.eq e compose F(v)$. Lift
  $e$ to an equivalence $tilde(e):x'->tilde(y)$ and use the inner-fibration
  property to lift the comparison $2$-simplex. The resulting composite
  $tilde(e) compose v$ is an inert lift of $u$. The same comparison shows that
  the inert morphisms in $cal(O)^times.o$ are precisely the $F$-coCartesian
  morphisms lying over inert morphisms.
]

=== $cal(O)$-Monoidal $oo$-Categories

#proposition(title:[Recognizing $cal(O)$-Monoidal Structures])[
  Let $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad and let

  $ q:cal(C)^times.o->cal(O)^times.o $

  be a coCartesian fibration. The following conditions are equivalent.

  1. The composite $p compose q$ exhibits $cal(C)^times.o$ as an $oo$-operad

  2. Whenever $x in cal(O)^times.o_(chevron.l n chevron.r)$ corresponds to
     $x_1 ⊕ dots ⊕ x_n$, the inert projections induce an equivalence

  $
    cal(C)_x
    tilde.eq product_(i=1)^n cal(C)_(x_i)
  $
]

#proof[
  Lift the inert projections $x->x_i$ coCartesianly along $q$. Since inert
  maps already satisfy the Segal equivalence in $cal(O)^times.o$, the Segal map for
  $cal(C)^times.o$ restricts over $x$ to

  $ cal(C)_x->product_(i=1)^n cal(C)_(x_i) $

  Hence the object part of the operadic Segal condition is precisely (2).
  The coCartesian mapping-space formula and the mapping-space decomposition in
  $cal(O)^times.o$ identify the corresponding morphism conditions. Thus the full
  $oo$-operad axioms for $p compose q$ are equivalent to the fiberwise product
  condition.
]

#definition(title:[$cal(O)$-Monoidal $oo$-Category])[
  When the equivalent conditions above hold, we say that $q$ exhibits
  $cal(C)^times.o$ as an #emph[$cal(O)$-monoidal $oo$-category].
]

This definition turns every operation of $cal(O)$ into an operation on the
corresponding fibers. More precisely, if

$ f in Mul_cal(O) ({x_i}_(1<=i<=n);y) $

then coCartesian transport along $f$ gives a functor, well-defined up to a
contractible space of choices,

$
  times.o_f:product_(i=1)^n cal(C)_(x_i)->cal(C)_y
$

Thus an $cal(O)$-monoidal category assigns a category of objects to every
color and a many-variable tensor functor to every operation. Operadic
substitution in $cal(O)$ becomes composition of these tensor functors, with
all higher compatibilities inherited from coCartesian transport.

#example(title:[Symmetric Monoidal $oo$-Categories])[
  Take the commutative $oo$-operad

  $ Comm^times.o=Ner(Fin_*) $

  A $Comm$-monoidal $oo$-category is exactly a symmetric monoidal
  $oo$-category

  $ p:cal(C)^times.o->Ner(Fin_*) $

  with

  $ cal(C)^times.o_(chevron.l n chevron.r) tilde.eq cal(C)^n $

  CoCartesian transport along the active maps

  $
    chevron.l 0 chevron.r->chevron.l 1 chevron.r,
    quad
    mu_2:chevron.l 2 chevron.r->chevron.l 1 chevron.r
  $

  produces respectively the unit object and the tensor product

  $ 1 in cal(C), quad times.o:cal(C) times cal(C)->cal(C) $

  The maps $mu_n$ produce the $n$-fold tensor products, while permutations in
  $Fin_*$ supply symmetry. Functoriality and coCartesian transport encode the
  associativity, unit, symmetry, and all of their higher coherences.
]

#remark(title:[Symmetric Monoidal Means coCartesian])[
  Equivalently, a symmetric monoidal $oo$-category is an $oo$-operad

  $ p:cal(C)^times.o->Ner(Fin_*) $

  whose structure map $p$ is a coCartesian fibration. An arbitrary
  $oo$-operad supplies coCartesian lifts only for inert maps; requiring $p$ to
  be coCartesian supplies them for #emph[every] pointed map, in particular for
  the active fold maps which define tensor products. The base $Fin_*$ also
  contains all permutations, so their coCartesian transport provides the
  symmetry. Thus “symmetric” is encoded by the coCartesian operad over
  $Ner(Fin_*)$, rather than by adding a braiding separately.
]

== Algebra Objects

#quote[$cal(O)^times.o$-algebra $=$ a realization in $cal(C)^times.o$ of the operations
and laws prescribed by $cal(O)^times.o$.]

Here $cal(O)^times.o$ is the #emph[syntax]: its colors specify the types of objects,
its multimorphism spaces specify the available operations, and operadic
substitution specifies how those operations must compose. The monoidal
$oo$-category $cal(C)^times.o$ is the #emph[semantic environment] in which
this syntax is interpreted. Concretely, a map of $oo$-operads sends every
color $x$ to an object $a(x)$ and every operation

$ f in Mul_cal(O) ({x_i}_(1<=i<=n);y) $

to a morphism

$ a(f):a(x_1) times.o dots times.o a(x_n)->a(y) $

Preservation of inert morphisms respects the input slots, while preservation
of composition says that substitution in $cal(O)$ becomes composition in
$cal(C)^times.o$. Thus all the equations prescribed by $cal(O)$ hold in
$cal(C)$, coherently rather than merely on the nose.

=== Algebra Objects as Operadic Lifts

#definition(title:[Relative Algebra Objects])[
  Let

  $ p:cal(C)^times.o->cal(O)^times.o $

  be a fibration of $oo$-operads, and let
  $alpha:cal(P)^times.o->cal(O)^times.o$ be a map of $oo$-operads. A
  #emph[$cal(P)$-algebra object of $cal(C)$ relative to $cal(O)$] is a map of
  $oo$-operads $a:cal(P)^times.o->cal(C)^times.o$ such that

  $ p compose a=alpha $

  The full subcategory of
  $Fun_(cal(O)^times.o) (cal(P)^times.o,cal(C)^times.o)$ spanned by these maps is denoted by

  $ Alg_(cal(P)\/cal(O)) (cal(C)) $

  When $cal(P)=cal(O)$ and $alpha=id$, we abbreviate this to
  $Alg_cal(O) (cal(C))$. When the structural map $alpha$ is understood, we
  also omit the base $cal(O)$ from the subscript.
]

Thus an algebra object is a lift of the operadic theory $cal(P)^times.o$ through
$p$. Preservation of inert morphisms fixes the underlying tuple of objects;
the images of active morphisms supply the actual operations. Functoriality
then encodes their unit, substitution, and all higher coherence laws.

#example(title:[Commutative Algebra Objects])[
  If $cal(C)^times.o->Comm^times.o$ is symmetric monoidal, define

  $ cat("CAlg")(cal(C)):=Alg_Comm (cal(C)) $

  An object $c in cat("CAlg")(cal(C))$ consists of an underlying object of
  $cal(C)$ together with coherent operations

  $ 1->c, quad c^(times.o n)->c quad (n>=1) $

  invariant under permutations and compatible with substitution. If
  $cal(C)$ is an ordinary symmetric monoidal category, its operadic nerve
  recovers the nerve of the ordinary category of commutative algebra objects
  in $cal(C)$.
]

=== Three Basic Operads

#proposition(title:[The Trivial Operad Classifies Objects])[
  Let $cal(C)^times.o->Comm^times.o$ be a symmetric monoidal $oo$-category, and use the
  canonical inclusion $cat("Triv")^times.o->Comm^times.o$. Evaluation at the unique color
  induces an equivalence

    $ Alg_(cat("Triv")\/Comm) (cal(C)) tilde.eq cal(C) $
]

#proof[
  The operad $cat("Triv")^times.o$ contains only the inert bookkeeping maps and the
  unary identity. Hence a map
  $cat("Triv")^times.o->cal(C)^times.o$ is determined by the image $c$ of its unique color.
  All required inert lifts are then forced, up to a contractible space of
  choices, by the coCartesian structure of $cal(C)^times.o$.
]

#definition(title:[The $EE_0$-Operad])[
  Let $Fin_*^"inj"$ be the subcategory of $Fin_*$ containing every object and
  those pointed maps $f:chevron.l m chevron.r->chevron.l n chevron.r$ for
  which each nonbasepoint of the target has at most one preimage. Define

  $ EE_0^times.o:=Ner(Fin_*^"inj")->Ner(Fin_*) $
]

#remark(title:[$EE_0^times.o$ Contains More Than the Inert Maps])[
  An inert map requires every nonbasepoint of the target to have
  #emph[exactly one] preimage. The defining condition for $EE_0^times.o$ is weaker:
  every such fiber has cardinality at most one, and may therefore be empty.
  Thus $cat("Triv")^times.o$ contains the maps which only select and rearrange
  inputs, whereas $EE_0^times.o$ additionally allows an output to receive no input.
  Such an empty fiber represents a nullary operation, which becomes the unit
  map $1->c$ in an $EE_0$-algebra.
]

The only active operations of $EE_0^times.o$ have arity zero or one. The nullary
operation is a constant, hence becomes a unit map, while the unary operation
is the identity. Consequently there are inclusions

$ cat("Triv")^times.o->EE_0^times.o->Comm^times.o $

and restriction gives forgetful functors

$ cat("CAlg")(cal(C))->Alg_(EE_0) (cal(C))->cal(C) $

#proposition(title:[$EE_0$-Algebras Are Pointed Objects])[
  Let $cal(C)^times.o$ be a symmetric monoidal $oo$-category with unit $1$. Then
  $Alg_(EE_0) (cal(C))$ is equivalent to the $oo$-category whose objects are
  pairs

  $ (c,eta:1->c) $

  In particular, an $EE_0$-algebra is a unital object with no multiplication.
]

#proof[
  The active map
  $chevron.l 0 chevron.r->chevron.l 1 chevron.r$ supplies $eta:1->c$, and
  $EE_0^times.o$ has no active operations of arity at least two. The Segal condition
  forces all remaining values from $c$, while the inert maps carry no further
  algebraic choices. Thus restriction to the nullary operation and the unique
  color is fully faithful and essentially surjective.
]

#remark(title:[A Useful Hierarchy])[
  The three operads isolate three successive amounts of structure:

  $
    cat("Triv") &: "an object" \
    EE_0 &: "a map " 1->c \
    Comm &: "a coherently commutative unital multiplication on " c
  $

  This is why forgetting a commutative multiplication naturally passes first
  through its underlying pointed object and then through its underlying
  object.
]

=== Pointwise Algebra Objects

#proposition(title:[Algebras in Functor Categories])[
  Let $cal(C)^times.o->cal(O)^times.o$ be an $cal(O)$-monoidal $oo$-category and let $k$ be
  a simplicial set. Set

  $
    cal(D)^times.o
    :=Fun(k,cal(C)^times.o)
      times_(Fun(k,cal(O)^times.o)) cal(O)^times.o
  $

  where $cal(O)^times.o->Fun(k,cal(O)^times.o)$ sends an object to the corresponding
  constant diagram. Then $cal(D)^times.o->cal(O)^times.o$ is $cal(O)$-monoidal, its fiber
  at $x in cal(O)$ is

  $ cal(D)_x tilde.eq Fun(k,cal(C)_x) $

  and every operadic operation is computed pointwise. Consequently,

  $ Alg_cal(O) (cal(D)) tilde.eq Fun(k,Alg_cal(O) (cal(C))) $
]

#proof[
  CoCartesian transport in a functor category is detected pointwise. Hence
  the Segal product decomposition and every tensor operation in $cal(D)^times.o$
  are obtained by applying the corresponding construction in $cal(C)^times.o$ at
  each vertex of $k$. A section of $cal(D)^times.o$ preserving inert morphisms is
  therefore exactly a $k$-diagram of such sections of $cal(C)^times.o$.
]

=== Monoidal Functors

#definition(title:[$cal(O)$-Monoidal Functor])[
  Let $p:cal(C)^times.o->cal(O)^times.o$ and $q:cal(D)^times.o->cal(O)^times.o$ be
  $cal(O)$-monoidal $oo$-categories. An #emph[$cal(O)$-monoidal functor] is a
  functor

  $ F:cal(C)^times.o->cal(D)^times.o $

  over $cal(O)^times.o$ which carries $p$-coCartesian morphisms to
  $q$-coCartesian morphisms. When $cal(O)=Comm$, this is a symmetric monoidal
  functor.

  The $oo$-category of such functors is denoted by

  $ Fun_cal(O)^times.o (cal(C),cal(D)) $
]

Equivalently, $F$ consists of functors $F_x:cal(C)_x->cal(D)_x$ for the
colors $x$ of $cal(O)$, together with coherent equivalences

$ F_y (times.o_f (c_1,dots,c_n)) tilde.eq times.o_f (F_(x_1)(c_1),dots,F_(x_n)(c_n)) $

for every operation $f in Mul_cal(O) ({x_i}_(1<=i<=n);y)$.

#proposition(title:[Fiberwise Equivalence Criterion])[
  An $cal(O)$-monoidal functor $F:cal(C)^times.o->cal(D)^times.o$ is an equivalence if and
  only if, for every color $x in cal(O)$, the induced functor

  $ F_x:cal(C)_x->cal(D)_x $

  is an equivalence. In the one-colored case, it is therefore enough to test
  the underlying functor $cal(C)->cal(D)$.
]

#proof[
  The Segal equivalence identifies the fiber over a tuple
  $x_1 ⊕ dots ⊕ x_n$ with the product of the fibers over its entries. Thus
  equivalence on all color fibers implies equivalence on every fiber of
  $cal(O)^times.o$. Since $F$ preserves coCartesian transport, it is a natural
  transformation between the diagrams classified by the two coCartesian
  fibrations, and such a transformation is an equivalence exactly when it is
  pointwise an equivalence.
]

#remark[
  The monoidal hypothesis is essential: an arbitrary map of $oo$-operads can
  agree on the underlying unary $oo$-categories while differing on genuine
  multi-input operations.
]

== $oo$-Preoperads

The definition of an $oo$-operad is intrinsic but not especially convenient
for constructing limits, colimits, or derived mapping spaces. Marked
simplicial sets provide a model in which the inert morphisms are recorded as
part of the object.

=== Marked Simplicial Sets

#definition(title:[Marked Simplicial Set])[
  A #emph[marked simplicial set] is a pair $overline(x)=(x,M)$, where $x$ is a
  simplicial set and $M$ is a collection of edges containing every degenerate
  edge. We write $x^flat$ when only the degenerate edges are marked and
  $x^sharp$ when every edge is marked.
]

#definition(title:[$oo$-Preoperad])[
  An #emph[$oo$-preoperad] is a marked simplicial set $overline(x)=(x,M)$ equipped
  with a map

  $ r:x->Ner(Fin_*) $

  such that $r(e)$ is inert whenever $e in M$. A morphism of
  $oo$-preoperads is a map over $Ner(Fin_*)$ which preserves marked edges. We
  denote their category by $POp_oo$.
]

Equivalently, $POp_oo$ is the overcategory of marked simplicial sets over
$Ner(Fin_*)$ with all inert edges marked. Cartesian product with $k^sharp$
for a simplicial set $k$ tensors this category over simplicial sets and gives
the simplicial mapping objects $Map_(POp_oo)(overline(x),overline(y))$.

#definition(title:[Marked Operad Notation])[
  If $p:cal(O)^times.o->Ner(Fin_*)$ is an $oo$-operad, write

  $ cal(O)^(times.o,natural) $

  for the corresponding $oo$-preoperad in which precisely the inert
  morphisms are marked.
]

Thus a preoperad is only raw marked data over $Ner(Fin_*)$; the operadic horn
filling and Segal conditions will instead appear as fibrancy conditions.

=== The Operadic Model Structure

#theorem(title:[$oo$-Operadic Model Structure])[
  The category $POp_oo$ admits a left proper combinatorial simplicial model
  structure characterized by the following properties.

  1. A map $overline(x)->overline(y)$ is a cofibration if and only if the underlying
     map $x->y$ is a monomorphism

  2. It is a weak equivalence if and only if, for every $oo$-operad
     $cal(O)^times.o$, the induced map

     $
       Map_(POp_oo)(overline(y),cal(O)^(times.o,natural))
       ->Map_(POp_oo)(overline(x),cal(O)^(times.o,natural))
     $

     is a weak homotopy equivalence

  3. The fibrant objects are precisely the marked operads
     $cal(O)^(times.o,natural)$. A map between fibrant objects is a fibration
     exactly when its underlying map is a fibration of $oo$-operads
]

#proofsketch[
  Start with marked simplicial sets over $Ner(Fin_*)$ and localize so that the
  lifting conditions force inert coCartesian lifts, the decomposition of
  multimorphism spaces, and the Segal equivalences. The resulting fibrant
  objects satisfy exactly the three axioms of an $oo$-operad. The weak
  equivalences are then detected by enriched mapping spaces into these
  fibrant objects. General localization results for combinatorial simplicial
  model categories give existence and left properness.
]

#corollary(title:[A Presentation of $Op_oo$])[
  The simplicial localization of $POp_oo$ at the operadic weak equivalences is
  equivalent to $Op_oo$. Consequently, $Op_oo$ is presentable and admits all
  small limits and colimits.
]

#proofsketch[
  Every preoperad is cofibrant, since the map from the initial object is a
  monomorphism. After fibrant replacement, the enriched mapping Kan complex
  from $cal(O)^(times.o,natural)$ to $cal(P)^(times.o,natural)$ is precisely
  $Alg_cal(O)(cal(P))^(tilde.eq)$. These are the mapping spaces used to define
  $Op_oo$. Presentability follows from the combinatorial model, and small
  limits and colimits follow from presentability.
]

=== Small Models and Unary Operads

#remark(title:[Small Models for $cat("Triv")$ and $EE_0$])[
  There are operadic weak equivalences

  $
    {chevron.l 1 chevron.r}^flat
      ->cat("Triv")^(times.o,natural),
    quad
    (Delta^1)^flat->EE_0^(times.o,natural)
  $

  where the edge of $Delta^1$ in the second map represents the active map
  $chevron.l 0 chevron.r->chevron.l 1 chevron.r$. Thus, up to operadic weak
  equivalence, $cat("Triv")$ is generated by one color and $EE_0$ by one
  nullary operation, or equivalently one unit arrow.
]

#proposition(title:[$oo$-Categories as Unary $oo$-Operads])[
  There is a fully faithful functor

  $ Cat_oo->Op_oo $

  which regards an $oo$-category as an $oo$-operad having only unary
  operations. Its essential image consists precisely of those
  $p:cal(O)^times.o->Ner(Fin_*)$ which factor through
  $cat("Triv")^times.o$.
]

#proofsketch[
  If an operad factors through $cat("Triv")^times.o$, it has no nullary or
  genuinely multi-input operations. It is therefore determined by its fiber
  over $chevron.l 1 chevron.r$ and the unary composition there. Maps between
  such operads are exactly functors between these underlying
  $oo$-categories, which proves full faithfulness.
]

#remark(title:[Symmetric Monoidal $oo$-Categories inside $Op_oo$])[
  Symmetric monoidal $oo$-categories and symmetric monoidal functors form a
  subcategory

  $ Cat_oo^times.o subset Op_oo $

  Its objects are those $oo$-operads
  $cal(C)^times.o->Ner(Fin_*)$ whose projection is a coCartesian fibration,
  and its morphisms are the operad maps which preserve the corresponding
  coCartesian morphisms. This subcategory is not full: an arbitrary operad
  map need not be symmetric monoidal.
]

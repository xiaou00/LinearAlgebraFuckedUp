#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Stable $oo$-Categories

== The Motivation of the Subject

Ordinary category theory remembers a #emph[set] of maps between two objects. This is
often enough in classical algebra, but it is too small for homotopy theory and
derived mathematics. There, two maps may be connected by a homotopy, two
homotopies may themselves be homotopic, and these higher relations affect later
constructions. Higher Algebra keeps this information instead of collapsing it.

#emph[Localization.] When quasi-isomorphisms or weak equivalences are inverted, an
ordinary localization remembers only homotopy classes of maps. An
$oo$-categorical localization retains the whole mapping space. Its truncation is

$ Hom_(h C) (x,y) = pi_0 Map_C (x,y) $

Thus the ordinary derived category is useful, but it is only a shadow of the
enhanced object.

#emph[Coherence.] “Associative up to homotopy” is not enough by itself. The chosen
homotopies must agree with one another, their agreements must also agree, and so
on. $AA_oo$- and $EE_n$-algebras, encoded by $oo$-operads, package this infinite
system of compatibility conditions.

#emph[Stability.] Stable $oo$-categories provide functorial fibers, cofibers, shifts,
and mapping spectra. They unify derived categories and spectra while retaining
the information that a triangulated homotopy category forgets.

#remark(title: "Worldview")[
  Higher Algebra replaces “unique by equality” with “a contractible space of
  coherent choices.” Its guiding principle is simple: keep enough structure so
  that the next construction is invariant, functorial, and composable.
]

In short, $oo$-categories retain higher morphisms, stable $oo$-categories handle
derived and exact phenomena, and $oo$-operads describe algebraic operations up
to every required coherence. These tools are used because the mathematics is
already higher, not because abstraction is an end in itself.

== First Definitions: Stability

=== Pointed $oo$-Categories

#definition(title:[Zero Object, Pointed $oo$-Category])[
  Let $C$ be an $oo$-category, a #emph[zero object] is an object which is both initial and terminal. We will say that $C$ is #emph[pointed] if it admits a zero object. In this case, we will denote the zero object by $0 in C$.
]

Obviously, if $C$ is pointed, then the zero object is unique up to a contractible space of choices. The condition is equals to:

#proposition[
  Let $C$ be an $oo$-category, $C$ is pointed iff:

  1. $C$ admits initial and terminal objects $0,1$.
  2. Exists $0->1$.
]

=== Triangle, Fiber and Cofiber

#definition(title:[Triangle, (co)Fiber Sequence])[
  Let $C$ be a pointed $oo$-category, a #emph[triangle] in $C$ is a diagram $Delta^1 times Delta^1 -> C$ depicted as
  #align(center, diagram({
	node((-1, -1), [$x$])
	node((0, -1), [$y$])
	node((0, 0), [$z$])
	node((-1, 0), [$0$])
	edge((-1, -1), (-1, 0), "->")
	edge((-1, -1), (0, -1), [$f$], label-side: left, "->")
	edge((0, -1), (0, 0), [$g$], label-side: left, "->")
	edge((-1, 0), (0, 0), "->")
  }))
  where $0$ is the zero object. We say that a triangle in $C$ is a #emph[fiber sequence] if it is a pullback square, and a #emph[cofiber sequence] if it is a pushout square.
]

A triangle is basically a composite of two maps
$ x -->^f y -->^g z, quad g f tilde.eq 0 $

if this triangle is a pullback, then $x tilde.eq y times_z 0$, where $y times_z 0$ is exactly the fiber of $g$, hence $x tilde.eq fib(g)$. Similarly, if this triangle is a pushout, then $z tilde.eq y coprod_x 0$, where $y coprod_x 0$ is exactly the cofiber of $f$, hence $z tilde.eq cofib(f)$.

#remark[
  Let $C$ be a pointed $oo$-category, a triangle in $C$ consists of the following data:

  1. A pair of morphisms $f:x->y$ and $g:y->z$ in $C$.
  2. A 2-simplex in $C$ corresponding to a diagram
  $ simplex2(x,y,z,ab:f,bc:g,ac:h) $
  in $C$, which witnesses $h$ as a composite of $f$ and $g$.
  3. A 2-simplex in $C$ corresponding to a diagram
  $ simplex2(x,0,z,ab:0,bc:0,ac:h) $
  in $C$, which may view as a nullhomotopy of $h$.
]

By the notion of triangle, we can define the notion of fiber and cofiber in a pointed $oo$-category.

#definition(title:[(co)Fiber])[
  Let $C$ be a pointed $oo$-category containing a morphism $g:x->y$, a #emph[fiber] of $g$ is a fiber sequence
  #align(center, diagram({
	node((-1, 0), [$w$])
	node((0, 0), [$x$])
	node((0, 1), [$y$])
	node((-1, 1), [$0$])
	edge((-1, 0), (-1, 1), "->")
	edge((-1, 1), (0, 1), "->")
	edge((-1, 0), (0, 0), "->")
	edge((0, 0), (0, 1), [$g$], label-side: left, "->")
  }))
  Dually, a #emph[cofiber] of $g$ is a cofiber sequence
  #align(center, diagram({
	node((-1, 0), [$x$])
	node((0, 0), [$y$])
	node((0, 1), [$z$])
	node((-1, 1), [$0$])
	edge((-1, 1), (0, 1), "->")
	edge((-1, 0), (0, 0), [$g$], label-side: left, "->")
	edge((0, 0), (0, 1), "->")
	edge((-1, 0), (-1, 1), "->")
  }))
  We write $w=fib(g)$ and $z=cofib(g)$.
]

#proposition[
  Fix a pointed $oo$-category $C$ and a morphism $f:x->y$, if a cofiber of $f$ exists, then it is unique up to an equivalence. Precisely, consider the full subcategory
  $ E subset Fun(Delta^1 times Delta^1,C) $
  spanned by the cofiber sequences, let $theta:E->Fun(Delta^1,C)$ be the forgetful functor, which send a diagram
  #align(center, diagram({
	node((0, 0), [$x$])
	node((1, 0), [$y$])
	node((0, 1), [$0$])
	node((1, 1), [$z$])
	edge((0, 0), (1, 0), [$g$], label-side: left, "->")
	edge((1, 0), (1, 1), "->")
	edge((0, 0), (0, 1), "->")
	edge((0, 1), (1, 1), "->")
  }))
  to the morphism $g:x->y$. Then $theta$ is a Kan fibration. If every morphism in $C$ admits a cofiber, then $theta$ is a trivial Kan fibration.
]

#proposition[
  The functor
  $ cofib : Fun(Delta^1,C) -> C $
  is the left adjoint of the follwing functor: 
  $ C tilde.eq Fun(Delta^0,C) -> Fun(Delta^1,C) $
  by sending every object $x$ to the morphism $0->x$. Hence $cofib$ preserves colimits.
]

=== Stability

#definition(title:[Stable $oo$-Category])[
  An $oo$-category $C$ is #emph[stable] if it satisfies the following conditions:

  1. $C$ is pointed.
  2. Every morphism in $C$ admits a fiber and a cofiber.
3. A triangle in $C$ is a fiber sequence if and only if it is a cofiber sequence.
]

#proposition[
  If $C$ is a stable $oo$-category, then $C^op$ is also stable.
]

=== Closure Properties

#proposition[
  Let $C$ be a stable $oo$-category and $k$ a simplicial set. Then the $oo$-category $Fun(k,C)$ is stable.
]

#proposition[
  Let $C$ be a small stable $oo$-category, and let $kappa$ be a regular cardinal, then the $oo$-category $"Ind"_kappa (C)$ is stable.
]

== Homotopy Category of a Stable $oo$-Category

=== Intro

Let $m$ be a module over a commutative ring $R$. It admits a resolution
$ ... -> p_2 -> p_1 -> p_0 -> m -> 0 $
by projective $R$-modules $p_i$. There are generally many different choices, but they are always #emph[quasi-isomorphic] to each other: that is, a chain map between two resolutions that induces a isomorphism on homology. It's often convenient to work in the #emph[derived category] $"D"(R)$ of the ring $R$, the category obtained from the category of chain complexes of $R$-modules by formally inverting quasi-isomorphisms.

The derived category $"D"(R)$ of a commutative ring $R$ is usually not an abelian category. A morphism $f:x'->x$ in $"D"(R)$ usually does not have a kernel in $"D"(R)$. Instead, one can associate to $f$ its cofiber (#emph[mapping cone]) $x''$, which is well-defined up to noncanonical isomorphism.

Verdier introduced the notion of a #emph[triangulated category] to axiomatize the properties of the derived category by formating the mapping cones, we will soon review the theory of triangulated categories and then show that the homotopy category of a stable $oo$-category is triangulated.

=== Basic Homological Algebra

#definition(title:[Additive Category, Abelian Category])[
  Let $A$ be a category, we say that $A$ is #emph[additive] if it satisfies the following conditions:

  1. $A$ admits a zero object $0$.
  2. $A$ admits finite products and coproducts.
  
  For every pair of objects $x,y in A$, a #emph[zero morphism] is a map factors through $x->0->y$. It is unique, and denoted by $0$.

  3. For every pair $x,y$ the map $x coprod y -> x times y$ described by
    $ mat(id_x, 0; 0, id_y) $
    is an isomorphism, and denote the inverse by $phi_(x,y)$.

  We can now define the #emph[sum] of two morphisms $f,g:x->y$ to be the morphism $f+g:x->y$ by the composition
  $ x -->^(Delta_x) x times x -->^(f times g) y times y -->^(phi_(y,y)) y coprod y -->^(nabla_y) y $
  where $Delta_x$ is the diagonal map and $nabla_y$ is the codiagonal map. This construction makes $Hom_A (x,y)$ into a commutative monoid with identity $0$.

  4. For every $x,y$ the commutative monoid $Hom_A (x,y)$ is an abelian group. i.e. every morphism $f:x->y$ admits an additive inverse $-f:x->y$ such that $f+(-f)=0$.

  An additive category $A$ is #emph[abelian], if every morphism admits a kernel and a cokernel, and every monomorphism is a kernel of its cokernel, and the canonical map
  $ coker(ker(f)->x) -> ker(y->coker(f)) $
  is an isomorphism for every morphism $f:x->y$ in $A$.
]

#definition(title:[Triangulated Category])[
  A #emph[triangulated category] consists of the following data:

  1. An additive category $A$.
  2. A translation functor $A->A$ which is an equivalence of categories, by $x mapsto x[1]$.
  3. A collection of #emph[distinguished triangles]
    $ x -->^f y -->^g z -->^h x[1] $

  These data are required to satisfy the following axioms:

  1. Every morphism $f:x->y$ in $A$ can be extended to distinguished triangle in $A$.
  2. The collection of distinguished triangles is stable under isomorphisms.
  3. Given an object $x in A$, the diagram
    $ x -->^(id_x) x --> 0 --> x[1] $
    is a distinguished triangle.
  4. A diagram
    $ x -->^f y -->^g z -->^h x[1] $
    is a distinguished triangle if and only if the diagram
    $ y -->^g z -->^h x[1] -->^(-f[1]) y[1] $
    is a distinguished triangle.
  5. Given a commutative diagram
    #align(center, diagram({
      node((-1, 0), [$x$])
      node((0, 0), [$y$])
      node((1, 0), [$z$])
      node((2, 0), [$x[1]$])
      node((-1, 1), [$x'$])
      node((0, 1), [$y'$])
      node((1, 1), [$z'$])
      node((2, 1), [$x'[1]$])
      edge((2, 0), (2, 1), [$f[1]$], label-side: left, "->")
      edge((-1, 0), (-1, 1), [$f$], label-side: right, "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((-1, 1), (0, 1), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((0, 0), (0, 1), "->")
      edge((1, 0), (1, 1), "-->")
    }))
    where the rows are distinguished triangles, then there exists a morphism $z->z'$ making the whole diagram commutative.
  6. (#emph[Octahedral Axiom]) uppose given three distinguished triangles
    $ x -->^f y -->^u y\/x -->^d x[1], quad y -->^g z -->^v z\/y -->^(d') y[1], quad x -->^(g compose f) z -->^w z\/x -->^(d''')x[1] $
    in $A$, there exists a fourth distinguished triangle
    $ y\/x -->^phi z\/x -->^psi z\/y -->^theta y\/x[1] $
    such that the diagram
    #align(center, diagram({
      node((-3, -2), [$x$])
      node((-1, -3), [$z$])
      node((1, 0), [$z\/y$])
      node((-3, 0), [$y$])
      node((1, -2), [$z\/x$])
      node((-1, 1), [$y\/x$])
      edge((-3, -2), (-1, -3), text(color.hsl(0deg, 153, 110))[$g compose f$], label-side: left, "->", stroke: color.hsl(0deg, 153, 110))
      edge((-1, -3), (1, 0), text(color.hsl(120deg, 153, 82))[$v$], label-side: right, "->", stroke: color.hsl(120deg, 153, 82))
      edge((-3, -2), (-3, 0), text(color.hsl(240deg, 153, 153))[$f$], label-side: right, "->", stroke: color.hsl(240deg, 153, 153))
      edge((-3, 0), (-1, -3), text(color.hsl(120deg, 153, 82))[$g$], label-side: right, "->", stroke: color.hsl(120deg, 153, 82))
      edge((-1, -3), (1, -2), text(color.hsl(0deg, 153, 110))[$w$], label-side: left, "->", stroke: color.hsl(0deg, 153, 110))
      edge((1, -2), (1, 0), [$psi$], label-side: left, "->")
      edge((-3, 0), (-1, 1), text(color.hsl(240deg, 153, 153))[$u$], label-side: right, "->", stroke: color.hsl(240deg, 153, 153))
      edge((-1, 1), (1, -2), [$phi$], label-side: left, "->")
      edge((-1, 1), (-3, -2), text(color.hsl(240deg, 153, 153))[$d, +1$], label-side: right, "->", stroke: color.hsl(240deg, 153, 153))
      edge((1, -2), (-3, -2), text(color.hsl(0deg, 153, 110))[$d'', +1$], label-side: left, "->", stroke: color.hsl(0deg, 153, 110))
      edge((1, 0), (-3, 0), text(color.hsl(120deg, 153, 82))[$d', +1$], label-side: right, "->", stroke: color.hsl(120deg, 153, 82))
      edge((1, 0), (-1, 1), [$theta, +1$], label-side: left, "->")
    }))
    commutes.
]

=== Homotopy Category of a Stable $oo$-Category

Let $C$ be a stable $oo$-category. The entire construction rests on two facts:
pushout squares are pullback squares, and the space of choices of a limit or
colimit is contractible. The first produces the usual homological operations;
the second makes them coherent.

==== Suspension and Additivity

#definition(title:[Suspension and Loop Objects])[
  For $x in C$, define $Sigma x$ and $Omega x$ by a pushout square and a
  pullback square, respectively:

  #align(center, grid(
    columns: (auto, 42pt, auto),
    align: center + horizon,
    diagram({
      node((0, 0), [$x$])
      node((1.2, 0), [$0$])
      node((0, 1.2), [$0$])
      node((1.2, 1.2), [$Sigma x$])
      edge((0, 0), (1.2, 0), "->")
      edge((0, 0), (0, 1.2), "->")
      edge((1.2, 0), (1.2, 1.2), "->")
      edge((0, 1.2), (1.2, 1.2), "->")
    }),
    [],
    diagram({
      node((0, 0), [$Omega x$])
      node((1.2, 0), [$0$])
      node((0, 1.2), [$0$])
      node((1.2, 1.2), [$x$])
      edge((0, 0), (1.2, 0), "->")
      edge((0, 0), (0, 1.2), "->")
      edge((1.2, 0), (1.2, 1.2), "->")
      edge((0, 1.2), (1.2, 1.2), "->")
    }),
  ))

  The left square is a pushout and the right square is a pullback. We write
  $x[1]=Sigma x$ and $x[-1]=Omega x$
]

#proposition(title:[Suspension Is an Equivalence])[
  The functors $Sigma,Omega:C->C$ are inverse equivalences. Hence
  $[1]:h C->h C$ is an equivalence.
]

#proof[
  The square defining $Sigma x$ is also a pullback, so
  $Omega Sigma x tilde.eq x$. Dually, $Sigma Omega x tilde.eq x$. These
  equivalences are natural because the relevant spaces of choices are
  contractible.
]

#proposition(title:[Additivity of the Homotopy Category])[
  The homotopy category $h C$ is additive.
]

#proof[
  The zero map points every $Map_C (x,y)$, and suspension gives

  $ Map_C (Sigma x,y) tilde.eq Omega Map_C (x,y) $

  Therefore

  $ Hom_(h C) (x,y) tilde.eq pi_2 Map_C (x[-2],y) $

  The right side is an abelian group, and naturality makes composition
  bilinear. Thus $h C$ is preadditive.

  The zero object remains a zero object in $h C$. For $x,y in C$, put

  $ p := cofib (x[-1] ->^0 y) $

  The pushout universal property and the suspension equivalence give

  $ Map_C (p,t)
    tilde.eq Map_C (x,t) times Map_C (y,t) $

  Hence $p$ is a coproduct. A finite coproduct in a preadditive
  category is a biproduct: its projections are determined by the matrices
  $(id,0)$ and $(0,id)$. Thus $h C$ is additive.
]

==== Distinguished Triangles

For a morphism $f:x->y$, choose a coherent diagram in $C$

#align(center, diagram({
  node((0, 0), [$x$])
  node((1.4, 0), [$y$])
  node((2.8, 0), [$0$])
  node((0, 1.3), [$0$])
  node((1.4, 1.3), [$C_f$])
  node((2.8, 1.3), [$Sigma x$])
  edge((0, 0), (1.4, 0), [$f$], label-side: left, "->")
  edge((1.4, 0), (2.8, 0), "->")
  edge((0, 1.3), (1.4, 1.3), "->")
  edge((1.4, 1.3), (2.8, 1.3), [$delta_f$], label-side: left, "->")
  edge((0, 0), (0, 1.3), "->")
  edge((1.4, 0), (1.4, 1.3), "->")
  edge((2.8, 0), (2.8, 1.3), "->")
}))

in which both small squares are pushouts. Then $C_f tilde.eq cofib (f)$, the
outer rectangle gives $Sigma x$, and $delta_f$ is the connecting morphism.

#definition(title:[Distinguished Triangle in $h C$])[
  A triangle in $h C$

  $ x ->^f y ->^u z ->^delta x[1] $

  is #emph[distinguished] if it is isomorphic to a cofiber triangle

  $ x ->^f y -> C_f ->^delta_f Sigma x $

  arising from a coherent two-pushout diagram as above.
]

Restriction from coherent two-pushout diagrams to the arrow $f$ is a trivial
Kan fibration. Consequently its fibers are contractible: the triangle is
independent of all choices up to isomorphism in $h C$, and coherent squares of
arrows lift to morphisms of cofiber triangles.

#lemma(title:[The Sign from Transposing a Suspension Square])[
  Interchanging the two zero directions in a pushout square defining
  $Sigma x$ induces $-id_(Sigma x)$ in $h C$.
]

#proof[
  Under the natural identification

  $ Hom_(h C) (Sigma x,y) tilde.eq pi_1 Map_C (x,y) $

  transposition is loop reversal, hence multiplication by $-1$. Yoneda gives
  the result.
]

#theorem(title:[Triangulated Homotopy Category])[
  Let $C$ be a stable $oo$-category. With translation $x[1]=Sigma x$ and the
  distinguished triangles defined above, $h C$ is a triangulated category.
]

#proof[
  We verify Verdier's axioms.

  #emph[TR1: existence, invariance, and the identity triangle.] Every arrow
  $f:x->y$ extends to

  $ x -->^f y --> C_f -->^delta_f x[1] $

  by two pushouts. Isomorphism invariance is part of the definition, and
  $C_(id_x) tilde.eq 0$ gives

  $ x -->^(id_x) x --> 0 --> x[1] $

  #emph[TR2: rotation.] The right pushout square says that $x[1]$ is the
  cofiber of $y->C_f$. One further pushout gives

  $ y -->^u C_f -->^delta_f x[1] -->^(-f[1]) y[1] $

  The minus sign is precisely the sign of the preceding lemma. Since shifts
  preserve pushouts, desuspension and repeated rotation prove the converse.

  #emph[TR3: morphisms of triangles.] A commutative square in $h C$ is a
  coherent square in $C$ after choosing representatives and a homotopy. The
  trivial Kan fibration of cofiber extensions lifts it to a morphism of the
  two cofiber triangles. Its third component $C_f->C_(f')$ is the required
  map; uniqueness is neither asserted nor needed.

  #emph[TR4: the octahedral axiom.] For $x->^f y->^g z$, choose coherent
  cofiber models. Pushout pasting gives

  #align(center, diagram({
    node((0, 0), [$x$])
    node((1.35, 0), [$y$])
    node((2.7, 0), [$z$])
    node((0, 1.25), [$0$])
    node((1.35, 1.25), [$C_f$])
    node((2.7, 1.25), [$C_(g f)$])
    edge((0, 0), (1.35, 0), [$f$], label-side: left, "->")
    edge((1.35, 0), (2.7, 0), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1.25), "->")
    edge((1.35, 0), (1.35, 1.25), "->")
    edge((2.7, 0), (2.7, 1.25), "->")
    edge((0, 1.25), (1.35, 1.25), "->")
    edge((1.35, 1.25), (2.7, 1.25), [$phi$], label-side: left, "->")
  }))

  The left square and outer rectangle are pushouts, hence so is the right
  square. Pushing it out along $C_f->0$ identifies its cofiber with
  $C_g=z coprod_y 0$ and produces the fourth distinguished triangle

  $ C_f -->^phi C_(g f) -->^psi C_g -->^theta C_f[1] $

  All four triangles are faces of one coherent pushout diagram. Its remaining
  faces give exactly the commutative octahedron, including the shifted signs
  fixed by TR2. Thus TR4 holds and $h C$ is triangulated.
]

#corollary(title:[The Stable--Triangulated Dictionary])[
  Passing from $C$ to $h C$ carries the basic stable constructions to the
  usual triangulated ones:

  #align(center, table(
    columns: (1fr, 1fr),
    align: center + horizon,
    inset: (x: 18pt, y: 4pt),
    stroke: none,
    table.hline(y: 1, stroke: 0.65pt + muted),
    table.vline(x: 1, stroke: 0.65pt + muted),
    text(weight: "semibold", fill: ink)[stable $oo$-category],
    text(weight: "semibold", fill: ink)[triangulated category],
    [zero object], [zero object],
    [$Sigma, Omega$], [shifts $[1],[-1]$],
    [finite product $=$ finite coproduct], [biproduct],
    [cofiber/fiber sequence], [distinguished triangle],
    [exact functor], [triangulated functor],
  ))

  Thus every formal theorem about triangulated categories applies to $h C$.
  Exact functors descend to triangulated functors, and mapping spaces give the
  usual long exact sequences. The enhancement $C$ retains more: its cofibers
  and comparison maps are coherently functorial, unlike cones in $h C$.
]

== Exact Functors

=== The Definition

#definition(title:[Exact Functor])[
  A functor $F:C->D$ between stable $oo$-categories is #emph[exact] if it preserves zero objects and sends cofiber sequences in $C$ to cofiber sequences in $D$. Equivalently, $F$ preserves fiber sequences.
]

We have the following equivalent characterizations of exact functors.

#proposition[
  Let $F:C->D$ be a functor between stable $oo$-categories, then the following are equivalent:

  1. $F$ is exact.
  2. $F$ preserves finite limits.
  3. $F$ preserves finite colimits.
]

#proofsketch[
  Suppose first that $F$ is exact. It preserves suspensions, desuspensions,
  and finite biproducts. Moreover, the pushout of a span
  $y <-^f x ->^g z$ is the cofiber of

  $ x -->^((f,-g)) y plus z $

  Hence $F$ preserves pushouts. Since it also preserves the zero object, it
  preserves all finite colimits. Dually, or by expressing a pullback as the
  fiber of $y plus z -> w$, it preserves all finite limits.

  Conversely, a functor preserving finite colimits preserves the initial
  object and pushout squares, hence the zero object and cofiber sequences. A
  functor preserving finite limits preserves the terminal object and pullback
  squares; in a stable $oo$-category these are again the zero object and
  cofiber sequences. Thus either condition implies exactness.
]

=== Ext Functor

#definition(title:[Ext Functor])[
  We write
  $ Ext^n_C (x,y) := Hom_(h C) (x,y[n]) $
]

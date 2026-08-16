#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Preliminaries

== Pointed Simplicial Sets

=== Definition

#definition(title:[Pointed Simplicial Sets])[
  The category of #emph[pointed simplicial sets] is defined to be 
  $ sSet_* := sSet_(Delta^0\/) = (Delta^0 arrow.b sSet) $
  where $Delta^0$ is the obviously the terminal object of $sSet$.
]

#remark[
  Since for every $n$, there is a unique
  $ Delta^n -> Delta^0 $
  the base point of a pointed simplicial set $Delta^0->^x_0 x$ induces a constant $n$-simplex
  $ (x_0)_n in x_n, quad Delta^n->Delta^0->x $
  Geometrically, it is a $n$-simplex that is "collapsed" to the base point, with all its vertices identified with the base point.
]

=== Simplicial $n$-loops

Just like what we did in topology, we can define some "loops" in simplicial sets.

#definition(title:[Simplicial $n$-Loop])[
  A #emph[simplicial $n$-loop] of a pointed simplicial set $(x,x_0)$ is a simplex $sigma in x_n$, where
  $ d_i sigma = (x_0)_(n-1), quad i = 0,...,n $
  which means that the border of $sigma$ degenerate to the base point.
]

#remark[
  Equivalently, the restriction of $sigma:Delta^n->x$ to $partial Delta^n$ is the constant map at $x_0$.
  #align(center, diagram({
	node((-2, 0), [$partial Delta^n$])
	node((-2, 1), [$Delta^n$])
	node((-1, 1), [$x$])
	node((-1, 0), [$Delta^0$])
	edge((-2, 0), (-1, 0), "->")
	edge((-1, 0), (-1, 1), [$x_0$], label-side: left, "->")
	edge((-2, 1), (-1, 1), [$sigma$], label-side: right, "->")
	edge((-2, 0), (-2, 1), "->")
  }))
]

Because the border was collapsed to a point, $sigma$ factors uniquely through the quotient
$ Delta^n\/partial Delta^n -> x $
where the notation $Delta^n\/partial Delta^n$ is somehow called the #emph[$n$-sphere] $S^n$, defined by above. Hence we say

#quote[simplicial $n$-loop $<==>$ pointed simplicial map $S^n->x$]

== Wedge Products and Smash Products

=== Wedge Products

#definition(title:[Wedge Product])[
  Suppose $Delta^0->x$ and $Delta^0->y$ are two pointed simplicial sets, the #emph[wedge product] of $x$ and $y$ is defined to be
  $ x wedge y := x union.sq_(Delta^0) y $
  basically connecting the two base points together.
]

#figure(
  align(center, cetz.canvas(length: 0.68cm, {
    import cetz.draw: *

    let edge = 1.0pt + c-thm
    let vertex-radius = 0.075
    let base-radius = 0.105
    let map-arrow = (
      end: ">",
      scale: 0.72,
      fill: c-thm,
      stroke: c-thm,
    )

    let simplex(a, b, c, color) = {
      line(a, b, c, close: true, stroke: none, fill: color.transparentize(91%))
      line(a, b, c, close: true, stroke: edge)
    }
    let vertex(p) = circle(p, radius: vertex-radius, fill: white, stroke: 1pt + c-thm)
    let basepoint(p) = circle(p, radius: base-radius, fill: c-def, stroke: 1pt + c-def)

    // Two pointed simplices before gluing.
    let x0 = (0.25, 0.45)
    let x1 = (1.95, 0.45)
    let x2 = (1.10, 2.20)
    let y0 = (4.55, 0.45)
    let y1 = (2.85, 0.45)
    let y2 = (3.70, 2.20)
    simplex(x0, x1, x2, c-thm)
    simplex(y0, y1, y2, c-def)
    for p in (x1, x2, y1, y2) { vertex(p) }
    basepoint(x0)
    basepoint(y0)
    content((1.10, -0.02), text(size: 9pt, fill: muted)[$x$])
    content((3.70, -0.02), text(size: 9pt, fill: muted)[$y$])
    content((2.40, 1.30), text(size: 12pt, fill: ink)[$+$])

    // The quotient map identifies the two marked vertices.
    line((5.05, 1.32), (6.20, 1.32), stroke: edge, mark: map-arrow)
    content((5.62, 1.72), text(size: 8pt, fill: muted)[identify])

    // In the wedge, the two simplices meet only at their common basepoint.
    let w = (8.30, 0.45)
    let xl = (6.65, 0.45)
    let xt = (7.45, 2.20)
    let yr = (9.95, 0.45)
    let yt = (9.15, 2.20)
    simplex(xl, w, xt, c-thm)
    simplex(w, yr, yt, c-def)
    for p in (xl, xt, yr, yt) { vertex(p) }
    basepoint(w)
    content((8.30, 0.10), text(size: 8pt, fill: c-def)[$ast$])
    content((8.30, -0.25), text(size: 9pt, fill: muted)[$x wedge y$])
  })),
  caption: [The wedge product identifies the marked base vertices of two pointed simplicial sets.],
)

#remark[
  The wedge product is functorial in both variables, it is a bifunctor of 1-category
  $ (- wedge -) : sSet_* times sSet_* -> sSet_* $
  also on the category of animae, this is also a $oo$-bifunctor
  $ (- wedge -) : Ani_* times Ani_* -> Ani_* $
]

=== Smash Products

#definition(title:[Smash Product])[
  Suppose $Delta^0->x$ and $Delta^0->y$ are two pointed simplicial sets, the #emph[smash product] of $x$ and $y$ is defined to be
  $ x smash y := frac(x times y, x wedge y) $
  basically collapsing the wedge product to a point.
]

#figure(
  align(center, cetz.canvas(length: 0.68cm, {
    import cetz.draw: *

    let edge = 1.0pt + c-thm
    let light-edge = 0.75pt + c-thm.lighten(30%)
    let collapsed = 1.7pt + c-def
    let vertex-radius = 0.075
    let base-radius = 0.105
    let map-arrow = (
      end: ">",
      scale: 0.72,
      fill: c-thm,
      stroke: c-thm,
    )

    // Delta^1 x Delta^1, with its canonical two-simplex subdivision.
    let a = (0.35, 0.45)
    let b = (3.10, 0.45)
    let c = (3.10, 3.10)
    let d = (0.35, 3.10)
    line(a, b, c, close: true, stroke: none, fill: c-thm.transparentize(92%))
    line(a, c, d, close: true, stroke: none, fill: c-def.transparentize(93%))
    line(a, b, c, d, close: true, stroke: edge)
    line(a, c, stroke: light-edge)

    // These two basepoint axes form Delta^1 vee Delta^1 inside the product.
    line(a, b, stroke: collapsed)
    line(a, d, stroke: collapsed)
    for p in (a, b, d) {
      circle(p, radius: base-radius, fill: c-def, stroke: 1pt + c-def)
    }
    circle(c, radius: vertex-radius, fill: white, stroke: 1pt + c-thm)
    content((1.72, -0.02), text(size: 9pt, fill: muted)[$Delta^1 times Delta^1$])
    content(
      (0.05, 1.78),
      text(size: 8pt, fill: c-def)[$Delta^1 wedge Delta^1$],
      anchor: "east",
    )

    // Quotient map.
    line((3.75, 1.78), (5.15, 1.78), stroke: edge, mark: map-arrow)
    content((4.45, 2.18), text(size: 8pt, fill: muted)[collapse])

    // The two 2-simplices remain visible after the wedge becomes one vertex.
    let p = (6.15, 1.78)
    let v = (9.55, 1.78)
    merge-path(fill: c-thm.transparentize(92%), stroke: none, close: true, {
      bezier(p, v, (7.00, 3.20), (8.70, 3.20))
      line(v, p)
    })
    merge-path(fill: c-def.transparentize(93%), stroke: none, close: true, {
      bezier(p, v, (7.00, 0.36), (8.70, 0.36))
      line(v, p)
    })
    bezier(p, v, (7.00, 3.20), (8.70, 3.20), stroke: edge)
    line(p, v, stroke: light-edge)
    bezier(p, v, (7.00, 0.36), (8.70, 0.36), stroke: edge)
    circle(p, radius: base-radius, fill: c-def, stroke: 1pt + c-def)
    circle(v, radius: vertex-radius, fill: white, stroke: 1pt + c-thm)
    content((6.15, 1.38), text(size: 8pt, fill: c-def)[$ast$])
    content((7.85, -0.02), text(size: 9pt, fill: muted)[$Delta^1 smash Delta^1$])
  })),
  caption: [A minimal model of the smash product: the highlighted wedge in the triangulated product is collapsed to the marked vertex.],
)

#pagebreak(weak: true)

=== Some Theories on Wedge and Smash

Before discussing the formal properties, it is useful to keep the following
analogy in mind: pointed spaces behave much like modules, with the base point
playing the role of zero, the wedge product the role of direct sum, and the
smash product the role of tensor product. This is a guide to intuition rather
than an identification of the two settings.

#align(center, table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: (x: 18pt, y: 4pt),
  stroke: none,
  table.hline(y: 1, stroke: 0.65pt + muted),
  table.vline(x: 1, stroke: 0.65pt + muted),
  text(weight: "semibold", fill: ink)[$R$-modules],
  text(weight: "semibold", fill: ink)[pointed spaces],
  [$0$],
  [$ast$],
  [$m plus.o n$],
  [$x wedge y$],
  [$m times.o_R n$],
  [$x smash y$],
  [$Hom_R (m, n)$],
  [$Map_* (x, y)$],
))

All the equivalences below are natural in the pointed simplicial sets involved.
They can equally be read in the $oo$-category $Ani_*$ of pointed animae.

#proposition(title:[Wedge Product Laws])[
  The wedge product is symmetric and associative, and the one-point object
  $ast$ is its unit:

  #align(center)[
    $x wedge y tilde.eq y wedge x$ \
    $(x wedge y) wedge z tilde.eq x wedge (y wedge z)$ \
    $x wedge ast tilde.eq x$
  ]

  These equivalences express the fact that $x wedge y$ is the coproduct of
  $x$ and $y$ in the pointed category.
]

#proposition(title:[Smash Product Laws])[
  Let $S^0 = Delta^0 union.sq Delta^0$, with one summand chosen as the base
  point. The smash product is symmetric and associative, its unit is $S^0$,
  and the one-point object is absorbing:

  #align(center)[
    $x smash y tilde.eq y smash x$ \
    $(x smash y) smash z tilde.eq x smash (y smash z)$ \
    $x smash S^0 tilde.eq x$ \
    $x smash ast tilde.eq ast$
  ]
]

#proposition(title:[Distributivity and Tensor-Hom Adjunction])[
  Smash product distributes over wedge product:

  $ x smash (y wedge z) tilde.eq (x smash y) wedge (x smash z). $

  Moreover, pointed mapping spaces satisfy the natural adjunction

  $ Map_* (x smash y, z) tilde.eq Map_* (x, Map_* (y, z)). $

  Thus $x smash (-)$ preserves colimits, which explains the distributive law.
] <prop-tensor-hom-simplicial>

#proof[
  Write $x_0$, $y_0$, and $z_0$ for the chosen base points. By definition,
  the quotient map

  $ q: x times y -> x smash y $

  collapses $x wedge y = (x times {y_0}) union ({x_0} times y)$ to the
  base point. Hence a pointed map $g:x smash y -> z$ is the same thing as a
  map $f:x times y -> z$ satisfying

  $ f(x, y_0) = z_0 = f(x_0, y) $

  for every $x$ and $y$.

  Currying $f$ gives a map

  $ x -> Map(y, z), quad x mapsto (y mapsto f(x, y)) $

  The condition $f(x,y_0)=z_0$ says that every map $y->z$ in its image is
  pointed, so this map factors through $Map_* (y,z)$. The condition
  $f(x_0,y)=z_0$ says that $x_0$ is sent to the constant base-point map, so
  the curried map $x->Map_* (y,z)$ is itself pointed. This construction is
  reversible and natural. Applied degreewise, it gives the equivalence of
  pointed mapping spaces

  $ Map_* (x smash y, z) tilde.eq Map_* (x, Map_* (y, z)) $

  By symmetry, $x smash (-)$ is therefore left adjoint to $Map_* (x,-)$ and
  preserves all colimits. Since $y wedge z$ is the coproduct of $y$ and $z$
  in the pointed category, preservation of this coproduct gives

  $ x smash (y wedge z) tilde.eq (x smash y) wedge (x smash z) $

  as claimed.
]

In other words, $(sSet_*, smash, S^0)$ is a closed symmetric monoidal
category, with internal Hom object $Map_* (-,-)$. Likewise,
$(Ani_*, smash, S^0)$ is a closed symmetric monoidal $oo$-category.

#remark(title:[Spheres and Suspension])[
  For pointed spheres one obtains
  $ S^m smash S^n tilde.eq S^(m+n) $
  the proof is obvious and direct.
] 

== Suspension and Looping

=== Suspension

Intuitively, the suspension of a pointed simplicial set is obtained by taking the product with a simplicial interval and collapsing the two ends to points. Formally, we have

#definition(title:[Suspension])[
  The #emph[suspension] of a pointed simplicial set $x$ is defined to be
  $ Sigma x := S^1 smash x $
]

=== Looping

According to the "$n$-loop = pointed map from $n$-sphere" principle, we have

#definition(title:[Loop])[
  The #emph[loop] of a pointed simplicial set $x$ is defined to be
  $ Omega x := Map_* (S^1, x) $
]

=== Some theories on Suspension and Looping

#theorem(title:[Suspension-Loop Adjunction])[
  There is a natural equivalence of pointed mapping spaces

  $ Map_* (Sigma x, y) tilde.eq Map_* (x, Omega y) $

  for every pointed simplicial sets $x$ and $y$. In other words, there is an adjunction
  $ Sigma : sSet_* arrows.lr sSet_* : Omega $
]

#proof[
  Immediately by definition and by @prop-tensor-hom-simplicial.
]

=== Module Analogy

Let $R$ be a commutative ring. For a fixed $R$-module $ell$, the ordinary
tensor--Hom adjunction is

$ Hom_R (ell times.o_R m, n) tilde.eq Hom_R (m, Hom_R (ell, n)). $

Thus the pointed-space dictionary extends from individual operations to
adjoint functors:

#align(center)[
  $k smash (-) quad ↔ quad ell times.o_R (-)$ \
  $Map_* (k, -) quad ↔ quad Hom_R (ell, -)$.
]

Taking $k=S^1$ on the space side gives $Sigma ⊣ Omega$. The closer
algebraic analogue appears in the derived category $D(R)$, where the shifted
unit $R[1]$ satisfies

#align(center)[
  $R[1] times.o^"L"_R m tilde.eq m[1]$ \
  $"RHom"_R (R[1], n) tilde.eq n[-1]$.
]

Hence the shift $[1]$ is left adjoint to $[-1]$, and the two are inverse
equivalences. This last feature belongs to the stable setting: after pointed
spaces are stabilized to spectra, $Sigma$ and $Omega$ likewise become
inverse equivalences; in $Ani_*$ they are adjoint but not inverse in general. We can even claim ambitiously

#quote[Stable homotopy theory = Linear algebra over the sphere spectrum $SS$. ]

We will explore this analogy in further chapters.

== Homotopy Groups

The simplicial $n$-loops introduced earlier are individual representatives.
To obtain an invariant of the homotopy type of $x$, we identify representatives
that are homotopic through pointed maps.

#definition(title:[Homotopy Groups])[
  Let $(x,x_0)$ be a pointed anima, represented for example by a pointed Kan
  complex. For every $n >= 0$, define

  $ pi_n (x,x_0) := pi_0 Map_* (S^n, x) = [S^n, x]_* , $

  where $[S^n,x]_*$ denotes the set of pointed homotopy classes of maps. In
  terms of iterated loop spaces, the same definition is

  $ pi_n (x,x_0) = pi_0 (Omega^n x), $

  where $Omega^0 x=x$ and the base point of $Omega^n x$ is the constant loop at $x_0$.
]

#remark(title:[Why a Kan Replacement Is Needed])[
  If $x$ is an arbitrary pointed simplicial set, the expression above means
  the #emph[derived] pointed mapping space. Concretely, choose a pointed Kan
  fibrant replacement $x -> x^"fib"$ and set

  $ pi_n (x,x_0) := pi_0 Map_* (S^n, x^"fib"). $

  This makes $pi_n$ invariant under weak equivalence. When $x$ is already Kan,
  no replacement is necessary.
]

#remark(title:[Simplicial Description])[
  For a pointed Kan complex $(x,x_0)$, a map $S^n=Delta^n\/partial Delta^n -> x$
  is exactly an $n$-simplex $sigma in x_n$ satisfying

  $ d_i sigma = (x_0)_(n-1), quad 0 <= i <= n. $

  Therefore $pi_n (x,x_0)$ is the set of such simplicial $n$-loops modulo pointed
  simplicial homotopy relative to $partial Delta^n$. The quotient by homotopy
  is essential: the raw set of $n$-loops is not itself a homotopy invariant.
]

#proposition(title:[Group Structure])[
  For $n >= 1$, $pi_n (x,x_0)$ is a group; for $n >= 2$, it is abelian. The
  product of two classes $[f]$ and $[g]$ is represented by the composite

  $ S^n ->^"pinch" S^n wedge S^n ->^(f wedge g) x. $

  Equivalently, this is concatenation of components in the $n$-fold loop
  space $Omega^n x$. The identity is the constant map at $x_0$.
]

#proofsketch[
  The loop space $Omega^n x$ has concatenation, so its connected components
  form a group when $n >= 1$. For $n >= 2$, the two loop directions give two
  compatible multiplications; the Eckmann--Hilton argument makes the product
  commutative.
]

=== The Whitehead Theorem

#theorem(title:[Whitehead Theorem])[
  Suppose $f:x->y$ is a map of animae. Suppose
  $ pi_0 (x) -->^~ pi_0 (y), quad pi_n (x,x_0) -->^~ pi_n (y,f(x_0)) $
  holds for every base point $x_0$. Then $f$ is a categorical equivalence.
] <thm-whitehead>

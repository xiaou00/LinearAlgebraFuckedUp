#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *

#show: doc => conf(
  easy: true,
  doc,
)

= Associative Algebras

Associativity first appears as an elementary equation, but in topology and
in $oo$-categories that equation must be replaced by homotopy-coherent data.
The basic example is an $H$-space: it already has a multiplication and a unit
up to homotopy, yet need not be a genuine topological monoid.

== From $H$-Spaces to Associativity

#definition(title:[$H$-Space])[
  An #emph[$H$-space] is a pointed topological space $(x,e)$ equipped with a
  multiplication

  $
    m:x times x->x
  $

  such that the composites

  $
    x tilde.eq x times {e}->x times x->^m x,
    quad
    x tilde.eq {e} times x->x times x->^m x
  $

  are homotopic to $id_x$. Thus $e$ is a two-sided unit up to homotopy.
]

#definition(title:[Homotopy Associativity])[
  An $H$-space $(x,e,m)$ is #emph[homotopy associative] if the square

  #align(center, diagram({
    node((0, 0), [$x times x times x$], name: <xxx>)
    node((1.7, 0), [$x times x$], name: <xx-top>)
    node((0, 1.2), [$x times x$], name: <xx-left>)
    node((1.7, 1.2), [$x$], name: <x>)
    edge(<xxx>, <xx-top>, [$m times id_x$], label-side: left, "->")
    edge(<xxx>, <xx-left>, [$id_x times m$], label-side: right, "->")
    edge(<xx-top>, <x>, [$m$], label-side: left, "->")
    edge(<xx-left>, <x>, [$m$], label-side: right, "->")
  }))

  commutes up to a specified homotopy. Equivalently, the two maps

  $
    m(m(x_1,x_2),x_3)
    quad "and" quad
    m(x_1,m(x_2,x_3))
  $

  are joined by a path in the mapping space $Map(x^3,x)$.
]

This distinction gives three increasingly strong notions of associativity.
Strict associativity is an equality of the two triple products. Homotopy
associativity chooses a path between them. #emph[Coherent associativity]
also requires compatible homotopies between all ways of multiplying four or
more inputs. A single associativity homotopy does not contain this higher
compatibility.

#example(title:[Topological Monoids])[
  A topological monoid $(x,e,m)$ is an $H$-space whose unit and associativity
  laws hold strictly. Consequently it is homotopy associative, with constant
  homotopies witnessing the required identities.
]

#example(title:[The Based Loop Space])[
  For a pointed space $(y,y_0)$, let

  $
    Omega y:={p:[0,1]->y : p(0)=y_0=p(1)}
  $

  be its based loop space. The constant loop is the base point, and loop
  concatenation is defined by

  $
    m(p,q)(t):=cases(
      p(2t) quad & 0<=t<=1/2,
      q(2t-1) quad & 1/2<=t<=1.
    )
  $

  This multiplication is unital and associative up to homotopy, but it is
  not strictly associative with the displayed parametrization: the two ways
  of concatenating three loops traverse them at different speeds.
]

#remark(title:[Strictification and Delooping])[
  The examples lead to two related recognition problems:

  + when is a homotopy associative $H$-space equivalent, compatibly with its
    multiplication, to a topological monoid?
  + when is it equivalent to a loop space $Omega y$?

  An $H$-space is #emph[group-like] if its multiplication makes $pi_0(x)$ a
  group. Every loop space is group-like, and for path-connected $H$-spaces
  this condition is automatic. The remaining issue is precisely the missing
  hierarchy of coherent associativity homotopies.
]

The same pattern appears in a monoidal category $(cal(C),times.o,1)$. An
ordinary associative algebra object consists of an object $a$, a unit
$eta:1->a$, and a multiplication $mu:a times.o a->a$ satisfying

$
  mu compose (mu times.o id_a)
  =mu compose (id_a times.o mu),
  quad
  mu compose (eta times.o id_a)=id_a
  =mu compose (id_a times.o eta).
$

In a monoidal $oo$-category these equalities indicate only the first layer:
the associativity path, its higher compatibilities, and the unit coherences
must all be recorded. Later sections will formulate this complete structure
using the associative operad $cat("Assoc")$ and will study its finite stages
through $A_n$-algebras.

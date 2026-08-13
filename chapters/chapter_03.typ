#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Derived Categories

== Nerves of dg-Categories

=== Introduction of the Goal

Let $A$ be an additive category. The chain complexes in $A$ can be organized
into an $oo$-category $C$, described informally as follows:

1. The objects of $C$ are chain complexes in $A$.
2. Given $x_*,y_* in C$, the morphisms $x_*->y_*$ are chain maps.
3. Given $f,g:x_*->y_*$, a $2$-morphism $f->g$ is represented by a chain
   homotopy, that is, maps $h_n:x_n->y_(n+1)$ satisfying

   $ d_y compose h_n+h_(n-1) compose d_x=f_n-g_n $

4. ...

To make this precise, we could proceed in several steps:

1. Let $Ch(A)$ be the ordinary category of chain complexes in $A$.
2. For $x_*,y_* in Ch(A)$, form the mapping chain complex

   $ underline(Hom)_A (x_*,y_*)_m
     :=product_(n in ZZ) Hom_A (x_n,y_(n+m)) $

   with differential

   $ (partial f)_n:=d_y f_n-(-1)^m f_(n-1)d_x $

   Its degree-zero cycles are chain maps, its degree-zero boundaries are
   null-homotopic maps, and

   $ "H"_m (underline(Hom)_A (x_*,y_*))
     tilde.eq Hom_(h#h(0pt)Ch(A)) (x_*,y_*[-m]) $

   Composition is a chain map, so $Ch(A)$ is enriched over $Ch(Ab)$; in
   other words, it is a dg-category.

3. The connective truncation

   $ tau_(>=0):Ch(Ab)->Ch_(>=0) (Ab) $

   is right-lax monoidal. Concretely, it comes with coherent maps

   $ tau_(>=0) m ⊗ tau_(>=0) n
     ->tau_(>=0) (m ⊗ n) $

   Applying it to every mapping complex preserves units and composition.
   Thus $Ch(A)$ is enriched over nonnegatively graded chain complexes.

4. By the Dold--Kan correspondence from the preceding chapter,

   $ "DK":Ch_(>=0) (Ab)->Fun (Delta^op,Ab) $

   is an equivalence. The Alexander--Whitney construction equips $"DK"$
   with a right-lax monoidal structure, so it again transports enrichment.
   The resulting simplicial abelian group of morphisms is

   $ Map_Delta (x_*,y_*)
     :="DK" (tau_(>=0) underline(Hom)_A (x_*,y_*)) $

5. Forgetting the abelian-group structure degreewise turns these mapping
   objects into simplicial sets. Their bilinear composition gives a
   simplicial category, denoted $Ch_Delta (A)$. Every simplicial abelian group
   is a Kan complex, so every mapping simplicial set of $Ch_Delta (A)$ is Kan;
   hence this simplicial category is fibrant.

6. Finally, take the homotopy coherent nerve

   $ C_"dg" (A):=N_"hc" (Ch_Delta (A)) $

   Since $Ch_Delta (A)$ is fibrant, $C_"dg" (A)$ is an $oo$-category. It has
   the same objects as $Ch(A)$, while its mapping spaces retain chain maps,
   chain homotopies, and all higher coherent homotopies.

This procedure is indeed too complicated, so we will introduce some new concepts to simplify it.

=== What is a dg(differential graded)-category?

#definition(title:[dg-Category])[
  Let $k$ ba a commutative ring. A #emph[dg-category] over $k$ consists of the following data:

  1. A collection ${x,y,...}$ whose elements are called #emph[objects] of $C$.
  2. For every pair of $x,y in C$, a #emph[chain complex] of $k$-modules
    $ ... -> Map_C (x,y)_1 -> Map_C (x,y)_0 -> Map_C (x,y)_(-1) -> ... $
    which we will denoted by $Map_C (x,y)_*$.
  3. For every triple $x,y,z in C$ a composition map
    $ Map_C (y,z)_* times.o_k Map_C (x,y)_* -> Map_C (x,z)_* $
    which we can identify with a collection of $k$-bilinear maps
    $ compose : Map_C (y,z)_p times Map_C (x,y)_q -> Map_C (x,z)_(p+q) $
    satisfying the #emph[Leibniz rule]
    $ d (g compose f) = d g compose f + (-1)^p g compose d f $
  4. For each $x in C$, an #emph[identity morphism] $id_x in Map_C (x,x)_0$ such that
    $ g compose id_x = g, quad id_x compose f = f $
    forall $f in Map_C (y,x)_p$ and $g in Map_C (x,y)_q$.

  The composition law is required to be associative in the following sense: for every triple $f in Map_C (w,x)_p$, $g in Map_C (x,y)_q$ and $h in Map_C (y,z)_r$, we have
  $ h compose (g compose f) = (h compose g) compose f $
  In the case $k=ZZ$, we refer to $C$ as a #emph[dg-category] without further qualification.
]



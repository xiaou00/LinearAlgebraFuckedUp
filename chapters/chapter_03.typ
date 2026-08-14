#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Derived $oo$-Categories

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
  Let $k$ be a commutative ring. A #emph[dg-category] over $k$ consists of the following data:

  1. A collection ${x,y,...}$ whose elements are called #emph[objects] of $C$.
  2. For every pair of $x,y in C$, a #emph[chain complex] of $k$-modules
    $ ... -> Map_C (x,y)_1 -> Map_C (x,y)_0 -> Map_C (x,y)_(-1) -> ... $
    which we denote by $Map_C (x,y)_*$.
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

We now introduce a construction called the dg-nerve.

#definition(title:[dg-Nerve])[
  Let $C$ be a dg-category, we associate to $C$ to a simplicial set $Ner^dg (C)$ called the #emph[dg-nerve]. For each $n>=0$, we define
  $ Ner^dg (C)_n tilde.eq Hom_sSet (Delta^n, Ner^dg (C)) $ 
  to be the set of all ordered pairs $({x_i}_(0<=i<=n),{f_I})$ where:

  1. For $0<=i<=n$, $x_i$ denotes an object of the dg-category $C$.
  2. For every subset $I = {i_-<i_m<i_(m-1)<...<i_1<i_+} subset [n]$ with $m>=0$, $f_I$ is an element of the abelian group $Map_C (x_(i_-),x_(i_+))_m$, satisfying
    $ d f_I = sum_(1<=r<=m) (-1)^r
      (f_(I-{i_r})
        -f_(i_r<...<i_1<i_+) compose f_(i_-<i_m<...<i_r)) $
  
  If $alpha:[m]->[n]$ is a nondecreasing function, then the induced map $Ner^dg (C)_n->Ner^dg (C)_m$ is given by
  $ ({x_i}_(0<=i<=n),{f_I}) |-> ({x_(alpha(j))}_(0<=j<=m),{g_J}) $
  where
  $ g_J = cases(
    f_(alpha(J)) quad & "if" alpha|_J "is injective",
    id_(x_i) quad & "if" J = {j,j'} "with" alpha(j)=alpha(j')=i,
    0 quad & "otherwise"
  ) $
]

#example[
  Let $C$ be a dg-category, then:

  1. A 0-simplex of $Ner^dg (C)$ is an object of $C$.
  2. A 1-simplex of $Ner^dg (C)$ is a morphism of $C$, that is, a pair of objects $x,y in C$ together with an element $f in Map_C (x,y)_0$ satisfying $d f=0$.
  3. A 2-simplex of $Ner^dg (C)$ is a triple of objects $x,y,z in C$ together with triple of morphisms
    $ f in Map_C (x,y)_0, quad g in Map_C (y,z)_0, quad h in Map_C (x,z)_0 $
    satisfying $d f = d g = d h = 0$, together with an element $k in Map_C (x,z)_1$ satisfying $d k = (g compose f) - h$.
]

#remark[
  Let $C$ be a dg-category and let $C_0$ denote its underlying ordinary
  category. Then $Ner(C_0)$ is isomorphic to the simplicial subset of
  $Ner^dg (C)$ whose $n$-simplices are the pairs
  $({x_i}_(0<=i<=n),{f_I})$ with $f_I=0$ whenever $I$ has more than two
  elements. In particular, $Ner(C_0)->Ner^dg (C)$ is bijective on
  $n$-simplices for $n<=1$.
]

#proposition(title:[The dg-Nerve is an $oo$-Category])[
  If $C$ is a dg-category, then the simplicial set $Ner^dg (C)$ is an
  $oo$-category.
]

#proof[
  It is enough to fill every inner horn. Fix $0<j<n$ and a map

  $ phi_0:Lambda_j^n->Ner^dg (C) $

  Unwinding the definition, the horn specifies objects $x_0,...,x_n$ and
  elements $f_I$ satisfying the dg-nerve relation for every nonempty subset
  $I subset.eq [n]$, except for

  $ I=[n], quad I=[n]-{j} $

  Indeed, these are precisely the two nondegenerate simplices which do not
  lie in the $j$th horn. Define the missing elements by

  $ f_([n]-{j}):=
      sum_(0<p<n) (-1)^(p-j)
        f_({p,p+1,...,n}) compose f_({0,...,p})
      -sum_(0<p<n, p!=j) (-1)^(p-j) f_([n]-{p}) $

  and set

  $ f_([n]):=0 $

  We verify that these choices satisfy the two missing relations. With
  $f_([n])=0$, the relation indexed by $[n]$ has zero left-hand side; solving
  its right-hand side for the only unknown term $f_([n]-{j})$ gives exactly
  the displayed formula.

  It remains to check the relation indexed by $[n]-{j}$. For any subset $I$,
  let $R_I$ be the left-hand side minus the right-hand side of its dg-nerve
  relation. Expanding $d R_([n])$ with $d^2=0$ and the Leibniz rule, the terms
  obtained by deleting two vertices cancel in pairs, and the threefold
  composites cancel by associativity. Since $R_I=0$ for every proper face
  already contained in the horn, the result reduces to

  $ d R_([n])=(-1)^j R_([n]-{j}) $

  Our definition gives $R_([n])=0$, so its differential vanishes and hence
  $R_([n]-{j})=0$. We have therefore obtained an $n$-simplex extending $phi_0$.
  Every inner horn admits a filler, so $Ner^dg (C)$ is an $oo$-category.
]

#remark(title:[The dg-Nerve Need Not Be Stable])[
  The preceding proposition asserts only that $Ner^dg (C)$ is an
  $oo$-category. It need not be stable. For example, let $C$ have one object
  $x$ with

  $ Map_C (x,x)_*=k[0] $

  for a nonzero ring $k$. Then $Map_(Ner^dg (C)) (x,x)$ is the discrete space
  underlying $k$, hence is not contractible. Since $x$ is the only object, a
  zero object would have to be $x$; therefore $Ner^dg (C)$ is not even
  pointed and cannot be stable.

  Stability requires additional structure on $C$. A standard sufficient
  hypothesis is that $C$ be #emph[pretriangulated]: it contains a zero object
  and is closed under shifts and mapping cones in a way compatible with its
  dg enrichment. Under this hypothesis $Ner^dg (C)$ is stable. In particular,
  the dg-category $Ch(A)$ of chain complexes is pretriangulated, which is why
  $Ch_oo (A)=Ner^dg (Ch(A))$ is stable in the next section.
]

=== Mapping Spaces and the Coherent Nerve

For a dg-category $C$, let $h C$ denote the ordinary category with the same
objects and morphism sets

$ Hom_(h C) (x,y):="H"_0 (Map_C (x,y)_*) $

#proposition(title:[Homotopy Category and Mapping Spaces])[
  There is a canonical isomorphism

  $ h C tilde.eq h Ner^dg (C) $

  For every $x,y in C$, the right mapping space of the dg-nerve is naturally
  isomorphic to

  $ Map^R_(Ner^dg (C)) (x,y)
    tilde.eq "DK" (tau_(>=0) Map_C (x,y)_*) $

  Consequently, for every $m>=0$,

  $ pi_m Map_(Ner^dg (C)) (x,y)
    tilde.eq "H"_m (Map_C (x,y)_*) $
]

#proofsketch[
  The canonical map from the nerve of the closed degree-zero morphisms to
  $Ner^dg (C)$ is the identity on objects and morphisms. A $2$-simplex shows
  that two cycles $f,g in Map_C (x,y)_0$ represent the same morphism exactly
  when $f-g=d h$ for some $h in Map_C (x,y)_1$. This gives the first
  isomorphism.

  An $n$-simplex of the right mapping space has fixed initial and terminal
  vertices $x,y$. Unwinding the dg-nerve relation identifies its remaining
  elements, after the standard change of signs, with an $n$-simplex of the
  Dold--Kan object of $tau_(>=0) Map_C (x,y)_*$. The last assertion is then
  the identity $pi_m "DK" (c) tilde.eq "H"_m (c)$.
]

The same formula constructs a simplicial category $C_Delta$. Its objects are
those of $C$, and

$ Map_(C_Delta) (x,y)
  :="DK" (tau_(>=0) Map_C (x,y)_*) $

Composition is induced by the right-lax monoidal Alexander--Whitney map.
Every mapping object is a simplicial abelian group and hence a Kan complex,
so $C_Delta$ is a fibrant simplicial category.

#proposition(title:[Comparison of the Two Nerves])[
  There is a natural functor

  $ theta:N_"hc" (C_Delta)->Ner^dg (C) $

  which is an equivalence of $oo$-categories.
]

#proofsketch[
  The functor is the identity on objects and is obtained by applying the
  Alexander--Whitney formula to coherent simplices. On every pair $x,y$, the
  preceding proposition identifies the induced map of right mapping spaces
  with the identity of
  $"DK" (tau_(>=0) Map_C (x,y)_*)$. Thus $theta$ is fully faithful and
  essentially surjective, hence an equivalence.
]

This comparison explains why the direct formula for $Ner^dg (C)$ and the
longer construction by simplicial enrichment encode the same
$oo$-category.

=== Functoriality and the Model Structure

#definition(title:[dg-Functor])[
  Let $C,D$ be dg-categories over a commutative ring $k$. A dg-functor
  $F:C->D$ assigns an object $F(x)$ to every $x in C$ and a chain map

  $ F_(x,y):Map_C (x,y)_*->Map_D (F(x),F(y))_* $

  to every pair $x,y$, compatibly with identities and composition. It induces
  functors $h F:h C->h D$ and $Ner^dg (F):Ner^dg (C)->Ner^dg (D)$.
]

#theorem(title:[Model Structure on dg-Categories])[
  The category $dgCat_k$ of small dg-categories over $k$ admits a
  combinatorial model structure characterized as follows.

  1. A dg-functor $F:C->D$ is a weak equivalence, also called a
     #emph[quasi-equivalence], exactly when $h F$ is an equivalence and every
     map

     $ Map_C (x,y)_*->Map_D (F(x),F(y))_* $

     is a quasi-isomorphism.

  2. It is a fibration exactly when these maps of complexes are degreewise
     surjective and $h F$ is an isofibration: every isomorphism
     $F(x)->y$ in $h D$ lifts to an isomorphism $x->x'$ in $h C$.
]

#proposition(title:[The dg-Nerve is Right Quillen])[
  Let $L_"dg"$ denote the left adjoint of the dg-nerve. There is a Quillen
  adjunction

  $ L_"dg":sSet_"Joyal" arrows.lr Cat_("dg",k):Ner^dg $

  Thus $L_"dg"$ is left Quillen and $Ner^dg$ is right Quillen. The right
  adjoint sends a dg-category to its dg-nerve, while the left adjoint freely
  generates a dg-category from a simplicial set.

  In particular, a quasi-equivalence of dg-categories induces an equivalence
  of $oo$-categories, and a fibration induces a categorical fibration of
  dg-nerves.
]

The left adjoint is characterized by natural bijections

$ Hom_(Cat_("dg",k)) (L_"dg" (kappa),C)
  tilde.eq Hom_sSet (kappa,Ner^dg (C)) $

for every simplicial set $kappa$ and dg-category $C$. Equivalently, it is the
left Kan extension of its values on standard simplices:

$ L_"dg" (kappa)
  tilde.eq colim_(Delta^n->kappa) L_"dg" (Delta^n) $

Here $L_"dg" (Delta^n)$ is the universal dg-category whose dg-functors to
$C$ are the $n$-simplices of $Ner^dg (C)$. This universal description is all
that is needed for the Quillen adjunction; an explicit model can be obtained
by applying normalized chains to simplicial rigidification.

#proofsketch[
  The dg-nerve preserves small limits and filtered colimits, so it admits a
  left adjoint. Suppose $F:C->D$ is a fibration. In a lifting problem for an
  inner horn, the target filler determines the missing element in a mapping
  complex of $D$. Degreewise surjectivity lifts this element to $C$; the same
  formula used in the inner-horn proof then supplies the remaining face.
  Thus $Ner^dg (F)$ is an inner fibration. The isofibration condition on
  $h F$ lifts equivalences and makes it a categorical fibration.

  If $F$ is also a weak equivalence, the mapping-space formula above turns
  each quasi-isomorphism of mapping complexes into a weak homotopy
  equivalence, while the equivalence $h F$ gives essential surjectivity.
  Hence $Ner^dg (F)$ is a categorical equivalence. Therefore $Ner^dg$
  preserves fibrations and trivial fibrations and is right Quillen.
]

#remark(title:[Summary of the Construction])[
  The preceding discussion can be organized into the following chain of
  ideas.

  1. A dg-category stores morphisms from $x$ to $y$ in the chain complex
     $Map_C (x,y)_*$, rather than in a set.

  2. Connective truncation followed by Dold--Kan turns this complex into the
     mapping space of the dg-nerve:

     $ Map_(Ner^dg (C)) (x,y)
       tilde.eq "DK" (tau_(>=0) Map_C (x,y)_*) $

     Consequently,

     $ pi_m Map_(Ner^dg (C)) (x,y)
       tilde.eq "H"_m (Map_C (x,y)_*) $

     Thus the homology of a mapping complex becomes the homotopy of a
     mapping space. In degree zero this recovers
     $h Ner^dg (C) tilde.eq h C$.

  3. The direct dg-nerve and the homotopy coherent nerve of the associated
     simplicial category are equivalent. They are two models of the same
     $oo$-category: the former is explicit, while the latter explains the
     simplicial enrichment behind it.

  4. The model structure on dg-categories is designed so that a
     quasi-equivalence is exactly a quasi-isomorphism on every mapping
     complex together with an equivalence on homotopy categories. The
     mapping-space formula therefore shows that the dg-nerve sends every
     quasi-equivalence to an equivalence of $oo$-categories.

  5. These facts are compatible with the Quillen adjunction

     $ L_"dg":sSet_"Joyal" arrows.lr Cat_("dg",k):Ner^dg $

     Hence the dg-nerve is the bridge from differential graded algebra to
     $oo$-categories: chain homotopies and their higher compatibilities are
     retained as higher simplices. This statement gives only a Quillen
     #emph[adjunction]. It does not assert that the two model categories are
     Quillen equivalent.
]

== Derived $oo$-Categories

The dg-nerve remembers chain homotopies and all their higher coherences, but
it does not yet identify quasi-isomorphic complexes. The derived
$oo$-category is obtained by performing exactly this final localization.

=== Definition and Universal Property

Let $A$ be an abelian category. Regard $Ch(A)$ as the dg-category whose
mapping complexes were defined above, and put

$ Ch_oo (A):=Ner^dg (Ch(A)) $

Its homotopy category is the ordinary homotopy category $K(A)$ of chain
complexes. Let $W$ be the collection of quasi-isomorphisms, that is, chain
maps $f:x->y$ for which every map

$ "H"_n (f):"H"_n (x)->"H"_n (y) $

is an isomorphism.

#definition(title:[Derived $oo$-Category])[
  The #emph[derived $oo$-category] of $A$ is the $oo$-categorical
  localization

  $ Dcat(A):=Ch_oo (A)[W^(-1)] $

  It has the same objects as $Ch_oo (A)$, but every quasi-isomorphism is made
  into an equivalence. We write

  $ q:Ch_oo (A)->Dcat(A) $

  for the localization functor.
]

The definition is characterized by the universal property

$ Fun (Dcat(A),C) tilde.eq Fun_W (Ch_oo (A),C) $

where the right-hand side is the full subcategory of functors which carry
every quasi-isomorphism to an equivalence. Thus a construction on complexes
descends to $Dcat(A)$ precisely when it is invariant under quasi-isomorphisms;
the descent and all its coherences are then unique up to a contractible
space of choices.

#proposition(title:[Stable Verdier Quotient])[
  The $oo$-category $Ch_oo (A)$ is stable. Let $"Ac"(A)$ be its full stable
  subcategory of acyclic complexes. Then

  $ Dcat(A) tilde.eq Ch_oo (A) slash "Ac"(A) $

  is a stable Verdier quotient, and $q$ is exact. Moreover,

  $ h#h(0pt)Dcat(A) tilde.eq K(A) slash "Ac"(A) $

  is the classical triangulated derived category of $A$.
]

#proofsketch[
  Shifts and cofibers in $Ch_oo (A)$ are represented by shifts and mapping
  cones of complexes. A map $f$ is a quasi-isomorphism exactly when
  $cofib(f)$ is acyclic. Localizing at $W$ is therefore the same as killing
  the stable subcategory $"Ac"(A)$. A quotient of a stable $oo$-category by
  a stable subcategory is stable, and passage to the homotopy category gives
  the usual Verdier quotient.
]

Consequently, a cofiber sequence in $Dcat(A)$ is represented by a mapping-cone
sequence

$ x ->^f y -> "Cone" (f) -> x[1] $

and becomes a distinguished triangle in $h#h(0pt)Dcat(A)$. The $oo$-category retains
the functorial cofiber and all higher coherences which its triangulated
homotopy category forgets.

=== Homology, the $t$-Structure, and $Ext$

#proposition(title:[Standard $t$-Structure])[
  The derived $oo$-category has a canonical $t$-structure defined by

  $ Dcat(A)_(>=0):={x:"H"_n (x)=0 " for " n<0} $

  $ Dcat(A)_(<=0):={x:"H"_n (x)=0 " for " n>0} $

  Its truncation functors are induced by the good truncations of complexes,
  and its homology-object functors are the ordinary homology functors

  $ pi_n (x) tilde.eq "H"_n (x) $

  The inclusion of objects concentrated in degree zero induces an
  equivalence of abelian categories

  $ A tilde.eq Dcat(A)^(suit.heart) $
]

#proofsketch[
  Good truncations give a functorial fiber--cofiber sequence

  $ tau_(>=0) x->x->tau_(<=-1) x $

  and the two terms have the required homology vanishing. If
  $x in Dcat(A)_(>=0)$ and $y in Dcat(A)_(<=-1)$, every map $x->y$ vanishes by
  truncation, giving orthogonality. A complex with homology only in degree
  zero is quasi-isomorphic to that homology object placed in degree zero,
  which identifies the heart with $A$.
]

The usual bounded variants are recovered directly from this $t$-structure:

$ Dcat^+ (A):=union_(m in ZZ) Dcat(A)_(>=m),
  quad Dcat^- (A):=union_(n in ZZ) Dcat(A)_(<=n) $

$ Dcat^b (A):=union_(m<=n)
  (Dcat(A)_(>=m) inter Dcat(A)_(<=n)) $

For $x,y in Dcat(A)$ and $m>=0$, stability gives

$ pi_m Map_(Dcat(A)) (x,y)
  tilde.eq Hom_(h Dcat(A)) (x[m],y) $

For $a,b in A tilde.eq Dcat(A)^(suit.heart)$, define

$ Ext_A^n (a,b):=Hom_(h#h(0pt)Dcat(A)) (a,b[n]) quad (n>=0) $

Equivalently,

$ Ext_A^n (a,b) tilde.eq pi_0 Map_(Dcat(A)) (a,b[n]) $

This recovers the classical Yoneda $Ext$ groups. Notice the direction of the
shift: with our homological indexing,
$pi_m Map_(Dcat(A)) (a,b) tilde.eq Hom_(h Dcat(A)) (a,b[-m])$. Thus positive
$Ext$ is seen by shifting the target before taking the mapping space.

=== Resolutions and Derived Functors

The localization definition is conceptual, while resolutions make it
computable.

#definition(title:[$K$-Projective and $K$-Injective Complexes])[
  A complex $p$ is #emph[$K$-projective] if

  $ Map_(Ch_oo (A)) (p,a) tilde.eq ast $

  for every acyclic complex $a$. Dually, a complex $i$ is
  #emph[$K$-injective] if

  $ Map_(Ch_oo (A)) (a,i) tilde.eq ast $

  for every acyclic $a$.
]

#proposition(title:[Computing the Localization])[
  If every complex $x$ admits a quasi-isomorphism $p->x$ with $p$
  $K$-projective, then the full dg-subcategory of $K$-projective complexes
  presents $Dcat(A)$. Dually, if every $x$ admits a quasi-isomorphism $x->i$
  with $i$ $K$-injective, then the $K$-injective complexes present $Dcat(A)$.

  With either kind of replacement, derived mapping spaces can be computed by

  $ Map_(Dcat(A)) (x,y)
    tilde.eq "DK"(tau_(>=0) underline(Hom)_A (p,y)) $

  $ Map_(Dcat(A)) (x,y)
    tilde.eq "DK"(tau_(>=0) underline(Hom)_A (x,i)) $
]

#proofsketch[
  A quasi-isomorphism between $K$-projective complexes is a chain-homotopy
  equivalence, and the same holds for $K$-injectives. Moreover, mapping from
  a $K$-projective complex or into a $K$-injective complex already sends
  quasi-isomorphisms to equivalences. Hence the displayed mapping objects
  satisfy the universal property of the localization.
]

If $A$ is a Grothendieck abelian category, every complex admits a
$K$-injective resolution; in particular, $Dcat(A)$ is a presentable stable
$oo$-category. For module categories one may also use $K$-projective
resolutions.

Let $F:A->B$ be additive and apply it degreewise to complexes. If $F$ is
exact, it preserves quasi-isomorphisms and therefore induces an exact functor

$ Dcat(F):Dcat(A)->Dcat(B) $

For a nonexact functor, its total left and right derived functors, when they
exist, are the Kan extensions through $q$. In terms of adapted resolutions,
they are computed by

$ "L"F(x) tilde.eq F(p), quad "R"F(x) tilde.eq F(i) $

The point of a resolution is precisely that the right-hand side no longer
depends on the chosen representative of $x$.

#example(title:[Modules over a Ring])[
  For a ring $R$, the derived $oo$-category is

  $ Dcat(R):=Dcat(Mod_R) $

  If $p->m$ is a $K$-projective resolution and $n$ is another complex, then

  $ m ⊗_R^"L" n tilde.eq p ⊗_R n,
    quad "RHom"_R (m,n) tilde.eq underline(Hom)_R (p,n) $

  When $m,n$ are modules placed in degree zero, our homological convention
  gives

  $ "H"_r (m ⊗_R^"L" n) tilde.eq Tor_r^R (m,n),
    quad "H"_(-r) ("RHom"_R (m,n)) tilde.eq Ext_R^r (m,n) $
]

#remark(title:[Core Idea])[
  The construction has two logically separate stages:

  $ Ch(A) stretch(->)^("dg-nerve") Ch_oo (A)
    stretch(->)^("invert quasi-isomorphisms") Dcat(A) $

  The first stage promotes chain homotopies to coherent higher morphisms. The
  second discards the choice of resolution by identifying complexes with the
  same derived information. Stability then organizes cones into cofiber
  sequences, the standard $t$-structure recovers homology and the original
  abelian category, and resolutions provide concrete formulas for mapping
  spaces and derived functors.
]

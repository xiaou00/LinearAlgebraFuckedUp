#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Homological Algebra Reviewed

== $t$-Structures

=== Definition of $t$-Structures on Triangulated Categories

Recall that we say a full sub $oo$-category $C' subset C$ is a #emph[localization] if the inclusion functor has a left adjoint. We will introduce a class of localizations called #emph[$t$-structures] which are particularly important in homological algebra. 

#definition(title:[$t$-Structure on Triangulated Category])[
  Let $D$ be a triangulated category. A #emph[$t$-structure] on $D$ is a pair of full subcategories $(D_(>=0),D_(<=0))$ stable under isomorphisms, such that the following conditions hold:

  1. For $x in D_(>=0)$ and $y in D_(<=0)$, we have $Hom_D (x,y[-1])=0$.
  2. We have inclusions $D_(>=0)[1] subset D_(>=0)$ and $D_(<=0)[-1] subset D_(<=0)$.
  3. For any $x in D$, there exists a fiber sequence $x'->x->x''$ (i.e. $x' = fib (x->x'')$) where $x' in D_(>=0)$ and $x'' in D_(<=-1)$.
]

#remark[
  We denote $D_(>=n)$ for $D_(>=0)[n]$ and $D_(<=n)$ for $D_(<=0)[n]$ for any integer $n$.
]

#remark[
  In this definition, either of the full subcategories $D_(>=0)$ and $D_(<=0)$ determines the other. For example, an object $y in D$ belongs to $D_(<=-1)$ if and only if $Hom_D (x,y)$ vanishes for all $x in D_(>=0)$.
]

=== Definition of $t$-Structures on Stable $oo$-Categories

#definition(title:[$t$-Structure on Stable $oo$-Category])[
  Let $C$ be a stable $oo$-category, a #emph[$t$-structure] on $C$ is a $t$-structure $h C$, if $C$ is equipped with a $t$-structure, we let $C_(>=n)$ and $C_(<=n)$ denote the full subcategories of $C$ spanned by those objects which belong to $(h C)_(>=n)$ and $(h C)_(<=n)$, respectively.
]

#proposition[
  Let $C$ be a stable $oo$-category with a $t$-structure, for each $n in ZZ$, the full subcategory $C_(<=n)$ is a localization of $C$.
]

#proof[
  Since shifts are equivalences and carry $C_(<=n)$ to translates of
  $C_(<=-1)$, it is enough to treat $n=-1$.

  Recall the criterion for a full subcategory to be a localization. The
  inclusion $i:D->C$ has a left adjoint if, for every $x in C$, there is a map
  $eta_x:x->L x$ with $L x in D$ such that composition with $eta_x$ induces an
  equivalence

  $ Map_C (L x,y) -> Map_C (x,y) $

  for every $y in D$. Indeed, this is exactly the universal property
  characterizing $L x$ as the reflection of $x$ into $D$; these universal
  objects assemble into a functor $L:C->D$ left adjoint to $i$.

  Apply the third axiom of the $t$-structure to $x$. It gives a fiber, hence
  also cofiber, sequence

  $ x' -> x ->^eta_x x'' $

  with $x' in C_(>=0)$ and $x'' in C_(<=-1)$. We claim that $x''$ has the
  required universal property. Fix $y in C_(<=-1)$. Applying $Map_C (-,y)$
  gives a fiber sequence

  $ Map_C (x'',y) -> Map_C (x,y) -> Map_C (x',y) $

  It therefore remains to show that $Map_C (x',y)$ is contractible.

  For $k in ZZ$, write

  $ Ext_C^k (a,b):=Hom_(h C) (a,b[k])
    tilde.eq Hom_(h C) (a[-k],b) $

  If $k<=0$, then $-k>=0$, so the shift axiom gives
  $x'[-k] in C_(>=0)$. The orthogonality axiom and
  $y in C_(<=-1)$ now imply

  $ Ext_C^k (x',y)
    tilde.eq Hom_(h C) (x'[-k],y)
    tilde.eq 0 $

  For every $m>=0$, stability identifies the homotopy groups of the mapping
  space with these groups:

  $ pi_m Map_C (x',y) tilde.eq Ext_C^(-m) (x',y) tilde.eq 0 $

  Mapping spaces are Kan complexes. The case $m=0$ says that this mapping
  space is connected, and the higher cases say that all its homotopy groups
  vanish; the Whitehead criterion therefore makes it contractible. Hence
  $Map_C (x'',y)->Map_C (x,y)$ is an equivalence for every
  $y in C_(<=-1)$, so $x mapsto x''$ defines the left adjoint
  $tau_(<=-1):C->C_(<=-1)$. Shifting gives the localization
  $tau_(<=n):C->C_(<=n)$ for every $n in ZZ$.
]

#corollary[
  Each $C_(<=n)$ is closed under all limits which exist in $C$. Dually, each
  $C_(>=n)$ is closed under all colimits which exist in $C$.
]

== Truncation Functors

=== Definition of Truncation Functors

Indeed, local objects are characterized by equivalences of mapping spaces,
and such equivalences are preserved under limits. The second statement is
dual.

#remark(title:[Notation])[
  Write

  $ tau_(<=n):C->C_(<=n), quad tau_(>=n):C->C_(>=n) $

  for the left and right adjoints to the respective inclusions. Every
  $x in C$ then fits naturally into a fiber--cofiber sequence

  $ tau_(>=n) x -> x -> tau_(<=n-1) x $
]

Both truncation functors preserve every $C_(<=m)$ and every $C_(>=m)$. For
example, $tau_(<=n)$ either acts as the identity on $C_(<=m)$ or lands in the
smaller subcategory $C_(<=n)$. The assertion for $tau_(>=n)$ follows from the
displayed fiber sequence and closure under limits. The remaining statements
are dual.

#remark(title:[Warning])[
  The symbol $tau_(<=n)$ here denotes truncation for a $t$-structure, not the
  truncation of an arbitrary $oo$-category by homotopy dimension. A nonzero
  object of a stable $oo$-category is never truncated in the latter sense:
  for arbitrarily large $r$, its identity gives a nonzero class in
  $pi_r Map_C (x[-r],x)$.

  The notions agree after restricting the source to $C_(>=0)$. For $k>=-1$,
  an object $x$ belongs to $C_(<=k)$ exactly when $Map_C (y,x)$ is
  $k$-truncated for every $y in C_(>=0)$.
]

=== Commuting Truncations and the Heart

For $m,n in ZZ$, the universal properties give a natural transformation

$ theta:tau_(<=m) compose tau_(>=n)
  -> tau_(>=n) compose tau_(<=m) $

#proposition[
  The transformation $theta$ is an equivalence. If $m<n$, both sides are
  zero; if $m>=n$, they define the truncation of $x$ to the interval
  $[n,m]$.
]

#proofsketch[
  Both sides lie in $C_(>=n) inter C_(<=m)$. When $m<n$, orthogonality
  makes this intersection zero. When $m>=n$, apply $Ext_C^0 (-,y)$ for
  $y in C_(>=n) inter C_(<=m)$ to the two truncation sequences.
  Orthogonality identifies the outer maps, and the five lemma identifies the
  middle map induced by $theta$. Yoneda then shows that $theta$ is an
  equivalence.
]

#definition(title:[Heart])[
  The #emph[heart] of the $t$-structure is

  $ C^(suit.heart) := C_(>=0) inter C_(<=0) $

  Define the homology-object functors by

  $ pi_0:=tau_(<=0) compose tau_(>=0)
    tilde.eq tau_(>=0) compose tau_(<=0), quad
    pi_n (x):=pi_0 (x[-n]) $
]

For $x,y in C^(suit.heart)$ and $r>0$, orthogonality gives

$ pi_r Map_C (x,y) tilde.eq Ext_C^(-r) (x,y) tilde.eq 0 $

Thus mapping spaces in $C^(suit.heart)$ are discrete, so this $oo$-category is
the nerve of its homotopy category. The category $h C^(suit.heart)$ is abelian;
kernels and cokernels are obtained by applying $pi_0$ to fibers and cofibers.
Our indexing is homological: the object above is denoted $pi_n (x)$ rather
than $"H"_n (x)$.

=== General Localizations

Not every localization of a stable $oo$-category comes from a $t$-structure.
Given a collection $S$ of morphisms, the localization $S^(-1) C$ is the full
subcategory of #emph[$S$-local] objects. An object $x$ is $S$-local when, for
every $f:y'->y$ in $S$, composition with $f$ induces an equivalence

$ Map_C (y,x) -> Map_C (y',x) $

To compare this with a $t$-structure, complete $f$ to a cofiber sequence

$ y' -> y -> y'' $

Applying $Ext_C^i (-,x)$ gives

$ dots -> Ext_C^i (y'',x) -> Ext_C^i (y,x)
  -> Ext_C^i (y',x) -> Ext_C^(i+1) (y'',x) -> dots $

Consequently, $x$ is $f$-local exactly when

$ Ext_C^i (y,x) -> Ext_C^i (y',x) $

is an isomorphism for every $i<=0$. In particular, locality implies
$Ext_C^i (y'',x)=0$ for $i<=0$, while vanishing for $i<=1$ is sufficient for
locality. If $y'$ is zero, the exact criterion reduces simply to
$Ext_C^i (y,x)=0$ for every $i<=0$.

== Some More Propositions

=== Quasisaturated Localizations

#definition(title:[Quasisaturated Collection])[
  Let $C$ admit pushouts. A collection $S$ of morphisms is
  #emph[quasisaturated] if

  1. every equivalence belongs to $S$;
  2. $S$ satisfies two-out-of-three for every composable pair;
  3. a pushout of a morphism in $S$ again belongs to $S$.

  Intersections of quasisaturated collections are quasisaturated. Hence every
  collection of maps has a smallest quasisaturated closure, called the
  collection it #emph[generates].
]

#definition(title:[Closed under Extensions])[
  A full subcategory $E subset C$ is #emph[closed under extensions] if, for
  every fiber--cofiber sequence $x->y->z$, the conditions $x,z in E$ imply
  $y in E$.
]

Let $L:C->C$ be an idempotent localization, let $C_L$ be its essential image,
and let $S_L$ be the collection of maps $f$ for which $L(f)$ is an
equivalence. The collection $S_L$ is quasisaturated.

#proposition(title:[$t$-Structure Localizations])[
  The following conditions are equivalent:

  1. $S_L$ is generated by a collection of maps of the form $0->a$;
  2. $S_L$ is generated by all $0->a$ such that $L a tilde.eq 0$;
  3. the local subcategory $C_L$ is closed under extensions;
  4. for $a in C$ and $b in C_L$, the map
     $Ext_C^1 (L a,b)->Ext_C^1 (a,b)$ is injective;
  5. $C_(>=0):={a | L a tilde.eq 0}$ and
     $C_(<=-1):={a | L a tilde.eq a}$ determine a $t$-structure on $C$.
]

#proofsketch[
  The implication (1)$arrow.r$(2) follows by enlarging the chosen generators
  to all $L$-acyclic objects. For (2)$arrow.r$(3), mapping an acyclic generator
  into a fiber sequence shows that an extension of local objects is local.

  If (3) holds, an extension of $L a$ by a local object has local middle term;
  consequently an extension class which becomes split after pullback along
  $a->L a$ was already split. This is (4).

  Under (4), the fiber sequence

  $ fib (a->L a) -> a -> L a $

  gives the required truncation sequence. Adjunction gives orthogonality, and
  the injectivity in (4) supplies the remaining shifted orthogonality. Hence
  the two classes in (5) form a $t$-structure. Finally, if (5) holds, the
  cofiber of every map inverted by $L$ is in $C_(>=0)$; pushouts and
  two-out-of-three show that the maps $0->a$ with $a in C_(>=0)$ generate all
  of $S_L$.
]

Thus the localizations arising as negative truncations are exactly those
generated, up to quasisaturation, by killing objects.

=== Boundedness and Completion

#definition(title:[Bounded Objects])[
  Let $C^+$ consist of the objects lying in some $C_(>=n)$, and let $C^-$
  consist of those lying in some $C_(<=n)$. Put

  $ C^b:=C^+ inter C^- $

  The $t$-structure is #emph[left bounded], #emph[right bounded], or
  #emph[bounded] when $C=C^+$, $C=C^-$, or $C=C^b$, respectively.
]

#definition(title:[Left Completion])[
  The #emph[left completion] $hat(C)$ is the $oo$-category of compatible
  Postnikov towers $(x_n)_(n in ZZ)$ with

  $ x_n in C_(<=n), quad tau_(<=n) x_(n+1) tilde.eq x_n $

  Equivalently,

  $ hat(C) tilde.eq lim_n C_(<=n) $

  The canonical functor is

  $ C->hat(C), quad x mapsto (tau_(<=n) x)_n $

  We call $C$ #emph[left complete] when this functor is an equivalence.
]

#proposition(title:[Basic Properties of Completion])[
  The left completion has the following properties:

  1. $hat(C)$ is stable and inherits a $t$-structure;
  2. the functor $C->hat(C)$ is exact and induces equivalences

     $ C_(<=n) tilde.eq hat(C)_(<=n) $

     for every $n$;
  3. it induces an equivalence $C^+ tilde.eq hat(C)^+$ on left bounded
     objects.
]

#proofsketch[
  Limits and cofibers of compatible towers are formed levelwise, with the
  shift reindexing the tower, so $hat(C)$ is stable. The two halves of its
  $t$-structure are detected levelwise. A tower bounded above stabilizes at
  the corresponding truncation, which proves (2); shifting proves (3).
]

In particular, left completion changes only objects which are unbounded
below. Passing to the left bounded part and taking left completion are inverse
constructions. Right completion and right completeness are defined dually.

#proposition(title:[Criterion for Left Completeness])[
  Suppose that $C$ admits countable products and that $C_(>=0)$ is closed
  under them. Then the following are equivalent:

  1. $C$ is left complete;
  2. the only object in $inter.big_(n in ZZ) C_(>=n)$ is the zero object.
]

#proofsketch[
  Every countable tower has a limit, computed by the fiber sequence

  $ lim_n x_n -> product_n x_n -->^(id-"shift") product_n x_n $

  Hence a compatible Postnikov tower has a limit in $C$. For every $x$, the
  cofiber of the completion map

  $ x -> lim_n tau_(<=n) x $

  belongs to every $C_(>=n)$. Condition (2) therefore makes this map an
  equivalence. Conversely, if $x$ belongs to every $C_(>=n)$, then all its
  truncations vanish; left completeness forces $x tilde.eq 0$.
]

== Filtered Objects and Spectral Sequences

Let $C$ be a stable $oo$-category with a $t$-structure and heart
$A tilde.eq C^(suit.heart)$. A #emph[filtered object] is a functor
$x:N(ZZ)->C$, depicted as

$ dots -> x_(-1) ->^(f^0) x_0 ->^(f^1) x_1 -> dots $

Its $p$th associated graded object is

$ "gr"^p x:=cofib (x_(p-1)->x_p) $

We now construct a spectral sequence in $A$ beginning with

$ E_1^(p,q) tilde.eq pi_(p+q) "gr"^p x $

=== Interval Cofibers

#definition(title:[Complex Associated to a Filtration])[
  Adjoin a least element $-oo$ to $ZZ$. The filtered object $x$ extends to an
  interval diagram with values $x_(i,j)$ for $-oo<=i<=j$, defined by

  $ x_(-oo,j):=x_j, quad x_(i,j):=cofib (x_i->x_j) $

  Thus $x_(i,i) tilde.eq 0$, and for $i<=j<=k$ there is a canonical
  fiber--cofiber sequence

  $ x_(i,j) -> x_(i,k) -> x_(j,k) -> x_(i,j)[1] $
]

Equivalently, the square with vertices $x_(i,j),x_(i,k),0,x_(j,k)$ is a
pushout. Conversely, every interval diagram satisfying these two properties
is determined by the filtration $x_(-oo,j)$. More precisely, restriction to
the $-oo$th row is an equivalence of $oo$-categories. Hence all interval
cofibers and connecting maps above are functorial and independent of choices
up to a contractible space.

#remark(title:[Underlying Chain Complex])[
  Set

  $ c_p:=x_(p-1,p)[-p] $

  The connecting maps of adjacent intervals give

  $ dots -> c_1 -> c_0 -> c_(-1) -> dots $

  in $h C$. Two consecutive maps compose to zero because they are adjacent
  boundary maps in a coherent pushout diagram. Thus every filtered object has
  a canonical chain complex of graded pieces in its triangulated homotopy
  category.
]

=== The Spectral Sequence

#proposition(title:[Spectral Sequence of a Filtered Object])[
  For $r>=1$, define an object of the heart by

  $ E_r^(p,q):=im (
      pi_(p+q) x_(p-r,p)
      -> pi_(p+q) x_(p-1,p+r-1)
    ) $

  The connecting maps of the interval sequences induce differentials

  $ d_r:E_r^(p,q)->E_r^(p-r,q+r-1) $

  They satisfy $d_r^2=0$, and there are natural isomorphisms

  $ E_(r+1)^(p,q)
    tilde.eq ker (d_r:E_r^(p,q)->E_r^(p-r,q+r-1))
      slash im (d_r:E_r^(p+r,q-r+1)->E_r^(p,q)) $

  In particular, $(E_r,d_r)$ is a spectral sequence in $A$, natural in the
  filtered object $x$.
]

#proofsketch[
  For $r=1$, both terms in the defining image are $x_(p-1,p)$, giving the
  announced $E_1$-page. For general $r$, the differential is induced by the
  boundary map between the two relevant interval cofibers. The pushout
  identities imply that two successive boundary maps compose to zero.
  Exactness in the heart then identifies the image defining $E_(r+1)$ with
  the kernel of $d_r$ modulo the image of the incoming $d_r$.
]

The differential has bidegree $(-r,r-1)$ and lowers total degree by one. On
the first page one may equivalently write

$ E_1^(p,q) tilde.eq pi_q c_p $

so $d_1$ is simply the homology differential obtained from the underlying
chain complex of graded pieces.

#remark[
  If $C$ is the derived $oo$-category of an abelian category and $x$ is a
  filtered chain complex, this construction recovers the classical spectral
  sequence of a filtered complex. The interval-diagram formulation is useful
  because it makes every higher differential canonical and functorial.
]

=== Convergence

#definition(title:[Compatibility with Sequential Colimits])[
  The $t$-structure on $C$ is #emph[compatible with sequential colimits] if
  $C$ admits colimits indexed by $NN$ and $C_(<=0)$ is closed under them.
  Under this assumption the functors $pi_n:C->A$ preserve sequential
  colimits, and sequential colimits in the heart are exact.
]

#proposition(title:[Convergence for a Bounded-Below Filtration])[
  Suppose the $t$-structure is compatible with sequential colimits and
  $x_p tilde.eq 0$ for all sufficiently negative $p$. Put

  $ x_oo:=colim_p x_p, quad a_n:=pi_n x_oo $

  Then the spectral sequence converges to $pi_* x_oo$. Explicitly, for fixed
  $(p,q)$ the differentials eventually vanish, and $a_n$ has the exhaustive
  increasing filtration

  $ F^p a_n:=im (pi_n x_p->a_n) $

  whose associated graded pieces are

  $ E_oo^(p,q) tilde.eq F^p a_(p+q) slash F^(p-1) a_(p+q) $
]

#proofsketch[
  The lower bound makes the incoming and outgoing intervals defining
  $d_r$ eventually constant or zero, so every bidegree stabilizes. Since
  $pi_n$ commutes with the sequential colimit, the images of
  $pi_n x_p->pi_n x_oo$ form an exhaustive filtration. Applying the long
  exact sequence to

  $ x_(p-1) -> x_p -> "gr"^p x $

  identifies the stable page with the indicated subquotient.
]

== The Dold--Kan Correspondence

The classical Dold--Kan correspondence says that a simplicial object in an
abelian category is exactly a chain complex concentrated in nonnegative
degrees. Its stable $oo$-categorical form replaces chain complexes by
nonnegative filtrations; this retains all higher coherences and connects
directly with the preceding spectral sequence.

=== Normalization and Denormalization

Let $A$ be an abelian category and let
$x:Delta^op->A$ be a simplicial object, with face maps $d_i$ and degeneracy
maps $s_i$. Its #emph[normalized chain complex] $N x$ is defined by

$ N_n x:=inter_(i=1)^n ker (d_i:x_n->x_(n-1)),
  quad partial:=d_0:N_n x->N_(n-1) x $

The simplicial identities give $partial^2=0$. If

$ D_n x:=sum_(i=0)^(n-1) im (s_i) $

is the degenerate subobject, then there is a canonical decomposition

$ x_n tilde.eq N_n x ⊕ D_n x $

More generally, in an additive category the normalized piece is the image of
the idempotent

$ p_n:=(1-s_(n-1)d_n) dots (1-s_0d_1) $

whenever this idempotent splits.

#definition(title:[The Dold--Kan Functor])[
  Let $c=(c_n,partial)$ be a chain complex in nonnegative degrees. The
  #emph[Dold--Kan functor] constructs a simplicial object $"DK" (c)$ whose
  degree-$n$ object is

  $ "DK"(c)_n tilde.eq
    ⊕_(eta:[n] arrow.r.twohead [k]) c_k $

  where the sum runs over all order-preserving surjections
  $eta:[n] arrow.r.twohead [k]$. For $alpha:[m]->[n]$, factor

  $ eta compose alpha:[m] arrow.r.twohead [ell] arrow.r.hook [k] $

  into a surjection followed by an injection. On the $eta$-summand, the
  induced structure map is the identity if the injection is the identity,
  is $partial:c_k->c_(k-1)$ if it omits only $0$, and is zero otherwise.
  This rule defines all faces and degeneracies; the equality $partial^2=0$
  gives the simplicial identities.
]

Thus the copies indexed by nonidentity surjections freely supply exactly the
degenerate simplices missing from a chain complex. For example, a complex
concentrated in degree zero gives a constant simplicial object, while a
complex with $a$ in degree one and zero differential has
$"DK" (a[1])_n tilde.eq a^(⊕ n)$.

#theorem(title:[Classical Dold--Kan])[
  For every additive category $A$, the functor

  $ "DK":"Ch"_(>=0) (A)->Fun (Delta^op,A) $

  is fully faithful. It is an equivalence when $A$ is idempotent complete.
  In particular, for every abelian category there are inverse equivalences

  $ "DK":"Ch"_(>=0) (A) arrows.lr^~
    Fun (Delta^op,A):N $
]

#proofsketch[
  The simplicial identities produce a normalization idempotent on $x_n$.
  Its image is $N_n x$, and splitting the complementary degeneracy
  idempotents yields the canonical decomposition

  $ x_n tilde.eq ⊕_(eta:[n] arrow.r.twohead [k]) N_k x $

  This identifies $N "DK" (c)$ with $c$ and $"DK" (N x)$ with $x$.
  Additivity is enough for full faithfulness; idempotent completeness is
  exactly what guarantees the required splittings and hence essential
  surjectivity. In an abelian category the normalization can equivalently be
  formed by the displayed intersections of kernels.
]

#corollary[
  If $x$ is a simplicial abelian group, then its underlying simplicial set is
  a Kan complex and

  $ pi_n (x) tilde.eq "H"_n (N x) $

  Thus simplicial homotopy groups become ordinary homology groups under
  normalization.
]

=== Stable Dold--Kan

For a stable $oo$-category $C$, write

$ "Fil"_(>=0) (C):=Fun (Ner(NN),C),
  quad "s"C:=Fun (Ner(Delta)^op,C) $

Objects of the first category are sequences $d_0->d_1->dots$, while objects
of the second are simplicial objects of $C$.

#theorem(title:[Stable Dold--Kan])[
  Every stable $oo$-category $C$ admits inverse equivalences

  $ "DK":"Fil"_(>=0) (C) arrows.lr^tilde "s"C : N^"st" $

  No $t$-structure, countable colimits, or idempotent-completeness assumption
  is required.
]

The stable normalization $N^"st"$ sends a simplicial object $x$ to its
skeletal filtration

$ d_n:=abs("sk"_n x) $

where $abs("sk"_n x)$ is the finite geometric realization of the
$n$-skeleton.
If $ell_n x$ denotes the latching object, stability gives

$ cofib (d_(n-1)->d_n)[-n]
  tilde.eq cofib (ell_n x->x_n) $

The right-hand side is the stable normalized object in degree $n$. Hence the
underlying chain complex of this filtration is the normalized chain complex
of $x$ in $h C$. The equivalence itself contains the higher null-homotopies
and compatibilities which that chain complex alone forgets.

#remark(title:[Relation with the Spectral Sequence])[
  Suppose $C$ has a $t$-structure with heart $A$. Applying $pi_q$ degreewise
  to $x$ gives a simplicial object of $A$, and the first page of the spectral
  sequence of its skeletal filtration is

  $ E_1^(p,q) tilde.eq N_p (pi_q x) $

  Its first differential is the normalized differential. If the geometric
  realization exists and the convergence hypotheses above hold, then

  $ E_1^(p,q) arrow.r.double.long pi_(p+q) abs(x) $

  In this sense the stable Dold--Kan equivalence is the structural source of
  the spectral sequence attached to a simplicial object.
]

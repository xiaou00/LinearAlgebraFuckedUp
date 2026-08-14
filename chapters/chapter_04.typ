#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.5.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Spectra

== Why We Need Spectra?

=== "Linear" Matters

Since the title of this book is actually "Linear Algebra", we have to fix one thing: since the homotopy theory of pointed spaces is not "linear". For pointed spaces $X,Y$, consider
$ [X,Y]_* := pi_0 Map_* (X,Y) $
to be the homotopy classes of pointed maps, it is only a set, not a group. Things changes if $X$ is a suspension
$ X = Sigma X' $
then, through
$ Map_* (Sigma X',Y) tilde.eq Map_* (X',Omega Y) $
We have
$ [Sigma X',Y]_* = pi_1 Map_* (X',Y) $
naturally has a group structure. And if we suspension it again by
$ X = Sigma^2 X'' $
then we have
$ [Sigma^2 X'',Y]_* = pi_2 Map_* (X'',Y) $
which is an abelian group. In fact, by suspending the space enough times, making the homotopy theory more and more "linear".

By this idea, we would like to consider
$ [X,Y]_* -> [Sigma X,Sigma Y]_* -> [Sigma^2 X, Sigma^2 Y]_* -> ... $
and take the limit
$ [X,Y]^s = varinjlim(n) [Sigma^n X,Sigma^n Y] $
called the #emph[stable homotopy classes of maps] from $X$ to $Y$.For fine spaces, this forms an abelian group.

=== Inverting Suspension

There is a fatal problem exists in the suspension of pointed animae, which is that the suspension functor
$ Sigma: Ani_* -> Ani_* $
is not invertible, there does not exist a functor
$ Sigma^(-1): Ani_* -> Ani_* $
corresponding to the inverse of suspension (i.e. we want the $oo$-category to be stable). Stable homotopy theory wants to invert the suspension functor, and this is the main reason why we need #emph[spectra], which is a world where suspension forms an equivalence.
$ Sigma: Sp ->^~ Sp $
just like the $[1]$ functor on the derived category of an abelian category.

== Brown Representability Theorem

From now on, we will build a relation between cohomology theory and the theory of spectra, we will start with the Brown representability theorem, which is a very important theorem in stable homotopy theory.

=== Generalized Cohomology Theories

#definition(title:[Reduced Generalized Cohomology Theory])[
  A #emph[reduced generalized cohomology theory] on pointed CW complexes is a
  family of contravariant functors

  $ E^q:(h cat("CW")_*)^op->Ab quad (q in ZZ) $

  with the following properties.

  1. #emph[Reducedness.] $E^q (ast)=0$ for every $q$.

  2. #emph[Suspension.] There are natural isomorphisms

     $ E^q (x) tilde.eq E^(q+1) (Sigma x) $

  3. #emph[Exactness.] Every cofiber sequence

     $ a->x->x slash a->Sigma a $

     induces a natural long exact sequence

     $ dots->E^q (x slash a)->E^q (x)->E^q (a)
       ->E^(q+1) (x slash a)->dots $

  4. #emph[Wedge axiom.] For every family ${x_alpha}$,

     $ E^q (⋁_alpha x_alpha)
       tilde.eq product_alpha E^q (x_alpha) $

  The adjective #emph[generalized] means that no dimension axiom is imposed.
]

Thus $E^q$ is the degree-$q$ cohomology functor, not the $q$th power of a
single functor. Exactness implies the Mayer--Vietoris gluing property, while
the wedge axiom is already one of the Brown axioms. Consequently, after
forgetting the abelian-group structure, every $E^q$ is a Brown functor.

#example[
  Reduced singular cohomology $tilde("H")^q (-;G)$ is the basic example. Its
  dimension axiom says

  $ tilde("H")^0 (S^0;G) tilde.eq G,
    quad tilde("H")^q (S^0;G) tilde.eq 0 quad (q!=0) $

  Generalized theories such as topological $K$-theory need not satisfy this
  axiom.
]

#remark(title:[Homology versus Cohomology])[
  A reduced generalized #emph[homology] theory is instead a covariant family

  $ E_q:h cat("CW")_*->Ab $

  which sends wedges to direct sums and cofiber sequences to long exact
  sequences. Brown representability below directly concerns the
  contravariant cohomology functors $E^q$. Homology theories acquire their
  representing description after passing to spectra.
]

=== Classical Version

Let $h cat("CW")_*$ denote the homotopy category of pointed CW complexes.

#definition(title:[Brown Functor])[
  A contravariant functor

  $ F:(h cat("CW")_*)^op->Set_* $

  is a #emph[Brown functor] if it satisfies:

  1. #emph[Wedge axiom.]

     $ F(⋁_alpha x_alpha)
       tilde.eq product_alpha F(x_alpha) $

  2. #emph[Mayer--Vietoris axiom.] If $x=a union b$ is a union of pointed
     subcomplexes whose interiors cover $x$, then

     $ F(x)->F(a) times_(F(a inter b)) F(b) $

     is surjective.
]

Every representable functor $[-,y]_*$ has these properties. The wedge axiom
is the coproduct universal property, while Mayer--Vietoris follows from the
homotopy extension property for inclusions of CW subcomplexes.

#theorem(title:[Classical Brown Representability])[
  Every Brown functor is representable. More precisely, there exist a pointed
  CW complex $y$ and a universal class $u in F(y)$ such that

  $ T_u:[x,y]_*->F(x), quad [f] mapsto f^*u $

  is a natural bijection for every pointed CW complex $x$. The representing
  space $y$ is unique up to pointed homotopy equivalence.
]

#proofsketch[
  The representing pair $(y,u)$ is built by cells. First wedge onto $y$
  enough spheres so that every class in $F(S^n)$ is the pullback of $u$;
  this forces surjectivity on spheres. Next attach cells along every map
  $S^n->y$ which pulls $u$ back to the basepoint; the Mayer--Vietoris axiom
  extends $u$ across these cells and kills the kernel. Repeating this in every
  dimension and taking a mapping telescope gives

  $ [S^n,y]_* tilde.eq F(S^n) $

  for all $n$.

  A relative version of the same cell construction extends a map
  $a->y$ from a CW subcomplex $a subset x$ whenever its pullback of $u$
  agrees with a prescribed class in $F(x)$. Taking $a=ast$ proves that
  $T_u$ is surjective. Applying the relative statement to the two ends of a
  cylinder shows that two maps with the same pullback of $u$ are homotopic,
  so $T_u$ is injective. Whitehead's theorem upgrades the weak equivalences
  arising in the construction to homotopy equivalences, and Yoneda gives
  uniqueness of $y$.
]

#remark(title:[From Cohomology Theories to Spectra])[
  Let ${E^q}_(q in ZZ)$ be a reduced generalized cohomology theory on pointed
  CW complexes. Each functor $E^q$ satisfies the wedge and
  Mayer--Vietoris axioms, so Brown representability gives pointed CW
  complexes $e_q$ with

  $ E^q (x) tilde.eq [x,e_q]_* $

  The suspension isomorphism and the suspension--loop adjunction give

  $ [x,e_q]_* tilde.eq [Sigma x,e_(q+1)]_*
    tilde.eq [x,Omega e_(q+1)]_* $

  Yoneda therefore yields equivalences

  $ e_q tilde.eq Omega e_(q+1) $

  Hence the representing spaces assemble into an $Omega$-spectrum. This is
  the classical reason that spectra represent generalized cohomology
  theories.
]

=== Representability in an $oo$-Category

Let $C$ be an $oo$-category. A space-valued presheaf

$ P:C^op->Ani $

is #emph[representable] if there is an object $y in C$ and a natural
equivalence

$ P(x) tilde.eq Map_C (x,y) $

for every $x in C$. By the $oo$-categorical Yoneda lemma, choosing such an
equivalence is the same as choosing a #emph[universal element] $u in P(y)$
for which evaluation induces the displayed equivalences. The representing
object is unique up to equivalence.

Passing to connected components gives the ordinary representable functor

$ Hom_(h C) (-,y) tilde.eq pi_0 Map_C (-,y) $

on the homotopy category. Accordingly, a functor
$F:(h C)^op->Set$ is representable when there are $y in C$ and $u in F(y)$
such that

$ Hom_(h C) (x,y)->F(x), quad [f] mapsto f^*u $

is a bijection for every $x$. The theorem below concerns this Set-valued
notion: it reconstructs the representing object from the behavior of $F$ on
colimits in the underlying $oo$-category.

For an ordinary presentable category $D$, the adjoint functor theorem says
that $F:D^op->Set$ is representable exactly when it carries colimits in $D$
to limits of sets. The difficulty here is that $h C$ need not possess the
colimits which exist in $C$. Brown representability replaces that unavailable
criterion by conditions imposed directly on coproducts and pushouts in $C$.

#remark(title:[Basic Principle])[
  A representable contravariant functor turns colimits into limits, since

  $ Map_C (colim_i x_i,y) tilde.eq lim_i Map_C (x_i,y) $

  After applying $pi_0$, arbitrary coproducts still become products. For a
  pushout, connected components retain the existence, but not necessarily
  the uniqueness, of a gluing; this explains the surjectivity condition in
  Brown representability.
]

=== Cogroup Objects and Compact Generators

#definition(title:[Cogroup Object])[
  Let $D$ be a category with finite coproducts. A #emph[cogroup object] is an
  object $s in D$ equipped with a comultiplication

  $ Delta:s->s coprod s $

  together with a counit and coinverse, such that for every $y in D$ the
  induced operation

  $ Hom_D (s,y) times Hom_D (s,y)
    tilde.eq Hom_D (s coprod s,y)
    ->^Delta^* Hom_D (s,y) $

  is a group law. Equivalently, $Hom_D (s,-)$ naturally takes values in
  groups.
]

The guiding example is a suspension. If $C$ admits finite colimits and
$x->emptyset$ is a map to its initial object, then

$ Sigma x:=emptyset coprod_x emptyset $

is a cogroup object of $h C$. Indeed,
$Hom_(h C) (Sigma x,y)$ is a fundamental group of a mapping space, and its
group operation is loop concatenation. In a stable $oo$-category, $h C$ is
additive, so every object is a cogroup object; the comultiplication is the
diagonal $s->s plus s$ and the coinverse is $-id_s$.

#definition(title:[Compact Generators])[
  An object $s in C$ is #emph[compact] if $Map_C (s,-)$ preserves filtered
  colimits. A set ${s_alpha}_(alpha in A)$ #emph[generates $C$ under small
  colimits] if the smallest full subcategory containing every $s_alpha$ and
  closed under equivalences and small colimits is all of $C$.
]

Compactness lets maps out of $s_alpha$ detect a colimit at a finite stage;
generation means that the functors $Map_C (s_alpha,-)$ jointly detect
equivalences. These properties abstract the roles played by spheres and CW
cells in the classical proof.

=== General Brown Representability

#theorem(title:[Brown Representability])[
  Let $C$ be a presentable $oo$-category containing a set
  ${s_alpha}_(alpha in A)$ such that:

  1. every $s_alpha$ is a cogroup object of $h C$;
  2. every $s_alpha$ is compact;
  3. the objects $s_alpha$ generate $C$ under small colimits.

  Then a functor $F:(h C)^op->Set$ is representable if and only if it
  satisfies the following conditions.

  1. For every collection ${c_beta}$, the canonical map

     $ F(coprod_beta c_beta)->product_beta F(c_beta) $

     is a bijection.

  2. For every pushout $d' tilde.eq c' coprod_c d$, the canonical map

     $ F(d')->F(c') times_(F(c)) F(d) $

     is surjective.
]

#proofsketch[
  Necessity follows from the mapping-space formula above. For sufficiency,
  begin with a pair $(x,u)$ and coproduct copies of the generators until

  $ Hom_(h C) (s_alpha,x)->F(s_alpha) $

  is surjective for every $alpha$. Use pushouts to kill its kernels, and
  iterate. Cogroup structures make these kernels groups, compactness lets
  maps from $s_alpha$ factor through a finite stage, and generation shows
  that the resulting universal pair represents $F$ on every object. This is
  exactly the classical argument #emph[add generators, then kill relations],
  with compact cogroup generators replacing spheres.
]

#corollary[
  Every compactly generated presentable stable $oo$-category satisfies the
  hypotheses of Brown representability, because every object of its homotopy
  category is a cogroup object. In particular, a contravariant functor on its
  homotopy category is representable exactly when it takes coproducts to
  products and pushouts to weak pullbacks of sets.
]

For connected pointed spaces, the compact cogroup generator is $S^1$; its
suspensions detect all higher homotopy groups. Thus the generalized theorem
recovers the classical Brown theorem, while its stable case is the form that
will be used for spectra.

#remark(title:[From Cohomology to Homotopy])[
  Brown representability turns a reduced generalized cohomology theory into
  homotopy-theoretic data. If $e_q$ represents $E^q$, then

  $ E^q (x) tilde.eq [x,e_q]_*,
    quad E^q (S^m) tilde.eq pi_m (e_q) $

  Thus cohomology classes are homotopy classes of maps, and the coefficient
  groups of the theory are homotopy groups of the representing spaces.
  Moreover, Yoneda identifies a natural cohomology operation
  $E^q->E'^r$ with a homotopy class of maps $e_q->e'_r$.

  The suspension axiom organizes the spaces $e_q$ into an $Omega$-spectrum,
  so a whole cohomology theory becomes a single stable homotopy type. Brown's
  theorem directly concerns contravariant cohomology theories. Covariant
  homology theories enter after stabilization: a representing spectrum $e$
  defines homology by the homotopy groups of $e smash Sigma^oo x$.
]

== Spectrum Objects

Spectrum objects are the basic device for extracting stable information from
an unstable $oo$-category. The key input is #emph[excision]: a linear functor
should turn a gluing problem into a pullback problem.

=== Reduced Excisive Functors

The classical model is singular homology. The simplicial abelian group
$ZZ "Sing"(x)_bullet$ is a Kan complex and

$ "H"_n (x;ZZ) tilde.eq pi_n (ZZ "Sing"(x)_bullet) quad (n>=0) $

For an open cover $x=u union v$, the Mayer--Vietoris sequence is obtained by
applying homotopy groups to the homotopy pullback square associated with
$u$, $v$, $u inter v$, and $x$. This is the prototype for the
following definition.

#definition(title:[Reduced Excisive Functor])[
  Let $C$ admit pushouts and let $D$ admit pullbacks. A functor
  $F:C->D$ is #emph[excisive] if it carries every pushout square in $C$ to a
  pullback square in $D$.

  If $C$ and $D$ have final objects, then $F$ is #emph[reduced] if it carries
  a final object of $C$ to a final object of $D$. We write

  $ Exc_* (C,D) subset.eq Fun(C,D) $

  for the full subcategory of reduced excisive functors.
]

#remark(title:[Excision Is Exactness])[
  If $C$ and $D$ are stable, a functor $F:C->D$ is reduced and excisive if
  and only if it is exact. Thus excision is the unstable formulation of the
  familiar requirement that a linear functor preserve exact triangles.

  Equivalently, $F$ is exact precisely when it preserves zero objects and
  the canonical map

  $ Sigma_D F(x)->F(Sigma_C x) $

  is an equivalence for every $x$.
]

There is a useful one-object test for excision. Let $C$ be pointed with
finite colimits, let $D$ be pointed with finite limits, and let $F:C->D$ be
reduced. Applying $F$ to the suspension square of $x$ produces a canonical
map

$ eta_x:F(x)->Omega_D F(Sigma_C x) $

#proposition(title:[Suspension Test for Excision])[
  The functor $F$ is excisive if and only if $eta_x$ is an equivalence for
  every $x in C$.
]

#proofsketch[
  If $F$ is excisive, it sends the suspension pushout of $x$ to the pullback
  defining $Omega_D F(Sigma_C x)$. Conversely, compare an arbitrary pushout
  square with the four suspension squares of its vertices. The maps
  $eta_x$ identify the resulting comparison map with an equivalence, so the
  image square is a pullback.
]

=== The Definition of a Spectrum Object

Let $Ani_*^"fin"$ be the $oo$-category of finite pointed animae. It is
generated by $S^0$ under finite colimits.

#definition(title:[Spectrum Object])[
  Let $C$ be an $oo$-category with finite limits. A #emph[spectrum object]
  of $C$ is a reduced excisive functor

  $ x:Ani_*^"fin"->C $

  The full $oo$-category of spectrum objects is

  $ Sp(C):=Exc_* (Ani_*^"fin",C) $
]

#remark(title:[Why Does This Definition Produce Spectra?])[
  At first sight, a spectrum object is merely a functor in
  $Fun(Ani_*^"fin",C)$. The reduced and excisive conditions force this
  functor to contain an infinite sequence of deloopings.

  For every $n>=0$, the suspension square

  #align(center, diagram({
    node((0, 0), [$S^n$])
    node((1, 0), [$ast$])
    node((0, 1), [$ast$])
    node((1, 1), [$Sigma S^n tilde.eq S^(n+1)$])
    edge((0, 0), (1, 0), "->")
    edge((0, 0), (0, 1), "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 1), (1, 1), "->")
  }))

  is a pushout in $Ani_*^"fin"$. Applying $x$ gives

  #align(center, diagram({
    node((0, 0), [$x(S^n)$])
    node((1, 0), [$x(ast)$])
    node((0, 1), [$x(ast)$])
    node((1, 1), [$x(S^(n+1))$])
    edge((0, 0), (1, 0), "->")
    edge((0, 0), (0, 1), "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 1), (1, 1), "->")
  }))

  Reducedness says $x(ast)$ is terminal, while excision says that the second
  square is a pullback. Therefore

  $ x(S^n)
    tilde.eq ast times_(x(S^(n+1))) ast
    tilde.eq Omega x(S^(n+1)) $

  Setting $x_n:=x(S^n)$ gives coherent equivalences

  $ x_n tilde.eq Omega x_(n+1) $

  Hence one reduced excisive functor automatically contains the infinite
  delooping data

  $ x_0 tilde.eq Omega x_1,
    quad x_1 tilde.eq Omega x_2,
    quad x_2 tilde.eq Omega x_3,
    quad dots $
]

The functor

$ Omega^oo:Sp(C)->C, quad x mapsto x_0 $

is evaluation at $S^0$. More precisely, if $C_*$ denotes the $oo$-category
of pointed objects of $C$, then

$ Sp(C) tilde.eq lim(dots->^Omega C_*->^Omega C_*) $

When $C$ is already pointed, this becomes the tower displayed at the
beginning of this section.

#remark(title:[Finite versus Compact])[
  The category $Ani_*^"fin"$ need not contain every compact pointed anima.
  The full subcategory of compact objects of $Ani_*$ is its idempotent
  completion. The finite category is the one used above because of its
  universal property under finite colimits.
]

=== Classical Sequential Spectra

The classical point-set model makes the tower of deloopings explicit.

#definition(title:[Sequential Spectrum])[
  A #emph[sequential prespectrum] is a sequence of pointed spaces
  $(x_0,x_1,dots)$ equipped with structure maps

  $ sigma_n:Sigma x_n->x_(n+1) $

  Equivalently, by adjunction, it has maps

  $ tilde(sigma)_n:x_n->Omega x_(n+1) $

  It is an #emph[$Omega$-spectrum] if every $tilde(sigma)_n$ is a weak
  homotopy equivalence.
]

For $k in ZZ$, the stable homotopy group of a prespectrum $x$ is

$ pi_k^s (x):=varinjlim(n) pi_(k+n) (x_n) $

where $n$ is taken sufficiently large that $k+n>=0$. A map is a
#emph[stable equivalence] if it induces an isomorphism on every $pi_k^s$.
The classical stable homotopy category is obtained by inverting these maps.
Every sufficiently well-behaved prespectrum admits a spectrification
$x->q x$ to an $Omega$-spectrum with the same stable homotopy groups.

#example(title:[Basic Spectra])[
  For a pointed space $x$, its suspension prespectrum has levels

  $ (Sigma^oo x)_n:=Sigma^n x $

  After spectrification this defines the suspension spectrum
  $Sigma^oo x in Sp$. In particular,

  $ SS:=Sigma^oo S^0 $

  is the sphere spectrum, and its homotopy groups are the stable stems

  $ pi_k (SS) tilde.eq varinjlim(n) pi_(k+n) (S^n) $

  If $a$ is an abelian group, the Eilenberg--Mac Lane spectrum $"H"a$ has
  spaces $K(a,n)$ and structure equivalences

  $ K(a,n) tilde.eq Omega K(a,n+1) $

  It is characterized by $pi_0 ("H"a) tilde.eq a$ and
  $pi_k ("H"a) tilde.eq 0$ for $k!=0$. Ordinary reduced cohomology is then
  represented by

  $ tilde("H")^q (x;a)
    tilde.eq [Sigma^oo x,Sigma^q "H"a]_Sp $
]

#remark(title:[Classical versus $oo$-Categorical Spectra])[
  The two descriptions encode the same stable homotopy theory.

  #align(center, table(
    columns: (1fr, 1fr),
    align: left + horizon,
    inset: (x: 10pt, y: 4pt),
    stroke: none,
    table.hline(y: 1, stroke: 0.65pt + muted),
    table.vline(x: 1, stroke: 0.65pt + muted),
    text(weight: "semibold", fill: ink)[classical model],
    text(weight: "semibold", fill: ink)[$oo$-categorical model],
    [spaces $x_n$ and maps $Sigma x_n->x_(n+1)$],
    [a functor $Ani_*^"fin"->Ani$],
    [$Omega$-spectrum condition],
    [reduced excision],
    [invert stable equivalences],
    [equivalences already encode localization],
    [chosen point-set structure maps],
    [all homotopy coherences retained],
  ))

  More precisely, localizing any standard model category of classical
  spectra at its stable equivalences presents the $oo$-category
  $Sp tilde.eq Sp(Ani)$. Thus an $oo$-categorical spectrum should be compared
  with the stable homotopy type of a classical spectrum, not with one chosen
  point-set presentation.
]

=== Stability

#theorem(title:[Stability Criterion])[
  For a pointed $oo$-category $C$, the following conditions are equivalent.

  1. The $oo$-category $C$ is stable.

  2. It admits finite colimits and $Sigma_C:C->C$ is an equivalence.

  3. It admits finite limits and $Omega_C:C->C$ is an equivalence.
]

#proofsketch[
  In a stable $oo$-category, pushouts and pullbacks agree, so suspension and
  looping are inverse equivalences. Conversely, if looping is invertible,
  every pullback can be delooped into a pushout; hence pullbacks and
  pushouts agree. The suspension version is dual.
]

#theorem(title:[Stability of Excisive Functors])[
  Let $C$ be pointed and admit finite colimits, and let $D$ admit finite
  limits. Then $Exc_* (C,D)$ is a stable $oo$-category. In particular,
  $Sp(D)$ is stable.
]

#proofsketch[
  Reduced excisive functors are closed under finite limits, which are
  computed pointwise. Their loop functor is also pointwise, and the
  suspension test identifies it with an equivalence. The stability criterion
  therefore applies. Taking $C=Ani_*^"fin"$ gives the assertion for spectrum
  objects.
]

#corollary(title:[Recognizing Stability by Spectrum Objects])[
  Let $C$ admit finite limits. Then $C$ is stable if and only if evaluation
  at $S^0$ is an equivalence

  $ Omega_C^oo:Sp(C)->^tilde C $

  In this case, we denote its inverse by

  $ Sigma_C^oo:C->^tilde Sp(C) $

  Thus

  $ Omega_C^oo Sigma_C^oo tilde.eq id_C,
    quad Sigma_C^oo Omega_C^oo tilde.eq id_(Sp(C)) $

  For $c in C$, the spectrum $Sigma_C^oo c$ is determined levelwise by

  $ (Sigma_C^oo c)_n tilde.eq Sigma_C^n c $
]

#proofsketch[
  If $C$ is stable, then $Omega_C$ is an equivalence, so the tower

  $ dots->^(Omega_C) C->^(Omega_C) C $

  is essentially constant. Its limit is therefore $C$, and evaluation at
  the zeroth level is an equivalence. Conversely, $Sp(C)$ is stable; hence
  an equivalence $Sp(C) tilde.eq C$ transports the stable structure to $C$.
]

#remark[
  In general, $Sigma^oo$ denotes the suspension-spectrum or stabilization
  functor and is left adjoint to $Omega^oo$ when this adjoint exists. It is
  only when $C$ is already stable that this adjunction becomes an adjoint
  equivalence and $Sigma_C^oo$ is literally the inverse of $Omega_C^oo$.
]

=== The Universal Property of Stabilization

#theorem(title:[Universal Property])[
  Let $C$ be pointed and admit finite colimits, and let $D$ admit finite
  limits. Composition with evaluation at $S^0$ induces an equivalence

  $ Exc_* (C,Sp(D))->^tilde Exc_* (C,D) $
]

Hence every reduced excisive functor $C->D$ has an essentially unique
refinement whose values are coherent spectrum objects. Taking
$C=Ani_*^"fin"$ shows in particular that stabilization is idempotent

$ Sp(Sp(D)) tilde.eq Sp(D) $

#remark(title:[Formal Properties])[
  Spectrum objects and their limits are computed pointwise. Consequently,
  for every simplicial set $K$ there is a natural equivalence

  $ Sp(Fun(K,C)) tilde.eq Fun(K,Sp(C)) $

  If $C$ is presentable, the reduced and excisive conditions define an
  accessible localization of a functor category. Hence $Sp(C)$ is again
  presentable, as well as stable.
]

#remark(title:[Homology Theories])[
  A reduced spectrum-valued homology theory is, at its core, a reduced
  excisive functor

  $ E:Ani_*^"fin"->Sp $

  and its graded groups are recovered by

  $ E_n (x):=pi_n E(x) $

  Excision produces Mayer--Vietoris long exact sequences, while preservation
  of arbitrary wedges supplies the usual wedge axiom when the theory is
  extended from finite pointed animae to all pointed animae. Thus the
  spectrum packages all degrees and all connecting maps of a homology theory
  into one object.
]

== $oo$-Category of Spectra

=== Spectrum

The most important example of a stable $oo$-category is the category of
spectra itself. The preceding construction turns the classical sequence of
spaces and deloopings into the following intrinsic definition.

#definition(title:[The $oo$-Category of Spectra])[
  A #emph[spectrum] is a spectrum object of the $oo$-category of animae. We
  write

  $ Sp:=Sp(Ani) tilde.eq Sp(Ani_*) $

  for the $oo$-category of spectra. Equivalently,

  $ Sp tilde.eq Exc_* (Ani_*^"fin",Ani) $
]

#proposition(title:[Equivalent Sequential Description])[
  Equivalently, a spectrum is a sequence of pointed animae

  $ x=(x_0,x_1,x_2,dots) $

  together with coherent equivalences

  $ epsilon_n:x_n->^tilde Omega x_(n+1) quad (n>=0) $

  A morphism $f:x->y$ is a sequence of pointed maps
  $f_n:x_n->y_n$ compatible, up to coherent homotopy, with the equivalences
  $epsilon_n$. In particular,

  $ Sp tilde.eq lim(dots->^Omega Ani_*->^Omega Ani_*) $

  and the infinite-loop-space functor is evaluation at the zeroth term

  $ Omega^oo x tilde.eq x_0 $
]

#remark[
  This is the intrinsic $oo$-categorical version of a classical
  $Omega$-spectrum. The word #emph[coherent] is essential: besides the
  equivalences $x_n tilde.eq Omega x_(n+1)$, the $oo$-categorical limit keeps
  all higher compatibilities automatically. Thus one may safely remember a
  spectrum as the infinite delooping sequence

  $ x_0 tilde.eq Omega x_1,
    quad x_1 tilde.eq Omega x_2,
    quad x_2 tilde.eq Omega x_3,
    quad dots $
]

#definition(title:[Sphere Spectrum])[
  The #emph[sphere spectrum] is the suspension spectrum of the pointed
  $0$-sphere

  $ SS:=Sigma^oo S^0 in Sp $

  In the classical sequential model it is represented by the suspension
  prespectrum

  $ S^0, S^1, S^2, dots $

  with the canonical structure maps $Sigma S^n tilde.eq S^(n+1)$, followed
  by spectrification. Its homotopy groups are the stable stems

  $ pi_k (SS) tilde.eq varinjlim(n) pi_(k+n) (S^n) $
]

#remark(title:[The Stable Homotopy Analogue of $ZZ$])[
  The sphere spectrum plays the role of the integers in stable homotopy
  theory. The analogy is structural:

  - $ZZ$ is the tensor unit in $Ab$, while $SS$ is the smash-product unit in
    $Sp$

    $ ZZ ⊗ a tilde.eq a,
      quad SS smash x tilde.eq x $

  - $ZZ$ is the free rank-one generator of $Ab$, while $SS$ is a compact
    generator of $Sp$; maps from its shifts recover every homotopy group

    $ Hom_(h#h(0pt)Sp) (Sigma^n SS,x) tilde.eq pi_n (x) $

  - Their endomorphisms in degree zero agree

    $ End_(h#h(0pt)Sp) (SS) tilde.eq pi_0 (SS) tilde.eq ZZ $

  However, $SS$ is not the Eilenberg--Mac Lane spectrum $"H"ZZ$. The latter
  has only one nonzero homotopy group, whereas the higher stable stems
  $pi_n (SS)$ retain genuinely homotopical information. Thus $SS$ is the
  homotopically enriched analogue of $ZZ$, not merely $ZZ$ regarded as a
  spectrum.
]

#remark(title:[Relation with the Classical Category])[
  The homotopy category $h#h(0pt)Sp$ is the classical stable homotopy category.
  In particular, its morphisms are stable homotopy classes of maps. The
  various point-set models of spectra give different presentations, but
  after inverting stable equivalences they all present the same
  $oo$-category $Sp$.
]

#remark(title:[A Spectrum as a Homology Theory])[
  Let $e in Sp$. Under the definition above, $e$ is a reduced excisive
  functor

  $ e:Ani_*^"fin"->Ani $

  For a map $a->x$ of finite animae, form the pointed quotient

  $ x slash a:=x coprod_a ast $

  The relative groups associated with $e$ are

  $ e_n (x,a):=pi_n (e(x slash a)) quad (n>=0) $

  where the base point of $e(x slash a)$ is induced by
  $e(ast)->e(x slash a)$. Negative degrees are recovered by shifting the
  spectrum $e$.

  Reducedness gives $e_n (ast)=0$. Excision turns homotopy pushout squares
  of finite pointed animae into homotopy pullback squares, so applying
  homotopy groups produces excision, Mayer--Vietoris sequences, and the
  connecting maps of a generalized homology theory. Thus a spectrum is not
  merely a sequence of spaces: it coherently packages all degrees of a
  homology theory.
]

#corollary[
  The $oo$-category $Sp$ is stable. Its suspension and loop functors are
  inverse equivalences

  $ Sigma:Sp <->^tilde Sp:Omega $
]

The stable $oo$-category $Sp$ also carries a canonical Postnikov
$t$-structure, organized by the vanishing of its homotopy groups. This will
relate spectra to ordinary abelian groups through the heart of $Sp$.

=== The Postnikov $t$-Structure

For $x in Sp$ and $n in ZZ$, define its $n$th homotopy group by

$ pi_n (x):=Hom_(h#h(0pt)Sp) (Sigma^n SS,x) $

The infinite loop-space structure makes this an abelian group in every
degree, including degrees $0$ and $1$.

#proposition(title:[Postnikov $t$-Structure on Spectra])[
  The full subcategories

  $ Sp_(>=0):={x in Sp: pi_n (x)=0 " for " n<0} $

  and

  $ Sp_(<=0):={x in Sp: pi_n (x)=0 " for " n>0} $

  determine an accessible $t$-structure on $Sp$. It is both left and right
  complete.
]

If a spectrum $x$ is represented by compatible spaces
$x_n tilde.eq Omega x_(n+1)$, then

$ x in Sp_(<=m)
  <=> x_n " is " (n+m)"-truncated for every " n>=0 $

Thus the truncations of a spectrum are ordinary Postnikov truncations,
performed compatibly at every level.

#corollary(title:[The Heart of Spectra])[
  The heart of the Postnikov $t$-structure is canonically equivalent to the
  category of abelian groups

  $ Sp^(suit.heart) tilde.eq Ab $

  Under this equivalence, an abelian group $a$ corresponds to the
  Eilenberg--Mac Lane spectrum $"H"a$. Its $n$th space is $K(a,n)$, and its
  only nonzero homotopy group is

  $ pi_0 ("H"a) tilde.eq a $
]

#proofsketch[
  A spectrum in the heart has each level $x_n$ both $(n-1)$-connected and
  $n$-truncated, hence $x_n tilde.eq K(a,n)$ for one abelian group $a$.
  Conversely, the spaces $K(a,n)$ form an $Omega$-spectrum. Completeness
  follows because a spectrum is reconstructed from its compatible
  Postnikov truncations; a spectrum whose homotopy groups all vanish is
  therefore zero.
]

#remark(title:[The General Construction])[
  More generally, if $C$ is presentable, then $Sp(C)$ has an accessible
  $t$-structure whose negative part is characterized by

  $ x in Sp(C)_(<=-1) <=> Omega^oo x " is final in " C $

  Equivalently, its connective part is generated under colimits and
  extensions by the suspension spectra of objects of $C$.
]

=== Homotopy Groups and Compact Generation

#corollary(title:[Stable Whitehead Theorem])[
  A map $f:x->y$ of spectra is an equivalence if and only if

  $ pi_n (f):pi_n (x)->pi_n (y) $

  is an isomorphism for every $n in ZZ$.
]

#proofsketch[
  Apply the long exact sequence of homotopy groups to $fib(f)$. If every
  $pi_n (f)$ is an isomorphism, then all homotopy groups of $fib(f)$ vanish.
  Completeness of the Postnikov $t$-structure forces $fib(f) tilde.eq 0$.
]

#proposition(title:[Compact Generation])[
  The sphere spectrum $SS$ is a compact generator of $Sp$ in the stable
  sense: its shifts ${Sigma^n SS}_(n in ZZ)$ jointly detect equivalences.
  Consequently, $Sp$ is compactly generated, and its compact objects are
  precisely the retracts of finite cell spectra.
]

#proofsketch[
  Maps from the shifts of $SS$ compute the homotopy groups

  $ Hom_(h#h(0pt)Sp) (Sigma^n SS,x) tilde.eq pi_n (x) $

  so generation follows from the stable Whitehead theorem. Compactness is
  the fact that homotopy groups commute with filtered colimits. The compact
  objects are then obtained from $SS$ by finite cofibers, shifts, and
  retracts.
]

#remark[
  The proposition above is basically telling that the entire $Sp$ is generated by $SS$ via suspensions, colimits and retracts.
]

#remark(title:[Colimits and Infinite Loop Spaces])[
  The functors $pi_n:Sp->Ab$ preserve products and filtered colimits. The
  infinite-loop-space functor has the stronger connective statement

  $ Omega^oo:Sp_(>=0)->Ani $

  preserves sifted colimits. Outside the connective part, $Omega^oo$ is a
  right adjoint and should not be expected to preserve arbitrary colimits.
]

== Presentable Stable $oo$-Categories

Presentability is especially simple in the stable setting: finite colimits
are already built into stability, so arbitrary coproducts control all small
colimits.

=== Coproducts Control Colimits

#proposition(title:[Colimits in a Stable $oo$-Category])[
  Let $C$ be stable.

  1. The category $C$ admits all small colimits if and only if it admits all
     small coproducts.

  2. If $C$ and $D$ admit small colimits, an exact functor $F:C->D$
     preserves all small colimits if and only if it preserves small
     coproducts.

  3. If these conditions hold, an object $x in C$ is compact if and only if
     every map

     $ x->coprod_(alpha in A) y_alpha $

     factors, up to homotopy, through a finite subcoproduct.
]

#proofsketch[
  In a stable category, finite colimits are finite limits and are therefore
  already available. General colimits can be assembled from coproducts and
  cofibers, proving the first two statements. For the last, write a
  coproduct as the filtered colimit of its finite subcoproducts and apply the
  definition of compactness.
]

Thus, for exact functors, the apparently global problem of preserving every
colimit reduces to checking only coproducts.

=== Presentability and Generators

Recall that an object $g in C$ #emph[generates] a stable $oo$-category if

$ pi_0 Map_C (g,x)=ast => x tilde.eq 0 $

Equivalently, all shifts of $g$ jointly detect equivalences.
A $kappa$-compact object is one whose mapping-space functor preserves
$kappa$-filtered colimits.

#theorem(title:[Presentability Criterion])[
  A stable $oo$-category $C$ is presentable if and only if:

  1. $C$ admits small coproducts;
  2. its homotopy category $h C$ is locally small;
  3. for some regular cardinal $kappa$, it has a $kappa$-compact generator
     $g$.
]

#proofsketch[
  A presentable category has a small family of compact objects; their
  coproduct gives one $kappa$-compact generator for sufficiently large
  $kappa$. Conversely, close the shifts of $g$ under $kappa$-small colimits.
  This gives a small stable subcategory whose $kappa$-Ind-completion maps
  fully faithfully to $C$. Since $g$ detects zero objects, this map is an
  equivalence.
]

#remark[
  This criterion is visible entirely in $h C$. It is therefore the stable
  $oo$-categorical counterpart of compact-generation criteria for
  triangulated categories.
]

=== Stabilization and Its Presentable Universal Property

#theorem(title:[Presentability of Stabilization])[
  If $C$ is presentable, then $Sp(C)$ is presentable and

  $ Omega^oo:Sp(C)->C $

  admits a left adjoint $Sigma_+^oo:C->Sp(C)$. If $C$ is pointed, we write
  this functor as $Sigma^oo$.
]

The important point is not merely the existence of this adjunction, but its
universal property.

#theorem(title:[Free Stable Presentable Category])[
  Let $C$ and $D$ be presentable and suppose that $D$ is stable.
  Precomposition with $Sigma_+^oo$ induces an equivalence

  $ Fun^"L" (Sp(C),D)->^tilde Fun^"L" (C,D) $

  where $Fun^"L"$ denotes the $oo$-category of colimit-preserving functors.
]

Taking $C=Ani$ gives the fundamental characterization

$ Fun^"L" (Sp,D)->^tilde D,
  quad F mapsto F(SS) $

Hence $Sp$ is the stable presentable $oo$-category freely generated under
colimits by one object, the sphere spectrum. This is the precise categorical
sense in which $SS$ behaves like the free rank-one object $ZZ$.

#remark[
  If $G:D->Sp(C)$ is exact, then $G$ admits a left adjoint exactly when
  $Omega^oo G:D->C$ does. Stabilization therefore does not create a new
  obstruction to adjointness.
]

=== Stable Localizations and Accessible $t$-Structures

#proposition(title:[Stable Localizations])[
  Let $C$ be stable and let $C' subset.eq C$ be a reflective full
  subcategory with localization $L:C->C'$. Then $C'$ is stable if and only
  if $L$ is left exact.
]

Since a localization is a left adjoint, it already preserves colimits. Thus
left exactness is precisely what makes it exact and allows stability to pass
to the essential image.

#theorem(title:[Presentations by Spectral Presheaves])[
  An $oo$-category $C$ is presentable and stable if and only if there exist a
  small $oo$-category $E$ and an accessible left-exact localization

  $ Fun(E^op,Sp)->C $
]

This is the stable analogue of presenting an ordinary Grothendieck category
by a localization of a presheaf category: spaces are replaced by spectra,
and left exactness preserves the stable structure.

#proposition(title:[Generating Accessible $t$-Structures])[
  Let $C$ be presentable and stable.

  1. If $U subset.eq C$ is presentable and closed under small colimits and
     extensions, then there is a $t$-structure with $C_(>=0)=U$.

  2. Every small family ${x_alpha}$ generates an accessible $t$-structure:
     its connective part is the smallest full subcategory containing all
     $x_alpha$ and closed under extensions and small colimits.
]

#remark(title:[Accessibility Test])[
  For a $t$-structure on a presentable stable $oo$-category, the following
  conditions are equivalent: $C_(>=0)$ is presentable, $C_(<=0)$ is
  presentable, and the truncation functors $tau_(>=0)$ and $tau_(<=0)$ are
  accessible. Any of these conditions is what we mean by an
  #emph[accessible $t$-structure].
]

== Mapping Spectra

Mapping spaces in a stable $oo$-category admit compatible deloopings. A
single spectrum therefore packages maps in every shifted degree.

=== Construction

Let $C$ be a locally small stable $oo$-category and let $x,y in C$. For
$n>=0$, set

$ m_n:=Map_C (x,Sigma^n y) $

Since $Sigma^n y tilde.eq Omega Sigma^(n+1)y$ and mapping out of $x$
preserves limits, there are natural equivalences

$ m_n tilde.eq Omega m_(n+1) $

These equivalences, with their canonical coherences, define an
$Omega$-spectrum.

#definition(title:[Mapping Spectrum])[
  The #emph[mapping spectrum] from $x$ to $y$ is the spectrum

  $ Map_C^Sp (x,y) in Sp $

  whose $n$th space is $Map_C (x,Sigma^n y)$. Its infinite loop space is the
  original mapping space

  $ Omega^oo Map_C^Sp (x,y) tilde.eq Map_C (x,y) $
]

=== Basic Properties

#proposition[
  For $x,y in C$ and $a,b,n in ZZ$, the mapping spectrum satisfies:

  1. #emph[Homotopy groups recover shifted maps.]

     $ pi_n Map_C^Sp (x,y)
       tilde.eq Hom_(h C) (Sigma^n x,y)
       tilde.eq Hom_(h C) (x,Sigma^(-n)y) $

  2. #emph[Shifts become suspensions of spectra.]

     $ Map_C^Sp (Sigma^a x,Sigma^b y)
       tilde.eq Sigma^(b-a) Map_C^Sp (x,y) $

  3. #emph[Exactness.] The functors

     $ Map_C^Sp (x,-):C->Sp,
       quad Map_C^Sp (-,y):C^op->Sp $

     are exact.

  4. #emph[Detection of equivalences.] A map $f:y->z$ is an equivalence if
     and only if $Map_C^Sp (x,f)$ is an equivalence for every $x in C$.
]

For example, a cofiber sequence $x->y->z$ induces fiber sequences

$ Map_C^Sp (w,x)->Map_C^Sp (w,y)->Map_C^Sp (w,z) $

and

$ Map_C^Sp (z,w)->Map_C^Sp (y,w)->Map_C^Sp (x,w) $

Taking homotopy groups recovers the familiar long exact sequences of
$Ext$-groups. In the notation of Chapter 2,

$ pi_n Map_C^Sp (x,y) tilde.eq Ext_C^(-n) (x,y) $

#remark(title:[Spectral Enrichment])[
  Composition of maps refines canonically to maps of spectra

  $ Map_C^Sp (y,z) smash Map_C^Sp (x,y)
    ->Map_C^Sp (x,z) $

  together with unit maps

  $ SS->Map_C^Sp (x,x) $

  These maps are coherently associative and unital. In other words, every
  stable $oo$-category is canonically enriched over spectra. Ordinary
  mapping spaces are obtained by applying $Omega^oo$ and therefore remember
  only the infinite-loop-space face of this richer object.
]

#remark(title:[The Presentable Case])[
  If $C$ is presentable and stable, it is canonically tensored over $Sp$.
  For $e in Sp$ and $x in C$, there is an object $e ⊗ x in C$
  characterized by the tensor--Hom adjunction

  $ Map_C^Sp (e ⊗ x,y)
    tilde.eq Map_Sp^Sp (e,Map_C^Sp (x,y)) $

  The functor $e mapsto e ⊗ x$ preserves colimits and sends
  $SS$ to $x$. For $C=Sp$, the mapping spectrum is the usual function
  spectrum $F(x,y)$, and

  $ Map_Sp^Sp (SS,y) tilde.eq y $
]

== Cohomology and Homology Theories

Fix a spectrum $E in Sp$ and a pointed anima $x in Ani_*$. In formulas
below, we use the abbreviations

$ E smash x:=E smash Sigma^oo x,
  quad Map^Sp (x,E):=Map_Sp^Sp (Sigma^oo x,E) $

Thus the space $x$ is first stabilized; smash products and mapping spectra
are then formed inside $Sp$.

=== Cohomology First

#definition(title:[Reduced Generalized Cohomology Theory])[
  A #emph[reduced generalized cohomology theory] on pointed animae is a
  family of contravariant functors

  $ E^n:(h Ani_*)^op->Ab quad (n in ZZ) $

  satisfying the following axioms.

  1. #emph[Reducedness.]

     $ E^n (ast)=0 $

  2. #emph[Suspension.] There are natural isomorphisms

     $ E^n (Sigma x) tilde.eq E^(n-1) (x) $

  3. #emph[Exactness.] Every cofiber sequence

     $ a->x->x slash a->Sigma a $

     induces a natural long exact sequence

     $ dots->E^n (x slash a)->E^n (x)->E^n (a)
       ->E^(n+1) (x slash a)->dots $

  4. #emph[Wedge axiom.] For every family ${x_alpha}$,

     $ E^n (⋁_alpha x_alpha)
       tilde.eq product_alpha E^n (x_alpha) $

  The word #emph[generalized] means that no dimension axiom is required.
]

#definition(title:[Representing Spectrum])[
  Let ${E^n}_(n in ZZ)$ be a reduced generalized cohomology theory. A
  #emph[representing spectrum] is a spectrum $E in Sp$ together with natural
  isomorphisms

  $ E^n (x) tilde.eq
    Hom_(h#h(0pt)Sp) (Sigma^oo x,Sigma^n E) $

  for every pointed anima $x$ and every $n in ZZ$.
]

The more intrinsic object is not the separate family of abelian-group-valued
functors $E^n$, but the single spectrum-valued functor

$ E^bullet:Sp^op->Sp,
  quad y mapsto Map_Sp^Sp (y,E) $

The original theory on pointed animae is obtained by precomposing with the
suspension-spectrum functor

$ Ani_* stretch(->)^Sigma^oo Sp stretch(->)^(Map_Sp^Sp (-,E)) Sp $

and then taking homotopy groups. Explicitly,

$ E^n (x):=pi_(-n) Map^Sp (x,E)
    tilde.eq Hom_(h#h(0pt)Sp) (Sigma^oo x,Sigma^n E) $

Thus all groups $E^n (x)$ are the homotopy groups of one mapping spectrum,
not unrelated invariants in different degrees.

#proposition(title:[A Spectrum Represents Cohomology])[
  Every spectrum $E$ defines a reduced generalized cohomology theory by the
  formula above. The representing spectrum is unique up to equivalence.
]

#proofsketch[
  The suspension formula follows from the shift formula for mapping spectra.
  Mapping into $E$ carries cofiber sequences to fiber sequences and wedges
  to products. Taking homotopy groups gives exactness and the wedge axiom.
  Uniqueness follows from the stable Yoneda lemma.
]

#remark(title:[Brown Representability])[
  Conversely, Brown representability says that a reduced generalized
  cohomology theory satisfying the usual size hypotheses is represented by
  a spectrum $E$. Thus a whole family ${E^n}_(n in ZZ)$ is encoded by one
  stable object rather than by unrelated functors in each degree.
]

=== Homology

#definition(title:[Reduced Generalized Homology Theory])[
  A #emph[reduced generalized homology theory] is a family of covariant
  functors

  $ E_n:h Ani_*->Ab quad (n in ZZ) $

  satisfying reducedness, natural suspension isomorphisms

  $ E_n (Sigma x) tilde.eq E_(n-1) (x) $

  exactness for cofiber sequences, and the wedge axiom

  $ E_n (⋁_alpha x_alpha)
    tilde.eq ⊕_alpha E_n (x_alpha) $
]

#proposition(title:[Homology Represented by a Spectrum])[
  Every spectrum $E$ defines a reduced generalized homology theory by

  $ E_n (x):=pi_n (E smash x) $

  A cofiber sequence $a->x->x slash a$ induces long exact sequences

  $ dots->E_n (a)->E_n (x)->E_n (x slash a)
    ->E_(n-1) (a)->dots $
]

#proofsketch[
  Smashing with $E$ preserves colimits, so it preserves cofiber sequences
  and wedges. Taking homotopy groups gives the long exact sequence and turns
  wedges of spectra into direct sums of abelian groups.
]

=== The Derived Algebra Dictionary

The analogy with derived algebra becomes literal after replacing the ground
ring $R$ by the sphere spectrum $SS$. A coefficient spectrum $E$ behaves
like a module, mapping spectra behave like derived Hom, and smash products
behave like derived tensor products.

#align(center, table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: (x: 14pt, y: 5pt),
  stroke: none,
  table.hline(y: 1, stroke: 0.65pt + muted),
  table.vline(x: 1, stroke: 0.65pt + muted),
  text(weight: "semibold", fill: ink)[derived algebra],
  text(weight: "semibold", fill: ink)[stable homotopy],
  [$"RHom"_R (m,n)$],
  [$Map^Sp (x,E)$],
  [$Ext_R^q (m,n)$],
  [$E^q (x)$],
  [$m ⊗_R^"L" n$],
  [$x smash E$],
  [$Tor_q^R (m,n)$],
  [$E_q (x)$],
))

The two numerical theories are obtained by taking homotopy groups of the
corresponding spectrum-valued constructions

$ E^q (x)=pi_(-q) Map^Sp (x,E),
  quad E_q (x)=pi_q (x smash E) $

#example(title:[Ordinary and Stable Theories])[
  For an abelian group $a$, the Eilenberg--Mac Lane spectrum $"H"a$
  recovers ordinary reduced theories

  $ ("H"a)_n (x) tilde.eq tilde("H")_n (x;a),
    quad ("H"a)^n (x) tilde.eq tilde("H")^n (x;a) $

  Taking $E=SS$ instead gives stable homotopy and stable cohomotopy

  $ SS_n (x) tilde.eq pi_n (Sigma^oo x),
    quad SS^n (x)
      tilde.eq Hom_(h#h(0pt)Sp) (Sigma^oo x,Sigma^n SS) $
]

#remark[
  For an unpointed anima $x$, first adjoin a disjoint base point and use
  $x_+$. Thus the unreduced theory is written

  $ E_n (x):=pi_n (E smash Sigma_+^oo x) $
]

== The Eilenberg--Mac Lane Spectrum

=== The Construction

Let $a in Ab$. For $n>=0$, let $a[n]$ denote the nonnegatively graded chain
complex with $a$ in degree $n$ and zero elsewhere. Apply the Dold--Kan
functor and forget the abelian-group structure to obtain a pointed anima

$ K(a,n):="DK"(a[n]) $

Every simplicial abelian group is a Kan complex, and Dold--Kan identifies
homotopy groups with homology groups. Hence

$ pi_i K(a,n) tilde.eq
  cases(a & "if " i=n, 0 & "if " i!=n) $

Thus $K(a,n)$ is an Eilenberg--Mac Lane space. Shifting the chain complex
corresponds to delooping, giving natural equivalences

$ K(a,n) tilde.eq Omega K(a,n+1) $

These equivalences are coherent in $n$ and therefore define an
$Omega$-spectrum

$ K(a,0), K(a,1), K(a,2), dots $

#definition(title:[Eilenberg--Mac Lane Spectrum])[
  The spectrum determined by the sequence above is the
  #emph[Eilenberg--Mac Lane spectrum] of $a$, denoted

  $ "H"a in Sp $

  Equivalently, $"H"a$ is the object corresponding to $a$ under the
  equivalence

  $ Sp^(suit.heart) tilde.eq Ab $
]

#proposition[
  The spectrum $"H"a$ is characterized up to equivalence by

  $ pi_i ("H"a) tilde.eq
    cases(a quad& "if " i=0, 0 quad& "if " i!=0) $

  The construction is functorial and defines a fully faithful functor

  $ "H":Ab->Sp $

  whose essential image is the heart $Sp^(suit.heart)$.
]

#proofsketch[
  The zeroth space of $"H"a$ is the discrete group $K(a,0)$, and the
  equivalences $K(a,n) tilde.eq Omega K(a,n+1)$ identify the stable homotopy
  groups with the displayed Dold--Kan calculation. The description of the
  Postnikov heart then gives uniqueness, functoriality, and full
  faithfulness.
]

#remark(title:[Why It Represents Ordinary Theory])[
  For every pointed anima $x$, the general formulas represented by a
  spectrum specialize to

  $ tilde("H")^n (x;a)
    tilde.eq Hom_(h#h(0pt)Sp) (Sigma^oo x,Sigma^n "H"a) $

  and

  $ tilde("H")_n (x;a)
    tilde.eq pi_n ("H"a smash Sigma^oo x) $

  Hence the Dold--Kan construction of the spaces $K(a,n)$, the spectrum
  $"H"a$, and ordinary singular homology and cohomology are three levels of
  the same construction.
]

#remark[
  The spectrum $"H"ZZ$ is a commutative ring spectrum, and every $"H"a$ is
  naturally an $"H"ZZ$-module. This is the stable-homotopical form of the
  ordinary $ZZ$-module structure on an abelian group. It also clarifies the
  earlier distinction: $"H"ZZ$ encodes ordinary homological algebra, while
  the sphere spectrum $SS$ retains the higher stable stems.
]

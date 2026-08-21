#import "../template.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.1.2"

#show: doc => conf(
  easy: true,
  doc,
)

= Modules

Let $cal(C)^times.o$ be a symmetric monoidal category and let
$a in Alg(cal(C))$ be an associative unital algebra object, with multiplication
$mu:a times.o a->a$ and unit $eta:1->a$. A #emph[left $a$-module] is an
object $m in cal(C)$ equipped with an action

$ lambda:a times.o m->m $

which is associative and unital. Concretely, the following diagrams commute.

#align(center, grid(
  columns: (auto, 2em, auto),
  align: center + horizon,
  diagram({
    node((0, 0), [$a times.o a times.o m$], name: <aam>)
    node((1, 0), [$a times.o m$], name: <am-top>)
    node((0, 1), [$a times.o m$], name: <am-left>)
    node((1, 1), [$m$], name: <m>)
    edge(<aam>, <am-top>, [$mu times.o id_m$], label-side: left, "->")
    edge(<aam>, <am-left>, [$id_a times.o lambda$], label-side: right, "->")
    edge(<am-top>, <m>, [$lambda$], label-side: left, "->")
    edge(<am-left>, <m>, [$lambda$], label-side: right, "->")
  }),
  [],
  diagram({
    node((0, 0), [$1 times.o m$], name: <one-m>)
    node((1, 0), [$a times.o m$], name: <a-m>)
    node((1, 1), [$m$], name: <mm>)
    edge(<one-m>, <a-m>, [$eta times.o id_m$], label-side: left, "->")
    edge(<one-m>, <mm>, [$tilde.eq$], label-side: right, "->")
    edge(<a-m>, <mm>, [$lambda$], label-side: left, "->")
  }),
))

Dually, a right $a$-module has an action $rho:m times.o a->m$. We write
$cat("LMod")_a (cal(C))$ and $cat("RMod")_a (cal(C))$ for the corresponding categories. If
$a$ is commutative, the symmetry of $cal(C)^times.o$ canonically converts
left actions into right actions and conversely; in this case we simply write
$cat("Mod")_a (cal(C))$.

The basic operation on modules is the #emph[relative tensor product]. Given a
right $a$-module $m$ and a left $a$-module $n$, it is classically defined by
the balanced coequalizer

$
  m times.o a times.o n
  arrow.r.double
  m times.o n
  ->m times_a n
$

where the two parallel arrows are $rho times.o id_n$ and
$id_m times.o lambda$. When $a$ is commutative, this operation often makes
$cat("Mod")_a (cal(C))$ into a symmetric monoidal category whose unit is $a$.

#remark(title:[The Homotopy-Correct Construction])[
  The displayed coequalizer is only the classical shadow. In an
  $oo$-category the relative tensor product is computed by the geometric
  realization of the two-sided bar construction

  $
    m times_a n
    tilde.eq
    abs(cat("Bar")_bullet (m,a,n)),
    quad
    cat("Bar")_k (m,a,n)=m times.o a^(times.o k) times.o n
  $

  This requires the relevant geometric realizations to exist and tensoring
  to preserve them separately in each variable. Without these hypotheses,
  $m times_a n$ need not exist, and $cat("Mod")_a (cal(C))$ need not inherit the
  expected monoidal structure.
]

== Coherent $oo$-Operads

The module construction above needs more than associativity of the operad.
To form relative tensor products and compose module actions, one must be able
to insert an extra input into an operation and make these insertions compatible
with composition. A #emph[coherent $oo$-operad] is precisely a unital operad
for which these spaces of extensions glue by homotopy pushouts.

=== Semi-Inert Morphisms

#definition(title:[Semi-Inert and Null Morphisms])[
  A morphism $alpha:chevron.l m chevron.r->chevron.l n chevron.r$ in
  $Fin_*$ is #emph[semi-inert] if every non-basepoint $j in chevron.l n
  chevron.r^circle$ has at most one inverse image. It is #emph[null] if every
  element of $chevron.l m chevron.r$ is sent to the basepoint.

  Let $p:cal(O)^times.o->Ner(Fin_*)$ be an $oo$-operad. A morphism
  $u:x->y$ of $cal(O)^times.o$ is semi-inert if $p(u)$ is semi-inert and, for
  every inert $v:y->z$, the composite $v compose u$ is inert whenever its
  image under $p$ is inert. It is null if $p(u)$ is null.
]

#remark(title:[Input--Output Meaning])[
  Write $x=(x_1,dots,x_m)$ and $y=(y_1,dots,y_n)$. A morphism over
  $alpha:chevron.l m chevron.r->chevron.l n chevron.r$ is specified by
  operations

  $
    phi_j in Mul_cal(O) ({x_i}_(alpha(i)=j),y_j)
  $

  It is semi-inert exactly when, for every output $y_j$, either no input is
  assigned to it, or a unique input $x_i$ is assigned and $phi_j:x_i->y_j$
  is an equivalence. Thus semi-inert maps may #emph[insert empty input slots];
  inert maps are those with no empty output slot, while null maps have only
  empty slots. In a unital operad the operations belonging to the empty slots
  form contractible spaces.
]

Semi-inertness is insensitive to an inert change of coordinates: in a
commutative triangle $h=v compose u$, if $u$ is inert, then $v$ is semi-inert
if and only if $h$ is semi-inert.

=== Extension Spaces

#definition(title:[Extension of an Active Morphism])[
  Let $f:x->y$ be active. An #emph[extension of $f$] is a commutative square

  #align(center, diagram({
    node((0, 0), [$x$], name: <x>)
    node((1, 0), [$y$], name: <y>)
    node((0, 1), [$x'$], name: <xp>)
    node((1, 1), [$y'$], name: <yp>)
    edge(<x>, <y>, [$f$], label-side: left, "->")
    edge(<x>, <xp>, [$i$], label-side: right, "->")
    edge(<y>, <yp>, [$u$], label-side: left, "->")
    edge(<xp>, <yp>, [$f'$], label-side: right, "->")
  }))

  in which $i$ is semi-inert and inserts exactly one new input, $u$ is an
  equivalence, and $f'$ is active. The full $oo$-category of such squares and
  their equivalences is denoted $cat("Ext")(f)$.
]

#remark(title:[Meaning of an Extension])[
  Since $u$ is an equivalence, we may identify $y'$ with $y$. If $x_0$ is the
  new (single) input omitted by $i$, then we may similarly read $x'$ as
  $x plus.o x_0$. The defining square becomes

  #align(center, diagram({
    node((0, 0), [$x$], name: <x>)
    node((1, 0), [$y$], name: <y>)
    node((0, 1), [$x plus.o x_0$], name: <xx>)
    node((1, 1), [$y$], name: <yy>)
    edge(<x>, <y>, [$f$], label-side: left, "->")
    edge(<x>, <xx>, [$i$], label-side: right, "->")
    edge(<xx>, <yy>, [$f'$], label-side: right, "->")
    edge(<y>, <yy>, [$id_y$], label-side: left, "->")
  }))

  Thus an extension is precisely a coherent way to insert one extra input
  into $f$. More generally, for a chain $sigma$ of active morphisms and a
  downward-closed subset $s$ of its vertices, i.e. a morphism
  $ sigma : Delta^n -> cal(O)^times.o_"act" $
  $cat("Ext")(sigma,s)$ records compatible extension squares in which the new
  input is inserted at the vertices in $s$ and transported through the
  remaining active arrows. i.e.
  
  #align(center, diagram({
	node((-1, -1), [$x_0$])
	node((-1, 0), [$x'_0$])
	node((0, 0), [$x'_1$])
	node((0, -1), [$x_1$])
	node((1, -1), [$...$])
	node((1, 0), [$...$])
	node((2, -1), [$x_r$])
	node((2, 0), [$x_r plus.o x_(r,0)$])
	node((3, -1), [$...$])
	node((3, 0), [$...$])
	node((4, -1), [$x_n$])
	node((4, 0), [$x'_n$])
	node((-2, -1), [$sigma:$])
	node((2, 1), [$(r in s)$])
	edge((-1, -1), (0, -1), [$f_1$], label-side: left, "->")
	edge((0, -1), (1, -1), [$f_2$], label-side: left, "->")
	edge((-1, -1), (-1, 0), [$g_0$], label-side: right, "->")
	edge((0, -1), (0, 0), [$g_1$], label-side: right, "->")
	edge((-1, 0), (0, 0), [$f'_1$], label-side: right, "->")
	edge((0, 0), (1, 0), [$f'_2$], label-side: right, "->")
	edge((1, -1), (2, -1), [$f_r$], label-side: left, "->")
	edge((1, 0), (2, 0), [$f'_r$], label-side: right, "->")
	edge((2, -1), (2, 0), [$g_r$], label-side: right, "->")
	edge((4, -1), (4, 0), [$g_n$], label-side: left, "->")
	edge((2, -1), (3, -1), [$f_(r+1)$], label-side: left, "->")
	edge((2, 0), (3, 0), [$f'_(r+1)$], label-side: right, "->")
	edge((3, -1), (4, -1), [$f_n$], label-side: left, "->")
	edge((3, 0), (4, 0), [$f'_n$], label-side: right, "->")
	edge((-1, -1), (-1, 0), [$tilde.eq$], label-side: left)
	edge((0, -1), (0, 0), [$tilde.eq$], label-side: left, " ")
	edge((4, -1), (4, 0), [$tilde.eq$], label-side: right, " ")
  }))
  
  These categories supply the restriction maps
  needed for higher coherence. If the color category $cal(O)$ is Kan, every
  morphism in $cat("Ext")(sigma,s)$ is an equivalence, so it is a Kan complex.
]

#definition(title:[Coherent $oo$-Operad])[
  An $oo$-operad $cal(O)^times.o$ is #emph[coherent] if:

  + $cal(O)^times.o$ is unital
  + its underlying $oo$-category of colors $cal(O)$ is a Kan complex
  + for every composable pair of active morphisms
    $x->^f y->^g z$, the homotopy-coherent extension diagram

    #align(center, diagram({
      node((0, 0), [$cat("Ext")(id_y)$], name: <id>)
      node((0, 1), [$cat("Ext")(f)$], name: <f>)
      node((1, 0), [$cat("Ext")(g)$], name: <g>)
      node((1, 1), [$cat("Ext")(g compose f)$], name: <gf>)
      edge(<id>, <f>, "->")
      edge(<id>, <g>, "->")
      edge(<f>, <gf>, "->")
      edge(<g>, <gf>, "->")
    }))

    is a homotopy pushout square of Kan complexes.
]

#remark(title:[What the Pushout Says])[
  An extension of the composite $g compose f$ can be produced in two ways:
  insert the extra input at the $f$-stage, or insert it at the $g$-stage.
  Their common degenerate case is an extension of $id_y$. Coherence says that
  these are all the possibilities and that their identifications contain no
  hidden higher ambiguity.
]

Restriction along a morphism of simplices gives maps between extension
spaces. In particular, extensions of a longer active chain restrict to
extensions of any initial segment; when $cal(O)$ is Kan and the segment has a
largest selected vertex, the corresponding restriction is a trivial
fibration. This is the mechanism that makes iterated module constructions
independent of parenthesization.

=== Examples and Invariance

#proposition(title:[Basic Coherent Operads])[
  The commutative operad $Comm^times.o$ and the operad $EE_0^times.o$ are
  coherent. More generally, the little-cubes operads $EE_k^times.o$ are
  coherent for every $k>=0$.
]

#proofsketch[
  For $Comm^times.o$, every operation is determined by its underlying map of
  finite pointed sets, so each extension space is equivalent to the discrete
  set of possible new input positions; the coherence square becomes an
  elementary pushout of finite sets. The same computation for $EE_0^times.o$
  allows only nullary and unary active operations. The little-cubes case is a
  geometric refinement: configuration spaces replace finite sets, and the
  required square is obtained by gluing configurations according to where the
  new cube is inserted.
]

#proposition(title:[Invariance under Approximation])[
  Let $F:cal(O)^times.o->cal(O)'^times.o$ be a map of unital $oo$-operads
  whose color categories are Kan complexes, and suppose that $F$ is an
  approximation. If $cal(O)'^times.o$ is coherent, then
  $cal(O)^times.o$ is coherent. Conversely, coherence descends from
  $cal(O)^times.o$ to $cal(O)'^times.o$ when the induced map
  $pi_0 cal(O)->pi_0 cal(O)'$ is surjective.
]

#proofsketch[
  An approximation induces equivalences on the extension spaces
  $cat("Ext")(sigma,s)$. It therefore transports the defining homotopy-pushout
  square. Surjectivity on connected components ensures that every square in
  the target is represented by one in the source.
]

#remark(title:[Why Coherence Matters for Modules])[
  If a unital operad with Kan color space is presented as the assembly of a
  family of reduced operads $(cal(O)_x^times.o)_(x in cal(O))$, then it is
  coherent exactly when every fiber $cal(O)_x^times.o$ is coherent. Hence an
  $cal(O)$-algebra $a=(a_x)$ in an $cal(O)$-monoidal $oo$-category gives a
  compatible family of module categories

  $
    (cat("Mod")_(a_x)^(cal(O)_x)(cal(C)_x))_(x in cal(O))
  $

  Coherence is the condition that lets these fiberwise module theories glue
  and that makes their relative tensor products associative up to all higher
  homotopies. It is therefore the operadic hypothesis behind a usable theory
  of modules over $cal(O)$-algebras.
]

=== A Coherence Criterion

The definition by extension spaces is conceptual, but it appears to require
checking a homotopy-pushout square for every pair of active operations. There
is a more economical criterion involving only the source of a semi-inert
morphism.

#definition(title:[The Semi-Inert Arrow Category])[
  Let $cal(O)^times.o$ be a unital $oo$-operad. Define

  $
    cal(K)_cal(O)
    subset.eq
    Fun(Delta^1,cal(O)^times.o)
  $

  to be the full subcategory spanned by the semi-inert morphisms, and let

  $
    e_0,e_1:cal(K)_cal(O)->cal(O)^times.o
  $

  be evaluation at the source and target. A morphism of
  $cal(K)_cal(O)$ is called inert if both of its endpoint evaluations are
  inert.
]

#remark(title:[Flat Isofibrations])[
  An isofibration $r:x->s$ is #emph[flat] if pullback along $r$ preserves
  categorical equivalences over $s$. Thus flatness says that the fibers of
  $r$ vary homotopy-exactly under every base change; it is the
  $oo$-categorical replacement for a well-behaved family of categories.
]

#theorem(title:[Coherence Criterion])[
  Let $cal(O)^times.o$ be unital and suppose that its color category
  $cal(O)$ is a Kan complex. Then the following are equivalent:

  + $cal(O)^times.o$ is coherent
  + the source-evaluation map

    $
      e_0:cal(K)_cal(O)->cal(O)^times.o
    $

    is a flat isofibration
]

This reformulates coherence as a base-change property of a single functor.
Informally, once the source of a semi-inert arrow is moved through an active
operation, flatness guarantees that the space of compatible targets remains
homotopically correct.

==== Reduction to One Missing Input

#definition(title:[$m$-Semi-Inert Morphism])[
  A semi-inert morphism $u:x->x'$ is #emph[$m$-semi-inert] if the underlying
  pointed map

  $
    p(u):chevron.l n chevron.r->chevron.l n' chevron.r
  $

  leaves at most $m$ non-basepoint elements of
  $chevron.l n' chevron.r$ outside its image. We say that
  $cal(O)^times.o$ is #emph[$m$-coherent] when the flatness condition for
  $e_0$ is required only over such arrows.
]

Thus $0$-semi-inert arrows are inert up to equivalence, while a
$1$-semi-inert arrow inserts at most one genuinely new input. Although
flatness initially asks for every $m$, the unital structure lets us add the
missing inputs one at a time.

#proposition(title:[The One-Input Test])[
  For a unital $oo$-operad, the following conditions are equivalent:

  + $e_0:cal(K)_cal(O)->cal(O)^times.o$ is a flat isofibration
  + $cal(O)^times.o$ is $m$-coherent for every $m>=0$
  + $cal(O)^times.o$ is $1$-coherent
]

#proofsketch[
  Factor an $m$-semi-inert morphism into a chain in which each step inserts
  one missing output. The relevant extension categories for successive steps
  form flat families. Weak contractibility for the one-input fibers therefore
  propagates inductively from $m-1$ to $m$. The case $m=0$ is automatic from
  inert lifting.
]

==== A Local Contractibility Test

Fix an active cocone to a color $z$ and a diagram

#align(center, diagram({
  node((0, 0), [$x$], name: <x>)
  node((1, 0), [$y$], name: <y>)
  node((0, 1), [$x'$], name: <xp>)
  node((2, 1), [$z$], name: <z>)
  edge(<x>, <y>, "->")
  edge(<x>, <xp>, [$u$], label-side: right, "->")
  edge(<x>, <z>, [active], bend: -20deg, label-side: left, "->")
  edge(<y>, <z>, [active], label-side: left, "->")
  edge(<xp>, <z>, [active], label-side: right, "->")
}))

where $u$ is semi-inert. Let $cal(B)[sigma,z]$ be the $oo$-category of
factorizations obtained by adjoining a square

#align(center, diagram({
  node((0, 0), [$x$], name: <x>)
  node((1, 0), [$y$], name: <y>)
  node((0, 1), [$x'$], name: <xp>)
  node((1, 1), [$y'$], name: <yp>)
  node((2, 1), [$z$], name: <z>)
  edge(<x>, <y>, "->")
  edge(<x>, <xp>, [$u$], label-side: right, "->")
  edge(<y>, <yp>, [$v$], label-side: left, "->")
  edge(<xp>, <yp>, "->")
  edge(<yp>, <z>, [active], "->")
}))

such that $v$ is semi-inert and the induced pointed map

$
  p(x') coprod_(p(x)) p(y)->p(y')
$

is surjective. Objects of $cal(B)[sigma,z]$ are precisely the compatible ways
to transport the newly inserted inputs across the active map $x->y$.

#proposition(title:[Local Form of Flatness])[
  The source evaluation $e_0$ is flat if and only if every category
  $cal(B)[sigma,z]$ above is weakly contractible. It is enough to check this
  when $u$ is $1$-semi-inert.
]

#remark(title:[Why Surjectivity Appears])[
  Semi-inertness controls how many old inputs reach each output, while the
  surjectivity condition says that every output of $y'$ is accounted for by
  either $x'$ or $y$. Together they rule out an additional, invisible input
  appearing during transport.
]

#lemma(title:[Flat Families with Contractible Fibers])[
  Let $r:x->s$ be a flat inner fibration. Assume that every fiber $x_t$ is
  weakly contractible and that, for every vertex $a in x$, the induced map of
  relative overcategories

  $
    x_(a slash)->s_(r(a) slash)
  $

  has weakly contractible fibers. Then every base change
  $x times_s s'->s'$ is a weak homotopy equivalence. In particular, $r$ is a
  weak homotopy equivalence.
]

#proofsketch[
  Build $s'$ simplex by simplex. Flatness identifies the new pullback as a
  homotopy pushout. In dimensions greater than one the horn attachment is a
  categorical equivalence; dimensions zero and one reduce respectively to
  the contractibility of the fibers and of the relative overcategories.
]

#proofsketch[
  #emph[Proof of the coherence criterion.]
  The formal coherence square of extension spaces is a square of Kan
  fibrations. Taking a fiber at a chosen extension converts its homotopy
  pushout into one of the local categories $cal(B)[sigma,z]$. The comparison
  maps are trivial Kan fibrations, so the square is a homotopy pushout exactly
  when this local category is weakly contractible. The one-input test reduces
  the latter condition to $1$-semi-inert arrows, while the local flatness
  proposition identifies it with flatness of $e_0$.
]

#quote[
  Coherence is a global compatibility law, but it is detected locally by
  transporting one new input through one active operation.
]

== Module Objects

Let $a$ be an ordinary associative algebra. A left $a$-module is an object
$m$ equipped with an action $a times.o m->m$. The essential point is not the
binary map itself, but what happens under iteration: in every composite there
is exactly one input belonging to $m$, while all remaining inputs belong to
$a$. The algebra inputs may branch and multiply, but the module input follows
one distinguished path through the whole operation tree.

The same idea works for an arbitrary operad. Let
$p:cal(C)^times.o->cal(O)^times.o$ be an $cal(O)$-monoidal $oo$-category and
let $a in Alg_(cal(O)) (cal(C))$. For an operation

$ alpha in Mul_cal(O) ({x_j}_(1<=j<=n);y) $

and a chosen input $i$, an $cal(O)$-module $m$ over $a$ should supply an
action of the form

$
  a(x_1) times.o dots times.o m(x_i) times.o dots times.o a(x_n)
  ->^(lambda_(alpha,i)) m(y)
$

These maps must be compatible with equivalences, units and operadic
substitution. Under substitution, the distinguished input of the outer
operation is replaced by the distinguished input of the inner operation;
all other branches are evaluated by the algebra $a$.

#quote[
  An $cal(O)$-module is an $cal(O)$-algebra operation with exactly one input
  declared to be the module variable; composition follows that marked input
  and evaluates every side branch in the algebra.
]

#definition(title:[$cal(O)$-Module Object over an Algebra])[
  Assume that $p:cal(C)^times.o->cal(O)^times.o$ is coCartesian, and let
  $a in Alg_(cal(O)) (cal(C))$. An #emph[$cal(O)$-module object over $a$]
  consists of the following data.

  + For every color $x in cal(O)$, an object

    $ m(x) in cal(C)_x $

  + For every $n>=1$, every operation

    $ alpha in Mul_cal(O) ({x_j}_(1<=j<=n);y) $

    and every distinguished input $1<=i<=n$, an action map in $cal(C)_y$

    $
      lambda_(alpha,i):
      times.o_alpha
        (a(x_1),dots,a(x_(i-1)),m(x_i),a(x_(i+1)),dots,a(x_n))
      ->m(y)
    $

    Here

    $
      times.o_alpha:product_(1<=j<=n) cal(C)_(x_j)->cal(C)_y
    $

    is the operadic tensor functor classified by the coCartesian lift of
    $alpha$. Thus every input except the $i$th is evaluated in the algebra
    $a$, while the $i$th input and the output are evaluated in the module
    $m$.

  + These maps are equivariant under permutations of the inputs. For an
    identity operation $id_x$, the map $lambda_(id_x,1)$ is equivalent to
    $id_(m(x))$.

  + They are coherently compatible with substitution: after substituting
    operations into $alpha$, the unique inner operation containing the
    distinguished input is evaluated by a module action $lambda$, while all
    other inner operations are evaluated by the algebra structure of $a$.
    The resulting composite agrees coherently with the action associated to
    the substituted operation.

  There is no marked action for a nullary operation, since it has no input to
  distinguish. Nullary operations still enter through the algebra $a$ when
  they occur on an unmarked side branch.

  In the one-colored case, writing $a$ for the algebra and $m$ for the module,
  an $n$-ary operation $alpha$ with marked input $i$ therefore determines

  $
    lambda_(alpha,i):
    a^(times.o(i - 1)) times.o m times.o a^(times.o(n - i)) -> m
  $

  We denote the resulting $oo$-category of module objects and compatible
  module maps by $cat("Mod")_a^(cal(O)) (cal(C))$.
]

#remark(title:[First Examples])[
  For the commutative operad, the choice of the marked slot is immaterial and
  this recovers the usual notion of a module over a commutative algebra. For
  an associative operad, the order of the marked slot records the appropriate
  one-sided or two-sided action data prescribed by that operad. At the other
  extreme, $EE_0$ has no nontrivial multi-input operation, so an
  $EE_0$-module is only an object of the ambient category.
]

#remark(title:[Why Semi-Inert Arrows Appear])[
  The preceding action formula is the intuition, but by itself it does not
  record all higher coherences. A semi-inert arrow is precisely the
  combinatorial device that moves one marked input without copying it. Its
  occupied slots are evaluated by $a$, while its unique unoccupied slot is
  filled by $m$. Thus semi-inert arrows package all maps $lambda_(alpha,i)$
  and all compatibilities among them into a single operadic object.
]

=== From Semi-Inert Arrows to Partial Algebras

Retain the semi-inert arrow category $cal(K)_cal(O)$ and its evaluations

$ e_0,e_1:cal(K)_cal(O)->cal(O)^times.o $

Let $cal(K)_cal(O)^0$ be its full subcategory spanned by the null arrows. A
null arrow forgets every ordinary input; unitality gives the basic
contractibility statement

#lemma(title:[Null Arrows])[
  If $cal(O)^times.o$ is unital, then

  $
    (e_0,e_1):cal(K)_cal(O)^0
    ->cal(O)^times.o times cal(O)^times.o
  $

  is a trivial Kan fibration. In particular, a null arrow with prescribed
  source and target is unique up to a contractible space of choices.
]

A #emph[partial $cal(O)$-algebra] in $cal(C)$ records the algebra operations
seen along these null arrows. Denote its $oo$-category by
$cat("PAlg")_(cal(O)) (cal(C))$. Restricting a genuine algebra to null arrows
gives a canonical functor

$
  Alg_(cal(O)) (cal(C))->cat("PAlg")_(cal(O)) (cal(C))
$

The semi-inert construction produces an $oo$-category
$overline(cat("Mod"))^(cal(O)) (cal(C))^times.o$ over
$cal(O)^times.o$: its points are compatible lifts to $cal(C)^times.o$ of the
semi-inert arrows in $cal(K)_cal(O)$. We retain only those points that carry
inert morphisms of $cal(K)_cal(O)$ to inert morphisms of
$cal(C)^times.o$.

#remark(title:[What Is Being Marked?])[
  Over an object $(x_1,dots,x_n)$, a semi-inert arrow may leave one output
  without an old input. That empty position is the future module variable;
  all occupied positions are algebra variables. Transport along
  $cal(K)_cal(O)$ remembers coherently which slot is the module slot.
]

=== The Module Operad over an Algebra

#definition(title:[Module Operad])[
  Let $a in Alg_(cal(O)) (cal(C))$. The #emph[$cal(O)$-module operad over
  $a$], denoted $cat("Mod")_a^(cal(O)) (cal(C))^times.o$, is the
  $oo$-operad whose objects are $cal(O)$-module objects over $a$ and whose
  active morphisms are the coherently compatible marked action maps
  $lambda_(alpha,i)$.

  Precisely, it is obtained by the fiber product

  $
    cat("Mod")_a^(cal(O)) (cal(C))^times.o
    :=overline(cat("Mod"))^(cal(O)) (cal(C))^times.o
      times_(cat("PAlg")_(cal(O)) (cal(C))) {a}
  $

  The map to $cat("PAlg")_(cal(O)) (cal(C))$ forgets the marked module input
  and remembers the algebra inputs. Pulling back along $a$ therefore fixes
  every unmarked input to be $a$. Its fiber over a color $x in cal(O)$ is denoted
  $cat("Mod")_(a,x)^(cal(O)) (cal(C))$. Its objects are the possible module
  objects of color $x$, and its active operations encode the action of the
  algebra inputs on the distinguished module input.
]

Thus the construction separates two kinds of data

#align(center, diagram({
  node((0, 0), [$a$], name: <a>)
  node((2, 0), [$cat("PAlg")_(cal(O)) (cal(C))$], name: <pa>)
  node((0, 1), [$cat("Mod")_a^(cal(O)) (cal(C))^times.o$], name: <ma>)
  node((2, 1), [$overline(cat("Mod"))^(cal(O)) (cal(C))^times.o$], name: <m>)
  edge(<a>, <pa>, [algebra operations], "->")
  edge(<ma>, <m>, "->")
  edge(<ma>, <a>, "->")
  edge(<m>, <pa>, [restrict to null arrows], label-side: right, "->")
}))

The square is a pullback: fixing $a$ fixes the ordinary algebra inputs, while
the remaining variable is the module object.

#remark(title:[How to Read the Construction])[
  The fiber product can be read in four steps.

  + A semi-inert arrow chooses a single #emph[hole] among the inputs of an
    $cal(O)$-operation. The hole is never duplicated, so it can be followed
    through a composite operation.

  + A lift to $cal(C)^times.o$ decorates every occupied input by algebra data
    and decorates the hole by a variable object $m$. Before choosing $a$, this
    is the space $overline(cat("Mod"))^(cal(O)) (cal(C))^times.o$ of all such
    decorated marked operations.

  + Restriction to null arrows forgets the moving hole and reads only the
    algebra decoration. The fiber product with ${a}$ imposes the boundary
    condition that this decoration is the fixed algebra $a$. Thus the fiber
    product does not create an action: it selects exactly those marked
    operations whose unmarked branches already use the multiplication of
    $a$.

  + What remains free is the object occupying the hole. An active marked
    operation therefore has the form

  #align(center, diagram({
    node((0, 0), [$a(x_1)$], name: <a1>)
    node((1, 0), [$m(x_i)$], name: <mi>)
    node((2, 0), [$a(x_n)$], name: <an>)
    node((1, 1), [$(alpha,i)$], name: <op>)
    node((1, 2), [$m(y)$], name: <my>)
    edge(<a1>, <op>, "->")
    edge(<mi>, <op>, [marked], label-side: center, "->")
    edge(<an>, <op>, "->")
    edge(<op>, <my>, [$lambda_(alpha,i)$], label-side: right, "->")
  }))

  When marked operations are substituted, the marked edge is joined to the
  next marked edge, while every side branch is evaluated by $a$. Coherence of
  $cal(O)^times.o$ says that all ways of performing these substitutions give
  the same result up to a contractible space of choices. This is exactly why
  the selected diagrams assemble into an $oo$-operad.
]

#remark(title:[A Binary Example])[
  For a binary operation $mu$, choosing the second input gives

  $ a times.o m ->^(lambda_(mu,2)) m $

  Substituting multiplication into the algebra input and substituting another
  marked action into the module input produce the two sides of the familiar
  associativity law. The module axiom is therefore not added separately: it
  is the image of operadic substitution inside
  $cat("Mod")_a^(cal(O)) (cal(C))^times.o$.
]

#theorem(title:[Existence of the Module Operad])[
  Suppose that $cal(O)^times.o$ is coherent and that
  $p:cal(C)^times.o->cal(O)^times.o$ is a fibration of $oo$-operads. For every
  algebra $a in Alg_(cal(O)) (cal(C))$, the projection

  $
    cat("Mod")_a^(cal(O)) (cal(C))^times.o
    ->cal(O)^times.o
  $

  is a fibration of $oo$-operads. Hence modules over $a$, together with all
  their operadic action maps, form an honest $oo$-operad rather than merely a
  simplicial set of diagrams.
]

The role of coherence is now concrete: by the coherence criterion,
$e_0:cal(K)_cal(O)->cal(O)^times.o$ is flat. Consequently semi-inert lifts
survive base change and compose with the homotopy-exactness required by the
operad axioms.

=== Detecting Inert Morphisms

#proposition(title:[Inertness in the Module Operad])[
  A morphism $f$ in
  $cat("Mod")_a^(cal(O)) (cal(C))^times.o$ is inert if and only if:

  + its underlying morphism $f_0$ in $cal(O)^times.o$ is inert
  + for every $e_0$-coCartesian lift $tilde(f)$ of $f_0$ in
    $cal(K)_cal(O)$, the endpoint morphism in $cal(C)^times.o$ classified by
    $f$ and evaluated at $tilde(f)$ is inert
]

#remark(title:[Meaning of the Second Test])[
  The first condition checks the ordinary algebra slots. The second moves the
  distinguished module slot through every compatible semi-inert lift and
  checks it there. Thus an inert module morphism is inert in both the algebra
  directions and the marked module direction.
]

#proofsketch[
  The null-arrow lemma first makes the partial-algebra construction an
  $oo$-category over $cal(O)^times.o$. Coherence makes $e_0$ a flat
  isofibration, so pullback along semi-inert arrows preserves the categorical
  equivalences used in the operadic Segal conditions. The displayed
  inertness criterion is precisely the condition ensuring that these
  pullbacks preserve inert edges. Restricting to the fiber over $a$ then gives
  the stated fibration of $oo$-operads.
]

=== The $EE_0$ Sanity Check

#proposition(title:[$EE_0$-Modules])[
  Let $q:cal(C)^times.o->EE_0^times.o$ be a fibration of $oo$-operads. For
  every $EE_0$-algebra $a$, evaluation at the distinguished module input
  induces an equivalence

  $
    cat("Mod")_a^(EE_0) (cal(C))->cal(C)
  $
]

Indeed, $EE_0$ has no nontrivial multi-input operation that could impose an
additional action law. Once the $EE_0$-algebra $a$ is fixed, an $a$-module is
therefore just an arbitrary object of $cal(C)$. This extreme case confirms
that the module operad adds exactly the operations prescribed by the base
operad, and no hidden structure.

== Algebra Objects in Module Categories

The preceding construction does more than produce a category of modules: it
also remembers enough operadic structure to form algebras #emph[inside] that
category. Classically, if $a$ is a commutative algebra, then a commutative
algebra object of $cat("Mod")_a (cal(C))$ is simply a commutative algebra $b$
of $cal(C)$ together with a map $a->b$. The $oo$-categorical statement is the
same, but the map $a->b$ and all of its compatibilities are encoded by the
semi-inert construction.

Write $Alg_(cal(O)) (cal(C))^(a slash)$ for the undercategory whose objects
are morphisms $a->b$ of $cal(O)$-algebras.

=== The Universal Arrow Description

#proposition(title:[Algebras in the Universal Module Operad])[
  Suppose that $cal(O)^times.o$ is coherent and that
  $cal(C)^times.o->cal(O)^times.o$ is a fibration of $oo$-operads. There is a
  canonical equivalence

  $
    Alg_(cal(O)) (overline(cat("Mod"))^(cal(O)) (cal(C)))
    tilde.eq
    Fun(Delta^1,Alg_(cal(O)) (cal(C)))
  $

  Thus an algebra in the universal module construction is exactly an arrow
  $a->b$ between $cal(O)$-algebras.
]

#remark(title:[Why an Arrow Appears])[
  The source of a semi-inert arrow records the algebra inputs, while its
  distinguished empty slot records the future module variable. An algebra
  object supplies compatible operations at both endpoints. Evaluation at
  the two endpoints therefore produces two algebras $a,b$, and transport
  along the marked slot produces the algebra map $a->b$. Conversely, such a
  map lets every operation of $a$ act on $b$ through the corresponding
  operation of $b$.

  #align(center, diagram({
    node((0, 0), [$a$], name: <a>)
    node((1, 0), [$b$], name: <b>)
    node((0.5, 1), [$Alg_(cal(O)) (overline(cat("Mod"))^(cal(O)) (cal(C)))$],
      name: <alg>)
    edge(<a>, <b>, [algebra map], "->")
    edge(<alg>, <a>, [$e_0$], label-side: left, "->")
    edge(<alg>, <b>, [$e_1$], label-side: right, "->")
  }))
]

=== Algebras over a Fixed Algebra

#theorem(title:[Algebras in $a$-Modules])[
  Let $a in Alg_(cal(O)) (cal(C))$. Restricting the preceding equivalence to
  the fiber over $a$ gives a canonical equivalence

  $
    Alg_(cal(O)) (cat("Mod")_a^(cal(O)) (cal(C)))
    tilde.eq
    Alg_(cal(O)) (cal(C))^(a slash)
  $

  In other words, an $cal(O)$-algebra object in $a$-modules is precisely an
  $cal(O)$-algebra $b$ in $cal(C)$ equipped with a morphism $a->b$.
]

In the commutative case this reads

$
  cat("CAlg") (cat("Mod")_a (cal(C)))
  tilde.eq
  cat("CAlg") (cal(C))^(a slash)
$

The familiar phrase “a commutative $a$-algebra” therefore has no additional
meaning hidden in it: it is exactly a commutative algebra under $a$.

#proofsketch[
  The universal module operad maps to the arrow category of
  $Alg_(cal(O)) (cal(C))$ by endpoint evaluation. Coherence makes the source
  evaluation on semi-inert arrows flat, so restriction and the required Kan
  extensions preserve the operadic Segal conditions. The resulting endpoint
  functor is an equivalence. Pulling it back along the vertex ${a}$ identifies
  its fiber with the undercategory of arrows beginning at $a$.
]

=== Iterating the Module Construction

Let $cat("Mod")^(cal(O)) (cal(C))$ denote the total $oo$-category of pairs
$(b,m)$ consisting of an $cal(O)$-algebra $b$ and a $b$-module $m$. Its
projection remembers $b$. The preceding theorem upgrades to the pullback
formula

$
  cat("Mod")^(cal(O)) (cat("Mod")_a^(cal(O)) (cal(C)))
  tilde.eq
  cat("Mod")^(cal(O)) (cal(C))
  times_(Alg_(cal(O)) (cal(C)))
  Alg_(cal(O)) (cal(C))^(a slash)
$

An object on either side is therefore the same triple

$ a->b, quad m in cat("Mod")_b^(cal(O)) (cal(C)) $

#proposition(title:[Modules in Modules])[
  Let $b$ be an $cal(O)$-algebra object of
  $cat("Mod")_a^(cal(O)) (cal(C))$, and let $bar(b)$ be the target algebra in
  $cal(C)$ corresponding to the map $a->bar(b)$. Then there is a canonical
  equivalence

  $
    cat("Mod")_b^(cal(O))
      (cat("Mod")_a^(cal(O)) (cal(C)))
    tilde.eq
    cat("Mod")_(bar(b))^(cal(O)) (cal(C))
  $

  Thus a $b$-module internal to $a$-modules is just a module over the
  underlying algebra $bar(b)$ in $cal(C)$.
]

#remark(title:[Classical Reading])[
  For commutative rings, if $a->b$ is a ring map, then a $b$-module in the
  category of $a$-modules carries no extra structure beyond its ordinary
  $b$-module structure: the $a$-action is already obtained by restriction of
  scalars along $a->b$. The proposition is the fully coherent operadic form
  of this elementary fact.
]

#proofsketch[
  Both sides are obtained by fixing the same algebra arrow $a->bar(b)$ in the
  universal category of marked operations. The defining squares are homotopy
  pullbacks, and endpoint evaluation is an equivalence; taking the relevant
  fibers therefore gives the displayed equivalence of module
  $oo$-categories.
]

#quote[
  Algebra objects in $a$-modules are algebras under $a$, and modules over
  such an algebra are the same whether computed inside $a$-modules or in the
  original ambient category.
]

== Modules over Trivial Algebras

The simplest module theory is already instructive. In an ordinary symmetric
monoidal category, the unit object $1$ is a commutative algebra, and every
object $c$ has the canonical action

$
  1 times.o c tilde.eq c
$

Hence a module over $1$ is just an object of the ambient category. The next
result says that this remains true for a coherent $oo$-operad, including all
of its higher operations rather than merely its underlying $oo$-category.

#remark(title:[Trivial Algebra])[
  Recall that a trivial $cal(O)$-algebra $a$ takes every color $x$ to the
  chosen unit object $1_x$ in the corresponding fiber. Equivalently, $a$ is
  an initial object of $Alg_(cal(O)) (cal(C))$. Its structure maps contain no
  information beyond the unit constraints.
]

#proposition(title:[Modules over a Trivial Algebra])[
  Let $cal(O)^times.o$ be coherent, let
  $p:cal(C)^times.o->cal(O)^times.o$ be a fibration of $oo$-operads, and let
  $a$ be a trivial $cal(O)$-algebra in $cal(C)$. Then the forgetful map is an
  equivalence of $oo$-operads

  $
    theta:(cat("Mod")_a^(cal(O)) (cal(C)))^times.o
    tilde.eq
    cal(C)^times.o
  $

  Thus every object of $cal(C)$ admits an essentially unique $a$-module
  structure, functorially and compatibly with all operadic operations.
]

#remark(title:[What the Action Becomes])[
  A module operation has one distinguished module input; all remaining
  algebra inputs are values of $a$, hence unit objects. Substituting them into
  an operation leaves only the corresponding ambient operation on the module
  input. In the one-colored symmetric monoidal case this is simply

  $
    1 times.o dots.c times.o 1 times.o m times.o 1 times.o dots.c times.o 1
    tilde.eq m
  $

  Therefore the equivalence above forgets no action data: that data is forced
  by the unit laws and has a contractible space of choices.
]

#proofsketch[
  Unit objects provide the decisive lifting property: every semi-inert
  morphism in $cal(O)^times.o$ can be lifted to a $p$-coCartesian morphism by
  filling all unused inputs with units. The universal module construction can
  consequently be described by functors on the semi-inert arrow category.
  Restriction to its unit subcategory is a trivial Kan fibration: the required
  extensions exist as relative left Kan extensions, and their choices are
  contractible. Since trivial algebras themselves form a contractible fiber,
  the forgetful map $theta$ is essentially surjective and fully faithful.
  Its construction preserves inert morphisms, so this is an equivalence of
  $oo$-operads, not only an equivalence of underlying $oo$-categories.
]

In particular, for the unit commutative algebra one recovers

$
  cat("Mod")_1 (cal(C)) tilde.eq cal(C)
$

Combining this with the preceding section also gives

$
  Alg_(cal(O)) (cat("Mod")_a^(cal(O)) (cal(C)))
  tilde.eq
  Alg_(cal(O)) (cal(C))
$

because the trivial algebra $a$ is initial, so its undercategory is the whole
algebra category up to equivalence.

#quote[
  A module over the trivial algebra is not an object with extra structure; it
  is an ordinary object whose unique action is supplied by the unit laws.
]

== Limits of Modules

Let $cal(C)^times.o$ be a symmetric monoidal category, let $a$ be a
commutative algebra object, and let ${m_i}$ be a diagram of $a$-modules. If
the underlying diagram admits a limit $m=lim_i m_i$ in $cal(C)$, the maps

$
  a times.o m -> a times.o m_i -> m_i
$

assemble, by the universal property of $m$, to an action
$a times.o m -> m$. The associativity and unit identities can be checked
after projection to every $m_i$, so $m$ is also the limit in the category of
$a$-modules. The same argument survives in the operadic setting, with
ordinary limits replaced by relative limits in the appropriate fiber.

#proposition(title:[Limits Are Created in the Underlying Fiber])[
  Let $cal(O)^times.o$ be coherent and let

  $
    q:cal(C)^times.o -> cal(O)^times.o
  $

  be a fibration of $oo$-operads. Fix an algebra
  $a in Alg_(cal(O)) (cal(C))$ and a color $x in cal(O)$. Write

  $
    U_(a,x):cat("Mod")_(a,x)^(cal(O)) (cal(C))->cal(C)_x
  $

  for the underlying-object functor. Suppose that a diagram
  $p:K->cat("Mod")_(a,x)^(cal(O)) (cal(C))$ has an underlying
  $q$-limit cone in $cal(C)_x$. Then this cone admits an essentially unique
  compatible $a$-module structure, and hence determines a limit cone in
  $cat("Mod")_(a,x)^(cal(O)) (cal(C))$.

  More precisely, an extension $bar(p):K^triangle.l ->
  cat("Mod")_(a,x)^(cal(O)) (cal(C))$ is a limit diagram if and only if
  $U_(a,x) compose bar(p)$ is a $q$-limit diagram in $cal(C)_x$.
]

#remark(title:[The Relative Form])[
  The statement does not require $q$ to be coCartesian. For a general
  fibration, “limit” means a #emph[$q$-limit]: it is universal among cones
  whose image in $cal(O)^times.o$ is fixed. The theorem says that the
  diagonal map from the module operad to $cal(C)^times.o$ creates these
  relative limits. When $q$ is a coCartesian fibration and the base diagram
  is constant at $x$, this reduces to an ordinary limit in the fiber
  $cal(C)_x$.
]

#corollary(title:[Fiberwise Completeness])[
  Assume that $q$ is an $cal(O)$-monoidal $oo$-category. If the fiber
  $cal(C)_x$ admits $K$-indexed limits, then so does
  $cat("Mod")_(a,x)^(cal(O)) (cal(C))$, for every
  $a in Alg_(cal(O)) (cal(C))$, and $U_(a,x)$ preserves and reflects those
  limits

  $
    U_(a,x) (lim_K m_k) tilde.eq lim_K U_(a,x) (m_k)
  $

  In particular, products, pullbacks, and equalizers of modules are computed
  on their underlying objects whenever the corresponding limits exist in
  $cal(C)_x$.
]

=== Restriction of Scalars as Cartesian Transport

Let $cat("Mod")^(cal(O)) (cal(C))_x$ denote the $oo$-category of pairs
$(a,m)$ with $a in Alg_(cal(O)) (cal(C))$ and
$m in cat("Mod")_(a,x)^(cal(O)) (cal(C))$.

#proposition(title:[The Cartesian Fibration of Modules])[
  For every color $x in cal(O)$, the projection

  $
    phi_x:cat("Mod")^(cal(O)) (cal(C))_x
      ->Alg_(cal(O)) (cal(C))
  $

  is a Cartesian fibration. A morphism above a map of algebras
  $u:a->b$ is $phi_x$-Cartesian if and only if its image in $cal(C)_x$ is an
  equivalence. Consequently, Cartesian transport along $u$ is the
  restriction-of-scalars functor

  $
    u^*:cat("Mod")_(b,x)^(cal(O)) (cal(C))
      ->cat("Mod")_(a,x)^(cal(O)) (cal(C))
  $

  and it leaves the underlying object unchanged

  $
    U_(a,x) compose u^* tilde.eq U_(b,x)
  $

  The corresponding global projection
  $phi:cat("Mod")^(cal(O)) (cal(C))->Alg_(cal(O)) (cal(C))$ is likewise a
  Cartesian fibration, with the same criterion for Cartesian morphisms.
]

#remark(title:[What This Organizes])[
  The fiber of $phi_x$ over $a$ is precisely
  $cat("Mod")_(a,x)^(cal(O)) (cal(C))$. Thus one construction simultaneously
  records all module categories and all restriction-of-scalars functors

  For $m in cat("Mod")_(b,x)^(cal(O)) (cal(C))$, the relevant Cartesian
  lift is the upper edge in

  #align(center, diagram({
    node((0, 0), [$(a,u^*m)$], name: <uam>)
    node((1, 0), [$(b,m)$], name: <bm>)
    node((0, 1), [$a$], name: <a>)
    node((1, 1), [$b$], name: <b>)
    edge(<uam>, <bm>, [$tilde(u)$], "->")
    edge(<uam>, <a>, [$phi_x$], "->")
    edge(<bm>, <b>, [$phi_x$], "->")
    edge(<a>, <b>, [$u$], "->")
  }))

  Pulling its source back from the target $m$ produces the contravariant
  functor $u^*:cat("Mod")_(b,x)^(cal(O)) (cal(C))->
  cat("Mod")_(a,x)^(cal(O)) (cal(C))$.
]

=== Splitting the Inputs

#definition(title:[Splitting])[
  A #emph[splitting] of $chevron.l n chevron.r in Fin_*$ is a pair of inert
  morphisms

  $
    alpha:chevron.l n chevron.r->chevron.l n_0 chevron.r,
    quad
    beta:chevron.l n chevron.r->chevron.l n_1 chevron.r
  $

  whose selected non-basepoint inputs partition
  $chevron.l n chevron.r^circle$

  $
    alpha^(-1) (chevron.l n_0 chevron.r^circle)
      union
    beta^(-1) (chevron.l n_1 chevron.r^circle)
      = chevron.l n chevron.r^circle,
    quad
    alpha^(-1) (chevron.l n_0 chevron.r^circle)
      inter
    beta^(-1) (chevron.l n_1 chevron.r^circle)
      = emptyset
  $

  A splitting of a diagram $p:K->Ner(Fin_*)$ is a pair of natural
  transformations $alpha:p->p_0$ and $beta:p->p_1$ which gives such a
  splitting at every vertex. For a diagram $p:K->cal(O)^times.o$, the two
  transformations are additionally required to be inert. We say that
  $alpha$ is #emph[split] and call $beta$ its #emph[complement].
]

#remark(title:[Geometric Meaning])[
  A splitting separates the inputs of an operation into two blocks. In the
  module construction one block contains the distinguished module input and
  the other contains the algebra inputs

  #align(center, diagram({
    node((0, 0), [$chevron.l n chevron.r$], name: <n>)
    node((-1.1, 1), [$chevron.l n_0 chevron.r$], name: <n0>)
    node((1.1, 1), [$chevron.l n_1 chevron.r$], name: <n1>)
    edge(<n>, <n0>, [$alpha$], "->")
    edge(<n>, <n1>, [$beta$], "->")
  }))

  Inert lifts of $alpha$ and $beta$ exhibit the original object as the
  operadic product of the two blocks. The space of complements and compatible
  inert lifts is contractible, so this decomposition introduces no hidden
  choice.
]

#proposition(title:[Splitting Criterion for Module Limits])[
  Let $bar(p):K^triangle.l->cal(C)^times.o$ be a cone lying over a split
  diagram in $cal(O)^times.o$. Write $bar(p)_0$ and $bar(p)_1$ for the cones
  obtained from the two complementary inert projections. Then $bar(p)$ is a
  $q$-limit cone if and only if the required component cone is a $q$-limit
  cone after the complementary component has been fixed. Equivalently,
  operadic products allow the limit problem to be checked one block of inputs
  at a time.
]

#proofsketch[
  The universal module construction presents a module as a compatible
  functor on the category of semi-inert arrows. Coherence of
  $cal(O)^times.o$ makes source evaluation on that arrow category flat, so a
  relative limit cone in $cal(C)^times.o$ lifts through the required right
  Kan extension. Splittings reduce the lifting problem to its module block
  and algebra block. The algebra block is already fixed by $a$, while the
  module block is the underlying limit in $cal(C)_x$. The contractibility of
  complements makes these componentwise lifts glue uniquely up to
  equivalence. Applying the same argument to a map $a->b$ shows that its
  Cartesian lift changes only the action, which gives restriction of scalars.
]

#quote[
  Limits of modules are computed on underlying objects; variation of the
  algebra is encoded by Cartesian transport, and splitting the inputs is the
  mechanism that makes both statements compatible with operadic composition.
]

== Colimits of Modules

The classical calculation already contains the main idea. Let
$(m_i)_(i in I)$ be a diagram of left $a$-modules and suppose that
$m=colim_i m_i$ exists in the underlying symmetric monoidal category. If
tensoring with $a$ preserves this colimit, then

$
  a times.o m
  tilde.eq colim_i (a times.o m_i)
  ->colim_i m_i
  tilde.eq m
$

defines an action on $m$. Associativity and unitality follow from those of
the actions on the $m_i$, so $m$ is the colimit in the module category.

There are two points hidden in this short argument. First, “tensoring with
$a$ preserves colimits” must be interpreted simultaneously for every
operation of the base operad. Second, the action on the colimit must be
constructed with all higher coherences. Operadic colimit diagrams and the
semi-inert arrow category provide exactly these two ingredients.

=== Presentable $cal(O)$-Monoidal Categories

#definition(title:[Presentable $cal(O)$-Monoidal $oo$-Category])[
  Let $cal(O)^times.o$ be an $oo$-operad. An $cal(O)$-monoidal
  $oo$-category

  $
    q:cal(C)^times.o->cal(O)^times.o
  $

  is #emph[presentable] if the following conditions hold.

  + The map $q$ is a coCartesian fibration of $oo$-operads.

  + The fibration $q$ is compatible with small colimits: every fiber
    $cal(C)_x$ admits small colimits and every operadic tensor functor

    $
      times.o_alpha:
      product_(1<=i<=n) cal(C)_(x_i)->cal(C)_y
    $

    preserves them separately in each variable.

  + Every fiber $cal(C)_x$ is a presentable $oo$-category.
]

#remark(title:[The Operadic Meaning of the Hypothesis])[
  For a one-colored symmetric monoidal category, compatibility says that
  $c times.o (-)$ preserves small colimits for every $c$. For a colored
  operad it must hold for every operation

  $
    alpha in Mul_cal(O) ({x_i}_(1<=i<=n);y)
  $

  and in every input variable. This is the precise higher-categorical form
  of the classical condition used in the first calculation.
]

=== The Extension Theorem for Module Colimits

The main technical issue is not taking a colimit in one fiber, but extending
that colimit through the semi-inert diagrams which encode a moving module
input. We formulate the result in a form that separates the local colimit
condition from the global coherent extension.

Let $cal(O)^times.o$ be coherent, let

$
  q:cal(C)^times.o->cal(O)^times.o
$

be a fibration of $oo$-operads, and fix
$a in Alg_(cal(O)) (cal(C))$. Write

$
  psi:cat("Mod")_a^(cal(O)) (cal(C))^times.o
  ->cal(O)^times.o
$

for the module operad. Suppose that $K$ is an $oo$-category and that

$
  p:K->cat("Mod")_a^(cal(O)) (cal(C))^times.o
$

is a diagram. Fix an active cone

$
  overline(r):K^triangle.r->cal(O)^times.o_"act"
$

extending $psi compose p$, and let its cone point have value
$X in cal(O)^times.o$. Using the source evaluation
$e_0:cal(K)_cal(O)->cal(O)^times.o$, form

$
  overline(cal(D))
  :=K^triangle.r times_(cal(O)^times.o) cal(K)_cal(O),
  quad
  cal(D):=K times_(cal(O)^times.o) cal(K)_cal(O)
$

The module diagram $p$ is equivalently encoded by a functor

$
  F_p:cal(D)->cal(C)^times.o
$

compatible with the fixed partial algebra determined by $a$.

For an object $D=(v,id_X)$ over the cone point, let
$cal(D)_(\/D)^"act"$ be the full subcategory of

$
  cal(D) times_(overline(cal(D))) overline(cal(D))_(\/D)
$

spanned by arrows $D'->D$ whose source belongs to $cal(D)$ and whose image
in $cal(O)^times.o$ determines a square

#align(center, diagram({
  node((0, 0), [$X'$], name: <xp>)
  node((1, 0), [$Y'$], name: <yp>)
  node((0, 1), [$X$], name: <x>)
  node((1, 1), [$X$], name: <xx>)
  edge(<xp>, <yp>, "->")
  edge(<xp>, <x>, "->")
  edge(<yp>, <xx>, [$f$ #text[ active]], label-side: left, "->")
  edge(<x>, <xx>, [$id_X$], label-side: right, "->")
}))

This is the category of active ways to transport the distinguished module
input into the cone point.

#theorem(title:[Operadic Extension Theorem for Modules])[
  In the situation above, assume that for every
  $D=(v,id_X)$ the diagram

  $
    cal(D)_(\/D)^"act"->overline(cal(D))_(\/D)
      ->overline(cal(D))
  $

  admits an extension to an operadic $q$-colimit cone in
  $cal(C)^times.o$. Then the following statements hold.

  + There exists an extension

    $
      overline(p):K^triangle.r
      ->cat("Mod")_a^(cal(O)) (cal(C))^times.o
    $

    lying over $overline(r)$ and extending $p$.

  + Let
    $overline(F):overline(cal(D))->cal(C)^times.o$ be the functor
    corresponding to an arbitrary extension $overline(p)$. The cone
    $overline(p)$ is an operadic $psi$-colimit diagram if and only if, for
    every $D=(v,id_X)$, the composite

    $
      (cal(D)_(\/D)^"act")^triangle.r
      ->overline(cal(D))_(\/D)
      ->overline(cal(D))
      ->^overline(F) cal(C)^times.o
    $

    is an operadic $q$-colimit diagram.
]

#remark(title:[Local-to-Global Meaning])[
  The theorem says that a module colimit is checked at the single marked
  input. Every unmarked branch is already controlled by the fixed algebra
  $a$. Coherence of $cal(O)^times.o$ then guarantees that the locally
  constructed cone can be transported through every active operation and
  glued into one module object.
]

#proofsketch[
  Pull the extension problem back to the semi-inert arrow category
  $cal(K)_cal(O)$. A simplex there records a chain of pointed maps, each of
  which is active, inert, or neutral. Filter the relevant nerve first by the
  length of this chain and then by six classes: the new simplices whose last
  noninvertible stages are active, inert, neutral followed by active,
  active followed by inert, and the two boundary cases involving consecutive
  inert stages.

  The extension is constructed transfinitely along this filtration. At an
  active attachment, the required filler is supplied by the assumed
  operadic $q$-colimit. At an inert attachment, it is supplied by an inert
  lift in $cal(C)^times.o$. Neutral attachments reduce to inner-horn
  extensions. The coherence criterion makes source evaluation from
  $cal(K)_cal(O)$ flat; consequently the square controlling each attachment
  is a homotopy pushout. The relevant restriction maps are therefore trivial
  Kan fibrations, so every extension exists through a contractible space of
  choices.

  For the characterization of operadic $psi$-colimits, apply the same
  filtration after adjoining an arbitrary active target cocone. The local
  operadic $q$-colimit condition supplies all fillers in one direction. In
  the other direction, the uniqueness property of operadic colimit cones
  forces the local comparison cones to be operadic $q$-colimits. This proves
  both existence and the stated if-and-only-if criterion.
]

#quote[
  A colimit of modules is assembled locally at the marked input and glued
  globally by coherence of the operad.
]

=== Unit Objects and the Regular Module

The one-simplex case of the extension theorem gives a useful recognition
criterion. Let $m_0$ lie over the zero-input object of the module operad and
let

$
  f:m_0->m
$

be a morphism. It determines a functor $F_f$ on the pullback of
$cal(K)_cal(O)$ along the base edge $psi(f)$.

#corollary(title:[One-Edge Colimit Test])[
  The following conditions are equivalent.

  + The edge $f$ is classified by an operadic $psi$-colimit diagram

    $
      Delta^1->cat("Mod")_a^(cal(O)) (cal(C))^times.o
    $

  + The canonical comparison between the value of $F_f$ on the base edge
    and its value on the identity of the target is an equivalence

    $
      F_f (psi(f))->F_f (id_(psi(m)))
    $

  Moreover, for every $X in cal(O)^times.o$ there exists such an edge with
  $psi(m)=X$.
]

#proofsketch[
  For a one-object diagram, the local active transport category in the
  extension theorem has a final object. The local operadic colimit condition
  therefore reduces to the displayed comparison map. Existence follows from
  the existence part of the theorem.
]

#corollary(title:[Units in the Module Operad])[
  If $q:cal(C)^times.o->cal(O)^times.o$ is a fibration of $oo$-operads and
  $cal(O)^times.o$ is coherent, then

  $
    psi:cat("Mod")_a^(cal(O)) (cal(C))^times.o
    ->cal(O)^times.o
  $

  has unit objects.
]

Every algebra is canonically a module over itself. Indeed, the equivalence

$
  Alg_(cal(O)) (cat("Mod")_a^(cal(O)) (cal(C)))
  tilde.eq Alg_(cal(O)) (cal(C))^(a slash)
$

sends $id_a:a->a$ to the #emph[regular module], denoted $a_"reg"$. Write
$overline(a)$ for the corresponding $cal(O)$-algebra object of the module
operad.

#proposition(title:[The Regular Module Is the Unit])[
  Let $0$ be the zero object of the unital operad
  $cal(O)^times.o$. For every $X in cal(O)^times.o$, a choice of edge
  $0->X$ induces an edge

  $
    eta_X:overline(a)(0)->overline(a)(X)
  $

  in the module operad. This edge is an operadic $psi$-colimit diagram and
  exhibits the regular module $overline(a)(X)$ as the $X$-unit object of
  $cat("Mod")_a^(cal(O)) (cal(C))^times.o$.
]

#proofsketch[
  The comparison in the one-edge test becomes the identity map
  $a(X)->a(X)$. Hence $eta_X$ is an operadic $psi$-colimit. The construction
  is independent of the chosen edge $0->X$ up to a contractible space of
  choices because the total category of a unital operad is pointed.
]

#remark(title:[The Familiar One-Colored Case])[
  If $a$ is a commutative algebra in a symmetric monoidal category, the
  regular module is simply $a$ with action given by multiplication

  $
    a times.o a->a
  $

  When relative tensor products exist, it is the tensor unit of
  $cat("Mod")_a (cal(C))$

  $
    a times_a m tilde.eq m
  $
]

=== Colimits in the Fibers

#theorem(title:[$kappa$-Small Colimits of Modules])[
  Let $kappa$ be an uncountable regular cardinal. Suppose that
  $cal(O)^times.o$ is a $kappa$-small coherent $oo$-operad and that

  $
    q:cal(C)^times.o->cal(O)^times.o
  $

  is an $cal(O)$-monoidal $oo$-category compatible with $kappa$-small
  colimits. Then:

  + the projection

    $
      psi:cat("Mod")_a^(cal(O)) (cal(C))^times.o
      ->cal(O)^times.o
    $

    is a coCartesian fibration of $oo$-operads compatible with
    $kappa$-small colimits;

  + for every color $x in cal(O)$, the forgetful functor

    $
      U_(a,x):cat("Mod")_(a,x)^(cal(O)) (cal(C))->cal(C)_x
    $

    creates and detects $kappa$-small colimits.

  Explicitly, if $K$ is $kappa$-small and

  $
    overline(p):K^triangle.r
    ->cat("Mod")_(a,x)^(cal(O)) (cal(C))
  $

  is a cocone, then $overline(p)$ is a colimit diagram if and only if
  $U_(a,x) compose overline(p)$ is a colimit diagram in $cal(C)_x$.
]

#proofsketch[
  Compatibility gives the necessary operadic $q$-colimit cones in
  $cal(C)^times.o$. Apply the extension theorem to lift them to the module
  operad. For a diagram contained in the fiber over $x$, the local active
  transport category has the identity of $x$ as a final object. Its
  inclusion is left cofinal, so the local condition reduces to the
  underlying cone in $cal(C)_x$. Compatibility with $kappa$-small colimits
  then identifies an operadic $q$-colimit with the ordinary fiberwise
  colimit. The one-simplex case supplies coCartesian lifts, and the same
  argument in each variable proves compatibility of $psi$ with these
  colimits.
]

#remark(title:[What “Created” Means])[
  Begin with a diagram of modules and forget their actions. Take its colimit
  in $cal(C)_x$. The theorem supplies an essentially unique module action on
  that object for which the cocone maps are module maps. Thus the forgetful
  functor does not merely preserve the colimit: it constructs it and detects
  its universal property.
]

#remark(title:[Operadic versus Fiberwise Colimits])[
  For a general diagram in the total module operad, the correct condition is
  operadic: after adjoining any extra algebra inputs and applying any active
  operation of $cal(O)$, the underlying cone must remain a colimit in the
  appropriate fiber. When the diagram stays over one color and $q$ is
  compatible with the relevant colimits, this extra test is automatic and
  the theorem reduces it to an ordinary colimit in $cal(C)_x$.
]

=== Presentability of Module Categories

#theorem(title:[Presentability of Modules])[
  Let $cal(O)^times.o$ be a small coherent $oo$-operad, let

  $
    q:cal(C)^times.o->cal(O)^times.o
  $

  exhibit $cal(C)^times.o$ as a presentable $cal(O)$-monoidal
  $oo$-category, and let $a in Alg_(cal(O)) (cal(C))$. Then

  $
    psi:cat("Mod")_a^(cal(O)) (cal(C))^times.o
    ->cal(O)^times.o
  $

  exhibits the module operad as a presentable $cal(O)$-monoidal
  $oo$-category.
]

#proofsketch[
  The preceding theorem shows that $psi$ is coCartesian, compatible with all
  small colimits, and that every fiber admits small colimits. It remains to
  prove accessibility.

  Fix a color $x$. Let $cal(E)_x subset.eq
  (cal(O)^times.o)_(x slash)$ be the full subcategory spanned by semi-inert
  arrows $x->y$, and let $cal(E)_(0,x)$ be the full subcategory spanned by
  those arrows which are equivalences. The fixed algebra $a$ determines a
  functor $a':cal(E)_(0,x)->cal(C)^times.o$. The semi-inert description of
  modules identifies the fiber of modules at $x$ with the fiber over $a'$ of
  the restriction functor

  $
    Phi_x:
    Fun_(cal(O)^times.o) (cal(E)_x,cal(C)^times.o)
    ->Fun_(cal(O)^times.o) (cal(E)_(0,x),cal(C)^times.o)
  $

  where only functors preserving the relevant inert morphisms are retained.
  Since $cal(O)^times.o$ is small and the fibers of $cal(C)$ are
  presentable, both functor categories are accessible and $Phi_x$ is an
  accessible functor. Its fiber over $a'$ is therefore accessible. Combined
  with the existence of small colimits, this makes
  $cat("Mod")_(a,x)^(cal(O)) (cal(C))$ presentable. The argument applies to
  every color, completing the proof.
]

#quote[
  Under the standard presentability hypotheses, module categories inherit
  both the colimits and the operadic tensor operations of the ambient
  category; the forgetful functors compute those colimits fiber by fiber.
]

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
must all be recorded. The associative operad packages this complete system
of data.

== The Associative $oo$-Operad

We now recast ordinary associative algebras in the language of operads. The
essential combinatorial datum is not a permutation symmetry, but an ordering
of the inputs.

#definition(title:[The Colored Operad $Assoc$])[
  The one-colored operad $Assoc$ has a unique color $a$. For a finite
  set $I$, its $I$-ary operations are the linear orders on $I$:

  $
    Mul_(Assoc) ({a}_(i in I);a):="Lin"(I),
  $

  For $alpha:I->J$, orders on $J$ and on each fiber
  $alpha^(-1)({j})$ compose to the lexicographic order characterized by

  $
    i<i'
    "iff"
    alpha(i)<alpha(i')
    " or "
    (alpha(i)=alpha(i')=j " and " i <_j i').
  $

  The empty and singleton orders supply the nullary unit and unary identity.
]

#remark(title:[Fibers as Ordered Input Blocks])[
  For $j in J$, the fiber is the ordinary inverse-image set

  $
    alpha^(-1)({j})={i in I:alpha(i)=j}.
  $

  It is the block of inner inputs substituted into the $j$th input of the
  outer operation. The chosen order on $J$ orders the blocks, while the order
  on each fiber orders the elements inside that block. Concatenating these
  locally ordered blocks is precisely the lexicographic composition above.
]

#proposition(title:[$Assoc$ Controls Ordinary Associative Algebras])[
  Let $cal(E)$ be a symmetric monoidal category. A map of colored operads

  $
    Assoc->cal(E)
  $

  is equivalent to the choice of an associative algebra object $A in cal(E)$.
  The empty order gives the unit $1->A$, the standard order on two elements
  gives $A times.o A->A$, and the order on $n$ elements gives the iterated
  product $A^(times.o n)->A$. Lexicographic substitution is exactly the unit
  and associativity law.
]

#proofsketch[
  Given an operad map $F$, set $A=F(a)$. The images of the empty order and
  the standard two-element order give $eta$ and $mu$. Since $F$ preserves
  operadic substitution, inserting ordered blocks becomes iterated
  multiplication; the two decompositions of a three-element order give the
  associativity law, and inserting the empty order gives the unit laws.

  Conversely, from $(A,eta,mu)$ assign to a linearly ordered finite set its
  iterated product in that order, using $eta$ for the empty set. Associativity
  makes the result independent of parenthesization, while the unit law handles
  empty blocks. These two constructions are inverse.
]

#definition(title:[The Associative $oo$-Operad])[
  Applying the operadic nerve construction to $Assoc$ gives

  $
    Assoc->Ner(Fin_*).
  $

  Its objects lie over the pointed finite sets
  $chevron.l n chevron.r$. A morphism over a pointed map
  $f:chevron.l m chevron.r->chevron.l n chevron.r$ is a choice of linear
  order on every fiber $f^(-1)({j})$, $1<=j<=n$; composition orders the
  resulting blocks lexicographically. This is the #emph[associative
  $oo$-operad]. Its fiber over $chevron.l 1 chevron.r$ has a single color $a$.
]

#remark(title:[Fibers over Pointed Finite Sets])[
  For a nonbasepoint $j in chevron.l n chevron.r$, the fiber

  $
    f^(-1)({j})={i in {1,dots,m}:f(i)=j}
  $

  records exactly the inputs combined to form the $j$th output. The fiber
  over the basepoint is not ordered: its elements are inputs discarded by
  $f$, rather than inputs supplied to an operation. Hence one linear order is
  chosen for each actual output and no additional order is attached to the
  basepoint.
]

#definition(title:[Monoidal $oo$-Category and Associative Algebra])[
  A #emph[monoidal $oo$-category] is a coCartesian fibration of $oo$-operads

  $
    p:cal(C)^times.o->Assoc.
  $

  The underlying $oo$-category is the fiber over the unique color $a$,
  constructed by the pullback

  $
    cal(C)
    :=cal(C)^times.o
      times_(Assoc)
      {a}.
  $

  The standard order on $n$ elements induces the $n$-fold tensor functor

  $
    cal(C)^n->cal(C).
  $

  For $n=0$ this selects the unit object $1$, and for $n=2$ it is the tensor
  product $times.o:cal(C) times cal(C)->cal(C)$.

  An #emph[associative algebra object] is an algebra over
  $Assoc$ in $cal(C)^times.o$. We write

  $
    Alg(cal(C)):=Alg_(Assoc) (cal(C)).
  $

  Evaluation at the unique color gives the forgetful functor
  $theta:Alg(cal(C))->cal(C)$. Its value on an algebra $A$ remembers the
  underlying object, while the operadic section supplies coherently
  compatible maps $A^(times.o n)->A$ for all $n>=0$.
]

#remark(title:[Fibers of a Monoidal $oo$-Category])[
  The pullback defining $cal(C)$ keeps precisely the objects of
  $cal(C)^times.o$ lying over $a$ and the morphisms lying over $id_a$.
  More generally, write

  $
    cal(C)_(chevron.l n chevron.r)
    :=cal(C)^times.o
      times_(Assoc)
      {chevron.l n chevron.r}.
  $

  The operadic Segal condition gives an equivalence

  $
    cal(C)_(chevron.l n chevron.r) tilde.eq cal(C)^n:
  $

  the $n$ inert projections
  $chevron.l n chevron.r->chevron.l 1 chevron.r$ extract the $n$ components.
  CoCartesian transport along the active ordered fold map then combines this
  tuple into its $n$-fold tensor product.
]

#remark(title:[From Symmetric to Monoidal])[
  If $cal(C)^times.o->Comm^times.o$ is symmetric monoidal, then restriction
  along $Assoc->Comm^times.o$ gives the monoidal
  $oo$-category

  $
    cal(C)^times.o
    times_(Comm^times.o)
    Assoc
    ->Assoc.
  $

  Thus every symmetric monoidal $oo$-category has an underlying monoidal
  $oo$-category, obtained by forgetting symmetry but retaining the tensor
  product and all associativity coherences.
]

#remark(title:[Opposite Algebras])[
  Reversing every linear order defines an involution of
  $Assoc$. Pullback along this involution reverses the tensor
  product and sends an associative algebra $A$ to its #emph[opposite algebra]
  $A^op$. Applying the construction twice canonically recovers $A$.
]

#definition(title:[Nonunital Associative Algebras])[
  Let $Assoc_"nu"^times.o$ be the suboperad obtained by removing the
  nullary operation; equivalently, its structural pointed maps have no empty
  nonbasepoint fiber. Define

  $
    Alg^"nu" (cal(C))
    :=Alg_(Assoc_"nu") (cal(C)).
  $

  Restriction gives a forgetful functor

  $
    Alg(cal(C))->Alg^"nu" (cal(C))
  $

  which forgets the unit but retains the multiplication and all of its higher
  associativity coherences.
]

#definition(title:[Closedness and Invertibility])[
  A monoidal $oo$-category $cal(C)$ is #emph[left closed] if
  $c times.o (-)$ admits a right adjoint for every $c$, and #emph[right
  closed] if $(-) times.o c$ admits a right adjoint for every $c$. It is
  #emph[closed] if both conditions hold.

  An object $c in cal(C)$ is #emph[invertible] if there exists $d in cal(C)$
  with

  $
    c times.o d tilde.eq 1 tilde.eq d times.o c.
  $

  The full subcategory spanned by invertible objects inherits a monoidal
  structure.
]

#proposition(title:[The Free Associative Algebra])[
  Suppose $cal(C)$ admits countable coproducts and $times.o$ preserves them
  separately in each variable. Then the forgetful functor

  $
    theta:Alg(cal(C))->cal(C)
  $

  has a left adjoint $"Fr"$. Its underlying object is the tensor algebra

  $
    theta("Fr"(c))
    tilde.eq
    coprod_(n>=0) c^(times.o n),
    quad c^(times.o 0):=1.
  $

  Multiplication concatenates tensor words. Equivalently, maps
  $"Fr"(c)->A$ of associative algebras are naturally the same as maps
  $c->theta(A)$ in $cal(C)$.
]

#proofsketch[
  Put $T(c)=coprod_(n>=0)c^(times.o n)$. Preservation of coproducts gives

  $
    T(c) times.o T(c)
    tilde.eq
    coprod_(m,n>=0)c^(times.o (m+n)),
  $

  so concatenation of tensor words defines a multiplication on $T(c)$; the
  summand $c^(times.o 0)=1$ supplies its unit. Given $u:c->theta(A)$, its
  restriction to the $n$th summand is forced to be

  $
    c^(times.o n)->^(u^(times.o n)) A^(times.o n)->A,
  $

  with the last map the $n$-fold product of $A$. These maps assemble uniquely
  into an algebra map $T(c)->A$, and restriction to the degree-one summand
  recovers $u$. This proves the adjunction.
]

#proposition(title:[Coherence of the Associative Operad])[
  The $oo$-operad $Assoc$ is coherent. Consequently the
  general constructions of module objects and algebraic colimits developed
  earlier apply to associative algebra objects.
]

#proofsketch[
  The nullary operation is unique, so $Assoc$ is unital. The
  remaining coherence condition is tested on an active map of pointed finite
  sets. After fixing the underlying map, every lift is determined by linear
  orders on its nonbasepoint fibers, and the relevant extension spaces are
  therefore discrete spaces of compatible orders.

  Decompose a fiber into the elements lying before and after the distinguished
  input. Lexicographic composition identifies the corresponding square of
  extension spaces with a coproduct of squares indexed by these two ordered
  subsets. Each nonempty fiber of the comparison map has a canonical order
  and is contractible; hence every such square is a homotopy pushout. This is
  the required coherence condition.
]

== Monoid Objects of $oo$-Categories

The associative operad is not the only way to encode coherent
multiplication. A second model uses simplicial objects satisfying a Segal
product condition. We begin with its ordinary categorical origin.

#definition(title:[Ordinary Monoid Object])[
  Let $cal(C)$ be a category with finite products and terminal object
  $1_cal(C)$. A #emph[monoid object] of $cal(C)$ consists of an object
  $M in cal(C)$ and maps

  $
    e:1_cal(C)->M,
    quad
    mu:M times M->M
  $

  satisfying the unit and associativity identities

  $
    mu compose (e times id_M)=id_M
    =mu compose (id_M times e),
  $

  $
    mu compose (mu times id_M)
    =mu compose (id_M times mu).
  $
]

#example(title:[Monoids and One-Object Categories])[
  For $cal(C)=Set$, this is an ordinary monoid. Any monoid $M$ determines a
  category $cal(D)_M$ with one object $ast$, endomorphism set
  $Hom_(cal(D)_M)(ast,ast)=M$, and composition given by multiplication.
  Conversely, a category with one specified object is of this form exactly
  when that object is its only object.

  Its nerve

  $
    B M:=Ner(cal(D)_M)
  $

  satisfies $(B M)_n tilde.eq M^n$. Composition in the category is encoded by
  the face maps, while insertion of the identity is encoded by degeneracy
  maps.
]

#remark(title:[The Segal Map])[
  A simplicial set $X$ is the nerve of a monoid if and only if it has a single
  vertex and, for every $n>=0$, the maps selecting the consecutive edges
  induce a bijection

  $
    X([n])
    ->X({0,1}) times dots times X({n-1,n})
    tilde.eq X([1])^n.
  $

  For an $oo$-category, bijection is replaced by equivalence and the same
  condition becomes a definition.
]

#definition(title:[Monoid Object in an $oo$-Category])[
  Let $cal(C)$ be an $oo$-category with finite products. A #emph[monoid
  object] of $cal(C)$ is a simplicial object

  $
    X:Ner(Delta^op)->cal(C)
  $

  such that, for every $n>=0$, the Segal map

  $
    X([n])
    ->product_(i=1)^n X({i-1,i})
    tilde.eq X([1])^n
  $

  is an equivalence. Write $Mon(cal(C))$ for the full subcategory of
  $Fun(Ner(Delta^op),cal(C))$ spanned by these objects. For $n=0$, the
  condition says that $X([0])$ is terminal.
]

#remark(title:[Recovering Unit and Multiplication])[
  Put $M=X([1])$. The degeneracy and middle face map give

  $
    e:X([0])->X([1]),
    quad
    mu:M times M tilde.eq X([2])->^(d_1)X([1]).
  $

  The simplicial identities give the unit and associativity laws, and the
  higher simplices supply all compatibilities among those laws. Thus
  $X([1])$ contains the underlying object, but the entire simplicial object is
  needed to retain its coherent multiplication.
]

#definition(title:[The Cut Functor])[
  Let $Delta$ be the category of nonempty finite linearly ordered sets. Define
  a functor

  $
    "Cut":Ner(Delta^op)->Assoc
  $

  on objects by $"Cut"([n])=chevron.l n chevron.r$. If
  $alpha:[n]->[m]$ is a morphism of $Delta$, the corresponding pointed map

  $
    "Cut"(alpha):chevron.l m chevron.r->chevron.l n chevron.r
  $

  is given, for $i in {1,dots,m}$, by

  $
    "Cut"(alpha)(i):=cases(
      j quad & alpha(j-1)<i<=alpha(j) " for some " 1<=j<=n,
      ast quad & "otherwise".
    )
  $

  Each nonbasepoint fiber inherits the standard order from
  ${1,dots,m}$. Geometrically, the $j$th fiber records the interval of cuts
  lying between $alpha(j-1)$ and $alpha(j)$. Equivalently, the nonbasepoints
  of $chevron.l n chevron.r$ are the $n$ nontrivial cuts of $[n]$, while the
  basepoint represents the trivial cut.
]

#theorem(title:[Simplicial and Operadic Monoids Agree])[
  Let $cal(C)$ be an $oo$-category with finite products. Precomposition with
  the Cut functor induces an equivalence

  $
    Mon_(Assoc)(cal(C)) tilde.eq Mon(cal(C)).
  $

  Consequently, for the Cartesian monoidal structure on $cal(C)$,

  $
    Alg_(Assoc)(cal(C)^times)
    tilde.eq Mon(cal(C)).
  $
]

#proofsketch[
  The functor $"Cut"$ is an approximation to the associative operad: it is an
  equivalence on the unique color, and every active ordered operation admits
  a contractible space of lifts from a simplex. Therefore approximation
  invariance for operadic monoids gives
  $Mon_(Assoc)(cal(C)) tilde.eq Mon(cal(C))$.

  Concretely, restriction sends the inert product decomposition over
  $chevron.l n chevron.r$ to the $n$ consecutive-edge maps of $[n]$, hence to
  the Segal equivalence $X([n]) tilde.eq X([1])^n$. Conversely, right Kan
  extension along $"Cut"$ reconstructs the ordered operations; contractibility
  of the lifting categories makes this reconstruction unique up to coherent
  equivalence. The second assertion is the earlier equivalence between
  operadic monoids and algebras in a Cartesian monoidal $oo$-category.
]

#definition(title:[Nonunital Monoid Object])[
  Let $Delta_"inj" subset Delta$ contain all objects and only injective
  monotone maps. A #emph[nonunital monoid object] of $cal(C)$ is a
  semisimplicial object

  $
    X:Ner(Delta_"inj"^op)->cal(C)
  $

  satisfying the same Segal equivalences for $n>=1$. Denote their
  $oo$-category by $Mon^"nu" (cal(C))$. Because degeneracy maps are absent,
  this structure retains multiplication and its associativity coherences but
  contains no unit.
]

#corollary(title:[The Nonunital Comparison])[
  The Cut functor restricts to an approximation

  $
    Ner(Delta_"inj"^op)->Assoc_"nu",
  $

  and consequently induces an equivalence

  $
    Mon_(Assoc_"nu")(cal(C))
    tilde.eq Mon^"nu" (cal(C)).
  $
]

== Planar $oo$-Operads and $AA_oo$-Algebras

The simplicial model also describes associative algebra objects in monoidal
$oo$-categories which are not Cartesian. The appropriate nonsymmetric
analogue of an $oo$-operad is a planar $oo$-operad over
$Ner(Delta^op)$.

#definition(title:[Inert Morphisms in $Delta$])[
  A morphism $alpha:[m]->[n]$ in $Delta$ is #emph[inert] if it is injective
  and its image is a convex interval

  $
    {i,i+1,dots,i+m} subset.eq [n].
  $

  Equivalently, the morphism induced by $alpha$ under the Cut functor is inert
  in $Assoc$. The basic inert maps are the inclusions

  $
    rho^j:[1] tilde.eq {j-1,j} arrow.r.hook [n],
    quad 1<=j<=n.
  $
]

#pagebreak(weak: true)

#definition(title:[Planar $oo$-Operad])[
  A #emph[planar $oo$-operad] is an $oo$-category equipped with a functor

  $
    q:cal(O)^times.o->Ner(Delta^op)
  $

  satisfying the following conditions.

  + Every inert morphism in the base admits a $q$-coCartesian lift.

  + If $c in cal(O)_[n]$ and
    $bar(rho)^j:c->c_j$ are $q$-coCartesian lifts of the interval
    projections $rho^j$, then these maps exhibit $c$ as the relative product
    of $c_1,dots,c_n$: mapping into $c$ over a fixed base map is equivalent to
    giving the compatible maps into all $c_j$.

  + The interval projections induce an equivalence of $oo$-categories

    $
      cal(O)_[n] tilde.eq (cal(O)_[1])^n
    $

    for every $n>=0$. In particular, the fiber over $[0]$ is contractible.
]

#remark(title:[Meaning of the Planar Fibers])[
  Here

  $
    cal(O)_[n]
    :=cal(O)^times.o
      times_(Ner(Delta^op))
      {[n]}.
  $

  The equivalence $cal(O)_[n] tilde.eq (cal(O)_[1])^n$ says that an object
  over an ordered $n$-simplex is exactly an ordered list of $n$ colors. The
  inert interval maps extract the colors one at a time. Unlike an ordinary
  $oo$-operad over $Fin_*$, no permutations of this list are built into the
  base.
]

#definition(title:[$AA_oo$-Monoidal $oo$-Category])[
  A planar $oo$-operad
  $q:cal(C)^times.o->Ner(Delta^op)$ is #emph[$AA_oo$-monoidal] if $q$ is a
  coCartesian fibration. CoCartesian transport along an arbitrary monotone
  map supplies ordered tensor products and all of their coherent
  associativity and unit data.

  A morphism of planar $oo$-operads is a functor over $Ner(Delta^op)$ which
  carries inert morphisms to inert morphisms.
]

#remark(title:[Planar Does Not Mean Symmetric])[
  A planar $oo$-operad is generally not an $oo$-operad over $Fin_*$ in the
  earlier sense. Its base remembers an order on the inputs and has no
  permutation morphisms. The Cut functor compares it with an $oo$-operad over
  the associative operad rather than with a symmetric theory.
]

#definition(title:[Planarization along Cut])[
  Let $p:cal(C)^times.o->Assoc$ be a fibration of $oo$-operads. Its
  #emph[planarization] is the pullback

  $
    cal(C)^"pl"
    :=cal(C)^times.o
      times_(Assoc)
      Ner(Delta^op)
    ->Ner(Delta^op).
  $

  An edge of $cal(C)^"pl"$ is inert precisely when its image in
  $cal(C)^times.o$ is inert. Moreover, $p$ is a coCartesian fibration if and
  only if its planarization is $AA_oo$-monoidal.
]

#theorem(title:[Comparison of Associative and Planar Operads])[
  Planarization along Cut induces an equivalence between the $oo$-category of
  $oo$-operads equipped with a map to $Assoc$ and the $oo$-category of planar
  $oo$-operads:

  $
    (Op_oo)_(\/Assoc) tilde.eq Op_oo^"pl".
  $

  In particular, every planar $oo$-operad is equivalent to one of the form

  $
    cal(C)^times.o
      times_(Assoc)
      Ner(Delta^op)
  $

  for a suitable fibration of $oo$-operads
  $cal(C)^times.o->Assoc$.
]

#proofsketch[
  The Cut functor is an approximation to $Assoc$: it detects the unique
  color, sends interval inclusions to inert maps, and has contractible spaces
  of active lifts. Hence pullback preserves and reflects the inert and Segal
  conditions. Approximation invariance gives full faithfulness, while
  operadic fibrant replacement over $Assoc$ gives essential surjectivity.
]

#definition(title:[$AA_oo$-Algebra Object])[
  Let $q:cal(O)^times.o->Ner(Delta^op)$ be a planar $oo$-operad. An
  #emph[$AA_oo$-algebra object] of $cal(O)$ is a section

  $
    A:Ner(Delta^op)->cal(O)^times.o,
    quad q compose A=id,
  $

  which carries inert morphisms to inert morphisms. Write
  $Alg_(AA_oo)(cal(O))$ for the full subcategory of
  $Fun_(Ner(Delta^op))(Ner(Delta^op),cal(O)^times.o)$ spanned by these
  sections.
]

#remark(title:[What the Section Encodes])[
  The value $A([1])$ is the underlying object, the values on $[n]$ are its
  ordered tensor powers, and the active maps encode multiplication.
  Functoriality supplies all higher coherences, so the construction depends
  on the entire planar $oo$-operad, not only on its fiber over $[1]$.
]

#proposition(title:[Associative Algebras as $AA_oo$-Algebras])[
  Let $p:cal(C)^times.o->Assoc$ be a fibration of $oo$-operads and let
  $cal(C)^"pl"$ be its planarization. Pullback along Cut induces an
  equivalence

  $
    Alg_(Assoc)(cal(C))
    tilde.eq Alg_(AA_oo)(cal(C)^"pl").
  $
]

#definition(title:[Nonunital $AA_oo$-Algebra])[
  Let $Delta_"inj" subset Delta$ be the injective subcategory. A
  #emph[nonunital $AA_oo$-algebra] of a planar $oo$-operad
  $cal(O)^times.o->Ner(Delta^op)$ is an inert-preserving section over
  $Ner(Delta_"inj"^op)$. Denote the resulting $oo$-category by
  $Alg_(AA_oo)^"nu" (cal(O))$.
]

#corollary(title:[The Nonunital Planar Comparison])[
  In the situation above, restriction of Cut induces an equivalence

  $
    Alg^"nu" (cal(C))
    tilde.eq Alg_(AA_oo)^"nu" (cal(C)^"pl").
  $
]

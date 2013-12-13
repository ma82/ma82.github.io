<!-- (progn (setq compilation-window-height 0)
            (setq compilation-scroll-output nil)
			(defun make-thom () (if (equal (buffer-name) "thomcat.md")
                                            (compile "runhaskell Make.hs")))
			(add-hook 'after-save-hook 'make-thom))
     (remove-hook 'after-save-hook 'make-thom)
--!>

<script type="text/x-mathjax-config">
  MathJax.Hub.Config({
    extensions: ["tex2jax.js","fp.js"],
    //                         ^^^^^load fp.js
    jax: ["input/TeX","output/HTML-CSS"],
    "HTML-CSS": {
      styles: {".MathJax_Preview": {visibility: "hidden"}}
    },
    tex2jax: {inlineMath: [["$","$"],["\\(","\\)"]]},
    TeX: {extensions: ["xypic.js", "AMSmath.js","AMSsymbols.js"]}
    //                  ^^^^^^^^load xypic.js
  });
</script>

[<span style="-moz-transform: scaleX(-1); -o-transform: scaleX(-1); -webkit-transform: scaleX(-1); transform: scaleX(-1); display: inline-block;">
    ©
</span> 2013 Matteo Acerbi](http://creativecommons.org/licenses/by-sa/3.0/)

Fusion law for tree homomorphisms
=================================

Abstract
--------

These notes describe a proof to a *fusion* law for *tree
homomorphisms* (@bahr11wgp) in terms of elementary category theory.

<!--
We discuss how it is possible to instantiate the abstract reasoning to
different more concrete settings.

As an example application we show a simple equational method which
allows to build modular compilers (@Day:2011:TMC:2362963.2362969) with
modular proofs of correctness, an approach we put into practice in the
dependently-typed language Agda.
-->

Introduction
------------

$\newcommand{\B}{\mathbf{B}}
 \newcommand{\P}{\mathbf{P}}
 \newcommand{\nt}{\Rightarrow}
 \newcommand{\id}{\text{id}}
 \newcommand{\indfun}{\leadsto}
 \newcommand{\cata}[1]{(\!∣ #1 ∣\!)
 \newcommand{\roll}{\text{roll}}
 \newcommand{\var}{\text{var}}}
 \newcommand{\eta}{\text{unit}}
 \newcommand{\join}{\text{join}}
 \newcommand{\sem}[1]{[\!∣ #1 ∣\!]}
 \newcommand{\catath}[1]{⟨\!∣ #1 ∣\!⟩}
 \newcommand{\Set}{\mathbf{Set}}
$We need a cartesian closed category $\B$ with an initial object $\bot$.

<!-- TODO. Or a comprehension category with unit? See the end. -->

If $1 : \B \to \B$ is the identity functor and $K_X : \B \to \B$ is
the constant functor to the object $X$,
$! : K_\bot \nt 1$ is the unique natural
transformation witnessing $\bot$'s initiality.

$\B$ must have finite coproducts. Given objects $X , Y : \B$, there is
an object $X + Y : \B$ and morphisms

$$\begin{align}
inl_{X,Y} : X \to X + Y\\
inr_{X,Y} : Y \to X + Y
\end{align}$$

such that or every $Z$, $f$ and $g$ as in the following diagram there
exists a *unique* morphism $[f \,, g] : X + Y \to Z$ that makes the
following diagram commute.

$$
\xymatrix{
& Z & \\
X \ar[ru]^{f} \ar[r]_{inl_{X,Y}} & X + Y \ar@{.>}[u]|{[f \,, g]} & Y \ar[l]^{inr_{X,Y}} \ar[lu]_{g}
}
$$

For any endofunctor $F : \B \to \B$, a pair $(X \in B , \alpha : F X
\to X)$ is called an $F$-algebra. A morphism $f : X \to Y$ such that
the diagram below commutes is an *$F$-algebra homomorphism* from
$\alpha$ to $\beta$.

$$
\xymatrix{F X \ar[d]^{\alpha} \ar[r]^{F k} & F Y \ar[d]^{\beta} \\
	    X \ar[r]^{f}                   & Y }
$$

For any $F$, $F$-algebras and $F$-algebra homomorphisms form a
category $Alg_F$.

We use the notation $F : \B \indfun \B$ for $\omega$-cocontinuous
(endo)functors $F$ over $\B$. A standard result is that all
$\omega$-cocontinuous functors admit an initial algebra, i.e. for any
$F : \B \indfun \B$ there exist an object $\mu F : \B$ and a morphism
$in_F : F (\mu F) \to \mu F$ which form an initial object of $Alg_F$.

By Lambek's lemma, the initial algebra $in_F : F (\mu F) \to \mu F$ is
an isomorphism: we call $out_F$ its inverse. For any inductive functor
$F$ we call *catamorphism* the *unique* algebra homomorphism from
$in_F$ to a given algebra $\alpha : F Y \to Y$, for which we adopt the
notation $\cata{\alpha}_F$ (@Meijer91functionalprogramming).

Initiality of $in_F$ can be expressed diagrammatically:

$$
\xymatrix{F (\mu F) \ar[d]^{in} \ar[r]^{F k} & F Y \ar[d]^{\alpha} \\
	     \mu F  \ar@{.>}[r]^{\cata{\alpha}}   & Y }
$$

We consider isomorphic objects, morphisms and functors *equal*, and we
drop subscripts when inferable from the context.

Free monad construction
-----------------------

For any $\omega$-cocontinuous functor $F : \B \indfun \B$ and object $X : \B$,
let us consider the assignment

$$F \star X = F + K_X$$

$F \star X$ is an cocontinous functor as well. We define a similar
notation for (the carrier of) its initial algebra:

$$F \bigstar X = \mu \, (F \star X)$$

We will refer to the following *constructors*.

$\begin{align}
\roll_{F,X} & : F (F \bigstar X) \to F \bigstar X\\
\roll_{F,X} & = in \cdot inl \\
\var_{F,X} & : X \to F \bigstar X\\
\var_{F,X} & = in \cdot inr
\end{align}$

Also $F \bigstar$ is a ($\omega$-cocontinuous) functor: we simply show
a valid definition for its action on morphisms.

$\begin{align}
F \bigstar \, \_ & : (X \to Y) \to (F X \to F Y)\\
F \bigstar \, f & = \cata{[ roll \,, var \cdot f ]}
\end{align}$

$F \bigstar$ is a monad as well, known as the *free monad* over $F$
(@Meijer91functionalprogramming).

<!--
TODO explain why free
-->

We will make use of the following definitions for monadic *unit* and
*multiplication*.

$\begin{align}
\eta_{F} & : 1 \nt F \bigstar\\
\eta_{F,X} & = var_{F,X}
\end{align}
$

$\begin{align}
\join_{F} & : F \bigstar \cdot F \bigstar \nt F \bigstar\\
\join_{F,X} & = \cata{[roll_{F,X} \,, id_{F\bigstar X}]}
\end{align}
$

We also notice that $$F \bigstar \bot = \mu (F + K_\bot) \cong \mu
F$$

Finally, leveraging cocontinuity, it is easy to prove that initiality
of $F \bigstar X$ corresponds to the uniqueness of $\cata{[\alpha \,,
\xi]}$ in the following commutative diagram:

$$
\xymatrix{
F (F \bigstar X) \ar[d]_{\roll_{F,X}} \ar[r]^{F \cata{[ \alpha \,, \xi ]}} & F Y \ar[d]^{\alpha} \\
F \bigstar X \ar@{.>}[r]^{\cata{[\alpha \,, \xi]}} & Y \\
X \ar[u]^{\var_{F,X}} \ar[ur]_{\xi}}
$$

Tree homomorphisms
------------------

For $\omega$-cocontinuous functors $F$ and $G$, we call a natural
transformation

$$\rho : F \nt G \bigstar$$

a *tree homomorphism* (@bahr11wgp).

For any $F$ and $G$ the following map is defined: each tree
homomorphism gives rise to a parameterised family of $F$-algebras.

$\begin{align}
\sem{\_} & : (F \nt G \bigstar) \to (F \cdot (G \bigstar) \nt G \bigstar) \\
\sem{\rho} & = [ \join \cdot \rho \,, \eta ]
\end{align}$

<!--
(TODO. If I wanted to say that this is a morphism, cartesian
closedness would not be enough!  In which categories every natural
transformations is a morphism, not a family of morphisms? I should
look into categorical semantics for polymorphic type theory)
-->

Leveraging $F \bigstar \bot \cong \mu F$, we obtain a morphism in $\B$
by taking the catamorphism of $\sem{\rho}$ at $\bot$.

$\begin{align}
\catath{\_}_{F,G} & : (F \nt G \bigstar) \to (\mu F \to \mu G)\\
\catath{ \rho }_{F,G} & = \cata{\sem{\rho}_\bot} = \cata{[ \join \cdot \rho \,, \eta ]_\bot }
\end{align}
$

The latter definition can be read as a semantic interpretation of any
tree homomorphism as a tree transformation, where by *tree* we intend
inductive *datatype*, or categorically, the carrier of an initial
algebra.

Fusion law
----------

### Statement

In the cited paper, Bahr and Hvitved describe the following binary
operator, taking in input both a $G$-algebra and a tree homomorphism
from $F$ to $G$, and returning an $F$-algebra.

$\begin{align}
\_⊡\_ & : (G Y \to Y) → (F \nt G \bigstar) → (F Y \to Y)\\
\alpha ⊡ \rho & = \cata{[ \alpha \,, ! ]} \cdot \rho \cdot \text{out}
\end{align}$

In the context of the Haskell programming language, the authors state
the validity of the following *fusion* law.

$$\frac {(G : \B \indfun \B)
	 (\alpha : Alg_G)
	 (\rho : F \nt G \bigstar)}
	{\cata{\alpha} \cdot \catath{\rho} = \cata{\alpha ⊡ \rho}} $$

### Proof

The cited paper does not provide a proof: we try to construct one
here, in a slightly more abstract setting. We will later discuss how
it relates to the original context.

For any $\rho$, we start by considering the commuting diagram given by
initiality.

$$
\xymatrix {
  F (\mu F) = F (F \bigstar \bot) \ar[dd]_{\text{in}_F = \roll_{F,\bot}} \ar[r]^{F \catath{\rho}}
& F (\mu F) = F (G \bigstar \bot) \ar[d]^{\rho_{G \bigstar \bot}} \\
& G \bigstar \mu G = G \bigstar (G \bigstar \bot) \ar[d]^{\join_{G,\bot}}   \\          
  \mu F = F \bigstar \bot \ar[r]^{\catath{\rho} = \cata{(\join_{G,\bot} \cdot \rho_{G \bigstar \bot}) \,,\, \var_{G,\bot}}}
& \mu G = G \bigstar \bot \\
\bot \ar[u]^{\var_{F,\bot}} \ar[ur]_{\var_{G,\bot}}}
$$

Consider now an algebra $\alpha : G T \to T$.

We add to the right of the diagram the arrow $\cata{\alpha} : \mu G
\to T$ (isomorphic to $\cata{[ \alpha , ! ]} : G \bigstar \bot \to T$)
and some other compatible morphisms.

$$
\xymatrix{
	F (F \bigstar \bot) \ar[dd]_{\text{in}_F = \roll_{F,\bot}} \ar[r]^{F \catath{\rho}} \ar@{}[ddr]|{(a)} & F (G \bigstar \bot) \ar[d]^{\rho_{G \bigstar \bot}}  \ar[r]^{F \cata{\alpha}} \ar@{}[dr]|{(b)} & F T \ar[d]^{\rho_{T}} \\
                                                                                                      & G \bigstar (G \bigstar \bot) \ar[d]^{\join_{G,\bot}} \ar[r]^{G \bigstar \cata{\alpha}} \ar@{}[dr]|{(c)} & G \bigstar T \ar[d]^{\cata{[\alpha , id]}} \\
F \bigstar \bot \ar[r]^{\catath{\rho}}                                                                 & G \bigstar \bot \ar[r]^{\cata{\alpha} = \cata{[\alpha , !]}}                                                                 & T \\
                                                                                                      & \bot \ar[lu]^{var_F} \ar[u]_{var_G} \ar[ur]_{!_T}
}
$$

We can notice that:

* square (a) commutes by *initiality* for free monads;

* square (b) commutes by *naturality* of $\rho$;

* the triangles at the bottom commute by *initiality* of $\bot$.

We now want to prove that square (c) is commutative as well, i.e.:

$$\cata{[ \alpha , \id ]}_{G\star T} \cdot G \bigstar \cata{[ \alpha \,, ! ]}_{G\star \bot} =
\cata{[ \alpha , ! ]}_{G\star \bot} \cdot \join_{G,\bot}$$

This property can be proved by *induction*.

1. $\roll$ case

$$\begin{align}
& \cata{[ \alpha , \id ]} \cdot G \bigstar \cata{[ \alpha \,, ! ]} \cdot \roll \\
\text{{definition of fmap $= G \bigstar$}}
& = \cata{[ \alpha , \id ]} \cdot \cata{[ \roll \,, \var \cdot \cata{[ \alpha \,, ! ]} ]} \cdot \roll \\
\text{{definition of $\cata{\_}$}}
& = \cata{[ \alpha , \id ]} \cdot \roll \cdot G\, \cata{[ \roll \,, \var \cdot \cata{[ \alpha \,, ! ]} ]} \\
\text{{definition of $\cata{\_}$}}
& = \alpha \cdot G\, \cata{[ \alpha , \id ]} \cdot G\, \cata{[\roll \,, \var \cdot \cata{[ \alpha \,, ! ]} ]} \\
\text{{$G (f \cdot g) = G f \cdot G g$}}
& = \alpha \cdot G\, (\cata{[ \alpha , \id ]} \cdot \cata{[\roll \,, \var \cdot \cata{[\alpha \,, ! ]}]}) \\
\text{{definition of fmap $= G \bigstar$}}
& = \alpha \cdot G\, (\cata{[ \alpha , \id ]} \cdot G \bigstar \cata{[ \alpha \,, ! ]}) \\
\{\textbf{induction hypothesis}\}
& = \alpha \cdot G\, (\cata{[ \alpha \,, ! ]} \cdot \join) \\ 
\text{{$G (f \cdot g) = G f \cdot G g$}}
& = \alpha \cdot G\, \cata{[ \alpha \,, ! ]} \cdot G\, \join \\ 
\text{{definition of $\cata{\_}$}}
& = \cata{[ \alpha \,, ! ]} \cdot \roll \cdot G\, \join \\
\text{{definition of join}}
& = \cata{[ \alpha \,, ! ]} \cdot \roll \cdot G\, (\!∣\roll \,, \id ∣\!) \\
\text{{definition of $\cata{\_}$}}
& = \cata{[ \alpha \,, ! ]} \cdot \cata{[\roll \,, \id]} \cdot \roll \\
\text{{definition of join}}
& = \cata{[ \alpha \,, ! ]} \cdot \join \cdot \roll
\end{align}$$

2. $\var$ case

$$\begin{align}
&   \cata{[ \alpha , \id ]} \cdot G \bigstar \cata{[ \alpha \,, ! ]} \cdot \var \\
\text{{definition of fmap and $\cata{\_}$}}
& = \cata{[ \alpha , \id ]} \cdot \var \cdot \cata{[ \alpha , ! ]} \\
\text{{definition of $\cata{\_}$}}
& = \cata{[ \alpha \,, ! ]} \\
\text{{definition of $\cata{\_}$}}
& = \cata{[ \alpha \,, ! ]} \cdot \cata{[ \roll \,, \id ]} \cdot \var \\
\text{{definition of join}}
& = \cata{[ \alpha \,, ! ]} \cdot \join \cdot \var
\end{align}$$

We conclude that also (c) is commutative, hence the whole diagram
commutes.

At the right edge of the upper part of the diagram one has the
$F$-algebra $(\!∣ \alpha , id ∣\!) \cdot \rho_T : F T \to T$. This is
exactly how $\alpha ⊡ \rho$ is defined.

The *initiality* property for free monads given above allows us to
conclude that $\cata{\alpha ⊡ \rho} = \cata{\alpha} \cdot
\catath{\rho}$.

<!--
(So many people seem to never justify this, why should I?)

### Justification of inductive reasoning

The appeal to induction can be justified using the techniques from
@DBLP:journals/corr/abs-1206-0357: we give a sketch of how to proceed.

(TODO. Set-valued predicate over B objects?
       It would be nice... Predicativity issues?)

We need to add to the requirements the existence of a category $\P$ of
predicates over objects of $\B$. The objects of $\P$ are pairs $(X :
\B \,, P : X \to \Set)$ of an object of $\B$ and a map from that
object to $\Set$. The morphisms of $\P$ are the predicate morphisms as
described in Ghani et al.'s paper.

$\P$ must contain all the identity predicates: indeed for every object
$X$ one has $((X \times X) \,, \lambda (x_1 , x_2). x_1 = x_2) : \P$.

TODO. My wish here was to generalise part 3 of the paper (Induction
Rules for Predicates over Set) to set-valued predicates over any base
category, so that I don't have to further specify my $\B$. Does that
makes any sense?

More concrete proofs
--------------------

### Constructive type theory

* Strict positivity => Polynomials/containers
* Indexed morphisms
* Proofs: naturality is not provable, we restrict to tree
  homomorphisms which are natural using a sigma type.
* Example: Agda

### System F$\omega$

* Proofs in a parametric setting.
* Model must be parametric (@DBLP:conf/csl/Atkey12), as parametricity
  implies naturality (TODO (again)).

### Haskell

* Parametric model?! Depends.
* Turing-completeness => category $\omega-CPO_\bot$ :
  $\omega$-complete partial orders with a bottom element and *strict*
  continuous functions between them.
  
    * Is this fine as a $\B$? TODO. Check.
    * Fusion law proof does not apply to lazy algebras and tree homomorphisms.

Example applications
--------------------

### Coproduct of tree homomorphisms

### Modular certified compilers

Are *smart algebras* equivalent to tree homomorphisms?
------------------------------------------------------

Conclusions
-----------

-->

References
----------

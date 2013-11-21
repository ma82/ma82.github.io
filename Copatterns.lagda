# A universe of functors closed under ν using copatterns

\begin{code}
{-# OPTIONS --copatterns #-}
module Copatterns where

open import Function      using    (_∘_ ; id)
open import Data.Product  using    (Σ ; _,_)
                          renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum as ⊎ using (_⊎_)
                          renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Unit

Pow : Set → Set₁
Pow I = I → Set

Pow/ : {I : Set} → Pow I → Set _
Pow/ = Pow ∘ Σ _

data _∋_ (A : Set) : A → Set where
  [_] : (a : A) → A ∋ a
\end{code}

## Syntax

\begin{code}
data De (I : Set) : Set₁ where
  `I   : (i : I)                       → De I
  `ν   : ∀ {R}(F : R → De (I ⊎ R)) → R → De I

infix 0 _▻_
_▻_ = λ (I O : Set) → O → De I

map : {I J : Set} → (I → J) → De I → De J
map f (`I i  ) = `I (f i)
map f (`ν F r) = `ν (λ r → map ⊎.[ inl ∘ f , inr ] (F r)) r

_`>>=_ : {I J : Set}(D : De J)(F : I ▻ J) → De I
`I j   `>>= G = G j
`ν F r `>>= G = `ν (λ k → F k `>>= ⊎.[ map inl ∘ G , `I ∘ inr ]) r

_`∘_ : {A B C : Set} → B ▻ C → A ▻ B → A ▻ C
(F `∘ G) a = F a `>>= G

`_[_] : {I J K : Set} → (I ⊎ K ▻ J) → (I ▻ K) → I ▻ J
` F [ G ] = F `∘ ⊎.[ `I , G ]

% : {I J : Set} → (I ⊎ J ▻ J) → I ▻ J
% F = ` F [ `ν F ]
\end{code}

## Semantics

\begin{code}
mutual

  ⟦_⟧ : ∀ {I} → De I → Pow I → Set
  ⟦ `I k   ⟧ X = X k
  ⟦ `ν F r ⟧ X = ν F X r

  record ν {I R}(F : (I ⊎ R) ▻ R)(X : Pow I)(r : R) : Set where
    coinductive
    constructor [_] 
    field       ]_[ : ⟦ % F r ⟧ X

⟦_⟧▻ : {I O : Set} → I ▻ O → Pow I → Pow O
⟦ F ⟧▻ X o = ⟦ F o ⟧ X

open ν
\end{code}

## Predicate lifting

### Box

We (now) use a coinductive-recursive definition.

\begin{code}
module Lifting {I}{X : Pow I}(P : Pow/ X) where

  mutual

    □ : (D : De I) → ⟦ D ⟧ X → Set
    □ (`I i)   xs = P (i , xs)
    □ (`ν F r) xs = ■ F r xs

    record ■ {R}(F : I ⊎ R ▻ R)(r : R)(xs : ⟦ `ν F r ⟧ X) : Set where
      coinductive
      constructor <_>
      field       >_< : □ (% F r) ] xs [

open Lifting; open ■
\end{code}

### All

\begin{code}
module All {I : Set}{X : Pow I}{P : Pow/ X}(m : ∀ x → P x) where

  ◽ : ∀     D   xs → □ P D xs
  ◾ : ∀ {R} F r xs → ■ P {R} F r xs
  ◽ (`I i) xs   = m (i , xs)
  ◽ (`ν F x) xs = ◾ F x xs
  > ◾ F r xs <  = ◽ (% F r) ] xs [
\end{code}

### Non-dependent predicates lemma

We can obtain functorial values from proofs of liftings of
non-dependent predicates.

\begin{code}
module □→⟦⟧ {I : Set}{X Y : Pow I} where

    □→⟦⟧ : ∀ D       → (xs : ⟦ D ⟧ X) → □ (Y ∘ fst)     D   xs → ⟦ D ⟧ Y
    ■→⟦⟧ : ∀ {R} F r → (xs : ν F X r) → ■ (Y ∘ fst) {R} F r xs → ν F Y r
    □→⟦⟧ (`I i  ) xs ih   = ih
    □→⟦⟧ (`ν F r) xs ih = ■→⟦⟧ F r xs ih
    ] ■→⟦⟧ F r xs ih [  = □→⟦⟧ (% F r) ] xs [ > ih < 
\end{code}

There are alternative (better) ways to obtain `■→⟦⟧` but this was
enough to exhibit a diverging behaviour that, thanks to Andreas Abel's
fix, does not actually appear anymore.

## Issue

`N` is the carrier of the terminal coalgebra of the identity functor.

\begin{code}
NF : ⊤ ▻ ⊤
NF = `ν (`I ∘ inr)

N = ⟦ NF ⟧▻ (λ _ → ⊤) _
\end{code}

`n` is an inhabitant of `N`. Observationally it is the unique element
of `N`, but intensionally this does not hold.

\begin{code}
n : N
] n [ = n
\end{code}

If we build another `N` in the same way Agda *decides* that it is
*not* definitionally equal to `n`. As we would expect, `id-nm` does
not typecheck.

\begin{code}
m : N
] m [ = m

-- id-nm : N ∋ n → N ∋ m
-- id-nm = id
\end{code}

We can build other elements of `N` by means of `□→⟦⟧` and `◽`, though.

\begin{code}
open All ; open □→⟦⟧

o : N
o = □→⟦⟧ (NF _) n (◽ (λ _ → tt) (NF _) n)

p : N
p = □→⟦⟧ (NF _) o (◽ (λ _ → tt) (NF _) o)
\end{code}

Again, neither of them is convertible with `n`.

\begin{code}
-- id-no : N ∋ n → N ∋ o
-- id-no = id

-- id-np : N ∋ n → N ∋ p
-- id-np = id
\end{code}

Is `o` convertible with `p`?

\begin{code}
-- id-op : N ∋ o → N ∋ p
-- id-op = id
\end{code}

No!

If I evaluate `o` or `p` using `C-c C-n` I do not get divergence (anymore).

If I `C-c C-a` in the type-level hole below I obtain

    Not implemented: The Agda synthesizer (Agsy) does not support
    copatterns yet

\begin{code}
-- inferN∋o : N ∋ o → N ∋ {!!}
-- inferN∋o x = x
\end{code}

2013 Nov 21, matteo.acerbi@gmail.com

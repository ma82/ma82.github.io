# Stack overflows with `--copatterns`

The following was tested on Agda's last commit (Tue Nov 19 10:59:34).

The current stable version from Hackage (2.3.2.2) does not accept
`■→⟦⟧`, however I do not understand the error message.

\begin{code}
{-# OPTIONS --copatterns #-}
module Copatterns where

open import Function      using    (_∘_ ; id)
open import Data.Product  using    (Σ ; _,_)
                          renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum as ⊎ using (_⊎_)
                          renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Unit

Π : ∀ {lA}(A : Set lA){lB} → (A → Set lB) → Set _
Π A B = (a : A) → B a

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
    field       ]_[ : ⟦ ` F [ `ν F ] r ⟧ X

⟦_⟧▻ : {I O : Set} → I ▻ O → Pow I → Pow O
⟦ F ⟧▻ X o = ⟦ F o ⟧ X

open ν
\end{code}

## Predicate lifting

### Box

We use a nested inductive-coinductive definition.

\begin{code}
module Lifting {I}{X : Pow I}(P : Pow/ X) where

  mutual

    data □ : (D : De I) → ⟦ D ⟧ X → Set₁ where
      □I : ∀ {k x}           → P (k , x)                  → □ (`I k)   x
      □ν : ∀ {R F}{r : R}{x} → ■ (` F [ `ν F ] r) (] x [) → □ (`ν F r) x

    record ■ (D : De I)(xs : ⟦ D ⟧ X) : Set₁ where
      coinductive
      constructor <_>
      field       >_< : □ D xs

open Lifting; open ■
\end{code}

### All

\begin{code}
module All {I : Set}{X : Pow I}{P : Pow/ X}(m : ∀ x → P x) where

  ◽ : ∀ D xs → □ P D xs
  ◾ : ∀ D xs → ■ P D xs
  ◽ (`I i  ) x = □I (m (i , x))
  ◽ (`ν F r) x = □ν (◾ _ ] x [)
--  ◾ D x        = < ◽ D x >    -- -> red!
  > ◾ D x    < = ◽ D x
\end{code}

### Non-dependent predicates lemma

We can obtain functorial values from proofs of liftings of
non-dependent predicates.

\begin{code}
module □→⟦⟧ {I : Set}{X Y : Pow I} where

  □→⟦⟧ : ∀ D → Σ (⟦ D ⟧ X) (□ (Y ∘ fst) D) → ⟦ D ⟧ Y
  ■→⟦⟧ : ∀ D → Σ (⟦ D ⟧ X) (■ (Y ∘ fst) D) → ⟦ D ⟧ Y
  □→⟦⟧ (`I j  ) (xs , □I ih) = ih
  □→⟦⟧ (`ν F j) (xs , □ν ih) = [ ■→⟦⟧ (` F [ `ν F ] j) (] xs [ , ih) ]
  ■→⟦⟧ D        (xs ,    ih) = □→⟦⟧ D (xs , > ih <)
\end{code}

## Issue

`N` is the terminal coalgebra of the identity functor.

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
*not* definitionally equal to `n`: as we would expect, `id-nm` does
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
o = □→⟦⟧ (NF _) (n , ◽ _ _ n)

p : N
p = □→⟦⟧ (NF _) (o , ◽ _ _ o)
\end{code}

Again, neither of them is convertible with `n`.

\begin{code}
-- id-no : N ∋ n → N ∋ o
-- id-no = id

-- id-np : N ∋ n → N ∋ p
-- id-np = id
\end{code}

However, is `o` convertible with `p`?

\begin{code}
-- id-op : N ∋ o → N ∋ p
-- id-op = id
\end{code}

When Agda tries to typecheck `id-op` on my machine it allocates ~ 2 GB
of memory and prints *stack overflow* after a while. The interactive
process does not exit but the file is not loaded.

More interestingly, this also happens if I leave it commented out,
load the file and evaluate `o` or `p` using `C-c C-n`.

Finally, this also happens if I `C-c C-a` in the type-level hole
below.

\begin{code}
-- inferN∋o : N ∋ o → N ∋ {!!}
-- inferN∋o x = x
\end{code}

2013 Nov 19, matteo.acerbi@gmail.com

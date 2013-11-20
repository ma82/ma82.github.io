# A universe of functors closed under identity, fixpoint and ∞

\begin{code}
module Inf where

open import Function      using (_∘_ ; id)
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

_⇛_ : {I : Set} → Pow I → Pow I → Set
X ⇛ Y = ∀ i → X i → Y i

data _∋_ (A : Set) : A → Set where
  [_] : (a : A) → A ∋ a
\end{code}

## Syntax

\begin{code}
data De (I : Set) : Set₁ where
  `I   : (i : I)                       → De I
  `co  : De I                          → De I
  `fix : ∀ {R}(F : R → De (I ⊎ R)) → R → De I

infix 0 _▻_
_▻_ = λ (I O : Set) → O → De I

map : {I J : Set} → (I → J) → De I → De J
map f (`I i    ) = `I (f i)
map f (`co D   ) = `co (map f D)
map f (`fix F r) = `fix (λ r → map ⊎.[ inl ∘ f , inr ] (F r)) r

_`>>=_ : {I J : Set}(D : De J)(F : I ▻ J) → De I
`I i     `>>= G = G i
`co D    `>>= G = `co (D `>>= G)
`fix F r `>>= G = `fix (λ k → F k `>>= ⊎.[ map inl ∘ G , `I ∘ inr ]) r

_`∘_ : {A B C : Set} → B ▻ C → A ▻ B → A ▻ C
(F `∘ G) a = F a `>>= G

`_[_] : {I J K : Set} → (I ⊎ K ▻ J) → (I ▻ K) → I ▻ J
` F [ G ] = F `∘ ⊎.[ `I , G ]

% : {I J : Set} → (I ⊎ J ▻ J) → I ▻ J
% F = ` F [ `fix F ]
\end{code}

## Semantics

\begin{code}
open import Coinduction

mutual

  ⟦_⟧ : ∀ {I} → De I → Pow I → Set
  ⟦ `I k     ⟧ X = X k
  ⟦ `co D    ⟧ X = ∞ (⟦ D ⟧ X)
  ⟦ `fix F r ⟧ X = Fix F X r

  data Fix {I R}(F : (I ⊎ R) ▻ R)(X : Pow I)(r : R) : Set where
    [_] : ⟦ % F r ⟧ X → Fix F X r

⟦_⟧▻ : {I O : Set} → I ▻ O → Pow I → Pow O
⟦ F ⟧▻ X o = ⟦ F o ⟧ X

∞map : {X Y : Set} → (X → Y) → ∞ X → ∞ Y
∞map f x = ♯ f (♭ x)

⟦_⟧map  : {I : Set}{X Y : Pow I} → ∀ D → X ⇛ Y → ⟦ D ⟧ X → ⟦ D ⟧ Y
⟦ `I i     ⟧map f   xs   = f i xs
⟦ `co D    ⟧map f   xs   = ♯ ⟦ D ⟧map f (♭ xs)
⟦ `fix F r ⟧map f [ xs ] = [ ⟦ % F r ⟧map f xs ]
\end{code}

## Predicate lifting

### Box

\begin{code}
data □ {I}{X : Pow I}(P : Pow/ X) : (D : De I) → ⟦ D ⟧ X → Set₁ where
  □I   : ∀ {k x}            → P (k , x)        → □ P (`I k)       x
  □co  : ∀ {D xs}           → ∞ (□ P D (♭ xs)) → □ P (`co D)      xs
  □fix : ∀ {R F}{r : R}{xs} → □ P (% F r) xs   → □ P (`fix F r) [ xs ]
\end{code}

### All

\begin{code}
module All {I : Set}{X : Pow I}{P : Pow/ X}(m : ∀ x → P x) where

  ◽  : ∀ D xs → □ P D xs
  ◽ (`I i    ) xs     = □I   (m     (i , xs))
  ◽ (`co D   ) xs     = □co  (♯ (◽ D (♭ xs)))
  ◽ (`fix F r) [ xs ] = □fix (◽ (% F r)   xs)
\end{code}

### Functorial values from proofs of liftings of non-dependent predicates

\begin{code}
module □→⟦⟧ {I : Set}{X Y : Pow I} where

  □→⟦⟧ : ∀ D → Σ (⟦ D ⟧ X) (□ (Y ∘ fst) D) → ⟦ D ⟧ Y
  □→⟦⟧ (`I k    ) (xs     , □I    y) = y
  □→⟦⟧ (`co D   ) (xs     , □co  ih) = ♯ □→⟦⟧ D (♭ xs , ♭ ih)
  □→⟦⟧ (`fix F r) ([ xs ] , □fix ih) = [ □→⟦⟧ _ (xs , ih) ]
\end{code}

## Example from [Copatterns.lagda](Copatterns.html)

Type `N` inhabited by `n`.

\begin{code}
NF : ⊤ ▻ ⊤
NF = `fix (`co ∘ `I ∘ inr)

N = ⟦ NF ⟧▻ (λ _ → ⊤) _

n : N
n = [ ♯ n ]
\end{code}

`m` and `n` are not convertible.

\begin{code}
m : N
m = [ ♯ m ]

-- id-nm : N ∋ n → N ∋ m
-- id-nm = id
\end{code}

We can build other elements of `N` by means of `□→⟦⟧` and `◽`.

\begin{code}
open All ; open □→⟦⟧

o : N
o = □→⟦⟧ (NF _) (n , ◽ _ _ n)

p : N
p = □→⟦⟧ (NF _) (o , ◽ _ _ o)
\end{code}

Neither of them is convertible with `n`.

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

If we `C-c C-n o` we do not get stack overflows.

Finally, Agsy timeouts in the following hole.

\begin{code}
-- inferN∋o : N ∋ o → N ∋ {!!}
-- inferN∋o = id
\end{code}

2013 Nov 20, matteo.acerbi@gmail.com

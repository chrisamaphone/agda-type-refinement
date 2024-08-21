open import Data.Product

data Nat : Set where
    Zero : Nat
    Succ : Nat → Nat

data isEven : Nat → Set
data isOdd : Nat → Set

data isEven where
    isEven/Z : isEven Zero
    isEven/S : (n : Nat) → isOdd n → isEven (Succ n)

data isOdd where
    isOdd/S : (n : Nat) → isEven n → isOdd (Succ n)

Refinement : Set → Set₁
Refinement A = A → Set


Even : Refinement Nat
Even = isEven

Odd : Refinement Nat
Odd = isOdd

_∧_ : ∀ {A} → Refinement A → Refinement A → Refinement A
R₁ ∧ R₂ = λ a → (R₁ a) × (R₂ a)


_⇒_ : ∀ {A B} → Refinement A → Refinement B → Refinement (A → B)
R₁ ⇒ R₂ = λ f → ∀ {a} → (R₁ a) → (R₂ (f a))

{--
-- the function Succ : Nat → Nat 
-- has the refinement
-- (Even ⇒ Odd) ∧ (Odd ⇒ Even) : Refinement (Nat → Nat)
-- in the sense that the type
-- ((Even ⇒ Odd) ∧ (Odd ⇒ Even)) (Succ)
-- is inhabited.
--}

succRefinement : Refinement (Nat → Nat)
succRefinement = (Even ⇒ Odd) ∧ (Odd ⇒ Even) 

succHasRefinement : succRefinement Succ
proj₁ succHasRefinement = λ e → isOdd/S _ e
proj₂ succHasRefinement = λ o → isEven/S _ o




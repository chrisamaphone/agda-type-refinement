open import Data.Product

data Nat : Set where
    Zero : Nat
    Succ : Nat → Nat

data isEven : Nat → Set
data isOdd : Nat → Set

data isEven where
    isEven/Z : isEven Zero
    isEven/S : {n : Nat} → isOdd n → isEven (Succ n)

data isOdd where
    isOdd/S : {n : Nat} → isEven n → isOdd (Succ n)

Refinement : Set → Set₁
Refinement A = A → Set


Even : Refinement Nat
Even = isEven

Odd : Refinement Nat
Odd = isOdd

data ⊤ : Set where
  unit : ⊤
  
TopNat : Refinement Nat
TopNat a = ⊤

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
proj₁ succHasRefinement = λ e → isOdd/S e
proj₂ succHasRefinement = λ o → isEven/S o

{-- Doubling example
TODO:
[X] define as function
[X] show it has refinement
[X] define as relation
[X] what does it mean for the relation to have the refinement?
--}

double : Nat → Nat
double Zero = Zero
double (Succ n) = Succ (Succ (double n))

doubleRefinement : Refinement (Nat → Nat)
doubleRefinement = TopNat ⇒ Even

doubleHasRefinement : doubleRefinement double
doubleHasRefinement {Zero} dTop = isEven/Z
doubleHasRefinement {Succ n} dTop
  with doubleHasRefinement {n}
... | dEven = isEven/S (isOdd/S (dEven unit))

-- Relation version
data isDouble : Nat → Nat → Set where
  isDouble/Z : isDouble Zero Zero
  isDouble/S : ∀ {n n2}
             → isDouble n n2
             → isDouble (Succ n) (Succ (Succ n2))

-- Not sure how to translate into a "refinement kind"
-- and show how it inhabits it, but can show:
isDoubleisEven : (n : Nat) → TopNat n
               → (n2 : Nat) → isDouble n n2
               → isEven n2
isDoubleisEven .Zero _ .Zero isDouble/Z = isEven/Z
isDoubleisEven .(Succ n) _ .(Succ (Succ _)) (isDouble/S {n} {n2} dDouble)
  with isDoubleisEven n unit n2 dDouble
... | dEven2 = isEven/S (isOdd/S dEven2)



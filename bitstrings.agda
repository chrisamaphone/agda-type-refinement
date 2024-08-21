{-- Type Refinements base --}
open import Data.Product

Refinement : Set → Set₁
Refinement A = A → Set

_∧_ : ∀ {A} → Refinement A → Refinement A → Refinement A
R₁ ∧ R₂ = λ a → (R₁ a) × (R₂ a)


_⇒_ : ∀ {A B} → Refinement A → Refinement B → Refinement (A → B)
R₁ ⇒ R₂ = λ f → ∀ {a} → (R₁ a) → (R₂ (f a))


{-- Bit strings
 -- Zero(One(E)) = e10 = 2
 -- "Std" means no leading zeros
 -- "Pos" means no leading zeros and no E
 -- "Bits" is the "top" subsort of the Bits type
 -- Expected subsort relationships:
 -- - Std ≤ Bits
 -- - Pos ≤ Std
 -- - Pos ≤ Bits
--}

data Bits : Set where
  E : Bits
  Zero : Bits → Bits
  One : Bits → Bits


data isStd : Bits → Set
data isBits : Bits → Set
data isPos : Bits → Set

data isStd where
  isStd/E : isStd E
  -- Note: the below is needed to "assert by fiat"
  -- the subsort relationship between Pos and Std.
  isStd/Pos : {b : Bits} → isPos b → isStd b

data isPos where
  isPos/One : {b : Bits} → isStd b → isPos (One b)
  isPos/Zero : {b : Bits} → isPos b → isPos (Zero b)

data isBits where
  isBits/I : {b : Bits} → isBits b 

_⊑_ : ∀ {A} → Refinement A → Refinement A → Set
R₁ ⊑ R₂ = ∀ {a} → (R₁ a) → (R₂ a)


subsortPosStd : isPos ⊑ isStd
subsortPosStd {E} ()
subsortPosStd {Zero b} (isPos/Zero posB)
  = isStd/Pos (isPos/Zero posB)
subsortPosStd {One b} (isPos/One stdB) = isStd/Pos (isPos/One stdB)

data Top : Set where
  Unit : Top
  
-- define "the top refinement" for any type
⊤ : (A : Set) → Refinement A
⊤ A = λ (a : A) → Top

⊤_Bits : Refinement Bits
⊤_Bits = ⊤ Bits

-- Std ⊑ Bits
subsortStdBits : isStd ⊑ ⊤_Bits
subsortStdBits {b} stdB = Unit

subsortTrans : ∀ {A : Set} → ∀ {R₁ R₂ R₃ : Refinement A} →
  (R₁ ⊑ R₂) → (R₂ ⊑ R₃) → R₁ ⊑ R₃
subsortTrans sub12 sub23 r1a = sub23 (sub12 r1a)

subsortPosBits : isPos ⊑ ⊤_Bits
subsortPosBits = subsortTrans {Bits} {isPos} {isStd} {⊤_Bits} subsortPosStd subsortStdBits

-- Sort checking
{--
-- Agda is complaining about the type decl here but not sure why.
-- Zero (One (E)) :> isPos
sortChecks : {A : Set} → (a : A) → Refinement A → Set
sortChecks {A} a s = s a
--}

-- Agda auto can figure this out
testCheck1 : isPos (Zero (One E))
testCheck1 = isPos/Zero (isPos/One isStd/E)

-- functions on refined data
-- increment
inc : (b : Bits) → isStd b → Σ Bits λ b1 → isPos b1
inc E isStd = (One E) , isPos/One isStd/E
inc (Zero b) (isStd/Pos (isPos/Zero posB)) = (One b) , (isPos/One (isStd/Pos posB))
inc (One b) (isStd/Pos (isPos/One stdB)) = Zero (proj₁ (inc b stdB)) , isPos/Zero (proj₂ (inc b stdB))

-- Agda auto can figure this out
twoIsStd : isStd (Zero (One E))
twoIsStd = isStd/Pos (isPos/Zero (isPos/One isStd/E))

incTwo : (Σ Bits λ b → isPos b)
incTwo = inc (Zero (One E)) twoIsStd
-- Result of C-c C-n:
-- One (One E) , isPos/One (isStd/Pos (isPos/One isStd/E))


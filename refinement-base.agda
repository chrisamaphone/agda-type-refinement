{-- Type Refinements base --}
open import Data.Product

Refinement : Set → Set₁
Refinement A = A → Set

-- "Top" sort for any type (that is, (T A) x for any x : A)
data Top : Set where
  Unit : Top
  
⊤ : (A : Set) → Refinement A
⊤ A = λ (a : A) → Top

-- Intersection sorts
_∧_ : ∀ {A} → Refinement A → Refinement A → Refinement A
R₁ ∧ R₂ = λ a → (R₁ a) × (R₂ a)

-- TODO union sorts

-- Function sorts
_⇒_ : ∀ {A B} → Refinement A → Refinement B → Refinement (A → B)
R₁ ⇒ R₂ = λ f → ∀ {a} → (R₁ a) → (R₂ (f a))

-- Subsorting

_⊑_ : ∀ {A} → Refinement A → Refinement A → Set
R₁ ⊑ R₂ = ∀ {a} → (R₁ a) → (R₂ a)

subsortTrans : ∀ {A : Set} → ∀ {R₁ R₂ R₃ : Refinement A} →
  (R₁ ⊑ R₂) → (R₂ ⊑ R₃) → R₁ ⊑ R₃
subsortTrans sub12 sub23 r1a = sub23 (sub12 r1a)

-- Synthesizing dependent functions from simply-typed functions
-- and witnesses that they inhabit a refined type
synthFun : {A B : Set} → {R : Refinement A} → {S : Refinement B}
         → (f : A → B) → (R ⇒ S) f →
              (a : A) → R a → Σ B λ b → S b
synthFun {A} {B} {R} {S} f fHasRSSort =
  λ a → λ aR → f a , fHasRSSort {a} aR


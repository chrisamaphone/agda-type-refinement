{-- Type Refinements base --}
open import Data.Product
open import Data.Sum
open import Agda.Primitive

data Refinement {l : Level} : (A : Set l) → Set (lsuc l) where
     ⊤   : (A : Set l) → Refinement A
     Base : {A : Set l} → (P : A → Set l) → Refinement A 
     _∩_ : {A : Set l} → Refinement A → Refinement A → Refinement A
     _∪_ : {A : Set l} → Refinement A → Refinement A → Refinement A
     _⇒_ : {A B : Set l} → Refinement A → Refinement B → Refinement (A → B)
     -- Augmenting with exists and forall
     R∃ : {A : Set l} → (I : Set) → (R : I → Refinement A) → Refinement A
     R∀ : {A : Set l} → (I : Set) → (R : I → Refinement A) → Refinement A
     RΠ : {A : Set l} → {B : A → Set l}
       → Refinement A → ((a : A) → Refinement (B a)) → Refinement ((a : A) → B a)

data Triv {l : Level} : Set l where
  Unit : Triv

-- Defining refinements on A as predicates on A
-- i.e. representing each sort constructor as a type family
hasRefinement : ∀ {l} {A : Set l} → Refinement A → A → Set l
hasRefinement {l} {A} (⊤ A) a = Triv
hasRefinement (R₁ ∩ R₂) a = hasRefinement R₁ a × hasRefinement R₂ a
hasRefinement (R₁ ∪ R₂) a = hasRefinement R₁ a ⊎ hasRefinement R₂ a
hasRefinement (R₁ ⇒ R₂) f = ∀ {a} → hasRefinement R₁ a → hasRefinement R₂ (f a)
hasRefinement (Base P) a = P a
hasRefinement (R∃ I R) a = Σ I λ i → hasRefinement (R i) a
hasRefinement (R∀ I R) a = ∀ i → hasRefinement (R i) a
hasRefinement (RΠ RA RB) f = ∀ {a} → hasRefinement RA a → hasRefinement (RB a) (f a)

-- Subsorting
_⊑_ : {A : Set} → Refinement A → Refinement A → Set
R₁ ⊑ R₂ = ∀ {a} → hasRefinement R₁ a → hasRefinement R₂ a

-- Redoing prev example: even and odd

data Nat : Set₀ where
  Zero : Nat
  Succ : Nat → Nat

data Even : Nat → Set
data Odd : Nat → Set

data Even where
  ev/z : Even Zero
  ev/s : ∀ {n} → Odd n → Even (Succ n)

data Odd where
  od/s : ∀ {n} → Even n → Odd (Succ n)

EvenR : Refinement Nat
EvenR = Base Even

OddR : Refinement Nat
OddR = Base Odd

-- Succ has refinement (EvenR ⇒ OddR) ∩ (OddR ⇒ EvenR)
SuccR : Refinement (Nat → Nat)
SuccR = (EvenR ⇒ OddR) ∩ (OddR ⇒ EvenR)

pfSuccR : hasRefinement SuccR Succ
proj₁ pfSuccR = od/s
proj₂ pfSuccR = ev/s

double : Nat → Nat
double Zero = Zero
double (Succ n) = Succ (Succ (double n))

DoubR : Refinement (Nat → Nat)
DoubR = (⊤ Nat) ⇒ EvenR

pfDoubR : hasRefinement DoubR double
pfDoubR {Zero} Unit = ev/z
pfDoubR {Succ a} Unit = ev/s (od/s (pfDoubR {a} Unit))

-- Example 2: empty/nonempty lists

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Emp {A : Set} : List A → Set where
  Emp/i : Emp []

data Nonemp {A : Set} : List A → Set where
  Nonemp/i : ∀ {x l} → Nonemp (x ∷ l)

data Len {A : Set} : List A → Nat → Set where
  Len/[] : Len [] Zero
  Len/∷  : ∀ {x l n} → Len l n → Len (x ∷ l) (Succ n)

tl : ∀ {A} → (l : List A) → Nonemp l → List A
tl (x ∷ l) _ = l

LenR : {A : Set} → (n : Nat) → Refinement (List A)
LenR n = Base (λ l → Len l n)

NonempR : {A : Set} →  Refinement (List A)
NonempR = Base Nonemp

-- Lists of length at least 1, with existential sort
LenSuccR : {A : Set} → Refinement (List A)
LenSuccR = R∃ Nat λ n → LenR (Succ n)

data Stuff : Set where
  a : Stuff
  b : Stuff
  c : Stuff

list1 : List Stuff
list1 = a ∷ (b ∷ [])

list1Sort : hasRefinement LenSuccR list1
proj₁ list1Sort = Succ Zero
proj₂ list1Sort = Len/∷ (Len/∷ Len/[])

-- Showing tl takes any list of length 1 to list of length 0

tlType : {A : Set} → Set
tlType {A} = (l : List A) → Nonemp l → List A

tlRefinement1 : ∀ {A} → Refinement (tlType {A})
tlRefinement1 {A} =
  RΠ (LenR (Succ Zero)) λ l → (⊤ (Nonemp l)) ⇒ LenR Zero

tlHasR1 : {A : Set} → hasRefinement (tlRefinement1 {A}) (tl {A})
tlHasR1 (Len/∷ DLen) Unit = DLen

-- Showing tl takes any list of length (S n) to list of length n
tlRefinement2 : ∀ {A} → Refinement (tlType {A})
tlRefinement2 {A} =
  R∀ Nat λ n → RΠ (LenR (Succ n)) λ l → (⊤ (Nonemp l)) ⇒ LenR n

tlHasR2 : {A : Set} → hasRefinement (tlRefinement2 {A}) (tl {A})
tlHasR2 len (Len/∷ DLen) Unit = DLen


{-- I think the story is shaping up to be something like:
-- Write the code  you want to write
-- Refine its type as an afterthought
-- In many different ways, if you like
-- Datasorts as "gradual typing" but from precise types to more precise ones -- or just as like, compositional verifications
-- More like extrinsic program proofs
--}

-- More examples:
-- Maybe some other list operations?

lmap : {A B : Set} → (A → B) → List A → List B
lmap f [] = []
lmap f (x ∷ xs) = (f x) ∷ (lmap f xs)

lmapType : {A B : Set} → Set
lmapType {A} {B} = (A → B) → List A → List B

lmapRefinement : {A B : Set} → Refinement (lmapType {A} {B})
lmapRefinement {A} {B} =
  ⊤ (A → B) ⇒ (R∀ Nat λ n → LenR n ⇒ LenR n)

lmapSort : ∀ {A B} → hasRefinement (lmapRefinement {A} {B}) (lmap {A} {B})
lmapSort {A} {B} {f} x Zero {.[]} Len/[] = Len/[]
lmapSort {A} {B} {f} x (Succ i) {.(_ ∷ _)} (Len/∷ Dlen) = Len/∷ (lmapSort Unit i Dlen)

lmapSortNE : ∀ {A B} → hasRefinement (⊤ (A → B) ⇒ (NonempR ⇒ NonempR)) (lmap {A} {B})
lmapSortNE {A} {B} {f} Unit {x ∷ l} Nonemp/i = Nonemp/i

-- Let's try stringing some things together!
list2 : List Nat
list2 = Zero ∷ (Zero ∷ ((Succ Zero) ∷ []))

tlL2 : List Nat
tlL2 = tl (lmap Succ list2) (Nonemp/i)
 
-- Want to see if: tlL2 has refinement LenR
list2Sort : hasRefinement (LenR (Succ (Succ (Succ Zero)))) list2 
list2Sort = Len/∷ (Len/∷ (Len/∷ Len/[]))


mapl2Sort : hasRefinement
          (LenR (Succ (Succ (Succ Zero))))
          (lmap Succ list2)
mapl2Sort = lmapSort {Nat} {Nat} {Succ} Unit (Succ (Succ (Succ Zero))) list2Sort


tlL2Sort : hasRefinement (LenR (Succ (Succ Zero))) tlL2
tlL2Sort = tlHasR2 {Nat} (Succ (Succ Zero)) mapl2Sort {Nonemp/i} Unit

-- Success!
-- More painful than necessary, though!


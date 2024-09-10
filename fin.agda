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

-- Function sorts
_⇒_ : ∀ {A B} → Refinement A → Refinement B → Refinement (A → B)
R₁ ⇒ R₂ = λ f → ∀ {a} → (R₁ a) → (R₂ (f a))

-- Subsorting

_⊑_ : ∀ {A} → Refinement A → Refinement A → Set
R₁ ⊑ R₂ = ∀ {a} → (R₁ a) → (R₂ a)

-- Representing "inhabitants of refinements" as (data, proof) pairs
elt : {A : Set} → Refinement A → Set
elt {A} R = Σ A λ x → R x

-- an elt of R ⇒ S
-- would have type
--          Σ (A → B) λ f → (R ⇒ S) f
-- expands to
--          Σ (A → B) λ f → ∀ {a} → R a → S (f a)
-- but we may want to use it at type
--          elt R → elt S
-- that is, (Σ x:A. R x) → Σ y:B. S y
eltFun : {A B : Set} → {R : Refinement A} → {S : Refinement B}
         → elt (R ⇒ S)
         → elt R → elt S
eltFun {A} {B} {R} {S} (f , fRefines) (a , aR) = f a , fRefines {a} aR

eltFunType : {A B : Set} → (R : Refinement A) → (S : Refinement B)
           → Set
eltFunType R S = elt R → elt S

-- Promoting elements of subsorts
promote : ∀ {A} → {R S : Refinement A}
        → R ⊑ S → elt R → elt S
promote dSub (r , rR) =  r , dSub rR

-- Problem: this "forgets" that it's the same element going out as coming in?
-- Can recover that info, at least
open import Relation.Binary.PropositionalEquality
promote-equiv : ∀ {A} → {aR aS : A} → {R S : Refinement A}
              → {dSub : R ⊑ S}
              → {dR : R aR} → {dS : S aS}
              → promote dSub (aR , dR) ≡ (aS , dS)
              → aR ≡ aS
promote-equiv refl = refl

{-- Finite numbers as refinements --}

data Nat : Set where
  Z : Nat
  S : Nat → Nat

-- A family of refinements, one for each nat N, consisting of numbers
-- less than or equal to N.
data isLeq : (Max : Nat) → Nat → Set where
  fZ : ∀ {n} → isLeq n Z
  fS : ∀ {n x} → isLeq n x → isLeq (S n) (S x)

fin : Nat → Refinement Nat
fin n = isLeq n


-- fin N subsort of fin M if N <= M
leqSubsort : (Big Sm : Nat) → isLeq Big Sm → fin Sm ⊑ fin Big
leqSubsort Big Sm dLeq {Z} dFinSm = fZ
leqSubsort Z .Z fZ {S a} dFinSm = dFinSm
leqSubsort (S Big) .(S Sm) (fS {x = Sm} dLeq) {S a} (fS dFinSm) =
  fS (leqSubsort Big Sm dLeq {a} dFinSm)

one : Nat
one = S Z

two : Nat
two = S one

three : Nat
three = S two

four : Nat
four = S three

finOneSubThree : fin one ⊑ fin three
finOneSubThree = leqSubsort three one (fS fZ)

finOneSubFinFour : fin one ⊑ fin four
finOneSubFinFour = leqSubsort four one (fS fZ)

-- example problem:
-- indexing into vectors:
-- if i have v : vec n and i : fin n, i can index into v:
--   "get v i" is safe.
-- want to also allow
--   "get v i'",
-- for an i' :: elt R where R ⊑ fin n
data Vec {A : Set} : Nat → Set where
  Nil : Vec Z
  Cons : {n : Nat} → A → Vec {A} n → Vec (S n)


get : ∀ {A len} → Vec {A} (S len) → elt (fin len) → A
get {A} {len} (Cons x _) (.Z , fZ) = x
get {A} {S len} (Cons _ xs) (.(S i) , fS {x = i} snd) =
  get {A} {len} xs (i , snd)

data Foo : Set where
  fooA : Foo
  fooB : Foo
  fooC : Foo
  fooD : Foo

exampleVec : Vec (S (S (S (S Z))))
exampleVec = Cons fooA (Cons fooB (Cons fooC (Cons fooD Nil)))

-- Direct application (manually write the proof that 1 <= 4):
exampleRun : Foo
exampleRun = get exampleVec (S Z , fS fZ)
-- Norms to "fooB"

-- every number N is a fin of itself
toFin : (n : Nat) → elt (fin n)
toFin Z = Z , fZ
toFin (S n) with toFin n
...            | (n' , dFin) = S n' , fS dFin

exampleRun2 : Foo
exampleRun2 = get exampleVec (promote finOneSubThree (toFin one))

-- Could try: nonempty vectors as refinements of Vec


-- another idea:
-- just write index with Option return type,
-- refine Option to Some, and show
-- that indexing with a fin of the appropriate length
-- always gets you a Some

data Option (A : Set) : Set where
  Some : A → Option A
  None : Option A

data isSome {A : Set} : Option A → Set where
  Yes : {a : A} → isSome (Some a)

some : {A : Set} → Refinement (Option A)
some oa = isSome oa

getOption : ∀ {A len} → Vec {A} (S len) → Nat → Option A
getOption {A} {len} (Cons x v) Z = Some x
getOption {A} {Z} (Cons x v) (S i) = None
getOption {A} {S len} (Cons _ v) (S i) = getOption v i

exampleRun3 : Option Foo
exampleRun3 = getOption exampleVec one
-- Some fooB
test3 : exampleRun3 ≡ Some fooB
test3 = refl

exampleRun4 : Option Foo
exampleRun4 = getOption exampleVec four
-- None
test4 : exampleRun4 ≡ None
test4 = refl

-- refining getOption: want
-- {A} → ⊤ (Vec {A} l) ⇒ fin l ⇒ some A

getFnRefinement : {A : Set} → {len : Nat}
                → Refinement (Vec {A} (S len) → Nat → Option A)
getFnRefinement {A} {len} =
  ⊤ (Vec {A} (S len)) ⇒ (fin len ⇒ some {A})

-- Want to show: getOption has this refinement
getOptionHasRefinement : ∀{A len}
                       → getFnRefinement {A} {len} getOption
-- getOptionHasRefinement {a = vec} x {idx} dIdxFinLen
getOptionHasRefinement {a = Cons x xs} dTop {Z} dIdxFinLen = Yes
getOptionHasRefinement {a = Cons x xs} dTop {S idx} (fS dIdxFinLen)
  with getOptionHasRefinement {a = xs} Unit {idx} dIdxFinLen
...  | dIsSome = dIsSome



{--
synthGetType : ∀ {A : Set} → {len : Nat} → Set
synthGetType {A} {len} =
  eltFunType (⊤ (Vec {A} (S len))) ((fin len ⇒ some {A}))
{-- Result:
λ {A} {len} →
  Σ (Vec (S len)) (λ a → Top) →
  Σ (Nat → Option A) (λ f → {a : Nat} → isLeq len a → isSome (f a))
--}
--}



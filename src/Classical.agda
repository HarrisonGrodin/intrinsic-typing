module Classical where

infix  4 _⊢_
infix  6 _%_
infix  4 _∋_
infixl 5 _,_
infix  9 S_

infix  5 ƛ_
infixl 7 _·_
infixr 8 _+_
infixr 9 _×_
infixr 7 _⇒_
infixr 7 _-_

data Type : Set where
  unit : Type
  void : Type
  _×_  : Type → Type → Type
  _+_  : Type → Type → Type
  _⇒_  : Type → Type → Type
  _-_  : Type → Type → Type
  ¬_   : Type → Type

data Bool : Set where
  T : Bool
  F : Bool

not : Bool → Bool
not T = F
not F = T

product₀ : Bool → Type
product₀ T = unit
product₀ F = void

product₂ : Bool → Type → Type → Type
product₂ T = _×_
product₂ F = _+_

implies : Bool → Type → Type → Type
implies T = _⇒_
implies F = _-_

data Judgement : Set where
  _%_  : Type → Bool → Judgement
  #    : Judgement

data Context : Set where
  ∅   : Context
  _,_ : Context → Judgement → Context

data _∋_ : Context → Judgement → Set where
  Z  : ∀ {Γ J} → (Γ , J) ∋ J
  S_ : ∀ {Γ J J₁} → Γ ∋ J → (Γ , J₁) ∋ J

data _⊢_ : Context → Judgement → Set where
  `     : ∀ {Γ J} → Γ ∋ J → Γ ⊢ J
  throw : ∀ {P Γ A} → Γ ⊢ A % P → Γ ⊢ A % (not P) → Γ ⊢ #
  letcc : ∀ {P Γ A} → Γ , A % P ⊢ # → Γ ⊢ A % not P
  ⟨⟩    : ∀ {P Γ} → Γ ⊢ (product₀ P) % P
  ⟨_,_⟩ : ∀ {P Γ A₁ A₂} → Γ ⊢ A₁ % P  → Γ ⊢ A₂ % P → Γ ⊢ (product₂ P A₁ A₂) % P
  left  : ∀ {P Γ A₁ A₂} → Γ ⊢ A₁ % P → Γ ⊢ (product₂ (not P) A₁ A₂) % P
  right : ∀ {P Γ A₁ A₂} → Γ ⊢ A₂ % P → Γ ⊢ (product₂ (not P) A₁ A₂) % P
  ƛ_    : ∀ {P Γ A₁ A₂} → Γ , A₁ % P ⊢ A₂ % P → Γ ⊢ (implies P A₁ A₂) % P
  _·_   : ∀ {P Γ A₁ A₂} → Γ ⊢ A₁ % (not P) → Γ ⊢ A₂ % P → Γ ⊢ (implies (not P) A₁ A₂) % P
  ♩_    : ∀ {P Γ A} → Γ ⊢ A % (not P) → Γ ⊢ ¬ A % P

ex-proj-a : ∀ {A₁ A₂} → ∅ ⊢ ((A₁ × A₂) ⇒ A₁) % T
ex-proj-a = ƛ (letcc (throw (left (` Z)) (` (S Z))))

ex-proj-b : ∀ {A₁ A₂} → ∅ ⊢ ((A₁ + A₂) - A₁) % F
ex-proj-b = ƛ (letcc (throw (left (` Z)) (` (S Z))))

ex-case : ∀ {A₁ A₂ B} → ∅ ⊢ ((A₁ + A₂) ⇒ (A₁ ⇒ B) ⇒ (A₂ ⇒ B) ⇒ B) % T
ex-case =
  ƛ ƛ ƛ letcc (throw (` (S S S Z)) ⟨
    letcc (throw (` (S S S Z)) (` Z · ` (S Z))) ,
    letcc (throw (` (  S S Z)) (` Z · ` (S Z) ))
  ⟩)

ex-mp' : ∀ {A₁ A₂} → ∅ ⊢ ((A₁ ⇒ A₂) × A₁ ⇒ A₂ × unit) % T
ex-mp' =
  ƛ letcc (throw (` Z) ⟨
    letcc (throw (` (S S Z)) (
      left (letcc (throw (right (` Z)) (` (S S S Z)) ) · (` Z))
    )) ,
    ⟨⟩
  ⟩)

ex-falsity : ∅ ⊢ void + void × void + (unit + unit ⇒ void) % F
ex-falsity = ⟨ ⟨⟩ , ⟨ left ⟨⟩ , left ⟨⟩ · ⟨⟩ ⟩ ⟩

ex-dne-not : ∀ {A} → ∅ , ¬ (¬ A) % T ⊢ A % T
ex-dne-not = letcc (throw (` (S Z)) (♩ (♩ (` Z))))

ex-not-false-implication : ∀ {A} → ∅ , A ⇒ void % T ⊢ ¬ A % T
ex-not-false-implication = ♩ letcc (throw (` (S Z)) (` Z · ⟨⟩))

ex-false-implication-not : ∀ {A} → ∅ , ¬ A % T ⊢ A ⇒ void % T
ex-false-implication-not = ƛ letcc (throw (` (S S Z)) (♩ ` (S Z)))

ex-dne-implication : ∀ {A} → ∅ , (A ⇒ void) ⇒ void % T ⊢ A % T
ex-dne-implication =
  letcc (throw (` (S Z)) (
    letcc (throw (` Z) (ƛ letcc (throw (` (S S S Z)) (` (S Z))))) · ⟨⟩
  ))

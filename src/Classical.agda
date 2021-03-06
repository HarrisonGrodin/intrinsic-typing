module Classical where

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_
infix 30 _true
infix 30 _false

infix  5 ƛᵗ_
infix  5 ƛᶠ_
infixl 7 _·ᵗ_
infixl 7 _·ᶠ_

data Type : Set where
  void : Type
  unit : Type
  _+_  : Type → Type → Type
  _×_  : Type → Type → Type
  _⇒_  : Type → Type → Type

data Judgement : Set where
  _true  : Type → Judgement
  _false : Type → Judgement
  #      : Judgement

data Context : Set where
  ∅   : Context
  _,_ : Context → Judgement → Context

data _∋_ : Context → Judgement → Set where
  Z : ∀ {Γ J} → (Γ , J) ∋ J
  S : ∀ {Γ J J₁} → Γ ∋ J → (Γ , J₁) ∋ J

data _⊢_ : Context → Judgement → Set where
  ` : ∀ {Γ J} → Γ ∋ J → Γ ⊢ J
  throw : ∀ {Γ A} → Γ ⊢ A false → Γ ⊢ A true → Γ ⊢ #
  letccᵗ : ∀ {Γ A} → Γ , A false ⊢ # → Γ ⊢ A true
  letccᶠ : ∀ {Γ A} → Γ , A true  ⊢ # → Γ ⊢ A false
  ⟨⟩ᵗ : ∀ {Γ} → Γ ⊢ unit true
  ⟨⟩ᶠ : ∀ {Γ} → Γ ⊢ void false
  ⟨_,_⟩ᵗ : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ true  → Γ ⊢ A₂ true  → Γ ⊢ (A₁ × A₂) true
  leftᶠ  : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ false → Γ ⊢ (A₁ × A₂) false
  rightᶠ : ∀ {Γ A₁ A₂} → Γ ⊢ A₂ false → Γ ⊢ (A₁ × A₂) false
  ⟨_,_⟩ᶠ : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ false → Γ ⊢ A₂ false → Γ ⊢ (A₁ + A₂) false
  leftᵗ  : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ true → Γ ⊢ (A₁ + A₂) true
  rightᵗ : ∀ {Γ A₁ A₂} → Γ ⊢ A₂ true → Γ ⊢ (A₁ + A₂) true
  ƛᵗ_    : ∀ {Γ A₁ A₂} → Γ , A₁ true ⊢ A₂ true → Γ ⊢ (A₁ ⇒ A₂) true
  _·ᶠ_   : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ true → Γ ⊢ A₂ false → Γ ⊢ (A₁ ⇒ A₂) false
  ƛᶠ_    : ∀ {Γ A₁ A₂} → Γ , A₁ false ⊢ A₂ false → Γ ⊢ (A₁ ⇒ A₂) false
  _·ᵗ_   : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ false → Γ ⊢ A₂ true → Γ ⊢ (A₁ ⇒ A₂) true

ex1 : ∀ {A₁ A₂} → ∅ ⊢ ((A₁ × A₂) ⇒ A₁) true
ex1 = ƛᵗ (letccᵗ (throw (leftᶠ (` Z)) (` (S Z))))

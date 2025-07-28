{-# OPTIONS --type-in-type #-}

id : {A : Set} → A → A
id x = x

℘ : Set → Set
℘ A = A → Set

infixr 9 _∘_
_∘_ : {A : Set} {B : ℘ A} {C : ∀ {x} → ℘ (B x)} →
  (∀ {x} (y : B x) → C y) → (g : ∀ x → B x) → ∀ x → C (g x)
(f ∘ g) x = f (g x)

const : {A : Set} {B : ℘ A} → ∀ x → B x → A
const x _ = x

flip : ∀ {A B : Set} {C : A → ℘ B} → (∀ x y → C x y) → (∀ y x → C x y)
flip f y x = f x y

map : ∀ {A B} → (A → B) → ℘ (℘ A) → ℘ (℘ B)
map f s p = s (p ∘ f)

infix 2 ∃
∃ : ∀ A → ℘ A → Set
∃ _ F = ∀ P → (∀ x → F x → P) → P

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B

infixr 4 _,_
_,_ : ∀ {A F} x → F x → ∃ A F
_,_ x p P f = f x p

infixr 6 _∧_
_∧_ : Set → Set → Set
P ∧ Q = ∃ P (const Q)

fst : ∀ {P F} → ∃ P F → P
fst ∃PF = ∃PF _ const

snd : ∀ {P Q} → P ∧ Q → Q
snd P∧Q = P∧Q _ (const {B = const _} id)

⊥ : Set
⊥ = ∀ P → P

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

U : Set
U = ∀ {A} → (℘ (℘ A) → A) → A

elim : ∀ {A} → (℘ (℘ A) → A) → U → A
elim f u = u f

cons : ℘ (℘ U) → U
cons S f = f (map (elim f) S)

decons : U → ℘ (℘ U)
decons = elim (map cons)

F₀ : ℘ U
F₀ u = ∀ F → decons u F → ¬ F (cons (decons u))

S₀ : ℘ (℘ U)
S₀ F = (u : U) → decons u F → ¬ F u

δ₁ : {u : U} → F₀ u → F₀ (cons (decons u))
δ₁ i F = i (F ∘ cons ∘ decons)

δ₂ : ∀ {F} → S₀ F → S₀ (F ∘ cons ∘ decons)
δ₂ i u = i (cons (decons u))

ℓ₀ : ∀ F → S₀ F → ¬ F (cons S₀)
ℓ₀ _ i c = i (cons S₀) (δ₂ i) c

ℓ₁ : S₀ F₀
ℓ₁ u d i = i F₀ d (δ₁ {u} i)

ℓ₂ : F₀ (cons S₀)
ℓ₂ F = ℓ₀ (F ∘ cons ∘ decons)

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

infix 3 _⇔_
_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) ∧ (Q → P)

⇔-refl : ∀ {P} → P ⇔ P
⇔-refl = id , id

⇔-sym : ∀ {P Q} → P ⇔ Q → Q ⇔ P
⇔-sym P⇔Q = snd P⇔Q , fst P⇔Q

⇔-trans : ∀ {P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans P⇔Q Q⇔R = fst Q⇔R ∘ fst P⇔Q , snd P⇔Q ∘ snd Q⇔R

Congr : ℘ (℘ U)
Congr F = (w : U) → F w ⇔ F (cons (decons w))

infix 4 _~_ _≈_ _≋_
_~_ : U → ℘ U
u ~ v = ∀ F → Congr F → F u → F v

_≈_ : ℘ U → ℘ (℘ U)
_≈_ F G = (u : U) → F u ⇔ G u

_≋_ : ℘ (℘ U) → ℘ (℘ (℘ U))
_≋_ S T = ∀ F → S F ⇔ T F

~-congrˡ : {u : U} → Congr (u ~_)
~-congrˡ w = (λ eqv F congr → fst (congr w) ∘ eqv F congr) , λ eqv F congr → snd (congr w) ∘ eqv F congr

~-congrʳ : {u : U} → Congr (_~ u)
~-congrʳ w = (λ eqv F congr → eqv F congr ∘ snd (congr w)) , λ eqv F congr → eqv F congr ∘ fst (congr w)

~-refl : {u : U} → u ~ u
~-refl _ _ = id

~-sym : {u v : U} → u ~ v → v ~ u
~-sym {u} u~v = u~v (_~ u) ~-congrʳ ~-refl

~-trans : {u v w : U} → u ~ v → v ~ w → u ~ w
~-trans u~v v~w F congr = v~w F congr ∘ u~v F congr

≈-refl : ∀ {F} → F ≈ F
≈-refl _ = ⇔-refl

≈-sym : ∀ {F G} → F ≈ G → G ≈ F
≈-sym F≈G u = ⇔-sym (F≈G u)

≈-trans : ∀ {F G H} → F ≈ G → G ≈ H → F ≈ H
≈-trans F≈G G≈H u = ⇔-trans (F≈G u) (G≈H u)

≋-refl : ∀ {S} → S ≋ S
≋-refl _ = ⇔-refl

≋-sym : ∀ {S T} → S ≋ T → T ≋ S
≋-sym S≋T F = ⇔-sym (S≋T F)

≋-trans : ∀ {R S T} → R ≋ S → S ≋ T → R ≋ T
≋-trans R≋S S≋T F = ⇔-trans (R≋S F) (S≋T F)

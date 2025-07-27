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

infix 3 _⇔_
_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) ∧ (Q → P)

⇔-refl : ∀ {P} → P ⇔ P
⇔-refl = id , id

⇔-sym : ∀ {P Q} → P ⇔ Q → Q ⇔ P
⇔-sym P⇔Q = snd P⇔Q , fst P⇔Q

⇔-trans : ∀ {P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans P⇔Q Q⇔R = fst Q⇔R ∘ fst P⇔Q , snd P⇔Q ∘ snd Q⇔R

_≈_ : ℘ U → ℘ (℘ U)
_≈_ F G = (u : U) → F u ⇔ G u

Congr : ℘ (℘ U)
Congr F = F ≈ F ∘ cons ∘ decons

infix 4 _~_ _≈_ _≋_
_~_ : U → ℘ U
u ~ v = ∀ {F} → Congr F → F u → F v

_≋_ : ℘ (℘ U) → ℘ (℘ (℘ U))
_≋_ S T = ∀ {F} → Congr F → S F ⇔ T F

~-congrˡ : {u : U} → Congr (u ~_)
~-congrˡ w = (λ eqv {_} congr → fst (congr w) ∘ eqv congr) , λ eqv {_} congr → snd (congr w) ∘ eqv congr

~-congrʳ : {u : U} → Congr (_~ u)
~-congrʳ w = (λ eqv {_} congr → eqv congr ∘ snd (congr w)) , λ eqv {_} congr → eqv congr ∘ fst (congr w)

~-refl : {u : U} → u ~ u
~-refl _ = id

~-sym : {u v : U} → u ~ v → v ~ u
~-sym {u} u~v = u~v ~-congrʳ ~-refl

~-trans : {u v w : U} → u ~ v → v ~ w → u ~ w
~-trans u~v v~w congr = v~w congr ∘ u~v congr

≈-refl : ∀ {F} → F ≈ F
≈-refl _ = ⇔-refl

≈-sym : ∀ {F G} → F ≈ G → G ≈ F
≈-sym F≈G u = ⇔-sym (F≈G u)

≈-trans : ∀ {F G H} → F ≈ G → G ≈ H → F ≈ H
≈-trans F≈G G≈H u = ⇔-trans (F≈G u) (G≈H u)

≋-refl : ∀ {S} → S ≋ S
≋-refl _ = ⇔-refl

≋-sym : ∀ {S T} → S ≋ T → T ≋ S
≋-sym S≋T congr = ⇔-sym (S≋T congr)

≋-trans : ∀ {R S T} → R ≋ S → S ≋ T → R ≋ T
≋-trans R≋S S≋T congr = ⇔-trans (R≋S congr) (S≋T congr)

Congr′ : ℘ (℘ (℘ U))
Congr′ S = ∀ {F G} → F ≈ G → S F ⇔ S G

≈-congrˡ : ∀ {F} → Congr′ (F ≈_)
≈-congrˡ G≈H = flip ≈-trans G≈H , flip ≈-trans (≈-sym G≈H)

≈-congrʳ : ∀ {F} → Congr′ (_≈ F)
≈-congrʳ G≈H = ≈-trans (≈-sym G≈H) , ≈-trans G≈H

≈-congr-injˡ : ∀ {F G} → Congr G → (F ≈_) ≋ (G ≈_) → F ≈ G
≈-congr-injˡ congr eqv = snd (eqv congr) ≈-refl

≈-congr-injʳ : ∀ {F G} → Congr F → (_≈ F) ≋ (_≈ G) → F ≈ G
≈-congr-injʳ congr eqv = fst (eqv congr) ≈-refl

≋-congr-map : ∀ {S} → Congr′ S → S ≋ map (cons ∘ decons) S
≋-congr-map congr = congr

≋-congr-β : ∀ {S} → Congr′ S → S ≋ decons (cons S)
≋-congr-β = ≋-congr-map

Congr″ : ℘ U
Congr″ = Congr′ ∘ decons

cons-congr-inj : ∀ {S T} → Congr′ S → Congr′ T → cons S ~ cons T → S ≋ T
cons-congr-inj {S} {T} congrS congrT eqv = {!!}
  where
    eqv₁ : S ≋ decons (cons S)
    eqv₁ = ≋-congr-β congrS

    eqv₂ : decons (cons S) ≋ decons (cons T)
    eqv₂ = eqv {λ (u : U) → decons (cons S) ≋ decons u}
      (λ u → {!!} , λ eq {F} congr → ⇔-trans (eq congr) (⇔-sym {!!}))
      (≋-refl {decons (cons S)})

    eqv₃ : decons (cons T) ≋ T
    eqv₃ = ≋-sym (≋-congr-β congrT)

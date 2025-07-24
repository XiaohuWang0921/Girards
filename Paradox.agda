{-# OPTIONS --type-in-type #-}

id : {A : Set} → A → A
id x = x

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

const : {A B : Set} → A → B → A
const x _ = x

ℙ : Set → Set
ℙ A = A → Set

map : ∀ {A B} → (A → B) → ℙ (ℙ A) → ℙ (ℙ B)
map f s p = s (p ∘ f)

infix 2 ∃
∃ : ∀ A → ℙ A → Set
∃ _ F = ∀ P → (∀ x → F x → P) → P

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B

infixr 4 _,_
_,_ : ∀ {A F} x → F x → ∃ A F
_,_ x p P f = f x p

infixr 6 _∧_
_∧_ : Set → Set → Set
P ∧ Q = ∃ P (const Q)

fst : ∀ {P Q} → P ∧ Q → P
fst P∧Q = P∧Q _ const

snd : ∀ {P Q} → P ∧ Q → Q
snd P∧Q = P∧Q _ (const id)

⊥ : Set
⊥ = ∀ P → P

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

U : Set
U = ∀ {A} → (ℙ (ℙ A) → A) → A

elim : ∀ {A} → (ℙ (ℙ A) → A) → U → A
elim f u = u f

cons : ℙ (ℙ U) → U
cons S f = f (map (elim f) S)

decons : U → ℙ (ℙ U)
decons = elim (map cons)

infix 3 _⇔_
_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) ∧ (Q → P)

Congr : ℙ (ℙ U)
Congr F = (w : U) → F w ⇔ F (cons (decons w))

infix 4 _~_
_~_ : U → ℙ U
u ~ v = ∀ F → Congr F → F u → F v

⇔-refl : ∀ {P} → P ⇔ P
⇔-refl = id , id

⇔-sym : ∀ {P Q} → P ⇔ Q → Q ⇔ P
⇔-sym P⇔Q = snd P⇔Q , fst P⇔Q

⇔-trans : ∀ {P Q R} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans P⇔Q Q⇔R = fst Q⇔R ∘ fst P⇔Q , snd P⇔Q ∘ snd Q⇔R

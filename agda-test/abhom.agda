{-# OPTIONS --cubical-compatible #-}

module abhom where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infix 4 _≡_

trp : ∀ {A} {B : A → Set} {a₁ a₂ : A} → (a₁ ≡ a₂) → B a₁ → B a₂
trp refl b = b

_∙_ : ∀ {A} {a₁ a₂ a₃ : A} → (a₂ ≡ a₃) → (a₁ ≡ a₂) → (a₁ ≡ a₃)

p ∙ refl = p

refl∙ : ∀ {A} {a₁ a₂ : A} (p : a₁ ≡ a₂) → p ≡ (refl ∙ p)
refl∙ refl = refl

[_] : ∀ {A B} {a₁ a₂ : A} (f : A → B) → (a₁ ≡ a₂) → (f a₁) ≡ (f a₂)  
[ f ] refl = refl

∙-assoc : ∀ {A} {a₁ a₂ a₃ a₄ : A} {p : a₃ ≡ a₄} {q : a₂ ≡ a₃} {r : a₁ ≡ a₂} → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙-assoc {r = refl} = refl

[refl∙] : ∀ {A} {a₁ a₂ : A} {p q : a₁ ≡ a₂} {α : p ≡ (refl ∙ q)} → ∙-assoc {r = q} ∙ ([ _∙_ refl ] (refl∙ q) ∙ α) ≡ α
[refl∙] {q = refl} {α = refl} = refl

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y

  step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y  =  x≡y

  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y  = y≡z ∙ x≡y

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

η≡ : ∀ {A B : Set} {f g : A → B} → (f ≡ g) → ∀ x → (f x) ≡ (g x)
η≡ refl x = refl

η≡-dep : ∀ {A} {B : A → Set} {f g : ∀ a → B a} → (f ≡ g) → ∀ x → (f x) ≡ (g x)
η≡-dep refl x = refl

postulate fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → (f x) ≡ (g x)) → (f ≡ g)
postulate fun-ext-dep : ∀ {A} {B : A → Set} {f g : ∀ a → B a} → (∀ x → (f x) ≡ (g x)) → (f ≡ g)
postulate fun-ext≡fun-ext-dep : ∀ {A B : Set} {f g : A → B} (p : ∀ x → (f x) ≡ (g x)) → fun-ext p ≡ fun-ext-dep {B = λ _ → B} p
postulate fun-ext-dep-comp : ∀ {A} {B : A → Set} {f g : ∀ a → B a} (p : f ≡ g) → p ≡ fun-ext-dep (η≡-dep p)

η≡-∙ : ∀ {A B : Set} {f g h : A → B} (p : g ≡ h) (q : f ≡ g) → ∀ x → η≡ (p ∙ q) x ≡ ((η≡ p x) ∙ (η≡ q x))
η≡-∙ refl refl x = refl

isProp : Set → Set
isProp A = ∀ (x y : A) → x ≡ y 

isSet : Set → Set
isSet A = ∀ (x y : A) → isProp (x ≡ y)

isGrpd : Set →  Set
isGrpd A = ∀ (x y : A) → isSet (x ≡ y)

is2Type : Set → Set
is2Type A = ∀ (x y : A) → isGrpd (x ≡ y)

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : ∀ a → B a → Σ A B 

fst : ∀ {A B} → Σ A B → A
fst (x , y) = x

snd : ∀ {A B} → ∀ (p : Σ A B) → B (fst p)
snd (x , y) = y

Σ≡ : ∀ {A B} {x y : Σ A B} → x ≡ y → Σ ((fst x) ≡ (fst y)) (λ p → (snd y) ≡ (trp {B = B} p (snd x)))
Σ≡ refl = refl , refl

≡Σ : ∀ {A B} {x y : Σ A B} (p : (fst x) ≡ (fst y)) → (snd y) ≡ (trp {B = B} p (snd x)) → x ≡ y
≡Σ {x = x₁ , x₂} {y = y₁ , y₂} refl refl = refl

Ω : ∀ A → A → Set
Ω A a = a ≡ a

ptdMap : ∀ A (a : A) B (b : B) → Set
ptdMap A a B b = Σ (A → B) λ f → b ≡ (f a)

cst⋆ : ∀ A (a : A) B (b : B) → ptdMap A a B b
cst⋆ A a B b = (λ _ → b) , refl

ptw-∙ : ∀ {A B a b} → ptdMap A a (Ω B b) refl → ptdMap A a (Ω B b) refl → ptdMap A a (Ω B b) refl
ptw-∙ {a = a} (f , f⋆) (g , g⋆) = (λ x → f x ∙ g x) , ( ([ _∙_ (f a) ] g⋆ ∙ f⋆) ) -- (([ (λ p → p ∙ (g a)) ] f⋆) ∙ [ (λ p → refl ∙ p) ] g⋆) ([ _∙_ (f a) ] g⋆ ∙ f⋆) 

≡-pdtMap : ∀ {A} {a : A} {B} {b : B} {f g : ptdMap A a B b} (p : f ≡ g) → (snd g) ≡ ((η≡ (fst (Σ≡ p)) a) ∙ (snd f))
≡-pdtMap {f = f} refl = refl∙ (snd f)

trp-pdtMap : ∀ {A} {a : A} {B} {b : B} {f g : A → B} (p : f ≡ g) (q : b ≡ f a) → (trp p q) ≡ (η≡ p a ∙ q)
trp-pdtMap refl q = refl∙ q

≡-pdtMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g) → (fst (Σ≡ (p ∙ q))) ≡ ((fst (Σ≡ p)) ∙ (fst (Σ≡ q)))
≡-pdtMap-∙ refl refl = refl

∙-wihtout-funext :
  ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g) →
  η≡ (fst (Σ≡ p) ∙ fst (Σ≡ q)) ≡ (λ x → η≡ (fst (Σ≡ p)) x ∙ η≡ (fst (Σ≡ q)) x)
∙-wihtout-funext refl refl = refl

trp-≡-ptdMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g)
   → ∙-assoc {r = snd f} ∙ ([ _∙_ (η≡ (fst (Σ≡ p)) a) ] (≡-pdtMap q) ∙ ≡-pdtMap p)
   ≡ (trp {B = λ π → snd h ≡ (π a ∙ snd f)} ((∙-wihtout-funext p q) ∙ [ η≡ ] (≡-pdtMap-∙ p q)) (≡-pdtMap (p ∙ q)))
trp-≡-ptdMap-∙ {a = a} {f = f} {h = h} refl refl = [refl∙] --refl refl = [ (λ x → trp {B = λ π → snd h ≡ (π a ∙ snd f)} x refl∙) ] (fun-ext-dep-comp refl) ∙ {! fun-ext-dep (η≡-∙ (fst (Σ≡ p)) (fst (Σ≡ q))) !}

abHom : ∀ BG shG B²H pt-B²H → Ω (ptdMap BG shG B²H pt-B²H) (cst⋆ BG shG B²H pt-B²H) → ptdMap BG shG (Ω B²H pt-B²H) refl  
abHom BG shG B²H pt-B²H p = (η≡ (fst (Σ≡ p))) , (≡-pdtMap p)
--with Σ≡ p
--... | p₁ , p₂ = (η≡ p₁) , (trp-pdtMap p₁ refl ∙ p₂)

abHom-unit : ∀ BG shG B²H pt-B²H → (abHom BG shG B²H pt-B²H) refl ≡ (cst⋆ BG shG (Ω B²H pt-B²H) refl)
abHom-unit BG shG B²H pt-B²H = refl

abHom-mult : ∀ BG shG B²H pt-B²H p q → (abHom BG shG B²H pt-B²H) (p ∙ q) ≡ ptw-∙ (abHom BG shG B²H pt-B²H p) (abHom BG shG B²H pt-B²H q)
abHom-mult BG shG B²H pt-B²H p q =  ≡Σ (∙-wihtout-funext p q ∙ ([ η≡ ] (≡-pdtMap-∙ p q))) (trp-≡-ptdMap-∙ p q ∙ refl∙ _)



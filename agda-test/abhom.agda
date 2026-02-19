
{-# OPTIONS --cubical-compatible #-}

module abhom where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

trp : ∀ {A} {B : A → Set} {a₁ a₂ : A} → (a₁ ≡ a₂) → B a₁ → B a₂
trp refl b = b

_∙_ : ∀ {A} {a₁ a₂ a₃ : A} → (a₂ ≡ a₃) → (a₁ ≡ a₂) → (a₁ ≡ a₃)

p ∙ refl = p

refl∙ : ∀ {A} {a₁ a₂ : A} {p : a₁ ≡ a₂} → p ≡ (refl ∙ p)
refl∙ {p = refl} = refl

[_] : ∀ {A B} {a₁ a₂ : A} (f : A → B) → (a₁ ≡ a₂) → (f a₁) ≡ (f a₂)  
[ f ] refl = refl 

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

postulate fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → (f x) ≡ (g x)) → (f ≡ g)

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
ptw-∙ {a = a} (f , f⋆) (g , g⋆) = (λ x → f x ∙ g x) ,  ([ _∙_ (f a) ] g⋆ ∙ f⋆) -- (([ (λ p → p ∙ (g a)) ] f⋆) ∙ [ (λ p → refl ∙ p) ] g⋆)

≡-pdtMap : ∀ {A} {a : A} {B} {b : B} {f g : ptdMap A a B b} (p : f ≡ g) → (snd g) ≡ ((η≡ (fst (Σ≡ p)) a) ∙ (snd f))
≡-pdtMap refl = refl∙

trp-pdtMap : ∀ {A} {a : A} {B} {b : B} {f g : A → B} (p : f ≡ g) (q : b ≡ f a) → (trp p q) ≡ (η≡ p a ∙ q)
trp-pdtMap refl q = refl∙

≡-pdtMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g) → (fst (Σ≡ (p ∙ q))) ≡ ((fst (Σ≡ p)) ∙ (fst (Σ≡ q)))
≡-pdtMap-∙ refl refl = refl


trp-≡-ptdMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g)
   → ([ _∙_ (η≡ (fst (Σ≡ p)) a) ] (≡-pdtMap q) ∙ ≡-pdtMap p)
   ≡ (trp {A = A → Ω B }  ({!fun-ext!} ∙ ([ η≡ ] (≡-pdtMap-∙ p q))) (≡-pdtMap (p ∙ q)))
trp-≡-ptdMap-∙ = {!!}

abHom : ∀ BG shG B²H pt-B²H → Ω (ptdMap BG shG B²H pt-B²H) (cst⋆ BG shG B²H pt-B²H) → ptdMap BG shG (Ω B²H pt-B²H) refl  
abHom BG shG B²H pt-B²H p = (η≡ (fst (Σ≡ p))) , (≡-pdtMap p)
--with Σ≡ p
--... | p₁ , p₂ = (η≡ p₁) , (trp-pdtMap p₁ refl ∙ p₂)

abHom-unit : ∀ BG shG B²H pt-B²H → (abHom BG shG B²H pt-B²H) refl ≡ (cst⋆ BG shG (Ω B²H pt-B²H) refl)
abHom-unit BG shG B²H pt-B²H = refl

abHom-mult : ∀ BG shG B²H pt-B²H p q → (abHom BG shG B²H pt-B²H) (p ∙ q) ≡ ptw-∙ (abHom BG shG B²H pt-B²H p) (abHom BG shG B²H pt-B²H q)
abHom-mult BG shG B²H pt-B²H p q =  ≡Σ (fun-ext (η≡-∙ (fst (Σ≡ p)) (fst (Σ≡ q))) ∙ ([ η≡ ] (≡-pdtMap-∙ p q))) {!(fun-ext (η≡-∙ (fst (Σ≡ p)) (fst (Σ≡ q))) ∙
 [ η≡ ] (≡-pdtMap-∙ p q))!}
--with Σ≡ p | Σ≡ q
--... | p- , p⋆ | q- , q⋆ = ≡Σ ( fun-ext (η≡-∙ p- q-) ∙ {![ η≡ ] ?!} ) {!!}




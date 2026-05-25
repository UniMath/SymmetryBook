{-# OPTIONS --cubical-compatible #-}

module abhom where

open import Agda.Primitive

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a

infix 4 _≡_

variable
  ℓ : Level
  A B : Set ℓ

trp : ∀ {B : A → Set ℓ} {a₁ a₂ : A} → (a₁ ≡ a₂) → B a₁ → B a₂
trp refl b = b

_⁻¹ :  ∀ {a₁ a₂ : A} → (a₁ ≡ a₂) → (a₂ ≡ a₁)
refl ⁻¹ = refl

_∙_ : ∀ {a₁ a₂ a₃ : A} → (a₂ ≡ a₃) → (a₁ ≡ a₂) → (a₁ ≡ a₃)

p ∙ refl = p

refl∙ : ∀ {a₁ a₂ : A} (p : a₁ ≡ a₂) → p ≡ (refl ∙ p)
refl∙ refl = refl

⁻¹∙ : ∀ {a₁ a₂ : A} (p : a₁ ≡ a₂) → refl ≡ ((p ⁻¹) ∙ p)
⁻¹∙ refl = refl

[_] : ∀ {a₁ a₂ : A} (f : A → B) → (a₁ ≡ a₂) → (f a₁) ≡ (f a₂)  
[ f ] refl = refl

[_]ᵈ : ∀ {B : A → Set ℓ} {a₁ a₂ : A} (f : ∀ a → B a) (p : a₁ ≡ a₂) → trp p (f a₁) ≡ (f a₂)
[ f ]ᵈ refl = refl

∙-assoc : ∀ {a₁ a₂ a₃ a₄ : A} {p : a₃ ≡ a₄} {q : a₂ ≡ a₃} {r : a₁ ≡ a₂} → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙-assoc {r = refl} = refl

[refl∙] : ∀ {a₁ a₂ : A} {p q : a₁ ≡ a₂} {α : p ≡ (refl ∙ q)} → ∙-assoc {r = q} ∙ ([ _∙_ refl ] (refl∙ q) ∙ α) ≡ α
[refl∙] {q = refl} {α = refl} = refl

[_]≡_∙_ : ∀ {a₁ a₂ a₃ : A} (f : A → B) (p : a₂ ≡ a₃) (q : a₁ ≡ a₂) →
           [ f ] (p ∙ q) ≡ [ f ] p ∙ [ f ] q
[ f ]≡ p ∙ refl = refl
 
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

-- η≡-dep : ∀ {A} {B : A → Set} {f g : ∀ a → B a} → (f ≡ g) → ∀ x → (f x) ≡ (g x)
-- η≡-dep refl x = refl

postulate fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → (f x) ≡ (g x)) → (f ≡ g)
-- postulate fun-ext-dep : ∀ {A} {B : A → Set} {f g : ∀ a → B a} → (∀ x → (f x) ≡ (g x)) → (f ≡ g)
-- postulate fun-ext≡fun-ext-dep : ∀ {A B : Set} {f g : A → B} (p : ∀ x → (f x) ≡ (g x)) → fun-ext p ≡ fun-ext-dep {B = λ _ → B} p
-- postulate fun-ext-dep-comp : ∀ {A} {B : A → Set} {f g : ∀ a → B a} (p : f ≡ g) → p ≡ fun-ext-dep (η≡-dep p)

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

fst _₋ : ∀ {A B} → Σ A B → A
fst (x , y) = x

_₋ = fst

snd _∗ : ∀ {A B} → ∀ (p : Σ A B) → B (fst p)
snd (x , y) = y

_∗ = snd

Σ≡ : ∀ {A B} {x y : Σ A B} → x ≡ y → Σ ((fst x) ≡ (fst y)) (λ p → (snd y) ≡ (trp {B = B} p (snd x)))
Σ≡ refl = refl , refl

≡Σ : ∀ {A B} {x y : Σ A B} (p : (fst x) ≡ (fst y)) → (snd y) ≡ (trp {B = B} p (snd x)) → x ≡ y
≡Σ {x = x₁ , x₂} {y = y₁ , y₂} refl refl = refl

Ω : ∀ A → A → Set
Ω A a = a ≡ a

ptdMap : ∀ A (a : A) B (b : B) → Set
ptdMap A a B b = Σ (A → B) λ f → b ≡ (f a)

-- _₋ : ∀ {A a B b} → ptdMap A a B b → A → B
-- (f₋ , f∗) ₋ = f₋

-- _∗ : ∀ {A a B b} (f : ptdMap A a B b) → b ≡ (f ₋) a
-- (f₋ , f∗) ∗ = f∗

Ω-map : ∀ {A a B b} → ptdMap A a B b → Ω A a → Ω B b
Ω-map f s = ((f ∗) ⁻¹) ∙ ([ (f ₋) ] s ∙ (f ∗))

cst⋆ : ∀ A (a : A) B (b : B) → ptdMap A a B b
cst⋆ A a B b = (λ _ → b) , refl

ptw-∙-unptd : ∀ {A : Set} {B b} → (A → Ω B b) → (A → Ω B b) → (A → Ω B b)
ptw-∙-unptd f g x =  f x ∙ g x 

ptw-∙ : ∀ {A B a b} → ptdMap A a (Ω B b) refl → ptdMap A a (Ω B b) refl → ptdMap A a (Ω B b) refl
ptw-∙ {a = a} (f , f⋆) (g , g⋆) = ptw-∙-unptd f g , ( ([ _∙_ (f a) ] g⋆ ∙ f⋆) ) -- (([ (λ p → p ∙ (g a)) ] f⋆) ∙ [ (λ p → refl ∙ p) ] g⋆) ([ _∙_ (f a) ] g⋆ ∙ f⋆) 

≡-ptdMap : ∀ {A} {a : A} {B} {b : B} {f g : ptdMap A a B b} (p : f ≡ g) → (snd g) ≡ ((η≡ (fst (Σ≡ p)) a) ∙ (snd f))
≡-ptdMap {f = f} refl = refl∙ (snd f)

trp-ptdMap : ∀ {A} {a : A} {B} {b : B} {f g : A → B} (p : f ≡ g) (q : b ≡ f a) → (trp p q) ≡ (η≡ p a ∙ q)
trp-ptdMap refl q = refl∙ q

≡-ptdMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g) → (fst (Σ≡ (p ∙ q))) ≡ ((fst (Σ≡ p)) ∙ (fst (Σ≡ q)))
≡-ptdMap-∙ refl refl = refl

∙-wihtout-funext :
  ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g) →
  η≡ (fst (Σ≡ p) ∙ fst (Σ≡ q)) ≡ (λ x → η≡ (fst (Σ≡ p)) x ∙ η≡ (fst (Σ≡ q)) x)
∙-wihtout-funext refl refl = refl

trp-≡-ptdMap-∙ : ∀ {A} {a : A} {B} {b : B} {f g h : ptdMap A a B b} (p : g ≡ h) (q : f ≡ g)
   → ∙-assoc {r = snd f} ∙ ([ _∙_ (η≡ (fst (Σ≡ p)) a) ] (≡-ptdMap q) ∙ ≡-ptdMap p)
   ≡ (trp {B = λ π → snd h ≡ (π a ∙ snd f)} ((∙-wihtout-funext p q) ∙ [ η≡ ] (≡-ptdMap-∙ p q)) (≡-ptdMap (p ∙ q)))
trp-≡-ptdMap-∙ {a = a} {f = f} {h = h} refl refl = [refl∙] --refl refl = [ (λ x → trp {B = λ π → snd h ≡ (π a ∙ snd f)} x refl∙) ] (fun-ext-dep-comp refl) ∙ {! fun-ext-dep (η≡-∙ (fst (Σ≡ p)) (fst (Σ≡ q))) !}

abHom : ∀ BG shG B²H pt-B²H → Ω (ptdMap BG shG B²H pt-B²H) (cst⋆ BG shG B²H pt-B²H) → ptdMap BG shG (Ω B²H pt-B²H) refl  
abHom BG shG B²H pt-B²H p = (η≡ (fst (Σ≡ p))) , (≡-ptdMap p)
--with Σ≡ p
--... | p₁ , p₂ = (η≡ p₁) , (trp-ptdMap p₁ refl ∙ p₂)

abHom-unit : ∀ BG shG B²H pt-B²H → (abHom BG shG B²H pt-B²H) refl ≡ (cst⋆ BG shG (Ω B²H pt-B²H) refl)
abHom-unit BG shG B²H pt-B²H = refl

abHom-mult : ∀ BG shG B²H pt-B²H p q → (abHom BG shG B²H pt-B²H) (p ∙ q) ≡ ptw-∙ (abHom BG shG B²H pt-B²H p) (abHom BG shG B²H pt-B²H q)
abHom-mult BG shG B²H pt-B²H p q =  ≡Σ (∙-wihtout-funext p q ∙ ([ η≡ ] (≡-ptdMap-∙ p q))) (trp-≡-ptdMap-∙ p q ∙ refl∙ _)

abs : ∀ {BG shG BH shH} → ptdMap BG shG BH shH → (Ω BG shG) → (Ω BH shH)
abs (f , f∗) s = (f∗ ⁻¹) ∙ ([ f ] s ∙ f∗)

map-Ω-gen : ∀ {A B} (x y : A → B) → Set
map-Ω-gen x y = ∀ a → x a ≡ y a

ptdMap-Ω-gen : ∀ {A a B b} (x y : ptdMap A a B b) → Set
ptdMap-Ω-gen {a = a} x y = Σ (map-Ω-gen (x ₋) (y ₋)) λ f₋ → y ∗ ≡ f₋ a ∙ (x ∗)

-- _₋ᵍ : ∀ {A a B b} {x y : ptdMap A a B b} → ptdMap-Ω-gen x y → (∀ a' → (x ₋) a' ≡ (y ₋) a')
-- _₋ᵍ = fst

-- _∗ᵍ : ∀ {A a B b} {x y : ptdMap A a B b} (f : ptdMap-Ω-gen x y) → _
-- _∗ᵍ = snd

∂₀ : ∀ {A a B b} {x y : ptdMap A a B b} → ptdMap-Ω-gen x y → ptdMap A a B b
∂₀ {x = x} _ = x

∂₁ : ∀ {A a B b} {x y : ptdMap A a B b} → ptdMap-Ω-gen x y → ptdMap A a B b
∂₁ {y = y} _ = y

□ : ∀ {x y : A → B} (f : ∀ a → x a ≡ y a) {a₁ a₂ : A} (p : a₁ ≡ a₂) → f a₂ ∙ [ x ] p ≡ [ y ] p ∙ f a₁
□ f refl = refl∙ _

_▵_▿_ :
  ∀ {s a₁ a₂ a₃ a₄ t : A} {dl : s ≡ a₁} {dr : s ≡ a₂} {u : a₁ ≡ a₂} {l : a₁ ≡ a₃} {r : a₂ ≡ a₄} {d : a₃ ≡ a₄} {ul : t ≡ a₃} {ur : t ≡ a₄} 
  → dr ≡ u ∙ dl → d ∙ l ≡ r ∙ u → ur ≡ d ∙ ul
  → (ul ⁻¹) ∙ (l ∙ dl) ≡ (ur ⁻¹) ∙ (r ∙ dr)
_▵_▿_ {dl = refl} {refl} {ul = refl} {refl} refl sq refl = refl∙ _ ∙ sq

_▵_ :
  ∀ {s a₁ a₂ a₃ : A} {dl : s ≡ a₁} {d : s ≡ a₂} {dr : s ≡ a₃} {h₁ : a₁ ≡ a₂} {h₂ : a₂ ≡ a₃}
  → d ≡ h₁ ∙ dl → dr ≡ h₂ ∙ d
  → dr ≡ (h₂ ∙ h₁) ∙ dl
_▵_ {dl = refl} {refl} {refl} refl t₂ = t₂ 

Ω-mapᵍ : ∀ {A B a b} {x y : ptdMap A a B b} (f : ptdMap-Ω-gen x y) → ∀ s → Ω-map x s ≡ Ω-map y s 
Ω-mapᵍ f s = (f ∗) ▵ (□ (f ₋) s) ▿ (f ∗)

ptw-∙ᵍ-unptd : ∀ {A B} {x y z : A → B} → map-Ω-gen y z → map-Ω-gen x y → map-Ω-gen x z
ptw-∙ᵍ-unptd g f a = g a ∙ f a

ptw-∙ᵍ : ∀ {A a B b} {x y z : ptdMap A a B b} → ptdMap-Ω-gen y z → ptdMap-Ω-gen x y → ptdMap-Ω-gen x z
ptw-∙ᵍ {x = x} g f = (ptw-∙ᵍ-unptd (g ₋) (f ₋)) , (_▵_ {dl = x ∗} (f ∗) (g ∗))

≡-to-ptdMap-Ω-gen : ∀ {A a B b} {x y : ptdMap A a B b} → x ≡ y → ptdMap-Ω-gen x y
≡-to-ptdMap-Ω-gen refl = (λ _ → refl) , refl∙ _

≡-ptw-∙ : ∀ {A a B b} {x y z : ptdMap A a B b} (p : y ≡ z) (q : x ≡ y) → ptdMap-Ω-gen x z
≡-ptw-∙ {x = x} {y} {z} p q = ptw-∙ᵍ {x = x} {y} {z} (≡-to-ptdMap-Ω-gen p) (≡-to-ptdMap-Ω-gen q)

-- [Ω]-preserves-∙ :
--   ∀ {A a B b} {x y z : ptdMap A a B b} (p : y ≡ z) (q : x ≡ y) →
--   [ Ω A ] p  ≡ [ Ω A ] p
-- [Ω]-preserves-∙ = ?

  

-- Ω-mapᵍ-preserves-ptw-∙ :
--   ∀ {A a B b} {x y z : ptdMap A a B b} (f : ptdMap-Ω-gen x y) (g : ptdMap-Ω-gen y z) →
--   ∀ s → Ω-mapᵍ {x = x} {y = z} (ptw-∙ᵍ {x = x} {y} {z} g f) s ≡ (Ω-mapᵍ {x = y} {z} g s ∙ Ω-mapᵍ {x = x} {y} f s)
-- Ω-mapᵍ-preserves-ptw-∙ f g s = {!!}



-- Ω-map-preserves-ptw-∙ :
--   ∀ {BG shG B²H pt-B²H} (f g : ptdMap BG shG (Ω B²H pt-B²H) refl) →
--   ∀ s → Ω-map (ptw-∙ f g) s ≡ ptw-∙-unptd (Ω-map f) (Ω-map g) s
-- Ω-map-preserves-ptw-∙ {pt-B²H = pt-B²H} f g s =
--   {!!} ∙ (Ω-mapᵍ-preserves-ptw-∙ {x = {!cst⋆ _ _ _ pt-B²H!} }f g s ∙ {!!})
-- fun-ext
--   (λ x →
--     begin abs (ptw-∙ f g) x
--     ≡⟨ {!!} ⟩ (((f∗ ⁻¹) ∙ ([ f- ] x ∙ f∗)) ∙ {!(g∗ ⁻¹) ∙ ([ g- ] x ∙ g∗)!})
--     ≡⟨⟩ abs f x ∙ abs g x ∎)


-- abs : ∀ {BG shG BH shH} → ptdMap BG shG BH shH → ptdMap (Ω BG shG) refl (Ω BH shH) refl
-- abs (f , f∗) = Ωf , ([ _∙_ (f∗ ⁻¹) ] (refl∙ f∗) ∙ ⁻¹∙ f∗)
--   where
--   Ωf : _ → _
--   Ωf s =  (f∗ ⁻¹) ∙ ([ f ] s ∙ f∗)

-- abs-ptw : ∀ {BG shG B²H pt-B²H} (f g : ptdMap BG shG (Ω B²H pt-B²H) refl) → abs (ptw-∙ f g) ≡ ptw-∙ (abs f) (abs g) 
-- abs-ptw f g = ≡Σ (fun-ext (λ s → {!!})) {!!}

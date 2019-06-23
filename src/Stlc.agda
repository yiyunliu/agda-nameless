module Stlc where
open import Data.Nat using (ℕ; _≟_; suc; zero; _⊔_; _≥_)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥)
open import Relation.Binary using (Decidable)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Function.Equality using (_⟶_)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans; cong;  _≡_; _≢_; setoid; inspect; [_])


data Term : Set where
  bvar : ℕ → Term
  fvar : ℕ → Term
  abs : Term → Term
  app : Term → Term → Term

module _ where
  close-t : ℕ → Term → ℕ → Term
  close-t depth t@(bvar x₁) x = t
  close-t depth (fvar x₁) x with x ≟ x₁
  ... | yes _ = bvar depth
  ... | no _  = fvar x₁
  close-t depth (abs t) x = abs (close-t (suc depth) t x)
  close-t depth (app t t₁) x = app (close-t depth t x) (close-t depth t₁ x)

  _⟫_⟪ : Term → ℕ → Term
  _⟫_⟪ = close-t 0

module _ where
  private
    ex₁ : abs (app (abs (bvar 1)) (fvar 0)) ⟫ 0 ⟪ ≡ abs (app (abs (bvar 1)) (bvar 1))
    ex₁ = refl

fresh : Term → ℕ
fresh (bvar x) = 0
fresh (fvar x) = suc x
fresh (abs t) = fresh t
fresh (app t t₁) = suc ((fresh t) ⊔ (fresh t₁))


module _ where
  open-t : ℕ → Term → ℕ → Term
  open-t depth t@(bvar x) new-var with x ≟ depth
  ... | yes _ = fvar new-var
  ... | no _  = t
  open-t depth t@(fvar x) new-var = t
  open-t depth (abs t) new-var = abs (open-t (suc depth) t new-var)
  open-t depth (app t t₁) new-var = app (open-t depth t new-var) (open-t depth t₁ new-var)

  _⟪_⟫ : Term → ℕ → Term
  _⟪_⟫ = open-t 0

module _ where
  private
    ex₂ : app ( abs ( app ( bvar 0) ( bvar 1))) ( bvar 0) ⟪ 2 ⟫ ≡
      app (abs (app (bvar 0) (fvar 2))) (fvar 2)
    ex₂ = refl

data free-var : ℕ → Term → Set where
  fvar : ∀ n n′ → n ≡ n′ → free-var n (fvar n′)
  abs  : ∀ n t → free-var n t → free-var n (abs t)
  app  : ∀ n t t′ → free-var n t ⊎ free-var n t′  → free-var n (app t t′)

free-var? : Decidable free-var
free-var? n (bvar x) = no (λ ())
free-var? n (fvar x) with x ≟ n
free-var? n (fvar .n) | yes refl = yes (fvar n n refl)
... | no  neq = no (helper neq)
  where helper : ∀ {x = n} {x} →
               ¬ x ≡ n → ¬ free-var n (fvar x)
        helper neq (fvar n n′ x) = contradiction (sym x) neq 
free-var? n (abs t) with (free-var? n t)
... | yes fv = yes (abs n t fv)
... | no nfv = no (helper nfv)
  where helper : ∀ {x = n} {t} →
         (free-var n t → ⊥) → free-var n (abs t) → ⊥
        helper neq (abs n t fv) = neq fv
free-var? n (app t t₁) with free-var? n t | free-var? n t₁
free-var? n (app t t₁) | yes p | fv₁? = yes (app n t t₁ (inj₁ p))
free-var? n (app t t₁) | no ¬p | yes p = yes (app n t t₁ (inj₂ p))
free-var? n (app t t₁) | no ¬p | no ¬p₁ = no (helper ¬p ¬p₁)
  where helper : ∀ {x = n} {t} {t₁} →
          (free-var n t → ⊥) →
          (free-var n t₁ → ⊥) → free-var n (app t t₁) → ⊥
        helper neq neq₁ (app n t t′ (inj₁ x)) = neq x
        helper neq neq₁ (app n t t′ (inj₂ y)) = neq₁ y

module _ where
  close-var-fv-0 : ∀ t x y n →  free-var y (close-t n t x) → free-var y t × y ≢ x
  close-var-fv-0 (fvar x₁) x y n mem with x ≟ x₁
  close-var-fv-0 (fvar x₁) x y n (fvar .y .x₁ x₂) | no ¬p = (fvar y x₁ x₂) , λ x₃ → ¬p (trans (sym x₃) x₂)
  close-var-fv-0 (abs t) x y n mem with close-var-fv-0 t x y (suc n)
  close-var-fv-0 (abs t) x y n mem | f with free-var? y (close-t (suc n) t x)
  close-var-fv-0 (abs t) x y n mem | f | yes p = abs y t (proj₁ (f p)) , proj₂ (f p)
  close-var-fv-0 (abs t) x y n mem | f | no ¬p with close-t (suc n) t x
  close-var-fv-0 (abs t) x y n (abs .y .t′ mem) | f | no ¬p | t′ = contradiction mem ¬p
  close-var-fv-0 (app t t₁) x y n (app .y .(close-t n t x) .(close-t n t₁ x) (inj₁ free-t))
    with close-var-fv-0 t x y n
  ... | f = (app y t t₁ (inj₁ (proj₁ (f free-t)))) , (proj₂ (f free-t))
  close-var-fv-0 (app t t₁) x y n (app .y .(close-t n t x) .(close-t n t₁ x) (inj₂ free-t₁))
    with close-var-fv-0 t₁ x y n
  ... | f = (app y t t₁ (inj₂ (proj₁ (f free-t₁)))) , (proj₂ (f free-t₁))

  close-var-fv-1 : ∀ t x y n → (free-var y t × y ≢ x) → free-var y (close-t n t x)
  close-var-fv-1 (fvar x₁) x y n (mem , y≢x)
    with x ≟ x₁
  close-var-fv-1 (fvar x₁) .x₁ y n (fvar .y .x₁ x , y≢x) | yes refl = contradiction x y≢x
  close-var-fv-1 (fvar x₁) x y n (mem , y≢x) | no ¬p = mem
  close-var-fv-1 (abs t) x y n (abs .y .t mem , y≢x) =
    abs y (close-t (suc n) t x) (close-var-fv-1 t x y (suc n) (mem , y≢x))
  close-var-fv-1 (app t t₁) x y n (app .y .t .t₁ (inj₁ x₁) , y≢x) =
    app y (close-t n t x) (close-t n t₁ x) (inj₁ (close-var-fv-1 t x y n (x₁ , y≢x)))
  close-var-fv-1 (app t t₁) x y n (app .y .t .t₁ (inj₂ y₁) , y≢x) =
    app y (close-t n t x) (close-t n t₁ x) (inj₂ (close-var-fv-1 t₁ x y n (y₁ , y≢x)))
    
  close-var-fv : ∀ t x y →  free-var y (t ⟫ x ⟪) ⇔ (free-var y t × y ≢ x)
  close-var-fv t x y = record
    { to = record { _⟨$⟩_ = close-var-fv-0 t x y zero
    ; cong = cong _ }
    ; from = record { _⟨$⟩_ = close-var-fv-1 t x y zero
    ; cong = cong _ } }


is-fresh : ℕ → Term → Set
is-fresh n x = ¬ free-var n x


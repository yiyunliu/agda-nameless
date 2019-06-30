module Stlc where
open import Data.Nat using (ℕ; _≟_; suc; zero; _⊔_; _≥_; _<_; _≤_; s≤s)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Relation.Nullary.Decidable using (from-no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥)
open import Relation.Binary using (Decidable)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Function.Equality using (_⟶_)
open import Function using (_∘_; flip)
open import Function.Equivalence using (_⇔_)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans; cong;  _≡_; _≢_; setoid; inspect; [_]; cong₂)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All using (map)
open import Data.List.Membership.DecPropositional _≟_ using (_∉_; _∈?_; _∈_)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any; ¬Any⇒All¬)
open import Data.List.Extrema.Nat using (max; xs≤max)
open import Data.Nat.Properties using (<-transʳ; <⇒≢; suc-injective)



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

ex₃ : is-fresh 3 (app (fvar 0) (fvar 1))
ex₃ (app .3 .(fvar 0) .(fvar 1) (inj₁ (fvar .3 .0 ())))
ex₃ (app .3 .(fvar 0) .(fvar 1) (inj₂ (fvar .3 .1 ())))

is-fresh? : Decidable is-fresh
is-fresh? x t with free-var? x t
is-fresh? x t | yes p = no (λ z → z p)
is-fresh? x t | no ¬p = yes ¬p

ex₄ : ¬ is-fresh 3 (app (fvar 3) (fvar 1))
ex₄ = from-no (is-fresh? 3 (app (fvar 3) (fvar 1)))

is-closed : Term → Set
is-closed t = ∀ x → is-fresh x t

is-closed? : ∀ t → Dec (is-closed t)
is-closed? (bvar x) = yes (λ x ())
is-closed? (fvar x) = no (λ z → z x (fvar x x refl))
is-closed? (abs t) with is-closed? t
is-closed? (abs t) | yes p = yes (λ x x₁ → p x (aux x₁))
  where aux : ∀ {t} {x} → free-var x (abs t) → free-var x t
        aux (abs n t fv) = fv
is-closed? (abs t) | no ¬p = no (λ z → ¬p (λ x z₁ → z x (abs x t z₁)))
is-closed? (app t t₁) with is-closed? t | is-closed? t₁
is-closed? (app t t₁) | yes p | yes p₁ = yes (λ x x₁ → aux p p₁ x₁)
  where aux : ∀ {t} {t₁} {x} →
            (∀ x₁ → free-var x₁ t → ⊥) →
            (∀ x₁ → free-var x₁ t₁ → ⊥) → free-var x (app t t₁) → ⊥
        aux p p₁ (app n t t′ (inj₁ x)) = p n x
        aux p p₁ (app n t t′ (inj₂ y)) = p₁ n y
is-closed? (app t t₁) | yes p | no ¬p = no (λ z → ¬p (λ x z₁ → z x (app x t t₁ (inj₂ z₁))))
is-closed? (app t t₁) | no ¬p | fv₁ = no (λ z → ¬p (λ x z₁ → z x (app x t t₁ (inj₁ z₁))))

module _ where
  open-var-fv-aux : ∀ t x y n → free-var y (open-t n t x) → free-var y t ⊎ y ≡ x
  open-var-fv-aux (bvar x₁) x y n with x₁ ≟ n
  open-var-fv-aux (bvar x₁) x y .x₁ | yes refl = λ x₂ → inj₂ (aux x₂)
    where aux : ∀ {x} {y} → free-var y (fvar x) → y ≡ x
          aux (fvar n n′ x) = x
  open-var-fv-aux (bvar x₁) x y n | no ¬p = λ x₂ → inj₁ x₂
  open-var-fv-aux (fvar x₁) x y n = inj₁
  open-var-fv-aux (abs t) x y n h  with open-var-fv-aux t x y (suc n)
  open-var-fv-aux (abs t) x y n (abs .y .(open-t (suc n) t x) h) | fv-or-eq with fv-or-eq h
  open-var-fv-aux (abs t) x y n (abs .y .(open-t (suc n) t x) h) | fv-or-eq | inj₁ x₁ = inj₁ (abs y t x₁)
  open-var-fv-aux (abs t) x y n (abs .y .(open-t (suc n) t x) h) | fv-or-eq | inj₂ y₁ = inj₂ y₁
  open-var-fv-aux (app t t₁) x y n h
    with open-var-fv-aux t x y n | open-var-fv-aux t₁ x y n
  open-var-fv-aux (app t t₁) x y n (app .y .(open-t n t x) .(open-t n t₁ x) (inj₁ x₁)) | v | v₁
    with v x₁
  open-var-fv-aux (app t t₁) x₂ y n (app .y .(open-t n t x₂) .(open-t n t₁ x₂) (inj₁ x₁)) | v | v₁ | inj₁ x = inj₁ (app y t t₁ (inj₁ x))
  open-var-fv-aux (app t t₁) x y₁ n (app .y₁ .(open-t n t x) .(open-t n t₁ x) (inj₁ x₁)) | v | v₁ | inj₂ y = inj₂ y
  open-var-fv-aux (app t t₁) x y n (app .y .(open-t n t x) .(open-t n t₁ x) (inj₂ y₁)) | v | v₁
    with v₁ y₁
  open-var-fv-aux (app t t₁) x y n (app .y .(open-t n t x) .(open-t n t₁ x) (inj₂ y₁)) | v | v₁ | inj₁ x₁ = inj₁ (app y t t₁ (inj₂ x₁))
  open-var-fv-aux (app t t₁) x y n (app .y .(open-t n t x) .(open-t n t₁ x) (inj₂ y₁)) | v | v₁ | inj₂ y₂ = inj₂ y₂
  open-var-fv : ∀ t x y → free-var y (t ⟪ x ⟫) → free-var y t ⊎ y ≡ x
  open-var-fv  = λ t x y → open-var-fv-aux t x y zero


data lc : Term → Set where
  lc-var : ∀ x → lc (fvar x)
  lc-app : ∀ t t′ → lc t → lc t′ → lc (app t t′)
  lc-abs : ∀ l t → (∀ x → x ∉ l → lc ( t ⟪ x ⟫ )) → lc (abs t)

data fresh-nat (l : List ℕ) : Set where
  fresh-nat-e : ∀ n → n ∉ l  →  fresh-nat l



fresh-nat-dec : ∀ l → fresh-nat l
fresh-nat-dec l = fresh-nat-e ((suc (max 0 l))) (All¬⇒¬Any (All.map  (neg-sym ∘ <⇒≢)
    (All.map (λ {i} ev → s≤s ev) (xs≤max 0 l))))
  where neg-sym : ∀ {x y} → x ≢ y → y ≢ x
        neg-sym {x} {.x} x≢y refl = x≢y refl


ex₅ : ¬ (lc (abs (bvar 3)))
-- you can put hole in with construct and add a where clause after it
ex₅ (lc-abs l .(bvar 3) f) with fresh-nat-dec l
ex₅ (lc-abs l .(bvar _) f) | fresh-nat-e n x with f n x
ex₅ (lc-abs l .(bvar _) f) | fresh-nat-e n x | ()


subst : ℕ → Term → Term → Term
subst x u (bvar x₁) = bvar x₁
subst x u (fvar x₁) with x ≟ x₁
... | yes _ = u
... | no  _ = fvar x₁
subst x u (abs t) = abs (subst x u t)
subst x u (app t t₁) = app (subst x u t) (subst x u t₁)

data lc-abs-body : Term → Set where
  cfinite-body : ∀ l t → (f : ∀ x → x ∉ l → lc ( t ⟪ x ⟫ )) → lc-abs-body t


app-inj : ∀ {t₁ t₂ t₁′ t₂′}  → Term.app t₁ t₂ ≡ Term.app t₁′ t₂′ → t₁ ≡ t₁′ × t₂ ≡ t₂′
app-inj {t₁} {t₂} .{t₁} .{t₂} refl = refl , refl

abs-inj : ∀ {t t′} → Term.abs t ≡ Term.abs t′ → t ≡ t′
abs-inj refl = refl

bvar-inj : ∀ {i j} → bvar i ≡ bvar j → i ≡ j
bvar-inj refl = refl

-- i understand the j = 0 special case, but not the i <> j magic..
open-rec-lc : ∀ i j u v t → i ≢ j →  open-t i (open-t j t v) u ≡ open-t j t v → t ≡ open-t i t u
open-rec-lc i j u v (bvar x) i≢j oo≡o with x ≟ i
open-rec-lc i j u v (bvar .i) i≢j oo≡o | yes refl with i ≟ j
open-rec-lc i .i u v (bvar .i) i≢j oo≡o | yes refl | yes refl = contradiction refl i≢j
open-rec-lc i j u v (bvar .i) i≢j oo≡o | yes refl | no ¬p with i ≟ i
open-rec-lc i j u v (bvar .i) i≢j oo≡o | yes refl | no ¬p | no ¬p₁ with bvar-inj oo≡o
... | eq = contradiction (¬p₁ refl) (λ z → z)
open-rec-lc i j u v (bvar x) i≢j oo≡o | no ¬p = refl
open-rec-lc i j u v (fvar x) i≢j oo≡o = refl
open-rec-lc i j u v (abs t) i≢j oo≡o with abs-inj oo≡o
... | eq = cong abs (open-rec-lc (suc i) (suc j) u v t (i≢j ∘ suc-injective) eq)
open-rec-lc i j u v (app t t₁) i≢j oo≡o with app-inj oo≡o
... | eq , eq′ = cong₂ app (open-rec-lc i j u v t i≢j eq) (open-rec-lc i j u v t₁ i≢j eq′)

open-var-lc : ∀ {u} n y  → lc u → u ≡ open-t n u y
open-var-lc n y (lc-var x) = refl
open-var-lc n y (lc-app t t′ lc-u lc-u₁) = cong₂ app (open-var-lc n y lc-u) (open-var-lc n y lc-u₁)
-- stuck. t is not necessarily locally closed.. need to strengthen the IH
open-var-lc n y (lc-abs l t f) with fresh-nat-dec (y ∷ l)
open-var-lc n y (lc-abs l t f) | fresh-nat-e fv fv∉l
  -- can't use let ev = f fv fv∉l because agda can't tell if open-var-lc terminates with an abstract ev!
   = cong abs (open-rec-lc (suc n) 0 y fv  t (λ ())
          (sym (open-var-lc {open-t 0 t fv} (suc n) y (f fv λ z → fv∉l (there z)))))


-- if u is not locally closed, the bvar might be captured by t
subst-open-var-aux : ∀ n x y u t → x ≢ y → lc u → subst x u (open-t n t y) ≡ open-t n (subst x u t) y
subst-open-var-aux n x y u (bvar x₁) x≢y lc-u with x₁ ≟ n
subst-open-var-aux n x y u (bvar .n) x≢y lc-u | yes refl with x ≟ y
subst-open-var-aux n x .x u (bvar _) x≢y lc-u | yes refl | yes refl = contradiction refl x≢y
subst-open-var-aux n x y u (bvar _) x≢y lc-u | yes refl | no ¬p = refl
subst-open-var-aux n x y u (bvar x₁) x≢y lc-u | no ¬p = refl
subst-open-var-aux n x y u (fvar x₁) x≢y lc-u with x ≟ x₁
subst-open-var-aux n x y u (fvar .x) x≢y lc-u | yes refl = open-var-lc n y lc-u
subst-open-var-aux n x y u (fvar x₁) x≢y lc-u | no ¬p = refl
subst-open-var-aux n x y u (abs t) x≢y lc-u = cong abs (subst-open-var-aux (suc n) x y u t x≢y lc-u)
subst-open-var-aux n x y u (app t t₁) x≢y lc-u = cong₂ app
  (subst-open-var-aux n x y u t x≢y lc-u)
  (subst-open-var-aux n x y u t₁ x≢y lc-u)


subst-open-var : ∀ x y u t → x ≢ y → lc u → subst x u (t ⟪ y ⟫) ≡ subst x u t ⟪ y ⟫
subst-open-var = subst-open-var-aux 0


subst-lc : ∀ x u t → lc u → lc t → lc (subst x u t)
subst-lc x u .(fvar x₁) lc-u (lc-var x₁) with x ≟ x₁
subst-lc .x₁ u .(fvar x₁) lc-u (lc-var x₁) | yes refl = lc-u
subst-lc x u .(fvar x₁) lc-u (lc-var x₁) | no ¬p = lc-var x₁
subst-lc x u .(app t t′) lc-u (lc-app t t′ lc-t lc-t₁) =
  lc-app (subst x u t) (subst x u t′) (subst-lc x u t lc-u lc-t)
    (subst-lc x u t′ lc-u lc-t₁)
subst-lc x u .(abs t) lc-u (lc-abs l t f) = lc-abs (x ∷ l) (subst x u t) aux
  where aux :  (x₁ : ℕ) → x₁ ∉ x ∷ l → lc (subst x u t ⟪ x₁ ⟫)
        aux x₁ not-in rewrite (sym (subst-open-var x x₁ u t (λ x₃ → not-in (here (sym x₃))) lc-u))
          = subst-lc x u _ lc-u (f x₁ λ z → not-in (there z))

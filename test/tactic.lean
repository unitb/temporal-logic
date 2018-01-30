
import temporal_logic

open temporal predicate

section
variable α : Type

variables Γ p q r : cpred
variables v₀ v₁ : tvar α
variables f : pred' α
variables h₀ : Γ ⊢ p ≡ q
include h₀
example : Γ ⊢ p ⋀ r ≡ q ⋀ r :=
begin [temporal]
  rw h₀,
end

example : Γ ⊢ p ⋀ r →  Γ ⊢ q ⋀ r :=
assume _,
begin [temporal]
  rw ← h₀,
end

variables h₁ : Γ ⊢ ◻(p ≡ q)
omit h₀
include h₁
example : Γ ⊢ ◻◇p ≡ ◻◇q :=
begin [temporal]
  rw h₁,
end

variables h₂ : Γ ⊢ ◻(v₀ ≃ v₁)
include h₂
example (h : Γ ⊢ ◇(◻(f ! v₀ ≡ q) ⋀ p))
: Γ ⊢ ◇(◻(f ! v₁ ≡ q) ⋀ p) :=
begin [temporal]
  rw ← h₂,
end

example (h : Γ ⊢ ◇(◻(f ! v₀ ≡ q) ⋀ p))
: Γ ⊢ ◇(◻(f ! v₁ ≡ q) ⋀ p) :=
begin [temporal]
  rw h₂ at h,
end
end

inductive nat.even : ℕ → Prop
 | zero : nat.even 0
 | succ_succ (n) : nat.even n → nat.even (nat.succ (nat.succ n))

section
open nat
lemma even_succ_succ (n : ℕ)
: nat.even (nat.succ $ nat.succ n) ↔ nat.even n :=
sorry
end
abbreviation succ : var ℕ ℕ := ⟨ nat.succ ⟩
abbreviation even : var ℕ Prop := ⟨ nat.even ⟩

variables Γ : cpred

example (x y : tvar ℕ)
(h₀ : Γ ⊢ ◻(⊙x ≃ succ!succ!x))
(h₁ : Γ ⊢ ◻(⊙y ≃ y))
(h₂ : Γ ⊢ even!x ≡ even!y)
: Γ ⊢ ◻(even!x ≡ even!y) :=
begin [temporal]
  apply induct _ _ _ _,
-- h₀ : ◻(⊙x ≃ succ ! succ ! x),
-- h₁ : ◻(⊙y ≃ y),
-- h₂ : even ! x ≡ even ! y
-- ⊢ ◻((even ! x ≡ even ! y) ⟶ ⊙(even ! x ≡ even ! y))
  { clear h₂,
    henceforth at ⊢ h₀ h₁,
-- _inst_1 : persistent Γ,
-- h₁ : ⊙y ≃ y,
-- h₀ : ⊙x ≃ succ ! succ ! x
-- ⊢ (even ! x ≡ even ! y) ⟶ ⊙(even ! x ≡ even ! y)
    intros h₃,
-- h₁ : ⊙y ≃ y,
-- h₀ : ⊙x ≃ succ ! succ ! x,
-- h₃ : even ! x ≡ even ! y
-- ⊢ ⊙(even ! x ≡ even ! y)
    explicit'
-- x x' y y' : ℕ,
-- h₃ : nat.even x ↔ nat.even y,
-- h₀ : x' = nat.succ (nat.succ x),
-- h₁ : y' = y
-- ⊢ nat.even x' ↔ nat.even y'
    { have := even_succ_succ x,
-- x x' y y' : ℕ,
-- h₃ : nat.even x ↔ nat.even y,
-- h₀ : x' = nat.succ (nat.succ x),
-- h₁ : y' = y,
-- this : nat.even (nat.succ (nat.succ x)) ↔ nat.even x
-- ⊢ nat.even x' ↔ nat.even y'
      guard_hyp h₀ := x' = nat.succ (nat.succ x),
      guard_target (nat.even x' ↔ nat.even y'),
      cc, } },
-- h₀ : ◻(⊙x ≃ succ ! succ ! x),
-- h₁ : ◻(⊙y ≃ y),
-- h₂ : even ! x ≡ even ! y
-- ⊢ even ! x ≡ even ! y
  { assumption },
end

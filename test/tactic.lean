
import temporal_logic

open temporal predicate

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
example (h : Γ ⊢ ◇(◻(f ;; v₀ ≡ q) ⋀ p))
: Γ ⊢ ◇(◻(f ;; v₁ ≡ q) ⋀ p) :=
begin [temporal]
  rw ← h₂,
end

example (h : Γ ⊢ ◇(◻(f ;; v₀ ≡ q) ⋀ p))
: Γ ⊢ ◇(◻(f ;; v₁ ≡ q) ⋀ p) :=
begin [temporal]
  rw h₂ at h,
end

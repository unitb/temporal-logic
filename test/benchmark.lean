
import temporal_logic

set_option profiler true
open temporal predicate

variables Γ : cpred
variables P Q R S : ℕ → cpred
include P Q R S

example : Γ ⊢ True :=
begin [temporal]
  iterate 100
  { have : ∀∀ x, P x ⟶ Q x ⟶ R x ⟶ S x,
    { intros,
      guard_target S x,
      admit },
    clear this },
  trivial
end

lemma leads_to_trans {p q r : cpred} {Γ}
  (Hpq : Γ ⊢ p ~> q)
  (Hqr : Γ ⊢ q ~> r)
: Γ ⊢ True :=
begin [temporal]
  iterate 10
  { have : p ~> r,
    { henceforth,
      intros hp,
      have := Hpq hp, revert this,
      rw ← eventually_eventually r,
      clear hp,
      monotonicity,
      apply Hqr },
    clear this },
  trivial
end

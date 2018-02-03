
import .lemmas

import data.set.basic

import util.data.minimum
import util.function
import util.logic

open temporal function predicate

local infix ` ≃ `:75 := v_eq
local attribute [instance] classical.prop_decidable
universe u

namespace temporal
namespace scheduling
section scheduling

parameter {evt : Type u}
parameter Γ : cpred
parameter r : tvar (set evt)
parameter Hr : Γ ⊢ ◻-(r ≃ (∅ : set evt))
parameter [nonempty evt]

abbreviation SCHED  (s : tvar evt) :=
◻(s ∊ r) ⋀
∀∀ (e : evt),
  ◻◇(↑e ∊ r) ⟶
  ◻◇(s ≃ ↑e ⋀ ↑e ∊ r)

section implementation

parameters {f : evt → ℕ} (Hinj : injective f)
parameter q : tvar (evt → ℕ)
parameter cur : tvar ℕ

infixr ` |+| `:80 := lifted₂ has_add.add

parameter cur_Spec : Γ ⊢ cur ≃ ↑0 ⋀ ◻(⊙cur ≃ cur |+| ↑1)

def next : tvar $ (evt → ℕ) → (evt → ℕ) :=
[| r cur, λ q : evt → ℕ, q |]

abbreviation Spec :=
q ≃ ↑f ⋀ ◻(⊙q ≃ next q)

parameter Hq : Γ ⊢ Spec

noncomputable def select : tvar evt :=
[| q r , inv q (↓ i, inv q i ∈ r)  |]

include Hq Hinj

def q_injective
: Γ ⊢ ◻(⟨injective⟩ ! q) :=
begin [temporal]
  cases Hq with Hq Hq',
  t_induction!,
  explicit' { cc },
  { henceforth at Hq',
    explicit' { admit } },
end

open set
include Hr
def sched_inv
: Γ ⊢ ◻(select ∊ r) :=
begin [temporal]
  have Hq := temporal.scheduling.q_injective,
  persistent, henceforth at *,
  explicit' [select]
  { apply @minimum_mem _ _ { i | inv q i ∈ r },
    simp [not_eq_empty_iff_exists],
    apply exists_imp_exists_simpl q,
    have := inv_is_left_inverse_of_injective Hq, simp [left_inverse] at this,
    conv in (inv q (q _))
    { rw [inv_is_left_inverse_of_injective Hq], },
    rw [← ne_empty_iff_exists_mem], exact Hr },
end

def sched_fairness (e : evt)
: Γ ⊢ ◻◇(↑e ∊ r) ⟶ ◻◇(select ≃ ↑e ⋀ ↑e ∊ r) :=
begin [temporal]
  cases Hq with _ Hq, persistent,
  apply inf_often_induction' (q ↑ e) ; intro q₀,
  { admit },
  { henceforth at ⊢ Hq,
    simp, intros hreq hq₀,
    apply next_entails_eventually,
    -- simp [select,next],
    explicit' [select,next]
    { by_cases h : e ∈ r' ; admit } },
end

def correct_sched
: Γ ⊢ SCHED select :=
begin [temporal]
  split,
  { apply temporal.scheduling.sched_inv, },
  { intro, apply temporal.scheduling.sched_fairness },
end

end implementation

class schedulable (α : Sort u) :=
  (f : α → ℕ)
  (inj : injective f)

lemma scheduler [schedulable evt]
  (hr : Γ ⊢ ◻-(r ≃ (∅ : set evt)))
: Γ ⊢ (∃∃ s, SCHED s) :=
begin [temporal]
  have := witness ↑(0 : ℕ) ( ↑(has_add.add 1) : tvar (ℕ → ℕ)) Γ,
  cases this with cur Hcur,
  have := witness ↑(schedulable.f : (evt → ℕ)) (next r cur) Γ,
  cases this with q Hq,
  existsi select r q,
  apply correct_sched _ _ hr (schedulable.inj evt),
  exact Hq,
end

end scheduling
end scheduling
export scheduling (schedulable)
end temporal

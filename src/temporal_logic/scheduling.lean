
import .lemmas

import data.set.basic

import util.data.minimum
import util.function
import util.logic
import tactic.norm_num

open temporal function predicate nat

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

infixl ` |+| `:80 := lifted₂ has_add.add
infixl ` |-| `:80 := lifted₂ has_sub.sub

-- TODO: instead of +1, go with cur+1 `max` ↓ i, inv q i
-- parameter cur_Spec : Γ ⊢ cur ≃ ↑0 ⋀ ◻(⊙cur ≃ cur |+| ↑1)

noncomputable def next' (r' : set evt) (x : ℕ × (evt → ℕ)) : ℕ × (evt → ℕ) :=
let (cur,q) := x,
    min := ↓ i : ℕ, inv q i ∈ r',
    cur' := max min $ cur+1 in
(cur',
  λ e,
  if min = q e then cur'
  else if q e < min  then q e
  else if q e < cur' then q e - 1
                     else q e)

noncomputable def next : tvar $ ℕ × (evt → ℕ) → ℕ × (evt → ℕ) :=
⟪ ℕ, next' ⟫ (⊙r)

section
parameter f
noncomputable def cur₀ : tvar ℕ :=
[| r , ↓ i : ℕ, inv f i ∈ r |]
end

noncomputable def Spec :=
⦃cur,q⦄ ≃ ⦃cur₀,f⦄ ⋀ ◻(⊙⦃cur,q⦄ ≃ next ⦃cur,q⦄)

parameter Hq : Γ ⊢ Spec

noncomputable def select : tvar evt :=
-- [| q r , inv q (↓ i, inv q i ∈ r)  |]
[| q cur, inv q cur  |]

include Hq Hinj

lemma q_injective
: Γ ⊢ ◻(⟨injective⟩ ! q) :=
begin [temporal]
  cases Hq with Hq Hq',
  t_induction!,
  explicit' [cur₀] { cc } ,
  { henceforth at Hq',
    explicit' [next] { admit } },
end

open set

include Hr
def sched_inv
: Γ ⊢ ◻(select ∊ r) :=
sorry
-- begin [temporal]
--   have Hq := temporal.scheduling.q_injective,
--   -- t_induction!,
--   henceforth! at *,
--   explicit' [select]
--   { apply @minimum_mem _ _ { i | inv q i ∈ r },
--     simp [not_eq_empty_iff_exists],
--     apply exists_imp_exists_simpl q,
--     have := inv_is_left_inverse_of_injective Hq, simp [left_inverse] at this,
--     conv in (inv q (q _))
--     { rw [inv_is_left_inverse_of_injective Hq], },
--     rw [← ne_empty_iff_exists_mem], exact Hr },
-- end

lemma sched_queue_liveness (q₀ : ℕ) (e : evt)
: Γ ⊢ ⊙(↑e ∊ r) ⋀ q ↑e |+| (q ↑e |-| cur) ≃ ↑q₀ ~>
  q ↑e |+| (q ↑e |-| cur) ≺≺ ↑q₀ ⋁ select ≃ ↑e ⋀ ↑e ∊ r :=
begin [temporal]
  { have Hq_inj := temporal.scheduling.q_injective,
    cases Hq with Hq₀ Hq,
    henceforth! at ⊢ Hq Hq_inj,
    have Hq_inj' : ⊙(⟨injective⟩ ! q) := holds_next _ _ Hq_inj,
    simp, intros hreq hq₀,
    apply next_entails_eventually,
    explicit' [select,next,next']
    { cases Hq with Hq Hq',
      replace Hq' := congr_fun Hq' e, simp at Hq',
      have Hcur : cur < cur',
      { subst cur', apply lt_of_lt_of_le,
        apply @lt_add_of_pos_right _ _ cur 1,
        norm_num, apply le_max_right, },
      simp [Hq'],
      repeat { ite_cases },
      { left, subst q₀,
        change _ + _ < _ + _,
        have : q e ≥ cur',
        { simp [Hq], apply le_of_not_gt h_2 },
        monotonicity Hcur, },
      { left, subst q₀,
        change _ + _ < _ + _,
        have : q e - 1 - cur' ≤ q e - cur,
        { transitivity 0,
          { apply le_of_eq,
            apply sub_eq_zero_of_le,
            transitivity q e, apply nat.sub_le,
            apply le_of_lt, simp [Hq,h_2], },
          apply nat.zero_le, },
        apply add_lt_add_of_lt_of_le _ this,
        apply nat.sub_lt_of_pos_le, norm_num,
        apply nat.succ_le_of_lt,
        apply @lt_of_le_of_lt _ _ _ (↓ (i : ℕ), inv q i ∈ r'),
        apply nat.zero_le,
        apply lt_of_le_of_ne _ h,
        apply le_of_not_gt h_1, },
      { exfalso,
        apply not_lt_of_le _ h_1,
        apply minimum_le,
        simp [has_mem.mem,set.mem],
        rw [inv_is_left_inverse_of_injective Hq_inj],
        exact hreq },
      { right, split,
        { apply inv_eq _ _ Hq_inj',
          simp [Hq',h,Hq] },
        assumption } } },
end

lemma sched_fairness (e : evt)
: Γ ⊢ ◻◇(↑e ∊ r) ⟶ ◻◇(select ≃ ↑e ⋀ ↑e ∊ r) :=
begin [temporal]
  suffices : ◻◇⊙(↑e ∊ r) ⟶ ◻◇(temporal.scheduling.select ≃ ↑e ⋀ ↑e ∊ r),
  { intro h, apply this,
    rw [← next_eventually_comm], apply henceforth_next _ _ h, },
  apply inf_often_induction' (q ↑ e |+| (q ↑ e |-| cur)) ; intro q₀,
  { admit },
  { apply temporal.scheduling.sched_queue_liveness }
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
  let f : tvar (evt → ℕ) := @schedulable.f evt _,
  let σ₀ := ⦃cur₀ r schedulable.f,f⦄,
  have := witness σ₀ (next r) Γ,
  cases this with cur Hcur,
  cases cur with cur q,
  existsi select q cur,
  apply correct_sched _ _ hr (schedulable.inj evt),
  simp [Spec,σ₀] at ⊢ Hcur,
  exact Hcur,
end

end scheduling
end scheduling
export scheduling (schedulable)
end temporal

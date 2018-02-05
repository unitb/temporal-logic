
import .lemmas

import data.set.basic

import util.data.minimum
import util.function
import util.logic
import tactic.norm_num

open temporal function predicate nat

local infix ` ≃ `:75 := v_eq
universe u

namespace temporal
namespace scheduling
section scheduling

local attribute [instance, priority 0] classical.prop_decidable

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
let q' : evt → ℕ := λ e : evt,
          match cmp min (q e) with
            | ordering.gt := q e
            | ordering.eq := cur'
            | ordering.lt :=
              if q e ≤ cur'
                     then q e - 1
                     else q e
          end
in
(cur', q')

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

/- TODO: split into lemmas -/
lemma q_injective
: Γ ⊢ ◻(⟨injective⟩ ! q) :=
begin [temporal]
  cases Hq with Hq Hq',
  t_induction!,
  explicit' [cur₀] { cc } ,
  { henceforth at Hq',
    explicit' [next,next']
    { cases Hq',
      replace Hq'_right := congr_fun Hq'_right,
      simp at Hq'_right,
      -- subst q',
      simp_intros i j,
      -- rename q qq, -- exfalso, clear_except cur ,
      intro,
      wlog i j : q i ≤ q j with Hij,
      have Hi := Hq'_right i,
      have Hj := Hq'_right j, clear Hq'_right,
      have h' : ∀ {x y : ℕ}, x < y → 0 < y,
      { introv hh₁,
        apply lt_of_le_of_lt (nat.zero_le _) hh₁, },
      ordering_cases (cmp (↓ (i : ℕ), inv q i ∈ r') (q i)) with h₁
      ; simp [next'._match_1] at Hi,
      { have H' : (↓ (i : ℕ), inv q i ∈ r') < q j := lt_of_lt_of_le h₁ Hij,
        have H'' : cmp (↓ (i : ℕ), inv q i ∈ r') (q j) = ordering.lt,
        { simp [cmp,cmp_using_eq_lt,H'] },
        rw [H'',next'._match_1] at Hj,
        ite_cases at Hi, rw [if_neg] at Hj,
        { apply ih, cc, },
        { apply not_le_of_gt,
          apply lt_of_lt_of_le _ Hij,
          apply lt_of_not_ge h, },
        ite_cases at Hj,
        { exfalso,
          clear H'' Hq'_left,
          rw [← Hj,← a,Hi] at h_1,
          apply h_1, clear h_1,
          transitivity q i, apply pred_le,
          assumption },
        { apply ih, rw [Hi,Hj,nat.sub_eq_iff_eq_add,nat.sub_add_cancel] at a,
          exact a, repeat { apply h', assumption }, }, },
      { apply ih,
        ordering_cases (cmp (↓ (i : ℕ), inv q i ∈ r') (q j)) with hh₁
        ; simp [next'._match_1] at Hj,
        ite_cases at Hj,
        { simp [Hj,a] at *, clear Hj a,
          exfalso, revert h, apply not_lt_of_ge _,
          apply le_of_eq Hi, },
        { rw ← a at Hj, rw [← Hi,Hj] at h,
          have h' : q j - 1 < q j,
          { apply nat.sub_lt (h' hh₁) zero_lt_one, },
          cases not_le_of_gt h' h, },
        { cc },
        { rw h₁ at hh₁,
          cases not_lt_of_ge Hij hh₁, } },
      { apply ih,
        ordering_cases (cmp (↓ (i : ℕ), inv q i ∈ r') (q j)) with hh₁
        ; simp [next'._match_1] at Hj,
        ite_cases at Hj,
        { cc },
        { exfalso,
          clear h Hq'_left,
          rw [← a,Hi] at Hj,
          rw [Hj] at h₁, revert h₁,
          apply not_lt_of_ge, apply (add_le_to_le_sub _ _).mp,
          apply hh₁, apply h' hh₁, },
        { clear h',
          rw [← Hi,a,Hj] at h₁,
          exfalso, revert h₁, apply not_lt_of_ge,
          apply le_max_left, },
        { cc }, } } },
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

/- TODO: split into lemmas -/
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
      ordering_cases (cmp (↓ (i : ℕ), inv q i ∈ r') (q e)) with h₁
      ; simp [next'._match_1] at Hq' ⊢,
      ite_cases at ⊢ Hq',
      { left, subst q₀,
        change _ + _ < _ + _,
        have : q e ≥ cur',
        { simp [Hq], apply le_of_not_ge h,  },
        monotonicity Hcur, },
      { left, subst q₀,
        change _ + _ < _ + _,
        have : q e - 1 - cur' ≤ q e - cur,
        { transitivity 0,
          { apply le_of_eq,
            apply sub_eq_zero_of_le,
            transitivity q e, apply nat.sub_le,
            simp [Hq,h], },
          apply nat.zero_le, },
        apply add_lt_add_of_lt_of_le _ this,
        apply nat.sub_lt_of_pos_le, norm_num,
        apply nat.succ_le_of_lt,
        apply lt_of_le_of_lt _ h₁,
        apply nat.zero_le, },
      { right, split,
        { apply inv_eq _ _ Hq_inj',
          simp [Hq',Hq], },
        assumption },
      { exfalso,
        apply not_lt_of_le _ h₁,
        apply minimum_le,
        simp [has_mem.mem,set.mem],
        rw [inv_is_left_inverse_of_injective Hq_inj],
        exact hreq }, }, }
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

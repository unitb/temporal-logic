
import data.stream

import util.meta.tactic
import util.logic
import util.classical
import util.predicate
import util.meta.tactic.propositional

import tactic

import temporal_logic.tactic

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal
open predicate stream

attribute [predicate] stream.drop pred'.mk
attribute [tl_simp, simp] pred'.mk

lemma henceforth_next (p : cpred)
: ◻p ⟹ ◻⊙p :=
begin [temporal]
  rw henceforth_next_intro p,
  mono, simp,
end

lemma next_henceforth (p : cpred)
: ◻p ⟹ ⊙◻p :=
begin [temporal]
  suffices : ◻◻p ⟶ ⊙◻p,
  { simp at this, apply this },
  intro h, apply h,
end

lemma next_eventually_comm (p : cpred)
: ⊙◇p = ◇⊙p :=
by lifted_pred [next,eventually,nat.succ_add]

lemma holds_next (Γ p : cpred) [persistent Γ]
  (h : Γ ⊢ p)
: Γ ⊢ ⊙p :=
begin [temporal]
  apply persistent_to_henceforth h,
end

/- distributivity -/

lemma eventually_and_entails {p q : cpred}
: ◇(p ⋀ q) ⟹ ◇p ⋀ ◇q :=
begin
  apply entails_p_and_of_entails ; mono ; propositional,
end

lemma entails_henceforth_or {p q : cpred}
: ◻p ⋁ ◻q ⟹ ◻(p ⋁ q) :=
begin [temporal]
  intros h, cases h with h h
  ; henceforth at ⊢ h
  ; [ left , right ]
  ; exact h
end

/- end distributivity -/

lemma eventually_of_leads_to {p q : cpred} {Γ}
  (h : Γ ⊢ p ~> q)
: Γ ⊢ ◇p ⟶ ◇q :=
begin [temporal]
  rw ← eventually_eventually q,
  apply eventually_imp_eventually h,
end

lemma inf_often_of_leads_to {p q : cpred} {Γ}
  (h : Γ ⊢ p ~> q)
: Γ ⊢ ◻◇p ⟶ ◻◇q :=
begin [temporal]
  rw ← eventually_eventually q,
    -- β : Type u₁
    -- p q : cpred
    -- h : p ~> q
    -- ⊢ ◻◇p ⟶ ◻◇◇q
  mono*,
    -- β : Type u₁
    -- p q : cpred
    -- h : p ~> q
    -- ⊢ p ⟶ ◇q
  apply h,
end

lemma leads_to_trans {p q r : cpred} {Γ}
  (Hpq : Γ ⊢ p ~> q)
  (Hqr : Γ ⊢ q ~> r)
: Γ ⊢ p ~> r :=
begin [temporal]
  henceforth,
  intros hp,
  have := Hpq hp, revert this,
  rw ← eventually_eventually r,
  clear hp,
  mono,
  apply Hqr,
end

@[tl_simp, simp]
lemma next_or (p q : cpred)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

@[tl_simp, simp]
lemma next_imp (p q : cpred)
: ⊙(p ⟶ q) = ⊙p ⟶ ⊙q :=
rfl

@[tl_simp, simp]
lemma next_proj (f : var α β) (v : tvar α)
: ⊙(f ! v) = f ! ⊙v :=
by lifted_pred [next]

@[tl_simp, simp]
lemma next_v_eq (p q : tvar α)
: ⊙(p ≃ q) = ⊙p ≃ ⊙q :=
by lifted_pred

open nat

@[tl_simp, simp]
lemma const_action (c : Prop) (v : tvar α)
: ⟦ v | λ _ _ : α, c ⟧ = (c : cpred) :=
by { refl }

-- @[predicate]
lemma action_on  (A : act α) (v : tvar γ) (f : γ → α)
: ⟦ v | A on f ⟧ = ⟦ ⟨f⟩ ! v | A ⟧ :=
by { lifted_pred }

lemma action_on'  (A : act α) (v : tvar γ) (f : γ → α)
: ⟦ v | λ s s', (A on f) s s' ⟧ = ⟦ ⟨f⟩ ! v | A ⟧ :=
by { lifted_pred }

@[predicate]
lemma exists_action  (A : γ → act α) (v : tvar α)
: (∃∃ i, ⟦ v | A i ⟧) = ⟦ v | λ s s', (∃ i, A i s s') ⟧ :=
by { lifted_pred }

instance or_persistent {p q : cpred}
  [persistent p]
  [persistent q]
: persistent (p ⋁ q) :=
begin
  constructor,
  apply mutual_entails,
  apply henceforth_str,
  begin [temporal]
    intro h,
    cases h with h h,
    { rw ← is_persistent p at h,
      revert h,
      mono,
      propositional, },
    { henceforth, right, exact h }
  end
end

instance imp_persistent {p q : cpred}
  [postponable p]
  [persistent q]
: persistent (p ⟶ q) :=
by { simp [p_imp_iff_p_not_p_or], apply_instance }

instance stable_persistent {p : cpred}
: persistent (◇ ◻ p) :=
begin
  constructor,
  apply mutual_entails,
  apply henceforth_str,
  begin [temporal]
    apply induct,
    henceforth,
    rw next_eventually_comm,
    mono,
    apply next_henceforth
  end
end

instance and_postponable {p q : cpred}
  [postponable p]
  [postponable q]
: postponable (p ⋀ q) :=
by { constructor, rw ← p_not_eq_p_not_iff_eq,
     simp only [p_not_p_and,is_persistent] with tl_simp, }

instance inf_often_postponable {p : cpred}
: postponable (◻ ◇ p) :=
begin
  constructor,
  rw ← p_not_eq_p_not_iff_eq,
  simp only [is_persistent] with tl_simp,
end

lemma induct_evt (p q : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ -q ⟶ ⊙(p ⋁ q)))
: Γ ⊢ (p ⟶ ◇q ⋁ ◻p) :=
begin [temporal]
  apply induct_evt' _ _ h,
end

theorem em (p : cpred) : ⊩ ◇◻p ⋁ ◻◇(- p) :=
begin [temporal]
  rw [← not_henceforth,← not_eventually,p_or_p_not_self]
end

lemma inf_often_of_stable (p : cpred) : (◇◻p) ⟹ (◻◇p) :=
begin [temporal]
  explicit τ
  { simp_intros h i [henceforth],
    cases h with j h,
    unfold eventually,
    existsi j,
    specialize h i,
    simp [drop_drop] at ⊢ h,
    apply h },
end

lemma weak_coincidence {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◻p)
    (Hq : Γ ⊢ ◇q)
: Γ ⊢ ◇(p ⋀ q) :=
begin [temporal]
  explicit τ
  { cases Hq with j Hq,
    specialize Hp j,
    simp [eventually],
    existsi (j),
    exact ⟨Hp,Hq⟩, }
end

lemma eventually_and_eventually (p q : cpred)
: ◇p ⋀ ◇q = ◇(p ⋀ ◇q) ⋁ ◇(◇p ⋀ q) :=
begin
  apply mutual_entails,
  begin [temporal]
    rw [← p_not_p_imp,not_eventually,p_not_p_and,not_eventually],
    intros H₀ H₁,
    cases H₀ with ha hb,
    have h := weak_coincidence H₁ ha,
    rw [p_and_comm,p_or_comm,p_and_p_or_p_not_self] at h,
    explicit τ
    { cases h with j h, cases hb with i ha,
      simp [eventually], existsi i,
      split ; [skip,exact ha],
      cases le_total i j with h' h',
      { existsi (j-i),
        simp [drop_drop,add_sub_of_le h'],
        apply h.left, },
      { exfalso, apply h.right (i-j),
        simp [drop_drop,add_sub_of_le h'],
        apply ha, } },
  end,
  { apply p_or_entails_of_entails
    ; apply entails_p_and_of_entails,
    all_goals {
      transitivity,
      apply eventually_and_entails,
      rw eventually_eventually,
      propositional, }, },
end

lemma event_ordering {Γ p q : cpred}
  (hp : Γ ⊢ ◇p)
  (hq : Γ ⊢ ◇q)
: Γ ⊢ ◇(p ⋀ ◇q) ⋁ ◇(◇p ⋀ q) :=
begin [temporal]
  rw [← eventually_and_eventually],
  split; assumption,
end

section
open tactic tactic.interactive (unfold_coes unfold itactic assert_or_rule)
open interactive interactive.types lean lean.parser
open applicative (mmap₂)
local postfix `?`:9001 := optional

private meta def event : lean.parser (name ⊕ pexpr) :=
(sum.inl <$> ident) <|> (sum.inr <$> brackets "(" ")" texpr)

private meta def event_to_event : name ⊕ pexpr → tactic expr
 | (sum.inl n) := resolve_name n >>= to_expr
 | (sum.inr e) := to_expr e

meta def interactive.event_ordering (aggr : parse $ optional $ tk "!") (e₀ e₁ : parse event)
  (ids : parse with_ident_list) : temporal unit :=
do e₀ ← event_to_event e₀, e₁ ← event_to_event e₁,
   h ← to_expr ``(event_ordering %%e₀ %%e₁) >>= note `h none,
   when e₀.is_local_constant $ tactic.clear e₀,
   when e₁.is_local_constant $ tactic.clear e₁,
   if aggr.is_some then do
     n₀ ← mk_fresh_name,
     n₁ ← mk_fresh_name,
     temporal.interactive.cases (none,to_pexpr h) [n₀,n₁],
     temporal.interactive.eventually n₁ none <|> fail "here",
     e₀ ← get_local n₁, temporal.interactive.cases (none,to_pexpr e₀) ids,
     cleanup,
     tactic.swap,
     temporal.interactive.eventually n₀ none <|> fail "there",
     e₀ ← get_local n₀, temporal.interactive.cases (none,to_pexpr e₀) ids,
     tactic.swap
   else temporal.interactive.cases (none,to_pexpr h) ids,
   return ()

end

lemma stable_and_of_stable_of_stable {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◇◻p)
    (Hq : Γ ⊢ ◇◻q)
: Γ ⊢ ◇◻(p ⋀ q) :=
begin [temporal]
  event_ordering Hp Hq with h h
  ; eventually h
  ; cases h with h₀ h₁
  ; [eventually h₁ ⊢,eventually h₀ ⊢]
  ; henceforth at *
  ; tauto
end

lemma henceforth_delay {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◇p)
    (Hq : Γ ⊢ ◻q)
: Γ ⊢ ◇(p ⋀ ◻q) :=
begin [temporal]
  eventually Hp ⊢,
  split ; assumption
end

@[tl_simp, simp]
lemma eventually_inf_often (p : cpred)
: ◇◻◇p = ◻◇p :=
mutual_entails
begin [temporal]
  intros hp,
  have := inf_often_of_stable (◇p) Γ hp, clear hp,
  rw eventually_eventually at this,
end
(eventually_weaken _)

lemma coincidence {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◇◻p)
    (Hq : Γ ⊢ ◻◇q)
: Γ ⊢ ◻◇(p ⋀ q) :=
begin [temporal]
  rw ← eventually_inf_often,
  eventually Hp |- ,
  henceforth at Hq |-,
  eventually Hq |-,
  split ; assumption,
end

lemma coincidence' {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◻p)
    (Hq : Γ ⊢ ◻◇q)
: Γ ⊢ ◻◇(p ⋀ q) :=
begin [temporal]
  apply coincidence _ Hq,
  assumption
end

lemma inf_often_p_or (p q : cpred)
: ◻◇(p ⋁ q) = ◻◇p ⋁ ◻◇q :=
begin
  refine mutual_entails _ _,
  begin [temporal]
    rw p_or_iff_not_imp (◻◇ p),
    intros h₀ h₁,
    rw [not_henceforth,not_eventually] at h₁,
    have := coincidence h₁ h₀, clear h₀ h₁,
    rw p_not_and_self_or at this,
    revert this, mono*,
    apply p_and_elim_right,
  end,
  refine p_or_entails_of_entails _ _
  ; mono* ; propositional,
end

@[monotonic]
lemma next_imp_next {p q : cpred} (h : p ⟹ q)
: ⊙ p ⟹ ⊙ q :=
by { pointwise h with τ, solve_by_elim }

@[monotonic]
lemma next_tl_imp_next {Γ p q : cpred}
  [persistent Γ]
  (h : ctx_impl Γ p q)
: ctx_impl Γ (⊙ p) (⊙ q) :=
by { rw ← is_persistent Γ at *,
     lifted_pred keep [tl_imp],
     replace h := h.apply (succ σ),
     apply h, clear h,
     intro i, rw [succ_add, ← add_succ],
     apply a (succ i), }

lemma eventually_and {Γ p q : cpred}
   (h₀ : Γ ⊢ ◻p)
   (h₁ : Γ ⊢ ◇q)
: Γ ⊢ ◇(p ⋀ q) :=
begin [temporal]
  eventually h₁ ⊢,
  split ; assumption
end

/- Actions -/

local infix ` <$> ` := fun_app_to_var
local infix ` <*> ` := combine_var

open function

lemma exists_of_eventually
  {p : β → Prop}
  {v : tvar β}
  (h : ⊩ ◇(p <$> v))
: ∃ x, p x :=
begin
  cases v with v,
  replace h := ew_str h 0,
  cases h with i h,
  existsi v i, simp [comp] at h,
  apply h,
end

open function

protected theorem leads_to_of_inf_often (Γ p q : cpred)
  (H : Γ ⊢ ◻◇q)
: Γ ⊢ p ~> q :=
begin [temporal]
  henceforth at H ⊢,
  intro, assumption,
end

protected theorem leads_to_strengthen_rhs (q : cpred) {Γ p r : cpred}
  (H : q ⟹ r)
  (P₀ : Γ ⊢ p ~> q)
: Γ ⊢ p ~> r :=
begin [temporal]
  apply leads_to_trans P₀,
  henceforth,
  intros H',
  apply H Γ H',
end

protected lemma leads_to_cancellation {Γ p q b r : cpred}
    (P₀ : Γ ⊢ p ~> q ⋁ b)
    (P₁ : Γ ⊢ q ~> r)
    : Γ ⊢ p ~> r ⋁ b :=
begin [temporal]
  henceforth,
  intros h,
  have := P₀ h, clear h,
  eventually this,
  rw [eventually_or],
  cases this with h h,
  { left, apply P₁ h },
  { right, assumption },
end

protected lemma leads_to_disj_rng {t : Sort u}
  {p : t → cpred} {Γ q} {r : t → Prop}
  (h : Γ ⊢ ∀∀ i, ↑(r i) ⟶ (p i ~> q))
: Γ ⊢ (∃∃ i, ↑(r i) ⋀ p i) ~> q :=
begin [temporal]
  rw [p_exists_range_subtype,tl_leads_to,p_exists_imp_eq_p_forall_imp],
  rw [henceforth_forall],
  intro i, cases i with i hi,
  apply h i hi,
end

protected theorem leads_to_disj {t}
  {p : t → cpred}
  {q Γ : cpred}
  (P₀ : Γ ⊢ ∀∀ i, p i ~> q)
: Γ ⊢ (∃∃ i, p i) ~> q :=
begin [temporal]
  have P₁ : ∀∀ i : t, ↑true ⟶ (◻(p i ⟶ ◇q)),
  { intros i, intro, apply P₀ i, },
  have P₂ := @temporal.leads_to_disj_rng _ _ _ _ (λ _, true) P₁,
  rw_using : (∃∃ (i : t), ↑((λ _, true) i) ⋀ p i) = (∃∃ i, p i) at P₂,
  { apply p_exists_congr,
    intro,
    apply True_p_and },
end

protected theorem leads_to_disj_gen {t}
  {p q : t → cpred}
  {Γ : cpred}
  (P₀ : Γ ⊢ ∀∀ i, p i ~> q i)
: Γ ⊢ (∃∃ i, p i) ~> (∃∃ i, q i) :=
begin [temporal]
  apply temporal.leads_to_disj _,
  intro j,
  apply temporal.leads_to_strengthen_rhs _ _ (P₀ j),
  apply p_exists_intro
end

section induction

variables {α' : Type u}
variables  {Γ : cpred}
variables  (f : tvar β) (p q : cpred)
variables [has_well_founded β]

protected lemma induction
  (P : Γ ⊢ ∀∀ v : β, p ⋀ (f ≃ v)  ~>  p ⋀ (f ≺≺ v) ⋁ q)
: Γ ⊢ p ~> q :=
begin [temporal]
  have h₂ : ∀∀ V : β, p ⋀ (f ≃ V) ~> q,
  { intro V,
    wf_induction V,
    apply temporal.leads_to_strengthen_rhs (q ⋁ q),
    { simp [or_self], },
    apply temporal.leads_to_cancellation (P _),
    rw_using : (p ⋀ (f ≺≺ x)) = (∃∃v, ↑(v << x) ⋀ (p ⋀ (f ≃ v))),
    { ext1 τ, simp only with predicate, rw exists_one_point (f.apply τ), simp [and_comm],
      intro k, simp, intros, subst k },
    apply @temporal.leads_to_disj_rng _ ,
    apply ih_1, },
  have h₃ := temporal.leads_to_disj h₂,
  rw_using : (∃∃ (i : β), p ⋀ (f ≃ i)) = p at h₃,
  { ext1 j, simp [function.comp,exists_one_point_right ], },
end

end induction

section inf_often_induction'

parameters {α' : Type u}  {β' : Type u₀}
parameters {Γ : cpred} (V : tvar β') (p q : cpred)
parameters [has_well_founded β']

lemma inf_often_induction'
  (S₀ : Γ ⊢ ∀∀ v : β', ◻( V ≃ v ⟶ ◻(V ≃ v) ⋁ ◇(V ≺≺ v ⋁ q)))
  (P₁ : Γ ⊢ ∀∀ v : β', (p ⋀ V ≃ v) ~> (V ≺≺ v ⋁ q))
: Γ ⊢ ◻◇p ⟶ ◻◇q :=
begin [temporal]
  intros Hp,
  unfold henceforth,
  have Hex : ∀∀ (v : β'), V ≃ v ~> q,
  { intro v,
    wf_induction v with v,
    have IH' := temporal.leads_to_disj_rng ih_1, clear ih_1,
    rw_using : (∃∃ (i : β'), ↑(i << v) ⋀ V ≃ i)
             = V ≺≺ v at IH',
    { ext τ,
      simp [flip,function.comp,p_exists], },
    have S₁ : ∀∀ v : β', V ≃ v ~> V ≺≺ v ⋁ q,
    { intro, henceforth!, intros Hv,
      replace S₀ := S₀ _ Hv,
      cases S₀ with S₀ S₀,
      { have H := coincidence' S₀ Hp,
        rw p_and_comm at H,
        henceforth at H, eventually H,
        apply P₁ _ H },
      { apply S₀, } },
    have H₃ := temporal.leads_to_cancellation (S₁ v) IH',
    exact cast (by simp) H₃ },
  replace Hex := temporal.leads_to_disj Hex,
  rw_using : (∃∃ (v : β'), (V ≃ v)) = True at Hex,
  { lifted_pred, existsi σ ⊨ V, refl },
  henceforth, apply Hex, simp,
end

end inf_often_induction'

section prophecy

variable {Γ : cpred}
-- variable [temporal.persistent Γ]
-- variables I N : cpred
variables PI J : tvar (α → Prop)
variables PN : tvar (act α)
variables PSync : cpred
variables h_PSync : Γ ⊢ ◻◇PSync
variables Init : cpred
-- variables h_Init : Γ ⊢ Init
variable h_PI : Γ ⊢ ∀∀ p : α, J p ⟶ PI p
variable h_PN : Γ ⊢ ◻(∀∀ p' : α, J p' ⟶ ∃∃ p : α, PN p p' ⋀ J p)
-- variable h_PSync' : Γ ⊢ PSync ⟶ ∃∃ p : α, J p ⋀ ∀∀ p', J p' ⟶ PN p p'
variable h_PSync' : Γ ⊢ ◻(PSync ⟶ ∃∃ p : α, PI p ⋀ J p)

-- variables (i j : ℕ)

-- def w : ℕ → α

include h_PI h_PN h_PSync h_PSync'
open nat
-- set_option profiler true
-- #check predicate.p_exists_imp_p_exists'
lemma prophecyI
: Γ ⊢ ∃∃ w : tvar α, PI w ⋀ ◻PN w (⊙w) ⋀ ◻J w :=
begin [temporal]
  have : ∃∃ x : α, (True : cpred),
  { henceforth at h_PSync,
    eventually h_PSync,
    have : ∃∃ x : α, PI x ⋀ J x := h_PSync' h_PSync,
    apply predicate.p_exists_entails_p_exists _ _ _ _ this,
    intro, simp },
  nonempty α,
  let x₀ : tvar α := ⟨ λ i, ε x, i ⊨ PI x ∧ i ⊨ J x ⟩,
  let f : tvar (α → α) := ⟨ λ i x', ε x, i ⊨ PN x x' ∧ succ i ⊨ J x' ⟩ ,
  have := back_witness x₀ f h_PSync,
  revert this,
  apply p_exists_p_imp_p_exists,
  intros w h,
  suffices : ◻J w,
  { split, split,
    henceforth at this,
    explicit' with this h_PI
    { solve_by_elim },
    admit, exact this },
  { suffices : ◻(J w ⋁ PSync ⋀ w ≃ x₀),
    { revert this, mono!, intro h',
      cases h' with h₀ h₁, exact h₁,
      henceforth at h_PSync',
      explicit' with h₀ h_PSync'
      { cases h₀,
        suffices : PI w ∧ J w, exact this.right,
        subst w, apply_epsilon_spec, } },
    apply henceforth_until,
    have : ◻◇((PSync ⋀ w ≃ x₀)), admit,
    revert this, mono!,
    apply until_backward_induction _ _,
    -- have : _ ⟶ (-PSync ⋀ J w)  𝒰  (PI w ⋀ J w) := until_backward_induction _ _,
    -- suffices : ◻(J w  𝒰  (PSync ⋀ w ≃ x₀)),
}
end

#check @until_backward_induction

end prophecy


attribute [irreducible] next
section
variables Γ : cpred
variables p q : tvar α
variables p' q' : tvar β
variable f : α → β
variables f₀ f₁ : tvar (α → β)

@[lifted_congr]
lemma lifted_coe_to_fun_arg
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ f₀ p ≃ f₀ q :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_coe_to_fun_fun
  (h : Γ ⊢ f₀ ≃ f₁)
: Γ ⊢ f₀ p ≃ f₁ p :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_congr₁
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ lifted₁ f p ≃ lifted₁ f q :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_congr₂ (g : α → β → γ)
  (h : Γ ⊢ p ≃ q)
  (h' : Γ ⊢ p' ≃ q')
: Γ ⊢ lifted₂ g p p' ≃ lifted₂ g q q' :=
by { lifted_pred using h h', simp [h,h'] }

@[lifted_congr]
lemma lifted_proj (v : var α β)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ v ! p ≃ v ! q :=
by { lifted_pred using h, simp [h] }

variable [persistent Γ]

@[timeless_congr]
lemma lifted_next (p q : tvar α)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ ⊙p ≃ ⊙q :=
begin
  lifted_pred keep,
  rw ← is_persistent Γ at a,
  have := h.apply (succ x) (a 1),
  simp at this, exact this,
end

@[timeless_congr]
lemma lifted_henceforth (p q : cpred)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ ◻p ≃ ◻q :=
begin
  apply mutual_p_imp
  ; change ctx_impl _ _ _
  ; mono
  ; apply p_imp_of_equiv,
  apply h, apply v_eq_symm h
end

@[timeless_congr]
lemma lifted_eventually (p q : cpred)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ ◇p ≃ ◇q :=
begin
  apply mutual_p_imp
  ; change ctx_impl _ _ _
  ; mono
  ; apply p_imp_of_equiv,
  apply h, apply v_eq_symm h
end

end

end temporal

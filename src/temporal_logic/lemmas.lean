
import data.stream

import util.meta.tactic
import util.logic
import util.classical
import util.predicate

import temporal_logic.tactic

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal
open predicate stream

attribute [predicate] stream.drop pred'.mk
attribute [simp] pred'.mk

lemma henceforth_next (p : cpred)
: ◻p ⟹ ◻⊙p :=
begin [temporal]
  rw henceforth_next_intro p,
  monotonicity, simp,
end

lemma next_henceforth (p : cpred)
: ◻p ⟹ ⊙◻p :=
begin [temporal]
  suffices : ◻◻p ⟶ ⊙◻p,
  { simp at this, apply this },
  intro h, apply h
end

lemma next_eventually_comm (p : cpred)
: ⊙◇p = ◇⊙p :=
by lifted_pred [next,eventually,nat.succ_add]

/- distributivity -/

lemma eventually_and_entails {p q : cpred}
: ◇(p ⋀ q) ⟹ ◇p ⋀ ◇q :=
begin
  apply entails_p_and_of_entails ; monotonicity ; propositional,
end

lemma entails_henceforth_or {p q : cpred}
: ◻p ⋁ ◻q ⟹ ◻(p ⋁ q) :=
sorry

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
  monotonicity,
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
  monotonicity,
  apply Hqr,
end

@[simp]
lemma next_or (p q : cpred)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

@[simp]
lemma next_imp (p q : cpred)
: ⊙(p ⟶ q) = ⊙p ⟶ ⊙q :=
rfl

@[simp]
lemma next_proj (f : var α β) (v : tvar α)
: ⊙(f ! v) = f ! ⊙v :=
by lifted_pred [next]

@[simp]
lemma next_v_eq (p q : tvar α)
: ⊙(p ≃ q) = ⊙p ≃ ⊙q :=
by lifted_pred

open nat

@[simp]
lemma const_action (c : Prop) (v : tvar α)
: ⟦ v | λ _ _ : α, c ⟧ = (c : cpred) :=
by { refl }

@[simp, predicate]
lemma models_action (A : act α) (v : tvar α) (i : ℕ)
: i ⊨ ⟦ v | A ⟧ ↔ A (i ⊨ v) (succ i ⊨ v) :=
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

@[simp, predicate]
lemma models_next (p : tvar α) (t : ℕ)
: t ⊨ ⊙p = succ t ⊨ p :=
by refl

lemma induct (p Γ : cpred)
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ (p ⟶ ◻p) :=
begin
  constructor,
  intros τ hΓ hp i,
  induction i with i,
  assumption,
  have := h.apply τ hΓ i i_ih,
  simp [next] at this,
  simp [this],
end

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
      monotonicity,
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
    monotonicity,
    apply next_henceforth
  end
end

instance and_postponable {p q : cpred}
  [postponable p]
  [postponable q]
: postponable (p ⋀ q) :=
by { constructor, rw ← p_not_eq_p_not_iff_eq,
     simp [p_not_p_and,is_persistent], }

instance inf_often_postponable {p : cpred}
: postponable (◻ ◇ p) :=
begin
  constructor,
  rw ← p_not_eq_p_not_iff_eq,
  simp [is_persistent],
end

lemma induct' (p : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ ◻ (p ⟶ ◻p) :=
begin [temporal]
  henceforth,
  apply induct _ _ h,
end

lemma induct_evt (p q : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ -q ⟶ ⊙(p ⋁ q)))
: Γ ⊢ ◻ (p ⟶ ◇q ⋁ ◻p) :=
begin
  lifted_pred using h,
  simp [henceforth] at *,
  intros,
  simp [or_iff_not_imp,eventually],
  intros hnq k,
  induction k with k,
  { simp [a] },
  { simp [add_succ],
    specialize h _ k_ih (hnq _),
    rw [or_comm,or_iff_not_imp] at h,
    apply h, rw [← add_succ,← add_succ],
    apply hnq }
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

meta def interactive.event_ordering (e₀ e₁ : parse event)
  (ids : parse with_ident_list) : temporal unit :=
do e₀ ← event_to_event e₀, e₁ ← event_to_event e₁,
   h ← to_expr ``(event_ordering %%e₀ %%e₁) >>= note `h none,
   when e₀.is_local_constant $ tactic.clear e₀,
   when e₁.is_local_constant $ tactic.clear e₁,
   temporal.interactive.cases (none,to_pexpr h) ids,
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
  ; split
  ; assumption,
end

lemma henceforth_delay {p q : cpred} {Γ}
    (Hp : Γ ⊢ ◇p)
    (Hq : Γ ⊢ ◻q)
: Γ ⊢ ◇(p ⋀ ◻q) :=
begin [temporal]
  eventually Hp ⊢,
  split ; assumption
end

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
    revert this, monotonicity,
    apply p_and_elim_right,
  end,
  refine p_or_entails_of_entails _ _
  ; monotonicity ; propositional,
end

@[monotonic]
lemma next_imp_next {p q : cpred} (h : p ⟹ q)
: ⊙ p ⟹ ⊙ q :=
by { pointwise h with τ, auto }

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

def le (x y : β') := x << y ∨ x = y

lemma inf_often_induction'
  (S₀ : Γ ⊢ ∀∀ v : β', ◻◇(V ≃ v) ⟶ ◇◻(V ≃ v) ⋁ ◻◇(V ≺≺ v ⋁ q))
  (P₁ : Γ ⊢ ∀∀ v : β', (p ⋀ V ≃ v) ~> (V ≺≺ v ⋁ q))
: Γ ⊢ ◻◇p ⟶ ◻◇q :=
begin [temporal]
  have Hex : ∀∀ (v : β'), (p ⋀ V ≃ v) ~> (q ⋁ ◻-p),
  { intro v,
    wf_induction v with v,
    have IH' := temporal.leads_to_disj_rng ih_1, clear ih_1,
    rw_using : (∃∃ (i : β'), ↑(i << v) ⋀ (p ⋀ V ≃ i))
             = (V ≺≺ v ⋀ p) at IH',
    { ext τ,
      simp [flip,function.comp],
      split ; simp ; intros, rw a_2, split ; assumption,
      split, repeat { split, assumption }, refl  },
    have S₂ : ∀∀ (v : β'), ◻◇(V ≺≺ v) ⟶ ◇◻(V ≺≺ v) ⋁ ◻◇(V ≺≺ v ⋁ q),
    { admit },
    have S₁ : ∀∀ (v : β'), (V ≃ v)  ~> ◻(V ≃ v) ⋁ ◻◇(V ≺≺ v ⋁ q),
    { admit }, clear S₀,
    have H₁ : (p ⋀ V ≃ v) ~> (V ≺≺ v ⋀ p) ⋁ q, admit,
    have H₃ := temporal.leads_to_cancellation H₁ IH',
    admit },
  have H := @temporal.leads_to_disj _ (λ v : β', (p ⋀ V ≃ v)) (q ⋁ ◻-p) _ Hex,
  dsimp [tl_leads_to] at H,
  rw_using : (∃∃ (v : β'), p ⋀ (V ≃ v)) = p at H,
  { ext τ, simp [function.comp,exists_one_point_right] },
  rw [p_or_comm] at H,
  intros h,
  have H₁ := inf_often_of_leads_to H h,
  rw [inf_often_p_or] at H₁,
  cases H₁ with H₁ H₁,
  { exfalso, revert h,
    simp, apply H₁, },
  { apply H₁ },
end

end inf_often_induction'

section inf_often_induction

parameters {β' : Type*}
parameters {Γ : cpred} (V : tvar β') (p q : cpred)
def V' := ⊙V
def p' := ⊙p
def q' := ⊙q
parameters [has_well_founded β']
parameters (h₀ : Γ ⊢ ◻◇p)
parameters (h₁ : Γ ⊢ ◻(q' ⋁ V' ≺≺ V ⋁ (- p' ⋀ V' ≃ V)))

def EQ (v : β') : cpred := V ≃ v
def LT (v : β') : cpred := V ≺≺ v

def ACT := q' ⋁ V' ≺≺ V ⋁ (- p' ⋀ V' ≃ V)

include h₁
include h₀

lemma P : Γ ⊢ ∀∀ v, (p ⋀ EQ v)  ~>  (p ⋀ LT v ⋁ q) :=
begin [temporal]
  intros v, henceforth,
  simp,
  intros Hp Hv,
  replace h₀ := p_impl_revert (henceforth_next (◇p) Γ) h₀,
  rw next_eventually_comm at h₀,
  have h₀ : ◇(ACT V p q ⋀ ⊙p ⋀ (EQ V v)),
  { suffices : ◇(ACT V p q ⋀ ⊙p ⋀ EQ V v) ⋁ ◻EQ V v,
    { cases this, assumption,
      rw p_and_comm,
      apply coincidence' a,
      apply coincidence' h₁ h₀, },
    revert Hv, strengthen_to ◻ _,
    apply induct_evt _ _ _,
    clear Hp,
    henceforth, admit },
  revert h₀, clear h₀, intro h₀,
  persistent without h₀,
  eventually h₀, clear h₁,
  rw [ACT] at h₀,
  revert h₀, simp,
  introv h₀ h₁ h₂,
  strengthen_to ⊙_,
  explicit τ
  { simp [next,EQ,LT,comp,flip,q',p',V'] at *,
    begin [smt] break_asms, end },
end

lemma inf_often_induction
: Γ ⊢ ◻◇q :=
begin [temporal]
  have P := P V p q h₀ h₁,
  revert h₀,
  apply inf_often_of_leads_to,
  apply temporal.induction V (p) (q) P,
end
end inf_often_induction

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
  ; monotonicity
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
  ; monotonicity
  ; apply p_imp_of_equiv,
  apply h, apply v_eq_symm h
end

end

end temporal

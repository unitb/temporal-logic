
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
  intros, assumption
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
lemma not_henceforth (p : cpred) : (- ◻p) = (◇-p) :=
begin
  funext1,
  simp [henceforth,not_forall_iff_exists_not,eventually],
end

lemma next_or (p q : cpred)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

lemma next_imp (p q : cpred)
: ⊙(p ⟶ q) = ⊙p ⟶ ⊙q :=
rfl

open nat

@[simp]
lemma const_action (c : Prop) (v : tvar α)
: ⟦ v <> λ _ _ : α, c ⟧ = (c : cpred) :=
by { refl }

@[simp, predicate]
lemma models_action (A : act α) (v : tvar α) (i : ℕ)
: i ⊨ ⟦ v <> A ⟧ ↔ A (i ⊨ v) (succ i ⊨ v) :=
by { refl }

@[predicate]
lemma action_on  (A : act α) (v : tvar γ) (f : γ → α)
: ⟦ v <> A on f ⟧ = ⟦ ↑f ;; v <> A ⟧ :=
by { lifted_pred }

@[simp, predicate]
lemma models_next (p : cpred) (t : ℕ)
: t ⊨ ⊙p = succ t ⊨ p :=
by refl

lemma eventually_p_or (p q : cpred)
: ◇(p ⋁ q) = ◇p ⋁ ◇q :=
begin
  funext1,
  simp [eventually,exists_or],
end

lemma induct (p Γ : cpred)
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ (p ⟶ ◻p) :=
begin
  constructor,
  intros τ hΓ hp i,
  induction i with i,
  assumption,
  have := h.apply τ hΓ i ih_1,
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
  [persistent $ - p]
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

instance not_inf_often_persistent {p : cpred}
: persistent (- ◻◇p) :=
by { simp, apply_instance }

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
    specialize h _ ih_1 (hnq _),
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
      split ; [exact ha,skip],
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
lemma next_tl_imp_next {Γ p q : cpred} (h : tl_imp Γ p q)
: tl_imp Γ (⊙ p) (⊙ q) :=
by { lifted_pred keep [tl_imp],
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

lemma eventually_exists (P : α → cpred)
: ◇(∃∃ x, P x) = ∃∃ x, ◇P x :=
begin
  funext1,
  unfold eventually p_exists,
  split
  ; intro H
  ; cases H with i H
  ; cases H with j H
  ; exact ⟨_,_,H⟩ ,
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
  rw [eventually_p_or],
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
    apply temporal.leads_to_strengthen_rhs _ _,
    show q ⋁ q ⟹ q,
    { simp [or_self], },
    apply temporal.leads_to_cancellation (P _),
    rw_using : (p ⋀ (f ≺≺ x)) = (∃∃v, ↑(v << x) ⋀ (p ⋀ (f ≃ v))),
    { funext1 τ, simp only with predicate, rw exists_one_point (f.apply τ), simp,
      intro k, simp, intros, subst k },
    apply @temporal.leads_to_disj_rng _ ,
    apply ih_1, },
  have h₃ := temporal.leads_to_disj h₂,
  rw_using : (∃∃ (i : β), p ⋀ (f ≃ i)) = p at h₃,
  { funext1 j, simp [function.comp,exists_one_point_right ], },
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
    { funext τ,
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
  { funext τ, simp [function.comp,exists_one_point_right] },
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
variables r : tvar β
variable f : α → β

@[lifted_congr]
lemma lifted_congr₁
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ lifted₁ f p ≃ lifted₁ f q :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_congr₂_a (g : α → β → γ)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ lifted₂ g p r ≃ lifted₂ g q r :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_congr₂_b (g : β → α → γ)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ lifted₂ g r p ≃ lifted₂ g r q :=
by { lifted_pred using h, simp [h] }

@[lifted_congr]
lemma lifted_proj (v : var α β)
  (h : Γ ⊢ p ≃ q)
: Γ ⊢ v ;; p ≃ v ;; q :=
by { lifted_pred using h, simp [h] }

@[timeless_congr]
lemma lifted_henceforth (p q : cpred)
  (h : ◻Γ ⊢ p ≃ q)
: ◻Γ ⊢ ◻p ≃ ◻q :=
begin
  apply mutual_p_imp
  ; change tl_imp _ _ _
  ; monotonicity
  ; apply p_imp_of_equiv,
  apply h, apply v_eq_symm h
end

@[timeless_congr]
lemma lifted_eventually (p q : cpred)
  (h : ◻Γ ⊢ p ≃ q)
: ◻Γ ⊢ ◇p ≃ ◇q :=
begin
  apply mutual_p_imp
  ; change tl_imp _ _ _
  ; monotonicity
  ; apply p_imp_of_equiv,
  apply h, apply v_eq_symm h
end

end

section simulation

section pair

variables {α' : Type u} {β' : Type u₀} {γ' : Type u₁}
variables (x : tvar α') (y : tvar β') (z : tvar γ')

def pair : tvar (α' × β') :=
lifted₂ prod.mk x y

notation `⦃` x `,` l:(foldl `,` (h t, pair h t) x `⦄`)  := l

@[simp]
lemma pair_model (i : ℕ) :
i ⊨ ⦃x,y⦄ = (i ⊨ y,i ⊨ x) :=
by { cases x, cases y, refl }

@[reducible]
def pair.fst : var (α' × β') α' :=
↑(@prod.fst α' β')

@[simp]
def pair.fst_mk (x : tvar α') (y : tvar β')
: pair.fst ;; ⦃y,x⦄ = x :=
by lifted_pred

-- @[simp]
def pair.fst_mk' (x : tvar α') (y : tvar β')
: ↑(@prod.fst α' β') ;; ⦃y,x⦄ = x :=
pair.fst_mk _ _

end pair

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters {A : act (α'×γ')} {C : act (β'×γ')}
parameters {J : pred' (α'×β'×γ')}

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> C ⟧

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ {w v o} v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

parameters {Γ : cpred}
parameters H : Γ ⊢ SPEC₁ v o

section witness
variables (i : ℕ) (Hi : i ⊨ Γ)
include H Hi

open classical

private noncomputable def ww : Π j : ℕ, { w : α' // j ≥ i → (w,j ⊨ v,j ⊨ o) ⊨ J }
 | j :=
if h : j > i then
     have h₀ : j ≥ 1,
       by { apply succ_le_of_lt,
            apply nat.lt_of_le_of_lt (nat.zero_le i) h },
     have h₁ : i ≤ j - 1,
       by { rw ← add_le_to_le_sub _ ; assumption },
     have Hdec : j - 1 < j,
       by { apply nat.sub_lt_of_pos_le, apply zero_lt_one,
            assumption },
     let hw := (ww (j-1)).property h₁ in
     have Hstep : C (j - 1 ⊨ v, j - 1 ⊨ o) (j ⊨ v, j ⊨ o),
       begin
         clear_except H Hi h₀ h₁ h, replace H := (H.apply _ Hi).right ((j-1) - i),
         simp at H, rw [← nat.add_sub_assoc,nat.add_sub_cancel_left,← succ_sub] at H
         ; apply H <|> assumption,
       end,
     let x := some (SIM (j ⊨ v) (j ⊨ o) hw Hstep) in
     have h₁ : j ≥ i → (x, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM (j ⊨ v) (j ⊨ o) hw Hstep)).right,
     ⟨x,h₁⟩
else if h' : i ≤ j then
     have h : i = j,
       by { apply le_antisymm h', apply le_of_not_gt, assumption },
     have h₀ : (j ⊨ v, j ⊨ o) ⊨ q,
          begin
            clear_except H Hi h,
            have := H.left.apply _ Hi, simp at this,
            subst i, apply this,
          end,
     let x₀ := some (SIM₀ (j ⊨ v) (j ⊨ o) h₀) in
     have h₁ : j ≥ i → (x₀, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM₀ (j ⊨ v) (j ⊨ o) h₀)).right,
     ⟨x₀,h₁⟩
else
  have h₁ : j ≥ i → (default α', j ⊨ v, j ⊨ o) ⊨ J,
    by { intro, exfalso, apply h', assumption, },
  ⟨default α',h₁⟩

private noncomputable def ww' (j : ℕ) := (ww i Hi j).val

end witness
include H SIM₀ SIM

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin
  simp [SPEC₀],
  lifted_pred keep,
  let w := ww' SIM₀ @SIM v o H _ a,
  existsi (⟨ w ⟩ : tvar α'),
  split,
  intro i,
  { simp,
    generalize h : w (x + i) = z,
    have h' : succ (x + i) > x,
    { apply lt_succ_of_le, apply nat.le_add_right },
    simp [w], rw [ww',ww], simp [dif_pos h'],
    rw ← h,
    apply_some_spec, simp, intros, assumption, },
  { dsimp [w,ww'], rw ww, simp,
    apply_some_spec,
    simp, intros, assumption, },
end
omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation SIM₀ @SIM _ _ h,
end

end simulation

section witness_construction

parameters {α' : Sort u}
parameters {p J : pred' α'}
parameters {A : act α'}

parameters H₀ : p ⟹ J
parameters FIS₀ : ∃ σ, σ ⊨ p
parameters FIS : ∀ σ, σ ⊨ J → ∃ σ', A σ σ'
parameters INV : ∀ σ σ', σ ⊨ J → A σ σ' → σ' ⊨ J

open classical

include H₀ INV

def A' : plift α' × unit → plift α' × unit → Prop :=
A on (plift.down ∘ prod.fst)

parameters [_inst : inhabited α']

include FIS₀ FIS _inst
lemma witness_construction
: ⊩ ∃∃ v, p ;; v ⋀ ◻⟦ v <> A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (plift α' × unit) α' := ↑(@plift.down α') ;; pair.fst,
  let p' : pred' (plift α' × unit) := p ;; prj,
  have _inst : inhabited (plift α') := ⟨ plift.up (default α') ⟩,
  let J' : pred' (plift α' × unit × unit) := J ;; ↑(@plift.down α') ;; pair.fst,
  have := @simulation _ _ _ p' (@True $ unit × unit) (A' H₀ INV) C J' _ _ _ o o Γ _,
  begin [temporal]
    revert this,
    let f : tvar (plift α') → tvar α' := λ v, ↑(λ x : plift α', x.down) ;; v,
    let SPEC := @SPEC₀ _ _ p' (A' H₀ INV),
    let SPEC' := λ (v : tvar α'), p ;; v ⋀ ◻⟦ v <> A ⟧,
    apply p_exists_imp_p_exists' (λ w, SPEC w o) SPEC' f,
    intro, simp only [SPEC,f,SPEC',SPEC₀,p',prj,proj_assoc,pair.fst_mk,A'],
    monotonicity, rw [action_on,coe_over_comp,proj_assoc,pair.fst_mk'],
    refl,
  end,
  { intros,
    revert FIS₀,
    apply exists_imp_exists' plift.up,
    introv h, split, simp [p',h],
    simp [J'], apply ew_str H₀ _ h, },
  { introv hJ hC, simp [J'] at hJ,
    have := FIS (w.down) hJ, revert this,
    apply exists_imp_exists' plift.up,
    introv hA, simp [A'], split,
    { apply INV _ _ hJ hA  },
    { apply hA } },
  { simp [SPEC₁,C], }
end

end witness_construction

end temporal

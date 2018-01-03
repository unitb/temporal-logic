
import data.stream

import util.meta.tactic
import util.logic
import util.predicate

import temporal_logic.tactic

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal
open predicate stream

attribute [predicate] stream.drop pred'.mk
attribute [simp] pred'.mk

lemma henceforth_next (p : cpred β)
: ◻p ⟹ ◻⊙p :=
begin [temporal]
  rw henceforth_next_intro p,
  monotonicity, simp,
  intros, assumption
end

lemma next_henceforth (p : cpred β)
: ◻p ⟹ ⊙◻p :=
begin [temporal]
  suffices : ◻◻p ⟶ ⊙◻p,
  { simp at this, apply this },
  intro h, apply h
end

lemma next_eventually_comm (p : cpred β)
: ⊙◇p = ◇⊙p :=
by lifted_pred [next,eventually,tail]

/- distributivity -/

lemma eventually_and_entails {p q : cpred β}
: ◇(p ⋀ q) ⟹ ◇p ⋀ ◇q :=
begin
  apply entails_p_and_of_entails ; monotonicity ; propositional,
end

lemma entails_henceforth_or {p q : cpred β}
: ◻p ⋁ ◻q ⟹ ◻(p ⋁ q) :=
sorry

lemma init_lam (p : Prop)
: (•p : cpred β) = p :=
rfl

@[simp]
lemma init_p_or {p q : pred' β}
: •(p ⋁ q) = •p ⋁ •q :=
rfl

@[simp]
lemma init_p_and {p q : pred' β}
: •(p ⋀ q) = •p ⋀ •q :=
rfl

lemma action_imp (p q : act β)
: (⟦ λ s s' : β, p s s' → q s s' ⟧ : cpred β) = ⟦ p ⟧ ⟶ ⟦ q ⟧ :=
rfl

lemma action_and_action (p q : act β)
: ⟦ p ⟧ ⋀ ⟦ q ⟧ = (⟦ λ s s' : β, p s s' ∧ q s s' ⟧ : cpred β) :=
rfl

lemma action_or_action (p q : act β)
: ⟦ p ⟧ ⋁ ⟦ q ⟧ = (⟦ λ s s' : β, p s s' ∨ q s s' ⟧ : cpred β) :=
rfl

/- end distributivity -/

lemma eventually_of_leads_to {p q : cpred β} {Γ}
  (h : Γ ⊢ p ~> q)
: Γ ⊢ ◇p ⟶ ◇q :=
begin [temporal]
  rw ← eventually_eventually q,
  apply eventually_imp_eventually h,
end

lemma inf_often_of_leads_to {p q : cpred β} {Γ}
  (h : Γ ⊢ p ~> q)
: Γ ⊢ ◻◇p ⟶ ◻◇q :=
begin [temporal]
  rw ← eventually_eventually q,
    -- β : Type u₁
    -- p q : cpred β
    -- h : p ~> q
    -- ⊢ ◻◇p ⟶ ◻◇◇q
  monotonicity,
    -- β : Type u₁
    -- p q : cpred β
    -- h : p ~> q
    -- ⊢ p ⟶ ◇q
  apply h,
end

lemma leads_to_trans {p q r : cpred β} {Γ}
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
lemma not_henceforth (p : cpred β) : (- ◻p) = (◇-p) :=
begin
  funext1,
  TL_simp [henceforth,not_forall_iff_exists_not,eventually],
end

@[simp]
lemma init_not (p : pred' β) : •-p = (-•p) :=
begin
  funext1,
  TL_simp [init],
end

lemma not_init (p : pred' β) : (-•p) = •-p :=
begin
  funext1,
  TL_simp [init],
end

lemma next_or (p q : cpred β)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

lemma next_imp (p q : cpred β)
: ⊙(p ⟶ q) = ⊙p ⟶ ⊙q :=
rfl

open nat

@[simp]
lemma action_drop (A : act β) (τ : stream β) (i : ℕ)
: τ.drop i ⊨ ⟦ A ⟧ ↔ A (τ i) (τ $ succ i) :=
by { unfold drop action, TL_simp [action] }

@[simp, predicate]
lemma models_action (A : act β) (τ : stream β)
: τ ⊨ ⟦ A ⟧ ↔ A (τ 0) (τ 1) :=
by { unfold drop action, TL_simp [action] }

@[simp]
lemma init_drop (p : pred' β) (τ : stream β) (i : ℕ)
: τ.drop i ⊨ (• p) ↔ τ i ⊨ p  :=
by { unfold drop action, simp [init_to_fun] }

@[simp, predicate]
lemma models_next (p : cpred β) (τ : stream β)
: τ ⊨ ⊙p = drop 1 τ ⊨ p :=
by refl

@[simp]
lemma next_init (p : pred' β) (τ : stream β)
: τ ⊨ ⊙•p = τ 1 ⊨ p :=
by refl

lemma models_henceforth (p : cpred β) (τ : stream β)
: τ ⊨ ◻p ↔ ∀ i, drop i τ ⊨ p :=
by { cases p, simp [henceforth] }

lemma eventually_p_or {β} (p q : cpred β)
: ◇(p ⋁ q) = ◇p ⋁ ◇q :=
begin
  funext1,
  TL_simp [eventually,exists_or],
end

lemma induct {β} (p Γ : cpred β)
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ (p ⟶ ◻p) :=
begin
  constructor,
  intros τ hΓ hp i,
  induction i with i,
  assumption,
  have := h.apply τ hΓ i ih_1,
  simp [next] at this, simp [tail_drop] at this,
  simp [drop_succ,this],
end

instance or_persistent {p q : cpred β}
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

instance imp_persistent {p q : cpred β}
  [persistent $ - p]
  [persistent q]
: persistent (p ⟶ q) :=
by { simp [p_imp_iff_p_not_p_or], apply_instance }

instance stable_persistent {p : cpred β}
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

instance not_inf_often_persistent {p : cpred β}
: persistent (- ◻◇p) :=
by { simp, apply_instance }

lemma induct' {β} (p : cpred β) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ ◻ (p ⟶ ◻p) :=
begin [temporal]
  henceforth,
  apply induct _ _ h,
end

lemma induct_evt {β} (p q : cpred β) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ -q ⟶ ⊙(p ⋁ q)))
: Γ ⊢ ◻ (p ⟶ ◇q ⋁ ◻p) :=
begin [temporal]
  henceforth,
  rw [← p_not_p_imp,not_eventually],
  intros hp hnq,
  explicit τ
  { simp_intros [henceforth],
    induction i with i,
    { apply hp  },
    { cases h i ih_1 (hnq i) with h h,
      { simp [tail_drop,drop_succ] at h ⊢,
        apply h, },
      { rw [tail_drop,← drop_succ] at h,
        cases hnq (succ i) h, } } },
end

theorem em {β} (p : cpred β) : ⊩ ◇◻p ⋁ ◻◇(- p) :=
begin [temporal]
  rw [← not_henceforth,← not_eventually,p_or_p_not_self]
end

lemma inf_often_of_stable (p : cpred β) : (◇◻p) ⟹ (◻◇p) :=
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

lemma weak_coincidence {p q : cpred β} {Γ}
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

lemma eventually_and_eventually (p q : cpred β)
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

lemma event_ordering {Γ p q : cpred β}
  (hp : Γ ⊢ ◇p)
  (hq : Γ ⊢ ◇q)
: Γ ⊢ ◇(p ⋀ ◇q) ⋁ ◇(◇p ⋀ q) :=
begin [temporal]
  rw [← eventually_and_eventually],
  split ; assumption
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

-- #check @p_or_entails_of_entails'
lemma stable_and_of_stable_of_stable {p q : cpred β} {Γ}
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

lemma henceforth_delay {p q : cpred β} {Γ}
    (Hp : Γ ⊢ ◇p)
    (Hq : Γ ⊢ ◻q)
: Γ ⊢ ◇(p ⋀ ◻q) :=
begin [temporal]
  eventually Hp ⊢,
  split ; assumption
end

lemma eventually_inf_often (p : cpred β)
: ◇◻◇p = ◻◇p :=
mutual_entails
begin [temporal]
  intros hp,
  have := inf_often_of_stable (◇p) Γ hp, clear hp,
  rw eventually_eventually at this,
end
(eventually_weaken _)

lemma coincidence {p q : cpred β} {Γ}
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

lemma coincidence' {p q : cpred β} {Γ}
    (Hp : Γ ⊢ ◻p)
    (Hq : Γ ⊢ ◻◇q)
: Γ ⊢ ◻◇(p ⋀ q) :=
begin [temporal]
  apply coincidence _ Hq,
  assumption
end

lemma inf_often_p_or (p q : cpred β)
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
lemma next_imp_next {p q : cpred β} (h : p ⟹ q)
: ⊙ p ⟹ ⊙ q :=
by { pointwise h with τ, auto }

@[monotonic]
lemma next_tl_imp_next {Γ p q : cpred β} (h : tl_imp Γ p q)
: tl_imp Γ (⊙ p) (⊙ q) :=
by { lifted_pred keep [tl_imp], -- intros h',
     replace h := h.apply σ.tail,
     apply h, clear h,
     intro i, simp [tail],
     apply a (i+1), }

lemma eventually_and {Γ p q : cpred β}
   (h₀ : Γ ⊢ ◻p)
   (h₁ : Γ ⊢ ◇q)
: Γ ⊢ ◇(p ⋀ q) :=
begin [temporal]
  eventually h₁ ⊢,
  split ; assumption
end

lemma eventually_exists (P : α → cpred β)
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

lemma forall_henceforth_one_point {t} (V : β → t) (P : stream t → cpred β)
: (∀∀ x : t, ◻•((V : var β t) ≃ x) ⟶ P (const x) : cpred β) = ↑(λ (s : stream β), s ⊨ P (map V s)) :=
sorry


/- Actions -/

lemma exists_action (t : Type u) (A : t → act β)
: (∃∃ x : t, ⟦ A x ⟧) = ⟦ λ σ σ', ∃ x, A x σ σ' ⟧ :=
begin
  funext1,
  TL_simp [temporal.action],
end

lemma or_action (A B : act β)
: ⟦ A ⟧ ⋁ ⟦ B ⟧ = ⟦ λ σ σ', A σ σ' ∨ B σ σ' ⟧ :=
begin
  funext1,
  refl
end

lemma action_entails_action (A B : act β)
  (h : ∀ σ σ', A σ σ' → B σ σ')
: ⟦ A ⟧ ⟹ ⟦ B ⟧ :=
begin
  lifted_pred,
  apply h
end

lemma exists_of_eventually
  {p : pred' β}
  {τ : stream β}
  (h : τ ⊨ ◇•p)
: ∃ x, x ⊨ p :=
begin
  apply exists_imp_exists' τ _ h,
  intro,
  simp [init,drop], apply id
end

open function

@[simp]
lemma henceforth_trading {α} (f : α → β) (p : cpred β)
: (◻ p) '∘ map f = ◻ (p '∘ map f) :=
begin
  funext1,
  unfold comp henceforth,
  apply forall_congr, intro i,
  TL_simp,
  refl,
end

@[simp]
lemma eventually_trading {α} (f : α → β) (p : cpred β)
: (◇ p) '∘ map f = ◇ (p '∘ map f) :=
begin
  funext1,
  unfold comp eventually,
  apply exists_congr, intro i,
  TL_simp, refl,
end

@[simp]
lemma init_trading {α} (f : α → β) (p : pred' β)
: (• p) ∘' ↑(map f) = • (p '∘ f) :=
begin
  funext1,
  TL_simp [comp,init],
  refl
end

@[simp]
lemma action_trading {α} (f : α → β) (a : act β)
: (action a ∘' ↑(map f)) = ( action $ a on f ) :=
begin
  funext1,
  refl,
end

@[simp]
lemma comp_map_app_eq_map {α} (p : cpred β) (f : α → β) (τ : stream α)
: map f τ ⊨ p ↔ τ ⊨ p '∘ map f :=
by cases p; refl

lemma inf_often_trace_trading {α} (τ : stream α) (f : α → β) (p : cpred β)
: τ ⊨ ◻◇(p '∘ map f) = map f τ ⊨ ◻◇p :=
by { TL_simp [eventually_trading,henceforth_trading], }

lemma inf_often_trace_init_trading {α} (τ : stream α) (f : α → β) (p : pred' β)
: τ ⊨ ◻◇•(p '∘ f) = map f τ ⊨ ◻◇•p :=
by { TL_simp [init_trading,eventually_trading,henceforth_trading], }

lemma inf_often_trace_action_trading {α} (τ : stream α) (f : α → β) (p : act β)
: τ ⊨ ◻◇⟦ p on f ⟧ = map f τ ⊨ ◻◇⟦ p ⟧ :=
by { simp }

lemma stable_trace_trading {α} (τ : stream α) (f : α → β) (p : cpred β)
: τ ⊨ ◇◻(p '∘ map f) = map f τ ⊨ ◇◻p :=
by { simp }

lemma stable_trace_init_trading {α} (τ : stream α) (f : α → β) (p : pred' β)
: τ ⊨ ◇◻•(p '∘ f) = map f τ ⊨ ◇◻•p :=
by { simp }

-- lemma stable_trace_init_trading (τ : stream α) (f : α → β) (p : β → Prop)
-- : (◇◻•(p ∘ f)) τ = (◇◻•p) (f ∘ τ) :=
-- by rw [init_trading,henceforth_trading,eventually_trading]

lemma inf_often_trace_action_init_trading {α} (τ : stream α) (f : α → α → β) (p : pred' β)
: τ ⊨ ◻◇⟦ λ σ σ', f σ σ' ⊨ p ⟧ = (λ i, f (τ i) (τ $ succ i)) ⊨ ◻◇•p :=
begin
  unfold henceforth eventually,
  rw ← iff_eq_eq,
  apply forall_congr, intro i,
  apply exists_congr, intro j,
  simp [drop_drop,init,action,drop],
  refl,
end

protected theorem leads_to_of_inf_often {α} (Γ p q : cpred α)
  (H : Γ ⊢ ◻◇q)
: Γ ⊢ p ~> q :=
begin [temporal]
  henceforth at H ⊢,
  intro, assumption,
end

protected theorem leads_to_strengthen_rhs {α} (q : cpred α) {Γ p r : cpred α}
  (H : q ⟹ r)
  (P₀ : Γ ⊢ p ~> q)
: Γ ⊢ p ~> r :=
begin [temporal]
  apply leads_to_trans P₀,
  henceforth,
  intros H',
  apply H Γ H',
end

protected lemma leads_to_cancellation {α} {Γ p q b r : cpred α}
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

protected lemma leads_to_disj_rng {α} {t : Sort u}
  {p : t → cpred α} {Γ q} {r : t → Prop}
  (h : Γ ⊢ ∀∀ i, ↑(r i) ⟶ (p i ~> q))
: Γ ⊢ (∃∃ i, ↑(r i) ⋀ p i) ~> q :=
begin [temporal]
  rw [p_exists_range_subtype,tl_leads_to,p_exists_imp_eq_p_forall_imp],
  rw [henceforth_forall],
  intro i, cases i with i hi,
  apply h i hi,
end

protected theorem leads_to_disj {α t}
  {p : t → cpred α}
  {q Γ : cpred α}
  (P₀ : Γ ⊢ ∀∀ i, p i ~> q)
: Γ ⊢ (∃∃ i, p i) ~> q :=
begin [temporal]
  have P₁ : ∀∀ i : t, ↑true ⟶ (◻(p i ⟶ ◇q)),
  { intros i, intro, apply P₀ i, },
  have P₂ := @temporal.leads_to_disj_rng  _ _ _ _ _ (λ _, true) P₁,
  rw_using : (∃∃ (i : t), ↑((λ _, true) i) ⋀ p i) = (∃∃ i, p i) at P₂,
  { apply p_exists_congr,
    intro,
    apply True_p_and },
end

section induction

variables {α' : Type u}
variables  {Γ : cpred α'}
variables  (f : var α' β) (p q : cpred α')
variables [has_well_founded β]

protected lemma induction
  (P : Γ ⊢ ∀∀ v : β, p ⋀ •(f ≃ v)  ~>  p ⋀ •(f ≺≺ v) ⋁ q)
: Γ ⊢ p ~> q :=
begin [temporal]
  have h₂ : ∀∀ V : β, p ⋀ •(f ≃ V) ~> q,
  { intro V,
    wf_induction V,
    apply temporal.leads_to_strengthen_rhs _ _,
    show q ⋁ q ⟹ q,
    { simp [or_self], },
    apply temporal.leads_to_cancellation (P _),
    rw_using : (p ⋀ •(f ≺≺ x)) = (∃∃v, ↑(v << x) ⋀ (p ⋀ •(f ≃ v))),
    { funext1 τ, simp only with predicate, rw exists_one_point (f.apply $ τ 0), simp,
      intro k, simp, intros, subst k },
    apply @temporal.leads_to_disj_rng _ β ,
    apply ih_1, },
  have h₃ := temporal.leads_to_disj h₂,
  rw_using : (∃∃ (i : β), p ⋀ •(f ≃ i)) = p at h₃,
  { funext1 i, TL_simp [function.comp,init,exists_one_point_right (f $ i 0)], },
end

end induction

section inf_often_induction'

parameters {α' : Type u}  {β' : Type u₀}
parameters {Γ : cpred α'} (V : var α' β') (p q : pred' α')
parameters [has_well_founded β']

def le (x y : β') := x << y ∨ x = y

lemma inf_often_induction'
  (S₀ : Γ ⊢ ∀∀ v : β', ◻◇•(V ≃ v) ⟶ ◇◻•(V ≃ v) ⋁ ◻◇•(V ≺≺ v ⋁ q))
  (P₁ : Γ ⊢ ∀∀ v : β', •(p ⋀ V ≃ v) ~> •(V ≺≺ v ⋁ q))
: Γ ⊢ ◻◇•p ⟶ ◻◇•q :=
begin [temporal]
  have Hex : ∀∀ (v : β'), •(p ⋀ V ≃ v) ~> (•q ⋁ ◻•-p),
  { intro v,
    wf_induction v with v,
    have IH' := temporal.leads_to_disj_rng ih_1, clear ih_1,
    rw_using : (∃∃ (i : β'), ↑(i << v) ⋀ •(p ⋀ V ≃ i))
             = •(V ≺≺ v ⋀ p) at IH',
    { funext τ,
      TL_simp [init,flip,function.comp],
      split ; simp ; intros, rw a_2, split ; assumption,
      split, repeat { split, assumption }, refl  },
    have S₂ : ∀∀ (v : β'), ◻◇•(V ≺≺ v) ⟶ ◇◻•(V ≺≺ v) ⋁ ◻◇•(V ≺≺ v ⋁ q),
    { admit },
    have S₁ : ∀∀ (v : β'), •(V ≃ v)  ~> ◻•(V ≃ v) ⋁ ◻◇•(V ≺≺ v ⋁ q),
    { admit }, clear S₀,
    have H₁ : •(p ⋀ V ≃ v) ~> •(V ≺≺ v ⋀ p) ⋁ •q, admit,
--    have H₂ : (•(flip lt v ∘ V ⋀ p) ~> •q) τ , admit,
    have H₃ := temporal.leads_to_cancellation H₁ IH',
--     have H₀ := @temporal.leads_to_trans _ (•(p ⋀ eq v ∘ V)) _ _ _ H₁ IH',
--     clear S₀,
--     have H₃ : (•(p ⋀ eq v ∘ V) ~> •q ⋁ ◻•-p) τ, admit,
-- --    apply temporal.leads_to_cancellation _ _, },
    admit },
  have H := @temporal.leads_to_disj _ _ (λ v : β', •(p ⋀ V ≃ v)) (•q ⋁ ◻•-p) _ Hex,
  dsimp [tl_leads_to] at H,
  rw_using : (∃∃ (v : β'), •p ⋀ •(V ≃ v)) = •p at H,
  { funext τ, TL_simp [init,function.comp,exists_one_point_right (V $ τ 0)] },
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

parameters {α' : Type*} {β' : Type*}
parameters {Γ : cpred α'} (f : α' → β') (p q : α' → Prop)
parameters [has_well_founded β']
parameters (h₀ : Γ ⊢ ◻◇•p)
parameters (h₁ : Γ ⊢ ◻⟦ λ s s', q s' ∨ f s' << f s ∨ (¬ p s' ∧ f s = f s') ⟧)

def EQ (v : β') : pred' α' := (f : var α' β') ≃ v
def LT (v : β') : pred' α' := (f : var α' β') ≺≺ v

include h₁
include h₀

lemma P : Γ ⊢ ∀∀ v, •(p ⋀ EQ v)  ~>  •(p ⋀ LT v ⋁ q) :=
begin [temporal]
  intros v, henceforth,
  simp,
  intros Hp Hv,
  replace h₀ := p_impl_revert (henceforth_next (◇•↑p) Γ) h₀,
  rw next_eventually_comm at h₀,
  -- replace h₀ := coincidence' h₁ h₀,
  -- henceforth at h₀,
  let ACT := λ (s s' : α'), q s' ∨ f s' << f s ∨ ¬p s' ∧ f s = f s',
  have h₀ : ◇(⟦ACT⟧ ⋀ ⊙•↑p ⋀ •(EQ f v)),
  { suffices : ◇(⟦ACT⟧ ⋀ ⊙•↑p ⋀ •EQ f v) ⋁ ◻•EQ f v,
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
  rw [action_eq_next] at h₀,
  revert h₀, simp,
  introv h₀ h₁ h₂ h₃,
  strengthen_to ⊙_,
  explicit τ
  { TL_simp [next,EQ,LT,comp,init,flip] at *,
    begin [smt] destruct h₁, end },
end

lemma inf_often_induction
: Γ ⊢ ◻◇•q :=
begin [temporal]
  have P := P f p q h₀ h₁,
  revert h₀,
  apply inf_often_of_leads_to,
  have inst := (λ _, classical.prop_decidable _ : decidable_pred p),
  apply temporal.induction (f : var α' β') (•p) (•q) P,
end
end inf_often_induction

-- lemma congr_inf_often_trace {α} {x : α} {τ : stream α} (f : α → β)
--   (Hinj : injective f)
-- : (◻◇•(eq x : pred' α)) τ ↔ (◻◇•(eq (f x) : pred' β)) (map f τ) :=
-- begin
--   let EQ_f := (eq (f x) : pred' β),
--   rw [ comp_map_app_eq_map (◻◇•EQ_f) f τ ],
--   rw [ (henceforth_trading f (◇•EQ_f)).symm ],
--   rw [ (eventually_trading f (•EQ_f)).symm  ],
--   rw [ (init_trading f (eq (f x))).symm ],
--   have H : EQ_f '∘ f = eq x,
--   { funext y,
--     simp,
--     split,
--     { apply Hinj },
--     apply congr_arg },
--   rw H,
-- end

-- lemma events_to_states {lbl : Type u} (s : stream lbl)
--   (act : lbl → β → β → Prop) {τ : stream β}
--   (h : ∀ i, act (s i) (τ i) (τ (succ i)))
--   (e : lbl)
-- : (◻◇•(eq e : pred' lbl)) s → (◻◇⟦act e⟧) τ :=
-- begin
--   intros h' i,
--   cases h' i with j h',
--   TL_simp [drop_drop, init_drop] at h',
--   TL_simp [eventually], existsi j,
--   simp [drop_drop,action,action_drop,h',drop],
--   apply h,
-- end

attribute [irreducible] next init

end temporal

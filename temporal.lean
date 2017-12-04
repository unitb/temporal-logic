
import data.stream

import util.meta.tactic
import util.logic
import util.predicate

namespace tactic.interactive
open lean interactive.types
open interactive lean.parser tactic
open list (hiding map) has_map predicate
local postfix *:9001 := many

meta def apply_left (r : parse texpr) : tactic unit :=
transitivity none ; [apply r >> done, skip]

meta def apply_right (r : parse texpr) : tactic unit :=
transitivity none ; [skip, apply r >> done]

meta def references_to (v : expr) : tactic (list expr) :=
do ctx ← local_context,
   ctx_t ← mmap infer_type ctx,
   return $ map prod.fst $ filter ((λ t, v.occurs t) ∘ prod.snd) $ zip ctx ctx_t

-- meta def focus_rhs (tac : itactic) : tactic unit :=
-- do `(_ ⟹ %%p) ← target <|> fail "expecting goal: _ ⟹ _",
--    t ← infer_type p,
--    q ← mk_meta_var t,
--    e ← to_expr ``(%%q ⟹ %%p),
--    h ← assert `h _, _

meta def mk_local_hyp (a' : expr) (hyp : pexpr) : tactic (expr × expr × expr) :=
do e' ← to_expr hyp,
   e ← if e'.is_local_constant
       then return e'
       else note `h none e',
   (expr.app f a)  ← infer_type e,
   is_def_eq a a' <|> fail format!"{a} and {a'} are not the same argument",
   return (e, f, a)

meta def revert_pred (a : expr) (h : expr × expr × expr) : tactic unit :=
do (expr.app g a') ← target,
   is_def_eq a a',
   tactic.revert h.1,
   refine ``(impl_of_p_impl %%a _)
   -- to_expr ``((%%h.2.1 ⟶ %%g) %%a) >>= tactic.change

meta def revert_p (hyps : parse pexpr_list_or_texpr) : tactic unit :=
do (expr.app g a) ← target,
   hyps' ← mmap (mk_local_hyp a) hyps,
   ls ← references_to a,
   let vars := hyps'.map prod.fst,
   mmap tactic.clear (ls.diff vars),
   if a.is_local_constant then do -- <|> fail format!"{a} is not a local constant",
     mmap' (revert_pred a) hyps',
     () <$ tactic.revert a
   else (mmap' (revert_pred a) hyps' >> tactic.generalize a),
   -- to_expr ``(entails_of_forall_impl _) >>= infer_type >>= trace,
   -- trace_state
   tactic.refine ``(entails_of_forall_impl _)
   -- to_expr ``(%%f ⟹ %%g) >>= tactic.change

private meta def apply_trans : expr → expr → list expr → tactic unit
 | _ _ [] := return ()
 | p q (e :: es) := refine ``(@function.comp %%p %%e %%q _ _) ; [ skip , apply_trans p e es ]

meta def imp_transitivity : parse (optional pexpr_list_or_texpr) → tactic unit
 | none :=
do `(%%p → %%q) ← target <|> fail "expecting implication",
   refine ``(@function.comp %%p _ %%q _ _) >> rotate_left 1
 | (some xs) :=
do xs' ← mmap to_expr xs,
   `(%%p → %%q) ← target <|> fail "expecting implication",
   focus1 (apply_trans p q xs'.reverse)

meta def apply' (e : parse texpr) : tactic unit :=
apply e <|> (intro1 >>= λ h, (apply' ; try (tactic.exact h)) >> try (tactic.clear h))

meta def TL_unfold (cs : parse ident*) (loc : parse location) : tactic unit :=
do unfold_coes loc, unfold (cs ++ [`pred'.apply]) loc

meta def coes_thms : list name :=
[`coe,`lift_t,`lift,`has_lift_t,`coe_t,`coe,`has_coe_t
,`coe_b,`coe,`has_coe,`coe_fn,`coe,`has_coe_to_fun
,`coe_sort,`coe,`has_coe_to_sort,`predicate.lifted₀]

meta def TL_simp
   (only_kw : parse only_flag)
   (args : parse simp_arg_list)
   (w : parse with_ident_list)
   (loc : parse location) : tactic unit :=
do std_lmm ← mmap (map (simp_arg_type.expr ∘ to_pexpr) ∘ mk_const) (coes_thms ++ [`predicate.pred'.apply,`temporal.init_to_fun]) ,
   repeat (simp only_kw args w loc <|> simp only_kw std_lmm w loc <|> unfold_coes loc <|> unfold [`predicate.pred'.apply] loc)

end tactic.interactive


-- section
-- variables b : Prop
-- variables c : ℕ → Prop
-- variable h : b → ∀ i, c i
-- variable h' : ℕ
-- include h h'
-- example : ∀ i, c i :=
-- begin
--   apply h , done,
-- end

-- end

namespace temporal

open predicate

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

@[reducible]
def cpred (β : Type u) := pred' (stream β)

def act (β : Sort u) := β → β → Prop

def action (a : act β) : cpred β :=
⟨ λ τ, a (τ 0) (τ 1) ⟩

def eventually (p : cpred β) : cpred β :=
⟨ λ τ, ∃ i, p (τ.drop i) ⟩
def henceforth (p : cpred β) : cpred β :=
⟨ λ τ, Π i, p (τ.drop i) ⟩
def next (p : cpred β) : cpred β :=
⟨ λ τ, p τ.tail ⟩
def init (p : pred' β) : cpred β :=
⟨ λ τ, p (τ 0) ⟩

prefix `•`:85 := init
prefix `⊙`:90 := next
prefix `◇`:95 := eventually -- \di
prefix `◻`:95 := henceforth -- \sqw
notation `⟦`:max act `⟧`:0 := action act
-- notation `⦃` act `⦄`:95 := ew act

lemma init_to_fun (p : pred' β) (τ : stream β) : (•p) τ = p (τ 0) := rfl

def tl_leads_to (p q : cpred β) : cpred β :=
◻(p ⟶ ◇q)

infix ` ~> `:50 := tl_leads_to

def tl_imp (h p q : cpred β) : Prop :=
◻ h ⟹ (p ⟶ q)

lemma tl_imp_intro (h : cpred β) {p q : cpred β}
  (h' : ◻h ⟹ (p ⟶ q))
: tl_imp h p q := h'

lemma tl_imp_elim (h : cpred β) {p q : cpred β}
  (h' : tl_imp h p q)
: ◻h ⟹ (p ⟶ q) := h'

lemma tl_imp_intro' (h : cpred β) {p q : cpred β}
  (h' : p ⟹ q)
: tl_imp h p q :=
begin
  unfold tl_imp, pointwise h' with τ h'',
  xassumption
end

lemma tl_imp_elim' {p q : cpred β}
  (h : tl_imp True p q)
: p ⟹ q :=
begin
  unfold tl_imp at h, pointwise h with τ h'',
  apply h,
  { intro, trivial },
  assumption,
end

lemma eventually_weaken {p : cpred β}
: (p ⟹ ◇ p) :=
begin
  pointwise with τ h,
  unfold_coes, unfold eventually pred'.apply,
  existsi 0,
  apply h
end
open stream
lemma eventually_weaken' {p : cpred β} {τ} (i) :
  p (drop i τ) → (◇ p) τ :=
begin
  intros h,
  TL_unfold eventually,
  existsi i,
  apply h
end

lemma eventually_of_next {p : cpred β} {τ}
  (H : ⊙p $ τ)
: ◇p $ τ :=
sorry

lemma next_entails_eventually {p : cpred β}
: ⊙p ⟹ ◇p :=
sorry

lemma henceforth_str {p : cpred β} :
  (◻p ⟹ p) :=
begin
  pointwise with τ h, apply h 0
end

lemma henceforth_str' {p : cpred β} {τ} (i) :
  (◻p) τ → p (drop i τ) :=
begin
  intros h, apply h i
end

lemma henceforth_delay {p : cpred β} {τ} (i) :
  (◻p) τ → (◻p) (drop i τ) :=
begin
  intros h j, simp [drop_drop], apply h
end

lemma init_eq_action {p : pred' β}
: •p = ⟦ λ s s', p s ⟧ :=
rfl

lemma next_init_eq_action {p : pred' β}
: ⊙•p = ⟦ λ s s', p s' ⟧ :=
rfl

lemma action_eq_next {p : β → β → Prop}
:  (⟦ p ⟧ : cpred β) = (∃∃ s : β, •eq s ⋀ ⊙•p s) :=
begin
  funext τ, TL_unfold action p_exists pred.p_exists,
  split
  ; try {TL_simp [next]}
  ; intros
  ; try {subst x}
  ; assumption,
end

lemma henceforth_next_intro (p : cpred β)
: ◻p = ◻(p ⋀ ⊙p) := sorry

@[simp]
lemma eventually_eventually (p : cpred β) : ◇◇ p = ◇ p :=
begin
  funext τ,
  split
  ; TL_unfold eventually
  ; intro h
  ; cases h with i h,
  { cases h with j h,
    existsi (j+i),
    rw drop_drop at h,
    apply h },
  { existsi (0 : ℕ),
    existsi i,
    apply h }
end

@[simp]
lemma henceforth_henceforth (p : cpred β) : ◻◻ p = ◻ p :=
begin
  funext _,
  split
  ; intro h,
  { intro i,
    have h' := h i 0,
    simp [drop_drop] at h',
    apply h' },
  { intros i j,
    simp [drop_drop],
    apply h }
end

lemma henceforth_drop {p : cpred β} {τ} (i : ℕ) :
(◻p) τ → (◻p) (τ.drop i) :=
begin
  intro h,
  rw ← henceforth_henceforth at h,
  apply h,
end

/- True / False -/

@[simp]
lemma hence_false : ◻(False : cpred β) = False :=
begin
  funext _,
  split ; intro h,
  { cases h 0 },
  { cases h }
end

@[simp]
lemma event_false : ◇(False : cpred β) = False :=
begin
  funext _,
  split ; intro h,
  { cases h with _ h, cases h },
  { cases h }
end

@[simp]
lemma init_false : (•False) = (False : cpred β) :=
begin
  funext1,
  split ; intro h,
  { cases h },
  { cases h }
end

@[simp]
lemma hence_true : ◻(True : cpred β) = True :=
begin
  funext1,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

@[simp]
lemma eventually_true : ◇(True : cpred β) = True :=
begin
  funext1,
  split ; intro h,
  { trivial },
  { apply exists.intro 0, trivial }
end

@[simp]
lemma init_true : (•True) = (True : cpred β) :=
begin
  funext1,
  split ; intro h ; trivial,
end

lemma init_exists {t} (p : t → pred' β)
: •(∃∃ i, p i) = ∃∃ i, •p i :=
begin
  funext x,
  TL_simp [p_exists,pred.p_exists,init]
end

/- monotonicity -/

@[monotonic]
lemma eventually_tl_imp_eventually {h p q : cpred β}
  (f : tl_imp h p q)
: tl_imp h (◇p) (◇q) :=
begin
  unfold tl_imp at ⊢ f,
  pointwise f with τ h',
  apply exists_imp_exists,
  intro i,
  apply f,
  apply henceforth_delay _ h',
end

@[monotonic]
lemma eventually_entails_eventually {p q : cpred β}
  (f : p ⟹ q)
: (◇p) ⟹ (◇q) :=
begin
  apply tl_imp_elim',
  monotonicity (tl_imp_intro' _ f),
end

lemma eventually_imp_eventually {p q : cpred β} {τ} (f : (◻ (p ⟶ q)) τ)
: ((◇p) ⟶ (◇q)) τ :=
begin
  apply exists_imp_exists,
  intro i,
  apply f,
end

@[monotonic]
lemma henceforth_tl_imp_henceforth {h p q : cpred β}
  (f : tl_imp h p q)
: tl_imp h (◻p) (◻q) :=
begin
  unfold tl_imp at *,
  pointwise f with τ h',
  TL_simp [henceforth], intro_mono i,
  apply f, apply henceforth_delay _ h',
end

@[monotonic]
lemma henceforth_entails_henceforth {p q : cpred β}
  (f : p ⟹ q)
: (◻p) ⟹ (◻q) :=
begin
  refine tl_imp_elim' _,
  monotonicity (tl_imp_intro' _ f),
end

lemma henceforth_imp_henceforth {p q : cpred β} {τ} (f : (◻ (p ⟶ q)) τ) : ((◻p) ⟶ (◻q)) τ :=
begin
  apply forall_imp_forall,
  intro i,
  apply f,
end

@[monotonic]
lemma init_entails_init {p q : pred' β} (f : p ⟹ q)
: (•p) ⟹ (•q) :=
begin
  pointwise f with i,
  xassumption,
end

lemma inf_often_entails_inf_often {p q : cpred β} (f : p ⟹ q)
: ◻◇p ⟹ ◻◇q :=
by monotonicity f

lemma inf_often_entails_inf_often' {p q : pred' β} (f : p ⟹ q)
: ◻◇•p ⟹ ◻◇•q :=
by monotonicity f

lemma stable_entails_stable {p q : cpred β} (f : p ⟹ q)
: ◇◻p ⟹ ◇◻q :=
by monotonicity f

lemma stable_entails_stable' {p q : pred' β} (f : p ⟹ q)
: ◇◻•p ⟹ ◇◻•q :=
by monotonicity f

/- end monotonicity -/
section
open tactic tactic.interactive (monotonicity unfold_coes unfold itactic)
open interactive interactive.types lean lean.parser

meta def TL_context (tac : itactic) : tactic unit :=
do `(◻%%h ⟹ (_ ⟶ _)) ← target,
   refine ``(tl_imp_elim %%h _),
   tac,
   refine ``(tl_imp_intro %%h _)

-- TL_intro
-- TL_revert

-- TL_swap
-- TL_rw

meta def TL_monotonicity (rule : parse (optional (sum.inl <$> texpr <|> tk ":" *> sum.inr <$> texpr))) : tactic unit :=
TL_context (monotonicity rule)

end

run_cmd add_interactive [`TL_monotonicity]

/- distributivity -/

lemma eventually_and_entails {p q : cpred β}
: ◇(p ⋀ q) ⟹ ◇p ⋀ ◇q :=
begin
  apply entails_p_and_of_entails ; monotonicity ; propositional
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

lemma eventually_of_leads_to' {p q : cpred β} {τ} (i : ℕ)
  (h : ◻(p ⟶ ◇q) $ τ)
: (◇p ⟶ ◇q) (τ.drop i)  :=
begin
  intro hp,
  rw ← eventually_eventually,
  apply eventually_imp_eventually _ hp,
  apply @henceforth_drop _ _ τ i h,
end

lemma eventually_of_leads_to {p q : cpred β} {τ}
  (h : (p ~> q) τ)
: (◇p ⟶ ◇q) τ  :=
by apply eventually_of_leads_to' 0 h

lemma inf_often_of_leads_to {p q : cpred β} {τ}
  (h : (p ~> q) τ)
: (◻◇p ⟶ ◻◇q) τ :=
begin
  intros P i,
  apply eventually_of_leads_to' _ h (P _)
end

lemma leads_to_trans {p q r : cpred β} {τ}
  (Hp : p ~> q $ τ)
  (Hq : q ~> r $ τ)
: p ~> r $ τ :=
begin
  intros i hp,
  apply eventually_of_leads_to' _ Hq,
  apply Hp _ hp,
end

lemma not_henceforth (p : cpred β) : (- ◻p) = (◇-p) :=
begin
  funext1,
  TL_simp [henceforth,not_forall_iff_exists_not,eventually],
end

lemma not_init (p : pred' β) : (-•p) = •-p :=
begin
  funext1,
  TL_simp [init],
end

lemma next_or (p q : cpred β)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

open nat

lemma action_drop (A : act β) (τ : stream β) (i : ℕ)
: ⟦ A ⟧ (τ.drop i) ↔ A (τ i) (τ $ succ i) :=
by { unfold drop action, TL_simp [action] }

lemma init_drop (p : pred' β) (τ : stream β) (i : ℕ)
: (• p) (τ.drop i) ↔ p (τ i)  :=
by { unfold drop action, simp [init_to_fun] }

lemma next_init (p : pred' β) (τ : stream β)
: (⊙•p) τ = p (τ 1) :=
rfl

lemma not_eventually {β} (p : cpred β)
: (-◇p) = (◻-p) :=
begin
  funext1,
  TL_simp [henceforth,not_forall_iff_exists_not,eventually],
end

lemma eventually_p_or {β} (p q : cpred β)
: ◇(p ⋁ q) = ◇p ⋁ ◇q :=
begin
  funext1,
  TL_simp [eventually,exists_or],
end

lemma induct_evt {β} (p q : pred' β) {τ} (h : (◻ (•p ⟶ ⊙(•p ⋁ •q))) τ)
: ◻ (•p ⟶ ◇• q ⋁ ◻•p) $ τ :=
begin
  intros j h₀,
  rw [p_or_iff_not_imp,not_eventually],
  intros h₁ i,
  induction i with i ih,
  { apply h₀ },
  { simp [drop_drop] at ih,
    have h₂ := (h (j+i) ih),
    unfold action drop at h₂,
    simp [drop_drop,add_succ],
    unfold init drop,
    TL_simp, rw [p_or_comm,next_or,p_or_iff_not_imp] at h₂, simp at h₂,
    apply h₂,
    have h₃ := h₁ (i + 1),
    rw [← p_not_eq_not,drop_drop,init_drop] at h₃,
    simp at h₃,
    simp [next_init,h₃], }
end

lemma induct' {β} (p : pred' β) {τ} (h : (◻ (•p ⟶ ⊙•p)) τ)
: ◻ (•p ⟶ ◻•p) $ τ :=
begin
  rw [← False_p_or (◻•p),← event_false,← init_false],
  apply induct_evt,
  TL_simp at h,
  TL_simp [init_false,p_or_False,h],
end

lemma induct {β} (p : pred' β) {τ} (h : (◻ (•p ⟶ ⊙•p)) τ)
: (•p ⟶ ◻•p) τ :=
begin
  revert_p h,
  refine entails_trans _ henceforth_str,
  pointwise with τ,
  apply induct',
end

theorem em {β} (p : cpred β) : ⦃ ◇◻p ⋁ ◻◇(- p) ⦄ :=
begin
  refine ew_wk _, intro τ,
  have h : (◇◻p ⋁ -◇◻p) τ,
  { TL_simp, apply classical.em },
  rw [not_eventually,not_henceforth] at h,
  apply h
end

theorem em' {β} (p : cpred β) (τ) : (◇◻p) τ ∨ (◻◇(- p)) τ :=
by apply em

lemma inf_often_of_stable {p : cpred β} : (◇◻p) ⟹ (◻◇p) :=
begin
  pointwise with τ h i,
  cases h with j h,
  TL_unfold eventually,
  existsi j,
  have h' := h i,
  simp [drop_drop] at ⊢ h',
  apply h',
end

lemma stable_and_of_stable_of_stable {p q : cpred β} {τ}
    (Hp : (◇◻p) τ)
    (Hq : (◇◻q) τ)
: (◇◻(p ⋀ q)) τ :=
begin
  TL_unfold eventually henceforth at Hp Hq,
  cases Hp with i Hp,
  cases Hq with j Hq,
  TL_unfold eventually henceforth,
  existsi (i+j), intro k,
  simp [drop_drop],
  have Hq' := Hq (i+k),
  have Hp' := Hp (j+k),
  simp [drop_drop] at Hp' Hq',
  exact ⟨Hp',Hq'⟩
end

lemma coincidence {p q : cpred β} {τ}
    (Hp : (◇◻p) τ)
    (Hq : (◻◇q) τ)
: (◻◇(p ⋀ q)) τ :=
begin
  intro i,
  cases Hp with j Hp,
  cases (Hq $ i+j) with k Hq,
  have Hp' := Hp (i+k),
  simp [drop_drop] at Hp',
  simp [drop_drop] at Hq,
  TL_unfold eventually,
  existsi (j+k),
  simp [drop_drop],
  exact ⟨Hp',Hq⟩
end

lemma coincidence' {p q : cpred β} {τ}
    (Hp : (◻p) τ)
    (Hq : (◻◇q) τ)
: (◻◇(p ⋀ q)) τ :=
by { apply coincidence _ Hq, revert_p Hp, apply eventually_weaken, }

lemma weak_coincidence {p q : cpred β} {τ}
    (Hp : (◻p) τ)
    (Hq : (◇q) τ)
: (◇(p ⋀ q)) τ :=
begin
  cases Hq with j Hq,
  specialize (Hp j),
  TL_unfold eventually,
  existsi (j),
  exact ⟨Hp,Hq⟩
end

lemma inf_often_p_or (p q : cpred β)
: ◻◇(p ⋁ q) = ◻◇p ⋁ ◻◇q :=
begin
  refine mutual_entails _ _,
  { pointwise with τ h₀,
    simp [or_iff_not_imp],
    intros h₁,
    rw [p_not_eq_not,not_henceforth,not_eventually] at h₁,
    have h₂ := coincidence h₁ h₀,
    rw p_not_and_self_or at h₂,
    revert_p h₂,
    monotonicity, propositional },
  refine p_or_entails_of_entails _ _
  ; monotonicity ; propositional,
end

@[monotonic]
lemma next_imp_next {p q : cpred β} (h : p ⟹ q)
: ⊙ p ⟹ ⊙ q :=
by { pointwise h with τ h, auto }

-- lemma entail_contrapos {p q : pred' β} : p ⟹ q → (-q) ⟹ -p :=
-- begin
--   intros h τ hnq hp,
--   apply hnq,
--   apply h _ hp,
-- end

lemma eventually_and {p q : cpred β} {τ : stream β}
   (h₀ : (◻p) τ)
   (h₁ : (◇q) τ)
: (◇(p ⋀ q) ) τ :=
begin
  TL_unfold eventually at h₀ h₁,
  cases h₁ with j h₁,
  TL_unfold eventually,
  existsi j,
  exact ⟨h₀ _,h₁⟩
end

lemma henceforth_and (p q : cpred β)
: ◻(p ⋀ q) = ◻p ⋀ ◻q :=
begin
  funext1,
  repeat { split ; intros }
  ; intros i ; try { simp, split },
  { apply (a i).left },
  { apply (a i).right },
  { apply a.left },
  { apply a.right },
end

lemma eventually_and_eventually (p q : cpred β)
: ◇p ⋀ ◇q = ◇(p ⋀ ◇q) ⋁ ◇(◇p ⋀ q) :=
begin
  apply mutual_entails,
  { rw [← p_not_p_imp], simp [not_eventually,p_not_p_and],
    pointwise with τ h₀ h₁,
    cases h₀ with ha hb,
    have h := weak_coincidence h₁ ha,
    rw [p_and_comm,p_or_comm,p_and_p_or_p_not_self] at h,
    cases h with j h, cases hb with i ha,
    TL_unfold eventually, existsi i,
    split ; [skip,exact ha],
    TL_unfold eventually,
    cases le_total i j with h' h',
    { existsi (j-i),
      simp [drop_drop,add_sub_of_le h'],
      apply h.left, },
    { exfalso, apply h.right (i-j),
      simp [drop_drop,add_sub_of_le h'],
      apply ha, } },
  { apply p_or_entails_of_entails
    ; apply entails_p_and_of_entails,
    all_goals {
      transitivity,
      apply eventually_and_entails,
      rw eventually_eventually,
      propositional, }, },
end

lemma eventually_exists (P : α → cpred β)
: ◇(∃∃ x, P x) = ∃∃ x, ◇P x :=
begin
  funext1,
  TL_unfold eventually p_exists,
  split
  ; intro H
  ; cases H with i H
  ; cases H with j H
  ; exact ⟨_,_,H⟩ ,
end

lemma henceforth_forall (P : α → cpred β)
: ◻(∀∀ x, P x) = ∀∀ x, ◻P x :=
begin
  funext1,
  TL_simp [henceforth,p_forall],
  rw forall_swap,
end

lemma forall_henceforth_one_point {t} (V : β → t) (P : stream t → cpred β)
: (∀∀ x : t, ◻•(eq x ∘ V) ⟶ P (const x) : cpred β) = ↑(λ (s : stream β), (P $ map V s) s) :=
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
  unfold p_entails ew,
  intro, simp,
  apply h
end

lemma exists_of_eventually
  {p : pred' β}
  {τ : stream β}
  (h : (◇•p) τ)
: ∃ x, p x :=
begin
  apply exists_imp_exists' τ _ h,
  intro,
  rw init_drop, apply id
end

open function

lemma henceforth_trading {α} (f : α → β) (p : cpred β)
: (◻ (p '∘ map f)) = (◻ p) '∘ map f :=
begin
  funext1,
  TL_unfold comp henceforth,
  apply forall_congr, intro i,
  TL_simp,
  refl,
end

lemma eventually_trading {α} (f : α → β) (p : cpred β)
: (◇ (p '∘ map f)) = (◇ p) '∘ map f :=
begin
  funext1,
  TL_unfold comp eventually,
  apply exists_congr, intro i,
  TL_simp, refl,
end

lemma init_trading {α} (f : α → β) (p : pred' β)
: • (p '∘ f) = (• p) '∘ map f :=
begin
  funext1,
  TL_simp [comp,init],
  refl
end

lemma action_trading {α} (f : α → β) (a : act β)
: ( action $ a on f ) = (action a '∘ map f) :=
begin
  funext1,
  refl,
end

lemma comp_map_app_eq_map {α} (p : cpred β) (f : α → β) (τ : stream α)
: p (map f τ) ↔ (p '∘ map f) τ :=
by cases p; refl

lemma inf_often_trace_trading {α} (τ : stream α) (f : α → β) (p : cpred β)
: (◻◇(p '∘ map f)) τ = (◻◇p) (map f τ) :=
by { TL_simp [eventually_trading,henceforth_trading], refl }

lemma inf_often_trace_init_trading {α} (τ : stream α) (f : α → β) (p : pred' β)
: (◻◇•(p '∘ f)) τ = (◻◇•p) (map f τ) :=
by { TL_simp [init_trading,eventually_trading,henceforth_trading], refl }

lemma inf_often_trace_action_trading {α} (τ : stream α) (f : α → β) (p : act β)
: (◻◇⟦ p on f ⟧) τ = (◻◇⟦ p ⟧) (map f τ) :=
by { rw [action_trading,eventually_trading,henceforth_trading], refl }

lemma stable_trace_trading {α} (τ : stream α) (f : α → β) (p : cpred β)
: (◇◻(p '∘ map f)) τ = (◇◻p) (map f τ) :=
by { rw [henceforth_trading,eventually_trading], refl }

lemma stable_trace_init_trading {α} (τ : stream α) (f : α → β) (p : pred' β)
: (◇◻•(p '∘ f)) τ = (◇◻•p) (map f τ) :=
by { rw [init_trading,henceforth_trading,eventually_trading], refl }


-- lemma stable_trace_init_trading (τ : stream α) (f : α → β) (p : β → Prop)
-- : (◇◻•(p ∘ f)) τ = (◇◻•p) (f ∘ τ) :=
-- by rw [init_trading,henceforth_trading,eventually_trading]

lemma inf_often_trace_action_init_trading {α} (τ : stream α) (f : α → α → β) (p : pred' β)
: (◻◇⟦ λ σ σ', p (f σ σ') ⟧) τ = (◻◇•p) (λ i, f (τ i) (τ $ succ i)) :=
begin
  TL_unfold henceforth eventually,
  rw ← iff_eq_eq,
  apply forall_congr, intro i,
  apply exists_congr, intro j,
  TL_simp [drop_drop,action_drop,init_drop],
end

protected theorem leads_to_of_inf_often {α} (p q : cpred α) {τ : stream α}
  (H : (◻◇q) τ)
: p ~> q $ τ :=
begin
  intros i hp,
  apply H i
end

protected theorem leads_to_strengthen_rhs {α} (q : cpred α) {p r : cpred α} {τ : stream α}
    (H : q ⟹ r)
    (P₀ : p ~> q $ τ)
    : p ~> r $ τ :=
begin
  apply leads_to_trans P₀,
  intros i H',
  apply eventually_weaken,
  revert_p H', apply H,
end

protected lemma leads_to_cancellation {α} {p q b r : cpred α} {τ : stream α}
    (P₀ : (p ~> q ⋁ b) τ)
    (P₁ : (q ~> r) τ)
    : (p ~> r ⋁ b) τ :=
begin
  intros i h,
  rw [eventually_p_or],
  apply p_or_p_imp_p_or_left,
  { apply eventually_of_leads_to' _ P₁ },
  rw [← eventually_p_or],
  apply P₀ _ h,
end

protected lemma leads_to_disj_rng {α} {t : Sort u}
         {p : t → cpred α} {q} {r : t → Prop} {τ : stream α}
         (h : ∀ i, r i → (p i ~> q) τ)
         : ( (∃∃ i, ↑(r i) ⋀ p i) ~> q ) $ τ :=
begin
  dunfold tl_leads_to,
  { rw [p_exists_range_subtype r p,p_exists_p_imp,henceforth_forall],
    simp,
    intro i,
    apply h _ i.property, },
end

protected theorem leads_to_disj {α t}
    {p : t → cpred α}
    {q : cpred α}
    {τ : stream α}
    (P₀ : ∀ i, p i ~> q $ τ)
    : (∃∃ i, p i) ~> q $ τ :=
begin
  have P₁ : ∀ i : t, (λ _, true) i → (◻(p i ⟶ ◇q)) τ,
  { intros i h, apply P₀, },
  have P₂ := @temporal.leads_to_disj_rng _ _ _ _ (λ _, true) _ P₁,
  have P₃ : (∃∃ (i : t), ↑((λ _, true) i) ⋀ p i) = (∃∃ i, p i),
  { apply p_exists_congr,
    intro,
    apply True_p_and },
  rw [P₃] at P₂,
  apply P₂
end

protected lemma induction {α}
  {τ : stream α} (f : α → β) (p q : cpred α)
  [decidable_pred p]
  {lt : β → β → Prop}
  (wf : well_founded lt)
  (P : ∀ v, p ⋀ •eq v ∘ f  ~>  p ⋀ •flip lt v ∘ f ⋁ q $ τ)
: (p ~> q) τ :=
begin
  have h₂ : ∀ V, ((p ⋀ •eq V ∘ f) ~> q) τ,
  { intro V,
    apply well_founded.induction wf V _,
    intros x IH,
    have Hq : q ⋁ q ⟹ q,
    { pointwise, simp [or_self], },
    apply temporal.leads_to_strengthen_rhs _ Hq,
    apply temporal.leads_to_cancellation (P _),
    have h' : (p ⋀ •flip lt x ∘ f) = (∃∃v, ↑(flip lt x v) ⋀ (p ⋀ (•↑(eq v) '∘ f))),
    { funext1,
      TL_simp [function.comp,init], },
    rw h',
    apply @temporal.leads_to_disj_rng _ β ,
    apply IH, },
  have h₃ := temporal.leads_to_disj h₂,
  have h₄ : (∃∃ (i : β), (λ (V : β), p ⋀ •eq V ∘ f) i) = p,
  { funext1 i, TL_simp [function.comp,init,exists_one_point_right (f $ i 0)], },
  rw h₄ at h₃,
  apply h₃,
end

section inf_often_induction'

parameters {α' β' : Type}
parameters {τ : stream α'} (V : α' → β') (p q : pred' α')
parameters {lt : β' → β' → Prop}
parameters (wf : well_founded lt)

def le (x y : β') := lt x y ∨ x = y

include wf

lemma inf_often_induction'
  (S₀ : ∀ v, (◻◇•(↑(eq v) '∘ V)) τ → (◇◻•↑(eq v) '∘ V) τ ∨ (◻◇•(↑(flip lt v ∘ V) ⋁ q)) τ)
  (P₁ : ∀ v, (•(p ⋀ ↑(eq v) '∘ V) ~> •(↑(flip lt v ∘ V) ⋁ q)) τ)
: (◻◇•p) τ → (◻◇•q) τ :=
begin
  have Hex : ∀ (v : β'), ((•(p ⋀ eq v ∘ V) ~> (•q ⋁ ◻•-p))) τ,
  { intro v,
    apply well_founded.induction wf v _, clear v,
    intros v IH,
    have IH' := temporal.leads_to_disj_rng IH,
    have H : (∃∃ (i : β'), ↑((λ (y : β'), lt y v) i) ⋀ (λ (y : β'), •(p ⋀ eq y ∘ V)) i)
             = •(flip lt v ∘ V ⋀ p),
    { clear IH' IH S₀ P₁,
      funext τ,
      TL_simp [init,flip,function.comp],
      rw [exists_one_point_right (V $ τ 0)],
      simp [eq_true_intro (@rfl _ (V $ τ 0))],
      intro,
      apply implies.trans and.elim_right
      ; admit },
    rw H at IH', clear IH H,
    have S₂ : ∀ (v : β'), (◻◇•↑(flip lt v) '∘ V) τ → (◇◻•↑(flip lt v) '∘ V) τ ∨ (◻◇•(↑(flip lt v) '∘ V ⋁ q)) τ,
    { admit },
    have S₁ : ∀ (v : β'), (•↑(eq v) '∘ V  ~> (◻•↑(eq v) '∘ V) ⋁ (◻◇•(flip lt v ∘ V ⋁ q))) τ,
    { admit }, clear S₀,
    have H₁ : (•(p ⋀ eq v ∘ V) ~> •(flip lt v ∘ V ⋀ p) ⋁ •q) τ, admit,
--    have H₂ : (•(flip lt v ∘ V ⋀ p) ~> •q) τ , admit,
    have H₃ := temporal.leads_to_cancellation H₁ IH',
--     have H₀ := @temporal.leads_to_trans _ (•(p ⋀ eq v ∘ V)) _ _ _ H₁ IH',
--     clear S₀,
--     have H₃ : (•(p ⋀ eq v ∘ V) ~> •q ⋁ ◻•-p) τ, admit,
-- --    apply temporal.leads_to_cancellation _ _, },
    admit },
  have H := @temporal.leads_to_disj _ _ (λ v, •(p ⋀ eq v ∘ V)) (•q ⋁ ◻•-p) τ Hex,
  have H' : (∃∃ (v : β'), •p ⋀ •(eq v ∘ V)) = •p,
  { funext τ, TL_simp [init,function.comp,exists_one_point_right (V $ τ 0)] },
  dsimp [tl_leads_to] at H,
  rw [H',p_or_comm] at H,
  intros h,
  have H₁ := inf_often_of_leads_to H h,
  rw [inf_often_p_or] at H₁,
  cases H₁ with H₁ H₁,
  { exfalso, revert h,
    change ¬ (◻◇•p) τ, rw p_not_eq_not,
    rw [not_henceforth,not_eventually,not_init],
    revert_p H₁, apply henceforth_str },
  { apply H₁ },
end

end inf_often_induction'

section inf_often_induction

parameters {α' : Type*} {β' : Type*}
parameters {τ : stream α'} (f : α' → β') (p q : pred' α')
parameters {lt : β' → β' → Prop}
parameters (wf : well_founded lt)
parameters (h₀ : (◻◇•p) τ)
parameters (h₁ : (◻⟦ λ s s', q s' ∨ lt (f s') (f s) ∨ (¬ p s' ∧ f s = f s') ⟧) τ)

def EQ (v : β') : pred' α' := eq v ∘ f
def LT (v : β') : pred' α' := flip lt v ∘ f

include h₁
section Q
parameters v : β'
lemma Q : ◻(•EQ v ⟶ ◇•(LT v ⋁ q) ⋁ ◻•EQ v) $ τ :=
begin
  apply induct_evt,
  rw [← init_p_or,next_init_eq_action,init_eq_action,← action_imp],
  revert_p h₁,
  monotonicity1,
  refine action_entails_action _ _ _,
  TL_simp [LT,EQ,comp,flip],
  intros s s' h₂ h₃,
  intros, subst v, revert h₂, monotonicity1,
  begin [smt] intros,eblast end,
end
-- set_option pp.all true
lemma  Q' : ◻(•EQ v ⟶ ◇(◻•LT v ⋁ •q) ⋁ ◻•EQ v) $ τ :=
begin
  have Q := Q f p q h₁ v,
  revert_p Q, rw init_p_or,
  monotonicity_n 2,
  monotonicity,
  admit, -- apply p_or_p_imp_p_or' _, apply entails_refl _, monotonicity1,
end
end Q
include h₀
lemma P : ∀ v, •(p ⋀ EQ v)  ~>  •(p ⋀ LT v ⋁ q) $ τ :=
begin
  intros v i Hp,
  have H₂ : (◻◇⟦λ (s s' : α'), p s' ∧ (q s' ∨ lt (f s') (f s))⟧) τ := sorry,
  have Q := Q f _ _ h₁ v _ Hp.right,
  -- have Q' := Q' f _ _ h₁ v _ Hp.right,
  rw [init_p_or,eventually_p_or] at Q,
  rcases Q with ⟨ Q' | Q'⟩  | Q',
  { revert_p [weak_coincidence (henceforth_delay i h₀) Q'],
    -- transitivity, apply henceforth_str,
    monotonicity, simp, propositional, admit },
  { revert_p [Q'], monotonicity, propositional, },
  { rw [← action_and_action,← action_or_action,← next_init_eq_action,← next_init_eq_action,action_eq_next] at H₂,
    rw ← eventually_eventually,
    revert_p [henceforth_str' i H₂,Q'], clear H₂,
    TL_monotonicity, distributivity (⋀),
    admit, }
    -- apply p_or_entails_of_entails,
    -- { apply_left p_and_elim_right,
    --   apply_left next_entails_eventually,
    --   monotonicity p_or_intro_right _ _, },
    -- { rw p_and_over_p_exists_left,
    --   apply p_exists_elim _ , intro x,
    --   apply_left next_entails_eventually,
    --   monotonicity, apply_right p_or_intro_left, },
    -- apply p_exists_elim _, intro, pointwise with τ h₀ h₁,
    -- have h₂ : f x = v, admit,
    -- rw h₂ at h₀, rw ← eventually_eventually,
    -- revert_p h₀, monotonicity,
    -- transitivity, apply p_and_elim_right,
    -- transitivity, apply next_entails_eventually,
    -- let LT := LT f, -- p ⋀ (q ⋁ LT v)
    -- monotonicity, change (p ⋀ (q ⋁ ↑λ s', _) ⟹ p ⋀ LT v ⋁ q),  },
end

include wf
lemma inf_often_induction
: (◻◇•q) τ :=
begin
  apply inf_often_of_leads_to _ h₀,
  have inst : decidable_pred (•p) := λ _, classical.prop_decidable _,
  have P := P f p q h₀ h₁,
  apply temporal.induction f (•p) (•q) wf P,
end
end inf_often_induction

lemma congr_inf_often_trace {α} {x : α} {τ : stream α} (f : α → β)
  (Hinj : injective f)
: (◻◇•(eq x : pred' α)) τ ↔ (◻◇•(eq (f x) : pred' β)) (map f τ) :=
begin
  let EQ_f := (eq (f x) : pred' β),
  rw [ comp_map_app_eq_map (◻◇•EQ_f) f τ ],
  rw [ (henceforth_trading f (◇•EQ_f)).symm ],
  rw [ (eventually_trading f (•EQ_f)).symm  ],
  rw [ (init_trading f (eq (f x))).symm ],
  have H : EQ_f '∘ f = eq x,
  { funext y,
    simp,
    split,
    { apply Hinj },
    apply congr_arg },
  rw H,
end

lemma events_to_states {lbl : Type u} (s : stream lbl)
  (act : lbl → β → β → Prop) {τ : stream β}
  (h : ∀ i, act (s i) (τ i) (τ (succ i)))
  (e : lbl)
: (◻◇•(eq e : pred' lbl)) s → (◻◇⟦act e⟧) τ :=
begin
  intros h' i,
  cases h' i with j h',
  TL_simp [drop_drop, init_drop] at h',
  TL_simp [eventually], existsi j,
  simp [drop_drop,action,action_drop,h',drop],
  apply h,
end

attribute [irreducible] next init

end temporal

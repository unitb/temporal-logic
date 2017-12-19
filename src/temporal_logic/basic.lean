
import util.predicate

@[user_attribute]
meta def strengthening_attr : user_attribute :=
{ name := `strengthening
, descr := "
Strenghtening lemmas to facilitate the stripping of small details in application.
Expected shape `∀ p : pred' α, ⊩ f p ⟶ g p`
" }

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
[`predicate.lifted₀
,`coe,`lift_t,`lift,`has_lift_t,`coe_t,`coe,`has_coe_t
,`coe_b,`coe,`has_coe,`coe_fn,`coe,`has_coe_to_fun
,`coe_sort,`coe,`has_coe_to_sort,`predicate.lifted₀]

meta def TL_simp
   (only_kw : parse only_flag)
   (args : parse simp_arg_list)
   (w : parse with_ident_list)
   (loc : parse location) : tactic unit :=
do std_lmm ← mmap (map (simp_arg_type.expr ∘ to_pexpr) ∘ mk_const) (coes_thms ++ [`predicate.pred'.apply,`temporal.init_to_fun]) ,
   repeat (simp only_kw args w loc <|> simp only_kw std_lmm w loc <|> unfold_coes loc <|> unfold [`predicate.pred'.apply,`predicate.lifted₀] loc)

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
⟨ λ τ, ∃ i, p.apply (τ.drop i) ⟩
def henceforth (p : cpred β) : cpred β :=
⟨ λ τ, Π i, p.apply (τ.drop i) ⟩
def next (p : cpred β) : cpred β :=
⟨ λ τ, p.apply τ.tail ⟩
def init (p : pred' β) : cpred β :=
⟨ λ τ, p.apply (τ 0) ⟩

prefix `•`:85 := init
prefix `⊙`:90 := next
prefix `◇`:95 := eventually -- \di
prefix `◻`:95 := henceforth -- \sqw
notation `⟦`:max act `⟧`:0 := action act
-- notation `⦃` act `⦄`:95 := ew act

lemma init_to_fun (p : pred' β) (τ : stream β) : (•p).apply τ = p.apply (τ 0) := rfl

def tl_leads_to (p q : cpred β) : cpred β :=
◻(p ⟶ ◇q)

infix ` ~> `:55 := tl_leads_to

@[reducible]
def tl_imp (h p q : cpred β) : Prop :=
ctx_impl (◻ h) p q

lemma tl_imp_intro (h : cpred β) {p q : cpred β}
  (h' : ◻h ⟹ (p ⟶ q))
: tl_imp h p q :=
begin
  constructor, intro,
  exact (h' True).apply σ trivial,
end

lemma tl_imp_elim (h : cpred β) {p q : cpred β}
  (h' : tl_imp h p q)
: ◻h ⟹ (p ⟶ q) :=
begin
  intro, revert Γ,
  apply intro_p_imp h',
end

lemma tl_imp_intro' (h : cpred β) {p q : cpred β}
  (h' : p ⟹ q)
: tl_imp h p q :=
h' _

@[simp]
lemma hence_true : ◻(True : cpred β) = True :=
begin
  funext1,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

lemma tl_imp_elim' {p q : cpred β}
  (h : tl_imp True p q)
: p ⟹ q :=
begin
  simp [tl_imp,ctx_impl] at h,
  apply h,
end

@[strengthening]
lemma eventually_weaken (p : cpred β)
: (p ⟹ ◇ p) :=
begin
  pointwise with τ h,
  unfold eventually pred'.apply,
  existsi 0,
  apply h
end
open stream
-- lemma eventually_weaken' {p : cpred β} {τ} (i) :
--   p (drop i τ) → (◇ p) τ :=
-- begin
--   intros h,
--   TL_unfold eventually,
--   existsi i,
--   apply h
-- end

-- lemma eventually_of_next {p : cpred β}
-- : ⊙p ⟹ ◇p :=
-- sorry

@[strengthening]
lemma next_entails_eventually (p : cpred β)
: ⊙p ⟹ ◇p :=
sorry

@[strengthening]
lemma henceforth_str (p : cpred β) :
  (◻p ⟹ p) :=
begin
  pointwise with τ h, apply h 0
end

-- lemma henceforth_str' {p : cpred β} {τ} (i) :
--   (◻p) τ → p (drop i τ) :=
-- begin
--   intros h, apply h i
-- end

-- lemma henceforth_delay {p : cpred β} {τ} (i) :
--   (◻p) τ → (◻p) (drop i τ) :=
-- begin
--   intros h j, simp [drop_drop], apply h
-- end

lemma init_eq_action {p : pred' β}
: •(p : pred' β) = ⟦ λ s s', s ⊨ p ⟧ :=
rfl

lemma next_init_eq_action {p : pred' β}
: ⊙•(p : pred' β) = ⟦ λ s s', s' ⊨ p ⟧ :=
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
  ; unfold eventually
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

-- lemma henceforth_drop {p : cpred β} {τ} (i : ℕ) :
-- (◻p) τ → (◻p) (τ.drop i) :=
-- begin
--   intro h,
--   rw ← henceforth_henceforth at h,
--   apply h,
-- end

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
  unfold tl_imp ctx_impl at ⊢ f,
  pointwise f with τ h',
  apply exists_imp_exists,
  intro i,
  apply f,
  rw ← henceforth_henceforth at h',
  apply h',
end

@[monotonic]
lemma eventually_entails_eventually {p q : cpred β}
  (f : p ⟹ q)
: (◇p) ⟹ (◇q) :=
begin
  apply tl_imp_elim',
  monotonicity (tl_imp_intro' _ f),
end

lemma eventually_imp_eventually {p q : cpred β} {Γ}
 (f : Γ ⊢ ◻ (p ⟶ q))
: Γ ⊢ (◇p) ⟶ (◇q) :=
begin
  constructor, introv hΓ,
  apply exists_imp_exists,
  intro i,
  apply f.apply _ hΓ,
end

@[monotonic]
lemma henceforth_tl_imp_henceforth {h p q : cpred β}
  (f : tl_imp h p q)
: tl_imp h (◻p) (◻q) :=
begin
  unfold tl_imp ctx_impl at *,
  pointwise f with τ h',
  TL_simp [henceforth], intro_mono i,
  apply f ,
  rw ← henceforth_henceforth at h',
  apply  h',
end

@[monotonic]
lemma henceforth_entails_henceforth {p q : cpred β}
  (f : p ⟹ q)
: (◻p) ⟹ (◻q) :=
begin
  refine tl_imp_elim' _,
  monotonicity (tl_imp_intro' _ f),
end

lemma henceforth_imp_henceforth {p q : cpred β} {Γ}
  (h : Γ ⊢ ◻ (p ⟶ q))
: Γ ⊢ (◻p) ⟶ (◻q) :=
begin
  pointwise h with τ,
  specialize h τ, simp [henceforth] at ⊢ h,
  introv h₀ h₁,
  auto,
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

lemma henceforth_forall (P : α → cpred β)
: ◻(∀∀ x, P x) = ∀∀ x, ◻P x :=
begin
  funext1,
  TL_simp [henceforth,p_forall],
  rw forall_swap,
end

@[simp]
lemma not_eventually {β} (p : cpred β)
: (-◇p) = (◻-p) :=
begin
  funext1,
  TL_simp [henceforth,not_forall_iff_exists_not,eventually],
end

end temporal
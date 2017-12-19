
import data.stream

import util.meta.tactic
import util.logic
import util.predicate

import unitb.semantics.tactic

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

class persistent (p : cpred β) : Prop :=
  (is_persistent : ◻p = p)
export persistent (is_persistent)

instance henceforth_persistent {p : cpred β} : persistent (◻p) :=
by { constructor, simp }

instance leads_to_persistent {p q : cpred β} : persistent (p ~> q) :=
by { constructor, simp [tl_leads_to,is_persistent] }

instance and_persistent {p q : cpred β} [persistent p] [persistent q]
: persistent (p ⋀ q) :=
by { constructor, simp [henceforth_and,is_persistent], }

instance true_persistent
: persistent (True : cpred β) :=
by { constructor, simp, }

instance false_persistent
: persistent (False : cpred β) :=
by { constructor, simp, }

instance forall_persistent {p : α → cpred β} [∀ i, persistent (p i)]
: persistent (p_forall p) :=
by { constructor, simp [henceforth_forall,is_persistent], }

def list_persistent (xs : list $ cpred β) :=
Π q ∈ xs, persistent q

lemma nil_persistent
: @list_persistent β [] :=
by { intros p h, cases h }

lemma cons_persistent (x : cpred β) (xs : list $ cpred β)
  [persistent x]
  (h : list_persistent xs)
: list_persistent (x :: xs) :=
by { intros p h, simp [list_persistent] at *,
     cases h ; [ subst p, skip ] ; auto, }

def with_h_asms {β} (Γ : cpred β) : Π (xs : list (cpred β)) (x : cpred β), Prop
 | [] x := Γ ⊢ x
 | (x :: xs) y := Γ ⊢ x → with_h_asms xs y

lemma indirect_judgement (h p : pred' β)
  (H : ∀ Γ, Γ ⊢ h → Γ ⊢ p)
: h ⊢ p :=
sorry

lemma judgement_trans (p q r : pred' β)
  (h₀ : p ⊢ q)
  (h₁ : q ⊢ r)
: p ⊢ r :=
sorry

lemma to_antecendent (xs : list (cpred β))
  [list_persistent xs]
  (p : cpred β)
  (h : ◻ xs.foldr (⋀) True ⊢ p)
: ∀ Γ, with_h_asms Γ xs p :=
begin
  intro,
  replace h := λ h', judgement_trans Γ _ _ h' h,
  induction xs with x xs,
  { simp at h, simp [with_h_asms,h], },
  { simp at h, simp_intros [with_h_asms],
    have _inst_2 : persistent x,
    { apply _inst_1, simp, },
    replace _inst_1 : Π (q : cpred β), q ∈ xs → persistent q,
    { intros, apply _inst_1, right, xassumption, },
    apply @ih_1 _inst_1, intros,
    apply h,
    begin [temporal]
      rw henceforth_and,
      split, simp [is_persistent,a],
      assumption
    end }
end

lemma from_antecendent (xs : list (cpred β)) (p : cpred β)
  (h : ∀ Γ, with_h_asms Γ xs p)
: ◻ xs.foldr (⋀) True ⊢ p :=
begin
  apply indirect_judgement,
  introv h', specialize h Γ,
  induction xs with x xs,
  { simp [with_h_asms] at h, apply h },
  { simp [list.foldr,henceforth_and] at h',
    apply ih_1,
    { revert h',
      apply p_impl_revert,
      apply p_and_elim_right },
    { apply h, revert h',
      apply p_impl_revert,
      apply p_and_entails_of_entails_left,
      apply henceforth_str, } }
end

lemma persistent_to_henceforth {p q : cpred β}
  (h : ◻ p ⊢ q)
: ◻ p ⊢ ◻ q :=
sorry

/- end monotonicity -/

instance has_coe_to_fun_henceforth (Γ p q : cpred β) : has_coe_to_fun (Γ ⊢ ◻(p ⟶ q)) :=
{ F := λ _, Γ ⊢ p → Γ ⊢ q
, coe := assume h, henceforth_str (p ⟶ q) Γ h  }

instance has_coe_to_fun_leads_to (Γ p q : cpred β) : has_coe_to_fun (Γ ⊢ p ~> q) :=
temporal.has_coe_to_fun_henceforth _ _ _

section
open tactic tactic.interactive (unfold_coes unfold itactic assert_or_rule)
open interactive interactive.types lean lean.parser
open applicative (mmap₂ lift₂)
open has_map
local postfix `?`:9001 := optional

meta def is_henceforth (e : expr) : temporal bool :=
do `(_ ⊢ %%t) ← infer_type e,
   succeeds $
     to_expr ``(persistent %%t) >>= mk_instance

meta def interactive.persistent (excp : parse without_ident_list) : temporal unit :=
do hs  ← get_assumptions,
   hs' ← hs.mfilter (map bnot ∘ is_henceforth),
   excp' ← mmap get_local excp,
   mmap' tactic.clear (hs'.diff excp')

private meta def mk_type_list (Γ pred_t : expr)  : list expr → temporal (expr × expr)
 | [] := do
   u ← mk_meta_univ,
   v ← mk_meta_var (expr.sort u),
   lift₂ prod.mk (to_expr ``(@list.nil $ cpred %%v))
                 (to_expr ``(@temporal.nil_persistent %%v))
 | (x :: xs) :=
   do (es,is) ← mk_type_list xs,
      v  ← mk_meta_var pred_t,
      `(_ ⊢ %%c) ← infer_type x, c' ← pp c,
      ls ← to_expr ``(list.cons %%c %%es),
      inst₀ ← to_expr ``(persistent %%c) >>= mk_instance,
      inst ← tactic.mk_mapp `temporal.cons_persistent [none,c,es,inst₀,is],
      return (ls,inst)

meta def persistently {α} (tac : temporal α) : temporal α :=
do asms ← get_assumptions,
   `(%%Γ ⊢ %%p) ← target >>= instantiate_mvars,
   pred_t ← infer_type Γ,
   Γ ← get_local Γ.local_pp_name,
   r ← tactic.revert_lst (Γ :: asms).reverse,
   guard (r = asms.length + 1) <|> fail format!"wrong use of context {Γ}",
   (asms',inst) ← mk_type_list Γ pred_t asms,
   ts ← mmap consequent asms,
   h ← to_expr  ``(@to_antecendent _ %%asms' %%inst %%p) >>= note `h none,
   `[simp only [temporal.with_h_asms] at h],
   refine ```(h _),
   get_local `h >>= tactic.clear,
      -- calling tac
   x ← focus1 tac,
      -- restore context to Γ
   to_expr ```(_ ⊢ _) >>= change,
   `(_ ⊢ %%q) ← target,
   refine ``(from_antecendent %%asms' %%q _),
   `[simp only [temporal.with_h_asms]],
   Γ ← tactic.intro Γ.local_pp_name,
   mmap₂ (λ l t : expr, do
      let n := l.local_pp_name,
      tactic.intro n,
      h ← get_local l.local_pp_name,
      tactic.interactive.change ``(%%Γ ⊢ %%t) none (loc.ns [some n]))
    asms ts,
   return x

#check henceforth
#check @persistent_to_henceforth
meta def interactive.henceforth (loc : parse location) : temporal unit :=
do when loc.include_goal $
     persistently (do
       refine ``(persistent_to_henceforth _)),
   loc.apply
     (λ h, do b ← is_henceforth h,
              when (¬ b) $ fail format!"{h} is not of the shape `□ _`",
              to_expr ``(p_impl_revert (henceforth_str _ _) %%h)
                >>= note h.local_pp_name none,
              tactic.clear h)
     (pure ())

meta def monotonicity1 : temporal unit :=
do asms ← get_assumptions,
   ex ← list.band <$> asms.mmap is_henceforth,
   trace ex,
   if ex
   then persistently $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          tactic.interactive.monotonicity1
   else tactic.interactive.monotonicity1

meta def monotonicity (e : parse assert_or_rule?) : temporal unit :=
do asms ← get_assumptions,
   ex ← list.band <$> asms.mmap is_henceforth,
   if ex
   then persistently $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          guard (e.is_none) <|> fail "rules not supported with in persistent constexts",
          tactic.interactive.monotonicity none
   else tactic.interactive.monotonicity e

meta def timeless (h : expr) : temporal (option name) :=
do try $ interactive.henceforth (loc.ns [some h.local_pp_name]),
   h ← get_local h.local_pp_name,
   `(%%Γ' ⊢ %%p) ← infer_type h | return none,
   `(•%%p) ← return p | none <$ clear h,
   some h.local_pp_name <$ temporal.revert h

meta def interactive.note
   (h : parse ident?)
   (q₁ : parse (tk ":" *> texpr))
   (_ : parse $ tk ",")
   (tac : tactic.interactive.itactic)
: tactic expr :=
do `(%%Γ ⊢ _) ← target,
   h' ← temporal.interactive.«have» h q₁ none,
   solve1 (do
     xs ← local_context >>= mmap timeless,
     let n := xs.filter_map id,
     tactic.revert Γ,
     refine ``(ew_wk _),
     τ ← intro1,
     try $ temporal.interactive.simp tt [] [`predicate] (loc.ns [none]) ,
     try $ tactic.interactive.TL_unfold [`init] (loc.ns [none]),
     try $ tactic.interactive.generalize none (``(%%τ 0),`σ),
     target >>= beta_reduction >>= change,
     intro_lst n,
     tac),
   tactic.revert h',
   refine ``(lifting_prop_asm %%Γ _),
   tactic.intro h'.local_pp_name

open tactic.interactive (rw_rules rw_rules_t rw_rule get_rule_eqn_lemmas to_expr')
open temporal.interactive (rw)

meta def interactive.rw_using
   (p  : parse cur_pos)
   (q₁ : parse (tk ":" *> texpr))
   (l : parse location)
   (_ :  parse $ tk ",")
   (tac : tactic.interactive.itactic)
: tactic unit :=
do h ← mk_fresh_name,
   h ← temporal.interactive.note h q₁ () tac,
   let rs : rw_rules_t := ⟨[{ rw_rule
                            . pos := p
                            , symm := ff
                            , rule := to_pexpr h }],none⟩,
   rw rs l,
   try (tactic.clear h)

meta def interactive.«suffices» (h : parse ident?) (t : parse (tk ":" *> texpr)?) : tactic unit :=
interactive.«have» h t none >> tactic.swap

run_cmd do
  let ls := [`monotonicity,`monotonicity1],
  ls.for_each $ λ l, do
    env    ← get_env,
    d_name ← resolve_constant l,
    (declaration.defn _ ls ty val hints trusted) ← env.get d_name,
    (name.mk_string h _) ← return d_name,
    let new_name := `temporal.interactive <.> h,
    add_decl (declaration.defn new_name ls ty (expr.const d_name (ls.map level.param)) hints trusted)

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

run_cmd add_interactive [`TL_monotonicity,`TL_context]

lemma henceforth_next (p : cpred β)
: ◻p ⟹ ◻⊙p :=
begin [temporal]
  rw henceforth_next_intro p,
  monotonicity, simp,
  intros, assumption
end

lemma next_eventually_comm (p : cpred β)
: ⊙◇p = ◇⊙p :=
begin
  lifted_pred [next,eventually,tail],
  apply exists_congr, simp_intros,
  apply eq.to_iff, apply congr_arg,
  funext i, simp [nth,drop],
end

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
lemma not_init (p : pred' β) : (-•p) = •-p :=
begin
  funext1,
  TL_simp [init],
end

lemma next_or (p q : cpred β)
: ⊙(p ⋁ q) = ⊙p ⋁ ⊙q :=
rfl

open nat

-- lemma action_drop (A : act β) (τ : stream β) (i : ℕ)
-- : ⟦ A ⟧ (τ.drop i) ↔ A (τ i) (τ $ succ i) :=
-- by { unfold drop action, TL_simp [action] }

-- lemma init_drop (p : pred' β) (τ : stream β) (i : ℕ)
-- : (• p) (τ.drop i) ↔ p (τ i)  :=
-- by { unfold drop action, simp [init_to_fun] }

-- lemma next_init (p : pred' β) (τ : stream β)
-- : (⊙•p) τ = p (τ 1) :=
-- rfl

@[simp]
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

private meta def goal_flag := tt <$ tk "⊢" <|> tt <$ tk "|-" <|> pure ff

meta def interactive.eventually (h : parse ident) (goal : parse goal_flag) : temporal unit :=
do `(%%Γ ⊢ ◇%%p) ← target <|> fail format!"expecting a goal of the form `◇ _`",
   h' ← get_local h,
   infer_type h' >>= trace,
   `(%%Γ' ⊢ %%q) ← infer_type h' <|> fail format!"{h} should be a temporal formula",
   is_def_eq Γ Γ',
   when (¬ goal) $
     to_expr ``((eventually_eventually %%p).symm) >>= tactic.rewrite_target,
   revert h',
   monotonicity1,
   () <$ intro (some h)

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
  ; [eventually h₀ ⊢,eventually h₁ ⊢]
  ; henceforth at h₀ h₁ ⊢
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
  have H := henceforth_delay Hp Hq,
  clear Hp Hq, rw ← eventually_inf_often,
  eventually H ⊢,
  rw [← henceforth_henceforth p,← henceforth_and] at H,
  henceforth at H ⊢,
  cases H with H₀ H₁,
  eventually H₁ ⊢,
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

-- lemma entail_contrapos {p q : pred' β} : p ⟹ q → (-q) ⟹ -p :=
-- begin
--   intros h τ hnq hp,
--   apply hnq,
--   apply h _ hp,
-- end

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
: (∀∀ x : t, ◻•(eq x ∘ V) ⟶ P (const x) : cpred β) = ↑(λ (s : stream β), s ⊨ P (map V s)) :=
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

lemma henceforth_trading {α} (f : α → β) (p : cpred β)
: (◻ (p '∘ map f)) = (◻ p) '∘ map f :=
begin
  funext1,
  unfold comp henceforth,
  apply forall_congr, intro i,
  TL_simp,
  refl,
end

lemma eventually_trading {α} (f : α → β) (p : cpred β)
: (◇ (p '∘ map f)) = (◇ p) '∘ map f :=
begin
  funext1,
  unfold comp eventually,
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
by { rw [action_trading,eventually_trading,henceforth_trading], refl }

lemma stable_trace_trading {α} (τ : stream α) (f : α → β) (p : cpred β)
: τ ⊨ ◇◻(p '∘ map f) = map f τ ⊨ ◇◻p :=
by { rw [henceforth_trading,eventually_trading], refl }

lemma stable_trace_init_trading {α} (τ : stream α) (f : α → β) (p : pred' β)
: τ ⊨ ◇◻•(p '∘ f) = map f τ ⊨ ◇◻•p :=
by { rw [init_trading,henceforth_trading,eventually_trading], refl }


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
  { right, assumption },
  { left, apply P₁ h },
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

protected lemma induction {α}
  {Γ : cpred α} (f : α → β) (p q : cpred α)
  {lt : β → β → Prop}
  (wf : well_founded lt)
  (P : Γ ⊢ ∀∀ v, p ⋀ •eq v ∘ f  ~>  p ⋀ •flip lt v ∘ f ⋁ q)
: Γ ⊢ p ~> q :=
begin [temporal]
  have h₂ : ∀∀ V, (p ⋀ •eq V ∘ f) ~> q,
  { intro V,
    wf_induction V using wf,
    apply temporal.leads_to_strengthen_rhs _ _,
    show q ⋁ q ⟹ q,
    { simp [or_self], },
    apply temporal.leads_to_cancellation (P _),
    rw_using : (p ⋀ •flip lt x ∘ f) = (∃∃v, ↑(flip lt x v) ⋀ (p ⋀ (•↑(eq v) '∘ f))),
    { funext1,
      TL_simp [function.comp,init] },
    apply @temporal.leads_to_disj_rng _ β ,
    apply ih_1, },
  have h₃ := temporal.leads_to_disj h₂,
  rw_using : (∃∃ (i : β), (λ (V : β), p ⋀ •eq V ∘ f) i) = p at h₃,
  { funext1 i, TL_simp [function.comp,init,exists_one_point_right (f $ i 0)], },
end

section inf_often_induction'

parameters {α' β' : Type}
parameters {Γ : cpred α'} (V : α' → β') (p q : pred' α')
parameters {lt : β' → β' → Prop}
parameters (wf : well_founded lt)

def le (x y : β') := lt x y ∨ x = y

include wf

lemma inf_often_induction'
  (S₀ : Γ ⊢ ∀∀ v, ◻◇•(↑(eq v) '∘ V) ⟶ ◇◻•↑(eq v) '∘ V ⋁ ◻◇•(↑(flip lt v ∘ V) ⋁ q))
  (P₁ : Γ ⊢ ∀∀ v, •(p ⋀ ↑(eq v) '∘ V) ~> •(↑(flip lt v ∘ V) ⋁ q))
: Γ ⊢ ◻◇•p ⟶ ◻◇•q :=
begin [temporal]
  have Hex : ∀∀ (v : β'), •(p ⋀ eq v ∘ V) ~> (•q ⋁ ◻•-p),
  { intro v,
    wf_induction v using wf with v,
    have IH' := temporal.leads_to_disj_rng ih_1, clear ih_1,
    rw_using : (∃∃ (i : β'), ↑(lt i v) ⋀ •(p ⋀ eq i ∘ V))
             = •(flip lt v ∘ V ⋀ p) at IH',
    { funext τ,
      TL_simp [init,flip,function.comp], },
    have S₂ : ∀∀ (v : β'), ◻◇•↑(flip lt v) '∘ V ⟶ ◇◻•↑(flip lt v) '∘ V ⋁ ◻◇•(↑(flip lt v) '∘ V ⋁ q),
    { admit },
    have S₁ : ∀∀ (v : β'), •↑(eq v) '∘ V  ~> (◻•↑(eq v) '∘ V) ⋁ (◻◇•(flip lt v ∘ V ⋁ q)),
    { admit }, clear S₀,
    have H₁ : •(p ⋀ eq v ∘ V) ~> •(flip lt v ∘ V ⋀ p) ⋁ •q, admit,
--    have H₂ : (•(flip lt v ∘ V ⋀ p) ~> •q) τ , admit,
    have H₃ := temporal.leads_to_cancellation H₁ IH',
--     have H₀ := @temporal.leads_to_trans _ (•(p ⋀ eq v ∘ V)) _ _ _ H₁ IH',
--     clear S₀,
--     have H₃ : (•(p ⋀ eq v ∘ V) ~> •q ⋁ ◻•-p) τ, admit,
-- --    apply temporal.leads_to_cancellation _ _, },
    admit },
  have H := @temporal.leads_to_disj _ _ (λ v, •(p ⋀ eq v ∘ V)) (•q ⋁ ◻•-p) _ Hex,
  dsimp [tl_leads_to] at H,
  rw_using : (∃∃ (v : β'), •p ⋀ •(eq v ∘ V)) = •p at H,
  { funext τ, TL_simp [init,function.comp,exists_one_point_right (V $ τ 0)] },
  rw [p_or_comm] at H,
  intros h,
  have H₁ := inf_often_of_leads_to H h,
  rw [inf_often_p_or] at H₁,
  cases H₁ with H₁ H₁,
  { apply H₁ },
  { exfalso, revert h,
    simp, apply H₁, },
end

end inf_often_induction'

section inf_often_induction

parameters {α' : Type*} {β' : Type*}
parameters {Γ : cpred α'} (f : α' → β') (p q : α' → Prop)
parameters {lt : β' → β' → Prop}
parameters (wf : well_founded lt)
parameters (h₀ : Γ ⊢ ◻◇•p)
parameters (h₁ : Γ ⊢ ◻⟦ λ s s', q s' ∨ lt (f s') (f s) ∨ (¬ p s' ∧ f s = f s') ⟧)

def EQ (v : β') : pred' α' := eq v ∘ f
def LT (v : β') : pred' α' := flip lt v ∘ f

include h₁
section Q
variable v : β'
lemma Q : Γ ⊢ ◻(•EQ v ⟶ ◇•(LT v ⋁ q) ⋁ ◻•EQ v) :=
begin [temporal]
  apply induct_evt,
  rw [not_init],
  rw [← init_p_or,next_init_eq_action,init_eq_action,init_eq_action],
  rw [← action_imp,← action_imp],
  henceforth at h₁ ⊢,
  revert h₁,
  apply action_entails_action _ _ _,
  show _,
  { introv h,
    TL_simp [EQ,LT,comp,flip],
    intros h₀ h₁, subst v,
    begin [smt] intros, destruct h, destruct a end, },
end
-- set_option pp.all true
lemma  Q' : Γ ⊢ ◻(•EQ v ⟶ ◇(◻•LT v ⋁ •q) ⋁ ◻•EQ v) :=
begin [temporal]
  have Q := (p_forall_to_fun _ _).mpr (Q f p q h₁),
  -- rw ← henceforth_forall at Q,
  henceforth, intro hv,
  -- rw henceforth_forall at Q,
  have Q' := Q v hv, clear hv,
  revert Q', rw init_p_or,
  monotonicity,
  admit, -- apply p_or_p_imp_p_or' _, apply entails_refl _, monotonicity1,
end
end Q
set_option pp.implicit false
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
  let ACT := λ (s s' : α'), q s' ∨ lt (f s') (f s) ∨ ¬p s' ∧ f s = f s',
  have h₀ : ◇(⟦ACT⟧ ⋀ ⊙•↑p ⋀ •(EQ f v)),
  { suffices : ◇(⟦ACT⟧ ⋀ ⊙•↑p ⋀ •EQ f v) ⋁ ◻•EQ f v,
    { cases this, tactic.swap, assumption,
      rw p_and_comm,
      apply coincidence' a,
      apply coincidence' h₁ h₀, },
    revert Hv, strengthen_to ◻ _,
    apply induct_evt _ _ _,
    clear Hp,
    henceforth,  },
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
  done,
  have h₂ : ◻◇⊙•↑p,
  { rw ← eventually_eventually at h₀, },
  simp at Hp,
  have H₂ : ◻◇⟦λ (s s' : α'), q s' ∨ (p s' ∧ lt (f s') (f s))⟧ := sorry,
  let EQ := EQ f,
  have Q' : ◇•(LT f v ⋁ ↑q) ⋁ ◻•EQ v := Q f _ _ h₁ v Hp.right,
  cases Q' with Q' Q',
  { clear Hp,
    rw ← eventually_eventually,
    henceforth at H₂,
    revert H₂,
    monotonicity,
    simp [action_eq_next],
    intros s Hs,
    henceforth at Q',
    rw_using : f s = v,
    { TL_simp only [init,EQ,temporal.EQ,comp] at Hs,
      subst s, subst v, }, clear Hs Q',
    transitivity,
    apply next_entails_eventually,
    simp [LT,flip,comp],
    monotonicity,
    ac_refl, },
  {  },
  clear Hp,
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

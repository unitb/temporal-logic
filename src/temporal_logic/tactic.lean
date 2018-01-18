
import util.predicate
import util.control.applicative
import util.meta.tactic
import meta.expr

import tactic

import temporal_logic.basic
import temporal_logic.persistent

open predicate

/-
   The auto quotation currently supports two classes of tactics: tactic and smt_tactic.
   To add a new class Tac, we have to
   1) Make sure it is a monad. That is, we have an instance for (monad Tac)
   2) There is a namespace Tac.interactive
   3) There is a definition: Tac.step {α : Type} (t : Tac α) : Tac unit
   4) (Optional) Tac.istep {α : Type} (line0 col0 : nat) (line col : nat) (tac : Tac α) : Tac unit
      Similar to step but it should scope trace messages at the given line/col,
      and ensure that the exception position is after (line0, col0)
   6) There is a definition Tac.save_info (line col : nat) : Tac unit
   7) There is a definition Tac.execute (tac : Tac unit) : tactic unit
   8) There is a definition Tac.execute_with (cfg : config) (tac : Tac unit) : tactic unit
      where config is an arbitrary type.
   TODO(Leo): improve the "recipe" above. It is too ad hoc.
-/

meta def temporal : Type → Type :=
tactic

open format

meta def format.intercalate (x : format) : list format → format :=
format.join ∘ list.intersperse x

meta def unlines : list format → format :=
format.intercalate line

meta instance : monad temporal :=
by { dunfold temporal, apply_instance }

meta instance : monad_fail temporal :=
by { dunfold temporal, apply_instance }

meta instance : alternative temporal :=
by { dunfold temporal, apply_instance }

meta instance andthen_seq : has_andthen (temporal unit) (temporal unit) (temporal unit) :=
by { dunfold temporal, apply_instance }

meta instance andthen_seq_focus : has_andthen (temporal unit) (list (temporal unit)) (temporal unit) :=
by { dunfold temporal, apply_instance }

namespace temporal
open tactic applicative
open interactive
open tactic.interactive (rw_rules rw_rules_t rw_rule get_rule_eqn_lemmas to_expr')
open has_to_tactic_format
open has_map list (filter)
section expr
open expr
variable {elab : bool}
meta def get_app_args_aux' : list (expr elab) → expr elab → list (expr elab)
| r (app f a) := get_app_args_aux' (a::r) f
| r e         := r

meta def get_app_args' : (expr elab) → list (expr elab) :=
get_app_args_aux' []

end expr

meta def guarded {α β} : list (tactic α × tactic β) → tactic β
 | [] := failed
 | ((x,y) :: xs) :=
do x ← try_core x,
   if x.is_some then
     y
   else guarded xs

meta def t_to_expr : pexpr → temporal expr
| e@(expr.app e₀ e₁) :=
   to_expr e <|>
do e' ← t_to_expr e₀,
   guarded
     [ ( to_expr ``(%%e' : _ ⊢ _ ⟶ _) >>= type_check
       , to_expr ``(p_impl_revert %%e' %%e₁))
     , ( to_expr ``(%%e' : _ ⊢ ◻(_ ⟶ _)) >>= type_check
       , to_expr ``(henceforth_deduction %%e' %%e₁))
     , ( to_expr ``(%%e' : _ ⊢ p_forall _) >>= type_check
       , to_expr ``(p_forall_revert %%e' %%e₁))
     , (return (), to_expr ``(%%e %%e₁)) ]
| e := to_expr e

meta def t_to_expr_for_apply (q : pexpr) : temporal expr :=
let aux (n : name) : tactic expr := do
  p ← resolve_name n,
  match p with
  | (expr.const c []) := do r ← mk_const c, save_type_info r q, return r
  | _                 := t_to_expr p
  end
in match q with
| (expr.const c [])          := aux c
| (expr.local_const c _ _ _) := aux c
| _                          := t_to_expr q
end

meta def beta_reduction' : expr → temporal expr
 | (expr.app e₀ e₁) :=
 do e₁ ← beta_reduction' e₁,
    e₀ ← beta_reduction' e₀,
    head_beta $ expr.app e₀ e₁
 | e := expr.traverse beta_reduction' e >>= head_eta

meta def beta_reduction (e : expr) : temporal expr :=
instantiate_mvars e >>= beta_reduction'

meta def succeeds {α} (tac : temporal α) : temporal bool :=
tt <$ tac <|> pure ff

meta def decl_to_fmt (vs : list expr) : expr × option expr → temporal format
| (t,val):=
do vs ← mmap pp vs, t ← pp t,
   let vs' := format.join $ vs.intersperse " ",
   match val with
    | (some val) :=
      do val ← pp val, return format!"{vs'} : {t} := {val}"
    | none := return format!"{vs'} : {t}"
   end

meta def asm_stmt (Γ e : expr) : temporal (expr × expr × option expr) :=
do t ← infer_type e,
   val ← get_local_value e,
   `(%%Γ' ⊢ %%p) ← return t | return (e,t,val),
   ( do is_def_eq Γ Γ',
        return (e,p,val) ) <|> return (e,t,val)

def compact {α β : Type*} [decidable_eq β] : list (α × β) → list (list α × β)
 | [] := []
 | ( (x,y) :: xs ) :=
   match compact xs with
    | [] := [ ([x],y) ]
    | ( (x',y') :: ys ) :=
      if y = y' then (x::x', y) :: ys
                else ([x],y) :: (x',y') :: ys
   end

meta def get_assumptions : temporal (list expr) :=
do `(%%Γ ⊢ _) ← target,
   ls ← local_context,
   mfilter (λ l, succeeds $
    do `(%%Γ' ⊢ %%e) ← infer_type l,
       is_def_eq Γ Γ') ls

meta def temp_to_fmt (g : expr) : temporal format :=
do  set_goals [g],
    `(%%Γ ⊢ %%p) ← target | to_fmt <$> read,
    hs ← local_context,
    hs' ← mmap (asm_stmt Γ) hs,
    hs' ← mfilter (λ x : _ × _, ff <$ is_def_eq Γ x.1 <|> pure tt) hs'
          >>= mmapp decl_to_fmt ∘ compact,
    p ← pp p,
    return $ format.intercalate line [format.intercalate (","++line) hs',format!"⊢ {p}"]

meta def save_info (p : pos) : temporal unit :=
do gs  ← get_goals,
   fmt ← mmap temp_to_fmt gs,
   set_goals gs,
   tactic.save_info_thunk p (λ _,
     if fmt.empty
       then "no goals"
       else format.join (fmt.intersperse $ line ++ line))

meta def step {α : Type} (c : temporal α) : temporal unit :=
c >>[tactic] cleanup

meta def istep {α : Type} (line0 col0 line col : nat) (c : temporal α) : temporal unit :=
tactic.istep line0 col0 line col c

meta def uniform_assumptions' (Γ : expr)
: expr → expr → temporal (option (expr × expr))
| h t := do
   t ← head_beta t,
   match t with
    | (expr.pi n bi t' e) :=
      do l ← mk_local' n bi t',
         (some (p,t)) ← uniform_assumptions' (h l) (e.instantiate_var l) | return none,
         let abs := t.lambdas [l],
         let p' := p.lambdas [l],
         p ← some <$> (prod.mk <$> to_expr ``( (p_forall_to_fun %%Γ %%abs).mpr %%p' )
                               <*> to_expr ``( p_forall %%abs )),
         return p
    | `(%%Γ' ⊢ %%p) := (is_def_eq Γ Γ' >> some (h,p) <$ guard (¬ Γ.occurs p))
    | p := guard (¬ Γ.occurs p) >> pure none
   end

meta def uniform_assumptions (Γ h : expr) : temporal unit :=
do t ← infer_type h,
   (some r) ← try_core (uniform_assumptions' Γ h t) | clear h,
   match r with
    | (some (pr,t)) :=
          do  p ← to_expr ``(%%Γ ⊢ %%t),
              assertv h.local_pp_name p pr,
              clear h
    | none := return ()
   end

meta def semantic_assumption (τ h : expr) : temporal ℕ :=
do `(%%τ' ⊨ _) ← infer_type h | return 0,
   (do is_def_eq τ τ',
       revert h, `[rw ← eq_judgement],
       return 1)
    <|> return 0

meta def sem_to_syntactic : tactic unit :=
do `(%%τ ⊨ _) ← target,
   α ← infer_type τ,
   `[rw ← eq_judgement],
   r ← local_context >>= mfoldl (λ a h, (+) a <$> semantic_assumption τ h) 0,
   tactic.interactive.generalize none () (``(↑(eq %%τ) : pred' %%α), `Γ),
   intron r


meta def execute (c : temporal unit) : tactic unit :=
do intros,
   t ← target,
   t' ← whnf t,
   match t' with
     | `(⊩ _) := () <$ tactic.intro `Γ
     | `(_ ⟹ _) := () <$ tactic.intro `Γ
     | `(∀ Γ : pred' _, Γ ⊢ _) := () <$ tactic.intro `Γ
     | `(%%Γ ⊢ _) := local_context >>= mmap' (uniform_assumptions Γ)
     | _ := to_expr ``(⊩ _) >>= tactic.change >> () <$ tactic.intro `Γ
          <|> refine ``(@id (_ ⊨ _) _) >> sem_to_syntactic
          <|> fail "expecting a goal of the form `_ ⊢ _` or `⊩ _ `"
   end,
   target >>= whnf >>= change,
   c

meta def revert (e : expr) : tactic unit :=
do `(%%Γ ⊢ _) ← target,
   t ← infer_type e,
   match t with
    | `(%%Γ' ⊢ _) :=
      do ppΓ ← pp Γ, ppΓ' ← pp Γ',
         is_def_eq Γ Γ' <|> fail format!"{ppΓ'} does not match {ppΓ'}",
         tactic.revert e, applyc `predicate.p_impl_revert
    | _ := tactic.revert e >> refine ``((p_forall_to_fun %%Γ _).mp _)
   end

section
open tactic.interactive interactive.types
meta def interactive.strengthening (tac : itactic) : temporal unit :=
do lmms ← attribute.get_instances `strengthening,
   `(%%Γ ⊢ _) ← target,
   p ← infer_type Γ >>= mk_meta_var,
   lmms.any_of $ λ l, do
     r ← tactic.mk_app l [p,Γ],
     tactic.refine ``(p_impl_revert %%r _ ),
     tac

meta def interactive.apply' (q : parse texpr) : temporal unit :=
do l ← t_to_expr_for_apply q, tactic.trace l,
   () <$ tactic.apply l <|> interactive.strengthening (() <$ tactic.apply l)
                        <|> () <$ tactic.apply l -- we try `tactic.apply l` again
                                                 -- knowing that if we go back to
                                                 -- it, it will fail and we'll have
                                                 -- a proper error message

end

meta def split : temporal unit :=
do `(%%Γ ⊢ %%p ⋀ %%q) ← target,
   interactive.apply ``(p_and_intro %%p %%q %%Γ _ _)

meta def consequent (e : expr) : temporal expr :=
do `(_ ⊢ %%p) ← infer_type e,
   return p

lemma to_antecendent (xs : list (cpred))
  (H : list_persistent xs)
  (p : cpred)
  (h : ◻ xs.foldr (⋀) True ⊢ p)
: ∀ Γ, with_h_asms Γ xs p :=
begin
  intro,
  replace h := λ h', judgement_trans Γ _ _ h' h,
  induction xs with x xs,
  { simp at h, simp [with_h_asms,h], },
  { simp at h, simp_intros [with_h_asms],
    have _inst_2 : persistent x,
    { apply H, simp, },
    replace H : Π (q : cpred), q ∈ xs → persistent q,
    { intros, apply H, right, xassumption, },
    apply @xs_ih H, intros,
    apply h,
    rw henceforth_and,
    simp [is_persistent],
    begin [temporal]
      split,
      assumption,
      assumption,
    end }
end

open tactic tactic.interactive (unfold_coes unfold itactic assert_or_rule)
open interactive interactive.types lean lean.parser
open applicative (mmap₂ lift₂)
open has_map
local postfix `?`:9001 := optional
section persistently

meta def is_henceforth (e : expr) : temporal bool :=
do `(_ ⊢ %%t) ← infer_type e | return tt,
   succeeds $
     to_expr ``(persistent %%t) >>= mk_instance

meta def interactive.persistent (excp : parse without_ident_list) : temporal unit :=
do hs  ← get_assumptions,
   hs' ← hs.mfilter (map bnot ∘ is_henceforth),
   excp' ← mmap get_local excp,
   mmap' tactic.clear (hs'.diff excp')

private meta def mk_type_list (Γ pred_t : expr)  : list expr → temporal (expr × expr)
 | [] := do
   lift₂ prod.mk (to_expr ``(@list.nil cpred))
                 (to_expr ``(temporal.nil_persistent))
 | (x :: xs) :=
   do (es,is) ← mk_type_list xs,
      v  ← mk_meta_var pred_t,
      `(_ ⊢ %%c) ← infer_type x, c' ← pp c,
      ls ← to_expr ``(list.cons %%c %%es),
      inst₀ ← to_expr ``(persistent %%c) >>= mk_instance,
      inst ← tactic.mk_mapp `temporal.cons_persistent [c,es,inst₀,is],
      return (ls,inst)

meta def persistently (tac : itactic) : temporal unit :=
focus1 $
do asms ← get_assumptions,
   `(%%Γ ⊢ %%p) ← target >>= instantiate_mvars,
   pred_t ← infer_type Γ,
   Γ ← get_local Γ.local_pp_name,
   r ← tactic.revert_lst (Γ :: asms).reverse,
   guard (r = asms.length + 1) <|> fail format!"wrong use of context {Γ}",
   (asms',inst) ← mk_type_list Γ pred_t asms,
   ts ← mmap consequent asms,
   h ← to_expr  ``(@to_antecendent %%asms' %%inst %%p) >>= note `h none,
   `[simp only [temporal.with_h_asms] at h],
   h ← get_local `h,
   refine ``(%%h _),
   get_local `h >>= tactic.clear,
      -- calling tac
   x ← focus1 tac,
      -- restore context to Γ
   done <|> (do
     to_expr ```(_ ⊢ _) >>= change,
     `(_ ⊢ %%q) ← target,
     refine ``(from_antecendent %%asms' %%q _),
     `[simp only [temporal.with_h_asms]],
     Γ ← tactic.intro Γ.local_pp_name,
     mmap₂ (λ l t : expr, do
       let n := l.local_pp_name,
       tactic.intro n,
       tactic.interactive.change ``(%%Γ ⊢ %%t) none (loc.ns [some n]))
         asms ts,
     return x)
   <|> (do
     to_expr ```(⊩ _) >>= change,
     `(⊩ %%q) ← target,
     () <$ intro `Γ)
end persistently

section lemmas
open list

lemma judgement_congr {Γ p q : cpred}
  (h : Γ ⊢ p ≡ q)
: Γ ⊢ p = Γ ⊢ q :=
sorry

def with_asms {β} (Γ : pred' β) : Π (xs : list (pred' β)) (x : pred' β), Prop
 | [] x := Γ ⊢ x
 | (x :: xs) y := Γ ⊢ x → with_asms xs y

lemma p_imp_intro_asms_aux {β} (ps : list (pred' β)) (φ q r : pred' β)
  (h : ∀ Γ, Γ ⊢ φ → with_asms Γ (ps ++ [q]) r)
  (Γ : pred' β)
  (h' : Γ ⊢ φ)
: with_asms Γ ps (q ⟶ r) :=
begin
  revert φ,
  induction ps ; introv h h',
  case list.nil
  { simp [with_asms] at h ⊢,
    apply p_imp_intro φ,
    { introv h₀, apply h, auto },
    auto, },
  case list.cons : p ps
  { simp [with_asms] at h ⊢,
    intro hp,
    have h_and := (p_and_intro φ p Γ) h' hp,
    revert h_and,
    apply ps_ih,
    intros, xassumption,
    apply p_and_elim_left φ p Γ_1 a,
    apply p_and_elim_right φ p Γ_1 a,  }
end

lemma p_imp_intro_asms {β} (ps : list (pred' β)) (q r : pred' β)
  (h : ∀ Γ, with_asms Γ (ps ++ [q]) r)
  (Γ : pred' β)
: with_asms Γ ps (q ⟶ r) :=
begin
  apply p_imp_intro_asms_aux _ True,
  { intros, apply h },
  simp
end

end lemmas

private meta def mk_type_list : list expr → temporal expr
 | [] := to_expr ``(list.nil)
 | (x :: xs) :=
   do es ← mk_type_list xs,
      `(_ ⊢ %%t) ← infer_type x,
      to_expr ``(list.cons %%t %%es)

meta def intro (n : option name) : temporal expr :=
do to_expr ``(_ ⊢ _ ⟶ _) >>= change <|>
      to_expr ``(_ ⊢ p_forall _) >>= change <|>
      fail "expecting `_ ⟶ _` or `∀∀ _, _`",
   g ← target,
   match g with
    | `(%%Γ ⊢ %%p ⟶ %%q)  := do
      ls ← get_assumptions,
      r ← revert_lst (Γ :: ls).reverse,
      guard (r = ls.length + 1) <|> fail format!"wrong use of context {Γ}: {r} ≠ {ls.length + 1}",
      ls' ← mk_type_list ls,
      h ← to_expr  ``(p_imp_intro_asms %%ls' %%p %%q) >>= note `h none,
      tactic.interactive.unfold [`temporal.with_asms,`has_append.append,`list.append] (loc.ns [`h]),
      h ← get_local `h, tactic.apply h,
      tactic.clear h,
      tactic.intro_lst ((Γ :: ls).map expr.local_pp_name),
      tactic.intro (n.get_or_else `_)
    | `(%%Γ ⊢ p_forall (λ _, %%P)) := do
      refine ``((p_forall_to_fun %%Γ (λ _, %%P)).mpr _),
      n ← tactic.intro (n.get_or_else `_),
      n <$ (to_expr ``(%%Γ ⊢ %%(P.instantiate_var n)) >>= change)
    | _ := fail "expecting `_ ⟶ _` or `∀∀ _, _`"
   end

/-- Introduces new hypotheses with forward dependencies -/
meta def intros_dep : tactic (list expr) :=
do `(_ ⊢ p_forall _) ← target | return [],
   lift₂ (::) (intro none) intros_dep

@[user_attribute]
meta def lifted_congr_attr : user_attribute :=
{ name := `lifted_congr
, descr := "congruence lemmas for temporal logic" }

@[user_attribute]
meta def timeless_congr_attr : user_attribute :=
{ name := `timeless_congr
, descr := "congruence lemmas for temporal logic" }

meta def apply_lifted_congr : tactic unit :=
do xs ← attribute.get_instances `lifted_congr,
   xs.any_of (λ thm, do l ← resolve_name thm >>= to_expr, apply l),
   return ()

meta def apply_timeless_congr : tactic unit :=
do xs ← attribute.get_instances `timeless_congr,
   xs.any_of (λ thm, do l ← resolve_name thm >>= to_expr, () <$ apply l) <|> apply_lifted_congr

meta def force (p : pexpr) (e : expr) : tactic expr :=
do p' ← to_expr p,
   unify e p',
   instantiate_mvars p' <* cleanup

meta def app_ctx_aux (g : expr → expr)
: list (expr → expr) → list expr → expr → list ( (expr → expr) × expr )
| r₀ r₁ (expr.app f a) := app_ctx_aux ((λ e, g $ f.mk_app (e :: r₁)) :: r₀) (a :: r₁) f
| r₀ r₁ e         := list.zip r₀ r₁

meta def app_ctx (g : expr → expr)
: expr → list ( (expr → expr) × expr ) :=
app_ctx_aux g [] []

meta def match_context_core : pattern → list ((expr → expr) × expr) → tactic (expr → expr)
| p []      := failed
| p ((f,e)::es) :=
  f <$ match_pattern p e
  <|>
  match_context_core p es
  <|>
  if e.is_app
  then match_context_core p (app_ctx f e)
  else failed

meta def match_context (p : pexpr) (e : expr) : tactic (expr → expr) :=
do new_p ← pexpr_to_pattern p,
   match_context_core new_p [(id,e)]

lemma v_eq_symm_h {α} {Γ : cpred} {v₀ v₁ : tvar α}
  (h : Γ ⊢ ◻(v₁ ≃ v₀))
: Γ ⊢ ◻(v₀ ≃ v₁) :=
begin
  revert h, apply p_impl_revert,
  revert Γ, change (_ ⟹ _),
  monotonicity,
  lifted_pred, intro h, rw h
end

meta def temporal_eq_proof (Γ h' x' y' t : expr) (hence : bool) (cfg : rewrite_cfg := {})
: tactic (expr × expr × list expr) :=
do let (x,y) := if cfg.symm then (y',x')
                            else (x',y'),
   err ← pp x,
   ctx ← match_context (to_pexpr x) t <|> fail format!"no instance of {err} found",
   let t' := ctx y,
   p ← to_expr ``(%%Γ ⊢ %%t ≃ %%t'),
   ((),prf) ← solve_aux p (
   if hence then do
     h ← if cfg.symm then to_expr ``(v_eq_symm_h %%h')
                     else return h',
     h' ← mk_fresh_name,
     note h' none h,
     interactive.persistent [],
     persistently (repeat apply_timeless_congr),
     h ← get_local h',
     `(%%Γ ⊢ _) ← target,
     rule ← to_expr ``(p_impl_revert (henceforth_str (%%x ≃ %%y) %%Γ) %%h),
     exact rule
   else do
     h ← if cfg.symm then to_expr ``(v_eq_symm %%h')
                     else return h',
     repeat apply_lifted_congr,
     exact h),
   prf' ← to_expr ``(judgement_congr %%prf),
   new_t ← to_expr ``(%%Γ ⊢ %%t'),
   return (new_t,prf',[])
/--
 Must distinguish between three cases on the shape of assumptions:
 h : Γ ⊢ ◽(x ≡ y)
 h : x = y
 h : x ↔ y

 two cases on the shape of target:
 e: f x
 e: Γ ⊢ f x

 two cases on the shape of target:
 h : Γ ⊢ ◽(x ≡ y) → Γ ⊢ f x = f y

 h : Γ ⊢ ◽(x ≡ y) → Γ ⊢ f x = Γ ⊢ f y
 h : Γ ⊢ ◽(x ≡ y) → Γ ⊢ f x ≡ f y
 h : Γ ⊢ ◽(x ≡ y) ⟶ f x ≡ f y
 h : ⊩ ◽(x ≡ y) ⟶ f x ≡ f y
 -/
meta def rewrite_tmp (Γ h : expr) (e : expr) (cfg : rewrite_cfg := {}) : tactic (expr × expr × list expr) :=
do e ← whnf e,
   match e with
    | e'@`(%%Γt ⊢ %%e) :=
    do ht ← infer_type h >>= whnf,
       match ht with
         | `(%%Γr ⊢ ◻%%p) :=
           do `(%%x ≃ %%y) ← force ``(_ ≃ _) p,
              temporal_eq_proof Γ h x y e tt cfg
         | `(%%Γr ⊢ %%p) :=
           do `(%%x ≃ %%y) ← force ``(_ ≃ _) p,
              temporal_eq_proof Γ h x y e ff cfg
         | _ :=
           do (new_t, prf, metas) ← rewrite_core h e cfg,
              prf' ← to_expr ``(congr_arg (judgement %%Γt) %%prf),
              new_t' ← to_expr ``(judgement %%Γt %%new_t),
              try_apply_opt_auto_param cfg.to_apply_cfg metas,
              (new_t', prf', metas) <$ is_def_eq Γ Γt <|> pure (new_t,prf,metas)
       end
     | _ := do
          (new_t, prf, metas) ← rewrite_core h e cfg,
          try_apply_opt_auto_param cfg.to_apply_cfg metas,
          return (new_t, prf, metas)
   end

meta def rewrite_target (Γ h : expr) (cfg : rewrite_cfg := {}) : tactic unit :=
do t ← target,
   (new_t, prf, _) ← rewrite_tmp Γ h t cfg,
   e ← to_expr ``(%%t = %%new_t),
   replace_target new_t prf

meta def rewrite_hyp (Γ h : expr) (hyp : expr) (cfg : rewrite_cfg := {}) : tactic expr :=
do hyp_type ← infer_type hyp,
   (new_hyp_type, prf, _) ← rewrite_tmp Γ h hyp_type cfg,
   replace_hyp hyp new_hyp_type prf

meta def rw_goal (Γ : expr) (cfg : rewrite_cfg) (rs : list rw_rule) : temporal unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, rewrite_target Γ e {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_target Γ e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || to_bool (t = h)

meta def rw_hyp (Γ : expr) (cfg : rewrite_cfg) : list rw_rule → expr → temporal unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule,
        when (not (uses_hyp e hyp)) $
          rewrite_hyp Γ e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_hyp Γ e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.empty)

meta def rewrite (rs : rw_rules_t) (loca : loc) (cfg : rewrite_cfg) : temporal unit :=
do `(%%Γ ⊢ _) ← target,
   match loca with
   | loc.wildcard := loca.try_apply (rw_hyp Γ cfg rs.rules) (rw_goal Γ cfg rs.rules)
   | _            := loca.apply (rw_hyp Γ cfg rs.rules) (rw_goal Γ cfg rs.rules)
   end,
   try (reflexivity reducible : temporal _),
   (returnopt rs.end_pos >>= save_info <|> skip)

meta def solve1 : temporal unit → temporal unit :=
tactic.interactive.solve1

protected meta def note (h : name) : option expr → expr → temporal expr
 | none  pr :=
do p ← infer_type pr >>= beta_reduction,
   assertv h p pr
 | (some p)  pr := assertv h p pr

/-- bind the initial value of state-dependent expression
    `e` to global (through time) name `n`
  -/
meta def bind_name (e : expr) (n h : name) : temporal expr :=
do refine ``(one_point_elim _ _ %%e _),
   x ← tactic.intro n,
   temporal.intro h,
   return x

meta def update_name (f : string → string) : name → name
 | (name.mk_string s p) := name.mk_string (f s) p
 | x := x

meta def strip_prefix : name → name
 | (name.mk_string s p) := name.mk_string s name.anonymous
 | (name.mk_numeral s p) := name.mk_numeral s name.anonymous
 | name.anonymous := name.anonymous

meta def existsi (e : expr) (id : name) : temporal unit :=
do `(%%Γ ⊢ ∃∃ _ : %%t, %%intl) ← target,
   infer_type Γ >>= match_expr ``(cpred),
   let r := e.get_app_fn,
   let v := if r.is_constant
            then update_name (λ s, s ++ "₀") (strip_prefix r.const_name)
            else if r.is_local_constant
            then update_name (λ s, s ++ "₀") r.local_pp_name
            else `v₀,
   t' ← infer_type e,
   w ← (match_expr ``(tvar %%t) t' >> (bind_name e v id) <|> return e),
   refine ``(p_exists_to_fun %%w _)

namespace interactive
open lean.parser interactive interactive.types lean
open expr tactic.interactive (rcases_parse rcases_parse.invert)
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def skip : temporal unit :=
tactic.skip

meta def done : temporal unit :=
tactic.done

meta def itactic : Type :=
temporal unit

meta def timetac (s : string) (tac : itactic) : temporal unit :=
tactic.timetac s tac

meta def solve1 : itactic → temporal unit :=
tactic.interactive.solve1

meta def clear : parse ident* → tactic unit :=
tactic.clear_lst

meta def explicit
  (st : parse (ident <|> pure `σ))
  (tac : tactic.interactive.itactic) : temporal unit :=
do `(%%Γ ⊢ _) ← target,
   asms ← get_assumptions,
   constructor,
   st ← tactic.intro st,
   hΓ ← tactic.intro `hΓ,
   asms.for_each (λ h, do
     e ← to_expr ``(judgement.apply %%h %%st %%hΓ),
     note h.local_pp_name none e,
     tactic.clear h),
   try $ tactic.interactive.simp none ff
       (map simp_arg_type.expr [``(function.comp),``(temporal.init)]) []
       (loc.ns $ none :: map (some ∘ expr.local_pp_name) asms),
   done <|> solve1 (tactic.clear hΓ >> tactic.clear Γ >> tac)

meta def same_type (e₀ e₁ : expr) : temporal unit :=
do t₀ ← infer_type e₀,
   t₁ ← infer_type e₁,
   is_def_eq t₀ t₁

meta def «let» := tactic.interactive.«let»

meta def «have»  (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic expr :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  `(%%Γ ⊢ _) ← target,
  t ← i_to_expr e,
  t' ← to_expr ``(%%Γ ⊢ %%t),
  v ← t_to_expr ``(%%p : %%t'),
  tactic.assertv h t' v
| none, some p := do
  p ← t_to_expr p,
  temporal.note h none p
| some e, none := do
  `(%%Γ ⊢ _) ← target,
  e' ← i_to_expr e,
  p ← i_to_expr ``(%%Γ ⊢ %%e),
  tactic.assert h p
| none, none := do
  `(%%Γ ⊢ _) ← target,
  t ← infer_type Γ >>= beta_reduction,
  e ← mk_meta_var t,
  i_to_expr ``(%%Γ ⊢ %%e) >>= tactic.assert h
end

meta def strengthen_to (e : parse texpr) : temporal unit :=
strengthening (to_expr ``(_ ⊢ %%e) >>= change)

meta def intro (n : parse ident_?) : temporal unit :=
() <$ temporal.intro n

meta def intros : parse ident_* → temporal unit
 | [] := repeat (intro `_)
 | xs := mmap' (intro ∘ some) xs

meta def introv : parse ident_* → tactic (list expr)
| []      := intros_dep
| (n::ns) := do hs ← intros_dep, h ← temporal.intro n, hs' ← introv ns, return (hs ++ h :: hs')

meta def revert (ns : parse ident*) : temporal unit :=
mmap get_local ns >>= mmap' temporal.revert

meta def exact (e : parse texpr) : temporal unit :=
tactic.interactive.exact e

meta def refine (e : parse texpr) : temporal unit :=
tactic.interactive.refine e

meta def apply (q : parse texpr) : temporal unit :=
focus1 $
do l ← t_to_expr_for_apply q,
   () <$ tactic.apply l <|> strengthening (() <$ tactic.apply l)
                        <|> () <$ tactic.apply l, -- we try `tactic.apply l` again
                                                  -- knowing that if we go back to
                                                  -- it, it will fail and we'll have
                                                  -- a proper error message
   all_goals (try $ execute (pure ()))

meta def trivial : temporal unit :=
`[apply of_eq_true (True_eq_true _)]

meta def rw (rs : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := { }) : temporal unit :=
rewrite rs l cfg ; (trivial <|> auto <|> reflexivity <|> return ())

meta def rewrite  (rs : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := { }) : temporal unit :=
rw rs l cfg

private meta def cases_arg_p : lean.parser (option name × pexpr) :=
with_desc "(id :)? expr" $ do
  t ← texpr,
  match t with
  | (local_const x _ _ _) :=
    (tk ":" *> do t ← texpr, pure (some x, t)) <|> pure (none, t)
  | _ := pure (none, t)
  end

meta def sequent_type (p : expr) : tactic (option (expr × expr × expr)) :=
do t ← infer_type p,
   `(%%Γ ⊢ _) ← target,
   match t with
    | `(%%Γ ⊢ %%q) := return (some (Γ,p,q))
    | `(⊩ %%q) := return (some (Γ,p Γ, q))
    | _ := return none
   end

meta def cases (e : parse cases_arg_p) (ids : parse with_ident_list) : temporal unit :=
do p' ← to_expr e.2,
   (some (Γ,p,q)) ← sequent_type p' | tactic.interactive.cases e ids,
   match q with
    | `(%%a ⋀ %%b) := do
      let h₀ : name := (ids.nth 0).get_or_else `a,
      let h₁ : name := (ids.nth 1).get_or_else `a,
      to_expr ``(p_and_elim_left %%a %%b %%Γ %%p) >>= note h₀ none,
      to_expr ``(p_and_elim_right %%a %%b %%Γ %%p) >>= note h₁ none,
      when p'.is_local_constant (tactic.clear p')
    | `(%%a ⋁ %%b) := do
      let h₀ : name := (ids.nth 0).get_or_else `a,
      let h₁ : name := (ids.nth 1).get_or_else `a,
      g ← target,
      note `h none p,
      revert [`h],
      when p'.is_local_constant (tactic.clear p'),
      apply ``(@p_or_entails_of_entails' _  %%Γ %%a %%b _ _)
      ; [ intros [h₀] , intros [h₁] ],
      tactic.swap
    | `(∃∃ x : %%t, %%e') := do
      let h₀ : name := (ids.nth 0).get_or_else `a,
      let h₁ : name := (ids.nth 1).get_or_else `a,
      h ← note `h none p',
      when p'.is_local_constant (tactic.clear p'),
      revert [`h], h ← to_expr ``(p_exists_imp_eq_p_forall_imp _ _),
      tactic.rewrite_target h, intros [h₀,h₁]
    | _ := do q ← pp q, fail format!"case expression undefined on {q}"
   end

-- meta def rcases (e : parse cases_arg_p)
--   (ids : parse (tk "with" *> rcases_parse)?)
-- : temporal unit :=
-- do let patts := rcases_parse.invert $ ids.get_or_else [default _],
--    _

meta def by_cases (q : parse texpr) (n : parse (tk "with" *> ident)?): tactic unit :=
let h := n.get_or_else `h in
cases (none, ``(predicate.em %%q)) [h,h]

meta def assume_negation (n : parse (tk "with" *> ident)?) : temporal unit :=
do `(_ ⊢ %%t) ← target,
   let h := n.get_or_else `h,
   cases (none, ``(predicate.em %%t)) [h,h],
   solve1 (do h ← get_local h, tactic.exact h)

meta def induction
  (obj : parse interactive.cases_arg_p)
  (rec_name : parse using_ident)
  (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?)
: tactic unit :=
do `(%%Γ ⊢ _) ← target,
   tactic.interactive.induction obj rec_name ids revert ;
     (local_context >>= mmap' (uniform_assumptions Γ))

meta def case (ctor : parse ident*) (ids : parse ident_*) (tac : itactic) : tactic unit :=
tactic.interactive.case ctor ids tac

meta def focus_left' (id : option name) : temporal expr :=
do `(%%Γ ⊢ _ ⋁ _) ← target | fail "expecting `_ ⋁ _`",
   `[rw [p_or_comm,← p_not_p_imp]],
   temporal.intro id

meta def focus_left (ids : parse with_ident_list) : temporal unit :=
() <$ focus_left' ids.opt_head

meta def focusing_left (ids : parse with_ident_list) (tac : itactic) : temporal unit :=
do x ← focus_left' ids.opt_head,
   focus1 (do
     tac,
     get_local x.local_pp_name >>= temporal.revert,
     `[rw [p_not_p_imp,← p_or_comm]])

meta def focus_right' (id : option name) : temporal expr :=
do `(%%Γ ⊢ _ ⋁ _) ← target | fail "expecting `_ ⋁ _`",
   `[rw [← p_not_p_imp]],
   temporal.intro id

meta def focus_right (ids : parse with_ident_list) : temporal unit :=
() <$ focus_right' ids.opt_head

meta def focusing_right (ids : parse with_ident_list) (tac : itactic) : temporal unit :=
do x ← focus_right' ids.opt_head,
   focus1 (do
     tac,
     get_local x.local_pp_name >>= temporal.revert,
     `[rw [p_not_p_imp]])

meta def split : temporal unit :=
do `(%%Γ ⊢ %%p ⋀ %%q) ← target,
   apply ``(p_and_intro %%p %%q %%Γ _ _)

meta def existsi : parse pexpr_list_or_texpr → parse with_ident_list → temporal unit
| []      _ := return ()
| (p::ps) xs :=
do e ← i_to_expr p,
   have h : inhabited name, from ⟨ `_ ⟩,
   temporal.existsi e (@list.head _ h xs),
   existsi ps xs.tail

meta def clear_except :=
tactic.interactive.clear_except

meta def action (ids : parse with_ident_list) (tac : tactic.interactive.itactic) : temporal unit :=
do `[ try { simp only [predicate.p_not_comp,temporal.next_eq_action,temporal.next_eq_action',temporal.not_action] },
      try { simp only [predicate.p_not_comp,temporal.init_eq_action,temporal.init_eq_action',temporal.not_action
                      ,temporal.action_and_action,predicate.models_pred
                      ,predicate.models_prop] },
      repeat { rw ← temporal.action_imp } ],
   get_assumptions >>= list.mmap' tactic.clear,
   `(%%Γ ⊢ temporal.action %%A  %%v ) ← target,
   refine ``(temporal.unlift_action %%A %%v _),
   tactic.intro_lst [`σ,`σ'],
   mmap' tactic.intro ids,
   solve1 tac

meta def print := tactic.print

meta def repeat (tac : itactic) : temporal unit :=
tactic.repeat tac

meta def lifted_pred
  (no_dflt : parse only_flag)
  (rs : parse simp_arg_list)
  (us : parse using_idents)
: temporal unit :=
tactic.interactive.lifted_pred ff no_dflt rs us

meta def propositional : temporal unit :=
tactic.interactive.propositional

meta def assumption : temporal unit :=
xassumption <|> strengthening xassumption

meta def try (tac : itactic) : temporal unit :=
tactic.try tac

meta def refl :=
do try (to_expr ``(ctx_impl _ _ _) >>= change),
   tactic.reflexivity

meta def reflexivity :=
do try (to_expr ``(ctx_impl _ _ _) >>= change),
   tactic.reflexivity

meta def ac_refl :=
do refine ``(entails_of_eq _ _ _ _) <|> refine ``(equiv_of_eq _ _ _ _),
   tactic.ac_refl

meta def unfold_coes (ids : parse ident *) (l : parse location) (cfg : unfold_config := { }) : temporal unit :=
tactic.interactive.unfold_coes l >>
tactic.interactive.unfold ids l cfg

meta def dsimp :=
tactic.interactive.dsimp

meta def simp (no_dflt : parse only_flag)
              (hs : parse simp_arg_list)
              (attr_names : parse with_ident_list)
              (locat : parse location)
              (cfg : simp_config_ext := {}) : temporal unit :=
-- if locat.include_goal
-- then strengthening $ tactic.interactive.simp no_dflt hs attr_names locat cfg
do tactic.interactive.simp none no_dflt hs attr_names locat cfg,
   try refl

meta def exfalso : temporal unit :=
do `(%%Γ ⊢ %%p) ← target,
   `[apply False_entails %%p %%Γ _]

meta def admit : temporal unit :=
tactic.admit

meta def left : temporal unit :=
do `(%%Γ ⊢ %%p ⋁ %%q) ← target,
   apply ``(p_or_intro_left %%p %%q %%Γ _)

meta def right : temporal unit :=
do `(%%Γ ⊢ %%p ⋁ %%q) ← target,
   apply ``(p_or_intro_right %%p %%q %%Γ _)

meta def auto : temporal unit :=
assumption ; assumption ; assumption ; done

meta def specialize (h : parse texpr) : temporal unit :=
tactic.interactive.specialize h

meta def type_check
   (e : parse texpr)
: tactic unit :=
do e ← t_to_expr e, tactic.type_check e, infer_type e >>= trace

def with_defaults {α} : list α → list α → list α
 | [] xs := xs
 | (x :: xs) (_ :: ys) := x :: with_defaults xs ys
 | xs _ := xs
meta def rename_bound (n : name) : expr → expr
 | (expr.app e₀ e₁) := expr.app e₀ (rename_bound e₁)
 | (expr.lam _ bi t e) := expr.lam n bi t e
 | e := e

meta def wf_induction
  (p : parse texpr)
  (rec_name : parse (tk "using" *> texpr)?)
  (ids : parse with_ident_list)
: tactic unit :=
do rec_name ← (↑rec_name : tactic pexpr) <|> return ``(has_well_founded.wf _),
   to_expr ``(well_founded.induction %%rec_name %%p) >>= tactic.apply,
   try $ to_expr p >>= tactic.clear,
   ids' ← tactic.intro_lst $ (with_defaults ids [`x,`ih_1]).take 2 ,
   h ← ids'.nth 1,
   hp ← to_expr ``((p_forall_subtype_to_fun _ _ _).mpr %%h),
   p ← rename_bound `y <$> infer_type hp,
   assertv h.local_pp_name p hp,
   tactic.clear h,
   return ()

private meta def show_aux (p : pexpr) : list expr → list expr → tactic unit
| []      r := fail "show tactic failed"
| (g::gs) r := do
  do { set_goals [g],
       g_ty ← target,
       ty ← i_to_expr p,
       unify g_ty ty,
       set_goals (g :: r.reverse ++ gs),
       tactic.change ty}
  <|>
  show_aux gs (g::r)

meta def «show» (q : parse $ texpr <* tk ",") (tac : tactic.interactive.itactic) : tactic unit :=
do gs ← get_goals,
   show_aux q gs [],
   solve1 tac

meta def replace (n : parse ident)
: parse (parser.tk ":" *> texpr)? → parse (parser.tk ":=" *> texpr)? → temporal unit
| none (some prf) :=
do prf ← t_to_expr prf,
   tactic.interactive.replace n none (to_pexpr prf) >> try (simp tt [] [] (loc.ns [some n]))
| none none :=
tactic.interactive.replace n none none
| (some t) (some prf) :=
do t' ← to_expr t >>= infer_type,
   tl ← tt <$ match_expr ``(pred' _) t' <|> pure ff,
   if tl then do
     `(%%Γ ⊢ _) ← target,
     prf' ← t_to_expr prf,
     tactic.interactive.replace n ``(%%Γ ⊢ %%t) (to_pexpr prf')
   else tactic.interactive.replace n t prf
| (some t) none :=
do t' ← to_expr t >>= infer_type,
   match_expr ``(pred' _) t' ,
   `(%%Γ ⊢ _) ← target,
   tactic.interactive.replace n ``(%%Γ ⊢ %%t) none

meta def transitivity : parse texpr? → temporal unit
 | none := apply ``(predicate.p_imp_trans )
 | (some p) := apply ``(@predicate.p_imp_trans _ _ _ %%p _ _ _)

end interactive

/- end monotonicity -/


section
open tactic tactic.interactive (unfold_coes unfold itactic assert_or_rule)
open interactive interactive.types lean lean.parser
open applicative (mmap₂ lift₂)
open has_map
local postfix `?`:9001 := optional

meta def interactive.henceforth (l : parse location) : temporal unit :=
do when l.include_goal $
     persistently (do
       refine ``(persistent_to_henceforth _)),
   match l with
    | loc.wildcard := l.try_apply
         (λ h, do b ← is_henceforth h,
                  when (¬ b) $ fail format!"{h} is not of the shape `□ _`",
                  to_expr ``(p_impl_revert (henceforth_str _ _) %%h)
                    >>= note h.local_pp_name none,
                  tactic.clear h)
         (pure ())
    | _ := l.apply
         (λ h, do b ← is_henceforth h,
                  when (¬ b) $ fail format!"{h} is not of the shape `□ _`",
                  to_expr ``(p_impl_revert (henceforth_str _ _) %%h)
                    >>= note h.local_pp_name none,
                  tactic.clear h)
         (pure ())
  end

meta def monotonicity1 (only_pers : parse only_flag) : temporal unit :=
do ex ← (if ¬ only_pers then do
      asms ← get_assumptions,
      list.band <$> asms.mmap is_henceforth
   else tt <$ interactive.persistent []),
   if ex
   then persistently $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          tactic.interactive.monotonicity1
   else tactic.interactive.monotonicity1

meta def monotonicity_n (n : ℕ) (only_pers : parse only_flag) : temporal unit  :=
do ex ← (if ¬ only_pers then do
      asms ← get_assumptions,
      list.band <$> asms.mmap is_henceforth
   else tt <$ interactive.persistent []),
   if ex
   then persistently $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          tactic.iterate_exactly n tactic.interactive.monotonicity1
   else tactic.interactive.monotonicity1

meta def monotonicity (only_pers : parse only_flag) (e : parse assert_or_rule?) : temporal unit :=
do ex ← (if ¬ only_pers then do
      asms ← get_assumptions,
      list.band <$> asms.mmap is_henceforth
   else tt <$ interactive.persistent []),
   if ex
   then persistently $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          tactic.interactive.monotonicity e
   else tactic.interactive.monotonicity e

meta def interactive.apply_mono (f e : parse ident) : temporal unit :=
do get_local e >>= temporal.revert,
   f ← get_local f,
   b ← is_henceforth f,
   if b then do
     interactive.persistent [],
     persistently  $ do
          to_expr ``(tl_imp _ _ _) >>= change,
          tactic.interactive.monotonicity (some $ sum.inl ``(%%f))
   else tactic.interactive.monotonicity (some $ sum.inl ``(%%f))

private meta def goal_flag := tt <$ tk "⊢" <|> tt <$ tk "|-" <|> pure ff

meta def interactive.eventually (h : parse ident) (goal : parse goal_flag) : temporal unit :=
do `(%%Γ ⊢ %%p) ← target,
   h' ← get_local h,
   `(%%Γ' ⊢ ◇%%q) ← infer_type h' | fail format!"{h} should be a temporal formula of the form ◇_",
   is_def_eq Γ Γ',
   revert h',
   if goal then do
     `(◇ %%p) ← pure p | fail format!"expecting a goal of the form `◇ _`",
     monotonicity1 ff
   else persistently (refine ``(p_imp_postpone _ %%q %%p _)),
   () <$ intro (some h)

meta def timeless (h : expr) : temporal (option name) :=
do try $ interactive.henceforth (loc.ns [some h.local_pp_name]),
   h ← get_local h.local_pp_name,
   `(%%Γ' ⊢ %%p) ← infer_type h | return none,
   `(@coe Prop cpred _ %%p) ← return p | none <$ clear h,
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
     try $ tactic.interactive.generalize none () (``(%%τ 0),`σ),
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
  let ls := [`monotonicity,`monotonicity1,`persistently],
  ls.for_each $ λ l, do
    env    ← get_env,
    d_name ← resolve_constant l,
    (declaration.defn _ ls ty val hints trusted) ← env.get d_name,
    (name.mk_string h _) ← return d_name,
    let new_name := `temporal.interactive <.> h,
    add_decl (declaration.defn new_name ls ty (expr.const d_name (ls.map level.param)) hints trusted)

end

end temporal

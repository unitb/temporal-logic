
import util.predicate
import util.control.applicative

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

-- namespace temporal

-- meta inductive proof : Type
--  | first_order : expr → proof
--  | invariant (inv act : expr) : proof → proof

-- meta structure goal :=
--   (Γ σ : expr)
--   (decl : list (name × expr))
--   (asms : list (name × expr))
--   (target : expr)

-- protected meta structure state :=
--   (goal : goal)

-- end temporal

-- section
-- open temporal
meta def temporal : Type → Type :=
tactic
-- end

open format
meta def unlines : list format → format :=
format.join ∘ list.intersperse line

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

-- meta def get_goals_ext : tactic (list $ list expr × expr) :=
-- do gs ← get_goals,
--    mmap (λ g, do
--        set_goals [g],
--        lift₂ prod.mk local_context target) gs
--     <* set_goals gs

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

-- meta def temp_asm_to_fmt (Γ e : expr) : temporal format :=
-- do `(%%Γ' ⊢ %%p) ← infer_type e | decl_to_fmt e none,
--    ( do is_def_eq Γ Γ',
--         decl_to_fmt e p ) <|> decl_to_fmt e none

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
    return $ unlines (hs' ++ [format!"⊢ {p}"])

meta def save_info (p : pos) : temporal unit :=
do s   ← tactic.read,
   gs  ← get_goals,
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

meta def uniform_assumptions (Γ h : expr) : temporal unit :=
do t ← infer_type h,
   match t with
    | `(%%Γ' ⊢ %%p) := (is_def_eq Γ Γ' >> guard (¬ Γ.occurs p)) <|> clear h
    | p := when (Γ.occurs p) $ clear h
   end

meta def execute (c : temporal unit) : tactic unit :=
do t ← target,
   match t with
    | `(⊩ _) := () <$ tactic.intro `Γ
    | `(_ ⟹ _) := () <$ tactic.intro `Γ
    | `(%%Γ ⊢ _) := local_context >>= mmap' (uniform_assumptions Γ)
    | _ := fail "expecting a goal of the form `_ ⊢ _` or `⊩ _ `"
   end,
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

meta def consequent (e : expr) : temporal expr :=
do `(_ ⊢ %%p) ← infer_type e,
   return p

section lemmas
open list
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
  case list.cons p ps
  { simp [with_asms] at h ⊢,
    intro hp,
    have h_and := (p_and_intro φ p Γ) h' hp,
    revert h_and,
    apply ih_1,
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
      r ← revert_lst (Γ :: ls).reverse <|> fail "revert",
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

meta def consequent_if (Γ : expr) : expr → temporal (expr × (expr → expr) × (expr → temporal expr))
 | e'@`(%%Γ' ⊢ %%e) :=
   do let f := λ p : expr, to_expr ``(congr_arg (judgement %%Γ') %%p),
      g ← to_expr ``(judgement %%Γ'),
      (e,g,f) <$ is_def_eq Γ Γ' <|> pure (e',id,return)
 | e := pure (e,id,return)

-- @[user_attribute]
-- meta def lifted_congr : user_attribute :=
-- { name := `lifted_congr
-- , descr := "congruence lemmas for temporal logic" }

@[user_attribute]
meta def strengthening_attr : user_attribute :=
{ name := `strengthening
, descr := "
Strenghtening lemmas to facilitate the stripping of small details in application.
Expected shape `∀ p : pred' α, ⊩ f p ⟶ g p`
" }

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
do (e',g,f) ← consequent_if Γ e,
   (new_t, prf, metas) ← rewrite_core h e' cfg,
   try_apply_opt_auto_param cfg.to_apply_cfg metas,
   prf' ← f prf,
   return (g new_t, prf', metas)

meta def rewrite_target (Γ h : expr) (cfg : rewrite_cfg := {}) : tactic unit :=
do t ← target,
   (new_t, prf, _) ← rewrite_tmp Γ h t cfg,
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

 -- tactic.interactive.rewrite _ _ _
meta def solve1 : temporal unit → temporal unit :=
tactic.interactive.solve1

meta def beta_reduction' : expr → temporal expr
 | (expr.app e₀ e₁) :=
 do e₁ ← beta_reduction' e₁,
    e₀ ← beta_reduction' e₀,
    head_beta $ expr.app e₀ e₁
 | e := expr.traverse beta_reduction' e >>= head_eta

meta def beta_reduction (e : expr) : temporal expr :=
instantiate_mvars e >>= beta_reduction'

protected meta def note (h : name) : option expr → expr → temporal expr
 | none  pr :=
do p ← infer_type pr >>= beta_reduction,
   assertv h p pr
 | (some p)  pr := assertv h p pr

namespace interactive
open lean.parser interactive interactive.types lean
open expr
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def skip : temporal unit :=
tactic.skip

meta def done : temporal unit :=
tactic.done

meta def itactic : Type :=
temporal unit

meta def solve1 : itactic → temporal unit :=
tactic.interactive.solve1

meta def clear : parse ident* → tactic unit :=
tactic.clear_lst

meta def explicit
  (st : parse (ident <|> pure `σ))
  (tac : tactic.interactive.itactic) : temporal unit :=
do `(%%Γ ⊢ _) ← target,
   asms ← get_assumptions <|> fail "assumption",
   constructor,
   st ← tactic.intro st,
   hΓ ← tactic.intro `hΓ,
   asms.for_each (λ h, do
     e ← to_expr ``(judgement.apply %%h %%st %%hΓ),
     note h.local_pp_name none e,
     tactic.clear h ),
   tactic.clear hΓ,
   tactic.clear Γ,
   solve1 tac

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
  v ← i_to_expr ``(%%p : %%t'),
  tactic.assertv h t' v
| none, some p := do
  p ← i_to_expr p,
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

meta def strengthening (tac : itactic) : temporal unit :=
do lmms ← attribute.get_instances `strengthening,
   `(%%Γ ⊢ _) ← target,
   p ← infer_type Γ >>= mk_meta_var,
   lmms.any_of $ λ l, do
     r ← tactic.mk_app l [p,Γ],
     refine $ ``(p_impl_revert %%r _ ),
     tac

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

meta def apply (q : parse texpr) : temporal unit :=
do l ← i_to_expr_for_apply q,
   tactic.apply l <|> strengthening (tactic.apply l)

meta def trivial : temporal unit :=
`[apply of_eq_true (True_eq_true _)]

meta def rw (rs : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := { }) : temporal unit :=
rewrite rs l cfg ; (trivial <|> auto <|> return ())

meta def rewrite  (rs : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := { }) : temporal unit :=
rw rs l cfg

-- simp
private meta def cases_arg_p : lean.parser (option name × pexpr) :=
with_desc "(id :)? expr" $ do
  t ← texpr,
  match t with
  | (local_const x _ _ _) :=
    (tk ":" *> do t ← texpr, pure (some x, t)) <|> pure (none, t)
  | _ := pure (none, t)
  end

meta def cases (e : parse cases_arg_p) (ids : parse with_ident_list) : temporal unit :=
do p ← to_expr e.2,
   `(%%Γ ⊢ %%q) ← infer_type p | tactic.interactive.cases e ids,
   match q with
    | `(%%a ⋀ %%b) := do
      let h₀ : name := (ids.nth 0).get_or_else `a,
      let h₁ : name := (ids.nth 1).get_or_else `a,
      to_expr ``(p_and_elim_left %%a %%b %%Γ %%p) >>= note h₀ none,
      to_expr ``(p_and_elim_right %%a %%b %%Γ %%p) >>= note h₁ none,
      when p.is_local_constant (tactic.clear p)
    | `(%%a ⋁ %%b) := do
      let h₀ : name := (ids.nth 0).get_or_else `a,
      let h₁ : name := (ids.nth 1).get_or_else `a,
      g ← target,
      note `h none p,
      revert [`h],
      when p.is_local_constant (tactic.clear p),
      apply ``(@p_or_entails_of_entails' _  %%Γ %%a %%b _ _)
      ; [ intros [h₀] , intros [h₁] ]
    | _ := do q ← pp q, fail format!"case expression undefined on {q}"
   end

meta def split : temporal unit :=
do `(%%Γ ⊢ %%p ⋀ %%q) ← target,
   apply ``(p_and_intro %%p %%q %%Γ _ _)

meta def assumption : temporal unit :=
xassumption <|> strengthening xassumption

meta def dsimp :=
tactic.interactive.dsimp

meta def simp (no_dflt : parse only_flag)
              (hs : parse simp_arg_list)
              (attr_names : parse with_ident_list)
              (locat : parse location)
              (cfg : simp_config_ext := {}) : temporal unit :=
-- if locat.include_goal
-- then strengthening $ tactic.interactive.simp no_dflt hs attr_names locat cfg
tactic.interactive.simp no_dflt hs attr_names locat cfg

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
tactic.interactive.type_check e

meta def induction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
tactic.interactive.induction p rec_name ids revert

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
  (rec_name : parse $ tk "using" *> texpr)
  (ids : parse with_ident_list)
  -- (revert : parse $ (tk "generalizing" *> ident*)?)
: tactic unit :=
do to_expr ``(well_founded.induction %%rec_name %%p) >>= tactic.apply,
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
  do {set_goals [g], g_ty ← target, ty ← i_to_expr p, unify g_ty ty, set_goals (g :: r.reverse ++ gs), tactic.change ty}
  <|>
  show_aux gs (g::r)

meta def «show» (q : parse $ texpr <* tk ",") (tac : tactic.interactive.itactic) : tactic unit :=
do gs ← get_goals,
   show_aux q gs [],
   solve1 tac

meta def replace :=
tactic.interactive.replace

meta def transitivity : parse texpr? → temporal unit
 | none := apply ``(predicate.p_imp_trans )
 | (some p) := apply ``(@predicate.p_imp_trans _ _ _ %%p _)

meta def refl :=
tactic.reflexivity

meta def reflexivity :=
tactic.reflexivity

meta def ac_refl :=
do refine ``(entails_of_eq _ _ _ _) <|> refine ``(equiv_of_eq _ _ _ _),
   tactic.ac_refl

end interactive
end temporal

section
variable {α : Type}
variables Γ p q r : pred' α
variable h₀ : Γ ⊢ p ⟶ q
variable h₁ : Γ ⊢ q ⟶ r
include h₀ h₁

example : Γ ⊢ p ⋁ r :=
begin [temporal]
  revert h₁,
  intro k3,
  -- turn
-- Γ : pred' α
-- p : pred' α
-- q : pred' α
-- r : pred' α
  -- to
-- Γ p q r : pred' α

-- remove Γ
end

end

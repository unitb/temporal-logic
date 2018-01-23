
import temporal_logic.fairness
import temporal_logic.pair
import temporal_logic.lemmas

universe variables u u₀ u₁ u₂
open predicate nat

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal

namespace simulation
section

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters (p : pred' (α'×γ')) (q : pred' (β'×γ'))
parameters (A : act (α'×γ')) (C : act (β'×γ'))
parameters (J : pred' (α'×β'×γ'))

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ! ⦃ o,v ⦄ ⋀
◻⟦ v,o | A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻⟦ v,o | C ⟧

parameters [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ w v o v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

section witness
variables x₀ : tvar α'
variables f : tvar (α' → α')
variables (i : ℕ)

open classical

private def w : ℕ → α'
 | 0 := i ⊨ x₀
-- (ε w', (w',i ⊨ o) ⊨ p ∧ (w', i ⊨ v, i ⊨ o) ⊨ J)
 | (succ j) := (i + j ⊨ f) (w j)
            -- (ε w', A (w j,i+j ⊨ o) (w',i + succ j ⊨ o) ∧
            --           (w', i + succ j ⊨ v, i + succ j ⊨ o) ⊨ J)

lemma witness
: ⊩ ∃∃ w, w ≃ x₀ ⋀ ◻( ⊙w ≃ f w ) :=
begin
  lifted_pred,
  existsi (⟨ λ i, w x₀ f x (i - x) ⟩ : tvar α'),
  simp [nat.sub_self,w],
  intro i,
  have h : x + i ≥ x := nat.le_add_right _ _,
  simp [next,nat.add_sub_cancel_left,succ_sub h,w],
end

lemma witness_elim {P : tvar α' → cpred} {Γ : cpred}
  (h : Γ ⊢ ∀∀ w, w ≃ x₀ ⋀ ◻( ⊙w ≃ f w ) ⟶ P w)
: Γ ⊢ ∃∃ w, P w :=
begin [temporal]
  have := witness x₀ f Γ,
  revert this,
  apply p_exists_p_imp_p_exists _ _ h,
end

open interactive interactive.types lean.parser tactic

meta def with_witness
  (w : parse $ ident_ <* tk ":")
  (p : parse texpr)
  (asm : parse $ optional $ tk "with" *> ident): temporal unit :=
do `(%%Γ ⊢ p_exists %%q) ← target,
   u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   t ← mk_app `temporal.tvar [t],
   t' ← to_expr ``(%%t → cpred),
   (_,p) ← solve_aux t' (do
     tactic.intro w
       <* (to_expr p >>= exact)),
   v ← mk_local_def w t,
   p' ← head_beta (p v),
   q' ← head_beta (q v),
   new_g ← to_expr ``(%%p' ⟶ %%q'),
   new_g ← to_expr ``(%%Γ ⊢ p_forall %%(new_g.lambdas [v])),
   h ← assert `h new_g,
   temporal.interactive.intros [w,asm.get_or_else `_],
   tactic.swap,
   mk_app `temporal.simulation.witness_elim [h] >>= exact

run_cmd do
  let n := `with_witness,
  env    ← get_env,
  d_name ← resolve_constant n,
  (declaration.defn _ ls ty val hints trusted) ← env.get d_name,
  (name.mk_string h _) ← return d_name,
  let new_name := `temporal.interactive <.> h,
  add_decl (declaration.defn new_name ls ty (expr.const d_name (ls.map level.param)) hints trusted)

end witness


parameters Γ : cpred
parameters H : Γ ⊢ SPEC₁ v o

noncomputable def Wx₀_f : tvar (β' → γ' → α') :=
λ v o, ε w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J

noncomputable def Wx₀ : tvar α' :=
Wx₀_f v o

noncomputable def Wf_f : tvar (β' → γ' → γ' → α' → α') :=
λ v' o o' w, ε w', A (w,o) (w',o') ∧
                   (w', v', o') ⊨ J

noncomputable def Wf : tvar (α' → α') :=
Wf_f (⊙v) o (⊙o)

noncomputable def Wtn (w : tvar α') :=
w ≃ Wx₀ ⋀ ◻(⊙w ≃ Wf w)

include SIM₀

lemma init_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ q!⦃o,v⦄ ⟶ p!⦃o,w⦄ :=
begin
  lifted_pred [nat.sub_self,Wtn] ,
  introv Hq, intros, simp [Hq,Wx₀,Wx₀_f],
  unfold_coes, simp [Wx₀,Wx₀_f],
  apply_epsilon_spec,
end

include H SIM
lemma J_inv_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(J ! ⦃o,v,w⦄) :=
begin [temporal]
  introv Hw,
  apply induct _ _ _ _,
  { replace Hw := Hw.right,
    simp, rw Hw,
    replace H := H.right,
    henceforth at H ⊢ , revert H,
    explicit
    { repeat { unfold_coes <|> simp [Wf,Wf_f] },
      intros, apply_epsilon_spec,  } },
  { replace Hw := Hw.left,
    rw [Hw,Wx₀,Wx₀_f],
    replace H := H.left,
    explicit {
    { unfold_coes, simp at ⊢ H,
      apply_epsilon_spec, } } },
end

lemma C_imp_A_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(⟦ v,o | C ⟧ ⟶ ⟦ w,o | A ⟧) :=
begin [temporal]
  intros w Hw,
  have := J_inv_in_w p q A C J SIM₀ @SIM v o Γ H,
  replace this := this w Hw,
  simp [action_eq],
  rw [Hw.right],
  clear H Hw,
  henceforth at ⊢ this,
  revert this,
  explicit {
    repeat { simp [Wf,Wf_f] <|> unfold_coes },
    intros,
    apply_epsilon_spec, },
end

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  with_witness w : temporal.simulation.Wtn w with Hw,
  have := H, revert this,
  simp only [SPEC₀,SPEC₁],
  apply ctx_p_and_p_imp_p_and',
  { apply temporal.simulation.init_in_w _ Hw },
  { type_check_result "foo",
    replace Hw := temporal.simulation.C_imp_A_in_w _ Hw,
    monotonicity only,
    apply Hw, },
end

omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation p q A C J SIM₀ @SIM _ _ _ h,
end

end
end simulation

export simulation (simulation simulation')

section witness_construction

parameters {α' : Sort u}
parameters {p J : pred' α'}
parameters {A : act α'}

parameters H₀ : p ⟹ J
parameters FIS₀ : ∃ σ, σ ⊨ p
parameters FIS : ∀ σ, σ ⊨ J → ∃ σ', A σ σ'
parameters INV : ∀ σ σ', σ ⊨ J → A σ σ' → σ' ⊨ J

open classical simulation

include H₀ INV

def A' : plift α' × unit → plift α' × unit → Prop :=
A on (plift.down ∘ prod.fst)

parameters [_inst : inhabited α']

include FIS₀ FIS _inst
lemma witness_construction
: ⊩ ∃∃ v, p ! v ⋀ ◻⟦ v | A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (plift α' × unit) α' := ⟨plift.down⟩ ! pair.fst,
  let p' : pred' (plift α' × unit) := p ! prj,
  have _inst : inhabited (plift α') := ⟨ plift.up (default α') ⟩,
  let J' : pred' (plift α' × unit × unit) := J ! ⟨plift.down⟩ ! pair.fst,
  have := @simulation _ _ _ p' (@True $ unit × unit) (A' H₀ INV) C J' _ _ _ o o Γ _,
  begin [temporal]
    revert this,
    let f : tvar (plift α') → tvar α' := λ v, ⟨plift.down⟩ ! v,
    let SPEC := @SPEC₀ _ _ p' (A' H₀ INV),
    let SPEC' := λ (v : tvar α'), p ! v ⋀ ◻⟦ v | A ⟧,
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
    { apply hA },
    { apply INV _ _ hJ hA  } },
  { simp [SPEC₁,C], }
end

end witness_construction

namespace refinement
section
open fairness
parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {evt : Type u₂}
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters (A : evt → act (α'×γ')) (C : evt → act (β'×γ'))
parameters {cs₀ fs₀ : evt → pred' (α'×γ')} {cs₁ fs₁ : evt → pred' (β'×γ')}
parameters (J : pred' (α'×β'×γ'))

section specs

parameters p q cs₀ fs₀ cs₁ fs₁

def SPEC₀.saf (v : tvar α') (o : tvar γ') : cpred :=
p ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ v,o | A i ⟧)

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
SPEC₀.saf v o ⋀
∀∀ i, sched (cs₀ i ! ⦃o,v⦄) (fs₀ i ! ⦃o,v⦄) ⟦ v,o | A i ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ v,o | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) ⟦ v,o | C i ⟧

def SPEC₂ (v : tvar β') (o : tvar γ') (s : tvar evt) : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, s ≃ ↑i ⋀ ⟦ v,o | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) (s ≃ ↑i ⋀ ⟦ v,o | C i ⟧)

end specs

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ w v o v' o' e,
  (w,v,o) ⊨ J →
  C e (v,o) (v',o') →
  ∃ w', A e (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ') (sch : tvar evt)

variable (Γ : cpred)

parameters β' γ'

variable Hpo : ∀ e w,
  one_to_one_po (SPEC₁ v o ⋀ SPEC₀.saf w o ⋀ ◻(J ! ⦃o,v,w⦄))
    (cs₁ e!⦃o,v⦄) (fs₁ e!⦃o,v⦄) ⟦ v,o | C e⟧
    (cs₀ e!⦃o,w⦄) (fs₀ e!⦃o,w⦄) ⟦ w,o | A e⟧
parameters {β' γ'}

section SPEC₂
variables H : Γ ⊢ SPEC₂ v o sch

open simulation (witness init_in_w C_imp_A_in_w) prod temporal.prod

def Next_a :=
λ σ σ', ∃ e, A e σ σ'

def Next_c :=
λ σ σ' : (evt × β') × γ', ∃ e, σ.1.1 = e ∧ (C e on map_left snd) σ σ'

section J
parameter evt
def J' : pred' (α' × (evt × β') × γ') :=
J ! ⟨prod.map_right $ prod.map_left prod.snd⟩

parameter q
def q' : pred' ((evt × β') × γ') :=
q ! ⟨prod.map_left prod.snd⟩

end J

variable w : tvar α'
open simulation
noncomputable def Wtn := Wtn p Next_a J' ⦃v,sch⦄ o

variable valid_witness
: Γ ⊢ Wtn w

lemma abstract_sch (e : evt)
: Γ ⊢ sch ≃ e ⋀ ⟦ w,o | A e ⟧ ≡ sch ≃ e ⋀ ⟦ w,o | Next_a ⟧ :=
sorry

section Simulation_POs
include SIM₀
lemma SIM₀' (v : evt × β') (o : γ')
  (h : (v, o) ⊨ q')
: (∃ (w : α'), (w, o) ⊨ p ∧ (w, v, o) ⊨ J') :=
begin
  simp [q',prod.map_left] at h,
  specialize SIM₀ v.2 o h,
  revert SIM₀, intros_mono,
  simp [J'],
end

omit SIM₀
include SIM
lemma SIM' (w : α') (v : evt × β') (o : γ') (v' : evt × β') (o' : γ')
  (h₀ : (w, v, o) ⊨ J')
  (h₁ : Next_c (v, o) (v', o'))
: (∃ (w' : α'), Next_a (w, o) (w', o') ∧ (w', v', o') ⊨ J') :=
sorry

include H
omit SIM
lemma H'
: Γ ⊢ simulation.SPEC₁ q' Next_c ⦃v,sch⦄ o :=
sorry

lemma witness_imp_SPEC₀_saf
  (h : Γ ⊢ Wtn w)
: Γ ⊢ SPEC₀.saf w o :=
sorry

omit H
parameters p q cs₁ fs₁
include Hpo p SIM₀ SIM

lemma SPEC₂_imp_SPEC₁
: (SPEC₂ v o sch) ⟹ (SPEC₁ v o) :=
begin [temporal]
  simp only [SPEC₁,SPEC₂,temporal.refinement.SPEC₁,temporal.refinement.SPEC₂],
  monotonicity, apply ctx_p_and_p_imp_p_and',
  { monotonicity, simp, intros x h₀ h₁,
    existsi x, exact h₁ },
  { intros h i h₀ h₁,
    replace h := h _ h₀ h₁,
    revert h, monotonicity, simp, }
end

lemma H_C_imp_A (e : evt)
: SPEC₂ v o sch ⋀ Wtn w ⋀ ◻(J ! ⦃o,v,w⦄) ⟹ ◻(sch ≃ ↑e ⋀ ⟦ v,o | C e ⟧ ⟶ ⟦ w,o | A e ⟧) :=
begin [temporal]
  intro H',
  have H : temporal.refinement.SPEC₁ v o ⋀
           temporal.refinement.Wtn w ⋀
           ◻(J ! ⦃o,v,w⦄),
  { revert H',  persistent,
    intros,
    casesm* _ ⋀ _, split* ; try { assumption },
    apply temporal.refinement.SPEC₂_imp_SPEC₁ _ Γ _
    ; auto, },
  clear Hpo,
  let J' := J' evt J,
  have SIM₀' := temporal.refinement.SIM₀', clear SIM₀,
  have SIM' := temporal.refinement.SIM',  clear SIM,
  have := C_imp_A_in_w p _ (Next_a A) (Next_c C) J' SIM₀' SIM' ⦃v,sch⦄ o Γ _ w _,
  { persistent, henceforth at this ⊢,
    simp, intros h₀ h₁, clear_except this h₀ h₁,
    suffices : sch ≃ ↑e ⋀ ⟦ w,o | A e ⟧, apply this.right,
    rw abstract_sch, split, assumption,
    apply this _,
    simp [Next_c],
    suffices : ⟦ ⦃v,sch⦄,o | λ (σ σ' : (evt × β') × γ'), (σ.fst).fst = e ∧ (C e on map_left snd) σ σ' ⟧,
    { revert this, action { simp, intro, subst e, simp, },  },
    rw [← action_and_action,← init_eq_action,action_on'], split, admit,
    simp [h₁], },
  clear_except H',
  simp [simulation.SPEC₁,SPEC₂,temporal.refinement.SPEC₂] at H' ⊢,
  cases_matching* _ ⋀ _, split,
  { simp [q'], assumption, },
  { select H' : ◻(p_exists _), clear_except H',
    henceforth at H' ⊢, cases H' with i H',
    simp [Next_c],
    suffices : ⟦ ⦃v,sch⦄,o | λ (σ σ' : (evt × β') × γ'), σ.fst.fst = i ∧ (C i on map_left snd) σ σ' ⟧,
    { revert this, action { simp, intro, subst i, simp } },
    rw [← action_and_action], },
  { cases_matching* _ ⋀ _, assumption, },
end

lemma Hpo' (e : evt)
: one_to_one_po (SPEC₂ v o sch ⋀ Wtn w ⋀ ◻(J ! ⦃o,v,w⦄))
/- -/ (cs₁ e ! ⦃o,v⦄)
      (fs₁ e ! ⦃o,v⦄)
      (sch ≃ ↑e ⋀ ⟦ v,o | C e ⟧)
/- -/ (cs₀ e ! ⦃o,w⦄)
      (fs₀ e ! ⦃o,w⦄)
      ⟦ w,o | A e ⟧ :=
begin
  have
  : temporal.refinement.SPEC₂ v o sch ⋀ temporal.refinement.Wtn w ⋀ ◻(J ! ⦃o,v,w⦄) ⟹
    temporal.refinement.SPEC₁ v o ⋀ temporal.refinement.SPEC₀.saf w o ⋀ ◻(J ! ⦃o,v,w⦄),
  begin [temporal]
    simp, intros h₀ h₁ h₂,
    split*,
    { apply temporal.refinement.SPEC₂_imp_SPEC₁ Hpo _ h₀, },
    { apply temporal.refinement.witness_imp_SPEC₀_saf ; auto, },
    { auto }
  end,
  constructor
  ; try { cases (Hpo e w)
        ; transitivity
        ; [ apply this
          , assumption ] },
  apply temporal.refinement.H_C_imp_A Hpo,
end

end Simulation_POs

include H SIM₀ SIM Hpo

lemma one_to_one
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  with_witness w : temporal.refinement.Wtn w with Hw,
  have this := H, revert this,
  dsimp [SPEC₀,SPEC₁],
  have H' := temporal.refinement.H' , -- o sch,
  apply ctx_p_and_p_imp_p_and' _ _,
  apply ctx_p_and_p_imp_p_and' _ _,
  { clear_except SIM₀ Hw H,
    replace SIM₀ := SIM₀' _ SIM₀,
    have := init_in_w p (q' evt q) (Next_a A) (J' evt J) SIM₀ ⦃v,sch⦄ o Γ,
    intro Hq,
    apply this _ Hw _,
    simp [q',proj_assoc], apply Hq, },
  { clear_except SIM SIM₀ Hw H,
    have H' := H' C v o sch _ H,
    replace SIM₀ := SIM₀' _ SIM₀,
    replace SIM := SIM' A C J SIM,
    have := temporal.simulation.C_imp_A_in_w p (q' evt q)
      (Next_a A) (Next_c C) (J' evt J) SIM₀ SIM ⦃v,sch⦄ o _ H' w Hw,
    -- replace this := this w ,
    -- have := C_imp_A_in_w p (q' evt q) (Next_a A) (Next_c C) (J' evt J) SIM₀ SIM ⦃v,sch⦄ o Γ H',
    { monotonicity only,
      simp [exists_action],
      intros e h₀ h₁, apply this _,
      simp [Next_c],
      suffices : ⟦ ⦃v,sch⦄,o | λ (σ σ' : (evt × β') × γ'), ((λ s s', s = e) on (prod.fst ∘ prod.fst)) σ σ' ∧ (C e on map_left snd) σ σ' ⟧,
      revert this, action
      { simp [function.on_fun],
        intros, subst e, assumption, },
      rw ← action_and_action, simp,
      rw [action_on,action_on,coe_over_comp,proj_assoc,← init_eq_action,coe_eq],
      simp, split ; assumption } },
  { intros h i,
    have H' := H' C v o sch _ H,
    replace h := h i,
    have hJ : ◻(J' evt J ! ⦃o,⦃v,sch⦄,w⦄),
    { replace SIM₀ := SIM₀' _ SIM₀,
      replace SIM := SIM' A C J SIM,
      apply simulation.J_inv_in_w p _ (Next_a A) _ (J' evt J) SIM₀ SIM _ o _ H' w Hw },
    simp [J'] at hJ,
    have Hpo' := Hpo' p q A C cs₁ fs₁ J _ _ _ o sch Hpo w i ; try { auto },
    apply replacement Hpo' Γ _ _,
    tauto, auto, },
end
end SPEC₂

section refinement_SPEC₂
include Hpo SIM₀ SIM
parameters cs₁ fs₁ cs₀ fs₀

lemma refinement_SPEC₂
: Γ ⊢ (∃∃ sch, SPEC₂ v o sch) ⟶ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  simp, intros sch Hc,
  apply one_to_one A C J SIM₀ SIM _ _ _ _ _  Hc
  ; assumption,
end
end refinement_SPEC₂

lemma refinement_SPEC₁
: SPEC₁ v o ⟹ (∃∃ sch, SPEC₂ v o sch) :=
sorry

include SIM₀ SIM
lemma one_to_one_refinement
  (h : ∀ c e a, one_to_one_po' (SPEC₁ c o ⋀ SPEC₀.saf a o ⋀ ◻(J ! ⦃o,c,a⦄))
         ⟨cs₁ e,fs₁ e,C e⟩
         ⟨cs₀ e,fs₀ e,A e⟩ ⦃o,c⦄ ⦃o,a⦄)
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  transitivity (∃∃ c sch, SPEC₂ q C cs₁ fs₁ c o sch),
  { apply p_exists_p_imp_p_exists ,
    intro v,
    apply refinement_SPEC₁, },
  { simp, intros c sch Hspec,
    specialize h c, simp [one_to_one_po'] at h,
    apply refinement_SPEC₂ A C cs₀ fs₀ cs₁ fs₁ J SIM₀ SIM c o _ _ _,
    exact h,
    existsi sch, assumption },
end

end
end refinement

end temporal


import temporal_logic.fairness
import temporal_logic.pair
import temporal_logic.lemmas

import util.meta.tactic

universe variables u u₀ u₁ u₂
open predicate nat

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal

namespace simulation
section

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters (p : pred' (γ'×α')) (q : pred' (γ'×β'))
parameters (A : act (γ'×α')) (C : act (γ'×β'))
parameters (J : pred' (γ'×α'×β'))

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ! ⦃ v,o ⦄ ⋀
◻⟦ o,v | A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ! ⦃ v,o ⦄ ⋀
◻⟦ o,v | C ⟧

parameters [inhabited α']
parameter SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J
parameter SIM
: ∀ w v o v' o',
  (o,w,v) ⊨ J →
  C (o,v) (o',v') →
  ∃ w', A (o,w) (o',w') ∧
        (o',w',v') ⊨ J

parameters (v : tvar β') (o : tvar γ')

parameters Γ : cpred
parameters H : Γ ⊢ SPEC₁ v o

noncomputable def Wx₀_f : tvar (β' → γ' → α') :=
λ v o, ε w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J

noncomputable def Wx₀ : tvar α' :=
Wx₀_f v o

noncomputable def Wf_f : tvar (β' → γ' → γ' → α' → α') :=
λ v' o o' w, ε w', A (o,w) (o',w') ∧
                   (o',w',v') ⊨ J

noncomputable def Wf : tvar (α' → α') :=
Wf_f (⊙v) o (⊙o)

noncomputable def Wtn (w : tvar α') :=
w ≃ Wx₀ ⋀ ◻(⊙w ≃ Wf w)

include SIM₀

lemma init_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ q!⦃v,o⦄ ⟶ p!⦃w,o⦄ :=
begin
  lifted_pred [nat.sub_self,Wtn] ,
  introv Hq, intros, simp [Hq,Wx₀,Wx₀_f],
  unfold_coes, simp [Wx₀,Wx₀_f],
  apply_epsilon_spec,
end
set_option trace.app_builder true
include H SIM
lemma J_inv_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(J ! ⦃v,w,o⦄) :=
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
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(⟦ o,v | C ⟧ ⟶ ⟦ o,w | A ⟧) :=
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
  select_witness w : temporal.simulation.Wtn w with Hw,
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

def A' : act $ unit × plift α' :=
A on (plift.down ∘ prod.snd)

parameters [_inst : inhabited α']

include FIS₀ FIS _inst
lemma witness_construction
: ⊩ ∃∃ v, p ! v ⋀ ◻⟦ v | A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (unit × plift α') α' := ⟨plift.down⟩ ! pair.snd,
  let p' : pred' (unit × plift α') := p ! prj,
  have _inst : inhabited (plift α') := ⟨ plift.up (default α') ⟩,
  let J' : pred' (unit × plift α' × unit) := J ! ⟨plift.down⟩ ! pair.fst ! pair.snd,
  have := @simulation _ _ _ _ (@True $ unit × unit) (A' H₀ INV) C J' _ _ _ o o Γ _,
  begin [temporal]
    revert this,
    let f : tvar (plift α') → tvar α' := λ v, ⟨plift.down⟩ ! v,
    let SPEC := @SPEC₀ _ _ p' (A' H₀ INV),
    let SPEC' := λ (v : tvar α'), p ! v ⋀ ◻⟦ v | A ⟧,
    apply p_exists_imp_p_exists' (λ w, SPEC w o) SPEC' f,
    intro, simp only [SPEC,f,SPEC',SPEC₀,p',prj,proj_assoc,pair.snd_mk,A'],
    monotonicity, rw [action_on,coe_over_comp,proj_assoc,pair.snd_mk'],
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

namespace one_to_one
section
open fairness
parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {evt : Type u₂}
parameters {p : pred' (γ'×α')} {q : pred' (γ'×β')}
parameters (A : evt → act (γ'×α')) (C : evt → act (γ'×β'))
parameters {cs₀ fs₀ : evt → pred' (γ'×α')} {cs₁ fs₁ : evt → pred' (γ'×β')}
parameters (J : pred' (γ'×α'×β'))

section specs

parameters p q cs₀ fs₀ cs₁ fs₁

def SPEC₀.saf (v : tvar α') (o : tvar γ') : cpred :=
p ! ⦃ v,o ⦄ ⋀
◻(∃∃ i, ⟦ o,v | A i ⟧)

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
SPEC₀.saf v o ⋀
∀∀ i, sched (cs₀ i ! ⦃v,o⦄) (fs₀ i ! ⦃v,o⦄) ⟦ o,v | A i ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ! ⦃ v,o ⦄ ⋀
◻(∃∃ i, ⟦ o,v | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃v,o⦄) (fs₁ i ! ⦃v,o⦄) ⟦ o,v | C i ⟧

def SPEC₂ (v : tvar β') (o : tvar γ') (s : tvar evt) : cpred :=
q ! ⦃ v,o ⦄ ⋀
◻(∃∃ i, s ≃ ↑i ⋀ ⟦ o,v | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃v,o⦄) (fs₁ i ! ⦃v,o⦄) (s ≃ ↑i ⋀ ⟦ o,v | C i ⟧)

end specs

parameters [inhabited α'] [inhabited evt]
parameter SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J
parameter SIM
: ∀ w v o v' o' e,
  (o,w,v) ⊨ J →
  C e (o,v) (o',v') →
  ∃ w', A e (o,w) (o',w') ∧
        (o',w',v') ⊨ J

parameters (v : tvar β') (o : tvar γ') (sch : tvar evt)

variable (Γ : cpred)

parameters β' γ'

variable Hpo : ∀ e w,
  one_to_one_po (SPEC₁ v o ⋀ SPEC₀.saf w o ⋀ ◻(J ! ⦃v,w,o⦄))
    (cs₁ e!⦃v,o⦄) (fs₁ e!⦃v,o⦄) ⟦ o,v | C e⟧
    (cs₀ e!⦃w,o⦄) (fs₀ e!⦃w,o⦄) ⟦ o,w | A e⟧
parameters {β' γ'}

section SPEC₂
variables H : Γ ⊢ SPEC₂ v o sch

open prod temporal.prod

def Next_a : act $ γ' × evt × α' :=
λ σ σ',
∃ e, σ.2.1 = e ∧ (A e on map_right snd) σ σ'

def Next_c : act $ γ' × evt × β' :=
λ σ σ',
∃ e, σ.2.1 = e ∧ (C e on map_right snd) σ σ'

section J
def J' : pred' (γ' × (evt × α') × (evt × β')) :=
J ! ⟨ prod.map_right $ prod.map prod.snd prod.snd ⟩

def p' : pred' (γ' × evt × α') :=
p ! ⟨prod.map_right prod.snd⟩

def q' : pred' (γ' × evt × β') :=
q ! ⟨prod.map_right prod.snd⟩

end J

variable w : tvar α'
open simulation function
noncomputable def Wtn := Wtn p' Next_a J' ⦃v,sch⦄ o

variable valid_witness
: Γ ⊢ Wtn ⦃w,sch⦄

lemma abstract_sch (e : evt)
: Γ ⊢ sch ≃ e ⋀ ⟦ o,w | A e ⟧ ≡ sch ≃ e ⋀ ⟦ o,sch,w | Next_a ⟧ :=
begin
  lifted_pred,
  split ; intro h ; split
  ; cases h with h₀ h₁ ; try { assumption },
  { simp [Next_a,on_fun,h₀], auto, },
  { simp [Next_a,on_fun,h₀] at h₁, auto }
end

section Simulation_POs
include SIM₀
lemma SIM₀' (v : evt × β') (o : γ')
  (h : (o, v) ⊨ q')
: (∃ (w : evt × α'), (o, w) ⊨ p' ∧ (o, w, v) ⊨ J') :=
begin
  simp [q',prod.map_left] at h,
  specialize SIM₀ v.2 o h,
  revert SIM₀, intros_mono,
  simp [J',p',map], intros, split,
  tauto,
end

omit SIM₀
include SIM
lemma SIM' (w : evt × α') (v : evt × β') (o : γ') (v' : evt × β') (o' : γ')
  (h₀ : (o, w, v) ⊨ J')
  (h₁ : Next_c (o, v) (o', v'))
: (∃ w', Next_a (o,w) (o',w') ∧ (o', w', v') ⊨ J') :=
sorry

include H
omit SIM
lemma H'
: Γ ⊢ simulation.SPEC₁ q' Next_c ⦃v,sch⦄ o :=
sorry

lemma witness_imp_SPEC₀_saf
  (h : Γ ⊢ Wtn ⦃w,sch⦄)
: Γ ⊢ SPEC₀.saf w o :=
sorry

omit H
parameters p q cs₁ fs₁
include Hpo p SIM₀ SIM

lemma SPEC₂_imp_SPEC₁
: (SPEC₂ v o sch) ⟹ (SPEC₁ v o) :=
begin [temporal]
  simp only [SPEC₁,SPEC₂,temporal.one_to_one.SPEC₁,temporal.one_to_one.SPEC₂],
  monotonicity, apply ctx_p_and_p_imp_p_and',
  { monotonicity, simp, intros x h₀ h₁,
    existsi x, exact h₁ },
  { intros h i h₀ h₁,
    replace h := h _ h₀ h₁,
    revert h, monotonicity, simp, }
end

lemma H_C_imp_A (e : evt)
: SPEC₂ v o sch ⋀ Wtn ⦃w,sch⦄ ⋀ ◻(J ! ⦃v,w,o⦄) ⟹
  ◻(sch ≃ ↑e ⋀ ⟦ o,v | C e ⟧ ⟶ ⟦ o,w | A e ⟧) :=
begin [temporal]
  intro H',
  have H : temporal.one_to_one.SPEC₁ v o ⋀
           temporal.one_to_one.Wtn ⦃w,sch⦄ ⋀
           ◻(J ! ⦃v,w,o⦄),
  { revert H',  persistent,
    intro, casesm* _ ⋀ _, split* ; try { assumption },
    apply temporal.one_to_one.SPEC₂_imp_SPEC₁ _ Γ _,
    auto, casesm* _ ⋀ _, auto, },
  clear Hpo,
  let J' := temporal.one_to_one.J',
  have SIM₀' := temporal.one_to_one.SIM₀', clear SIM₀,
  have SIM' := temporal.one_to_one.SIM',  clear SIM,
  have := C_imp_A_in_w p' _ (Next_a A) (Next_c C) J' SIM₀' SIM' ⦃v,sch⦄ o Γ _ ⦃w,sch⦄ _,
  { persistent, henceforth at this ⊢,
    simp, intros h₀ h₁, clear_except this h₀ h₁,
    suffices : sch ≃ ↑e ⋀ ⟦ o,w | A e ⟧, apply this.right,
    rw abstract_sch, split, assumption,
    apply this _,
    simp [Next_c],
    suffices : ⟦ o,sch,v | λ (σ σ' : γ' × evt × β'), (σ.snd).fst = e ∧ (C e on map_right snd) σ σ' ⟧,
    { revert this, action { simp, intro, subst e, simp, },  },
    rw [← action_and_action,← init_eq_action,action_on'], split, admit,
    simp [h₁], },
  clear_except H',
  simp [simulation.SPEC₁,SPEC₂,temporal.one_to_one.SPEC₂] at H' ⊢,
  cases_matching* _ ⋀ _, split,
  { simp [q'], assumption, },
  { select H' : ◻(p_exists _), clear_except H',
    henceforth at H' ⊢, cases H' with i H',
    simp [Next_c],
    suffices : ⟦ o,sch,v | λ (σ σ' : γ' × evt × β'), σ.snd.fst = i ∧ (C i on map_right snd) σ σ' ⟧,
    { revert this, action { simp, intro, subst i, simp } },
    rw [← action_and_action], },
  { cases_matching* _ ⋀ _, assumption, },
end

lemma Hpo' (e : evt)
: one_to_one_po (SPEC₂ v o sch ⋀ Wtn ⦃w,sch⦄ ⋀ ◻(J ! ⦃v,w,o⦄))
/- -/ (cs₁ e ! ⦃v,o⦄)
      (fs₁ e ! ⦃v,o⦄)
      (sch ≃ ↑e ⋀ ⟦ o,v | C e ⟧)
/- -/ (cs₀ e ! ⦃w,o⦄)
      (fs₀ e ! ⦃w,o⦄)
      ⟦ o,w | A e ⟧ :=
begin
  have
  : temporal.one_to_one.SPEC₂ v o sch ⋀ temporal.one_to_one.Wtn ⦃w,sch⦄ ⋀ ◻(J ! ⦃v,w,o⦄) ⟹
    temporal.one_to_one.SPEC₁ v o ⋀ temporal.one_to_one.SPEC₀.saf w o ⋀ ◻(J ! ⦃v,w,o⦄),
  begin [temporal]
    simp, intros h₀ h₁ h₂,
    split*,
    { apply temporal.one_to_one.SPEC₂_imp_SPEC₁ Hpo _ h₀, },
    { apply temporal.one_to_one.witness_imp_SPEC₀_saf ; auto, },
    { auto }
  end,
  constructor
  ; try { cases (Hpo e w)
        ; transitivity
        ; [ apply this
          , assumption ] },
  apply temporal.one_to_one.H_C_imp_A Hpo,
end

end Simulation_POs

include H SIM₀ SIM Hpo

lemma sched_ref (i : evt) (w : tvar (evt × α'))
 (Hw : Γ ⊢ Wtn w)
 (h : Γ ⊢ sched (cs₁ i ! ⦃v,o⦄) (fs₁ i ! ⦃v,o⦄) (sch ≃ ↑i ⋀ ⟦ o,v | C i ⟧))
: Γ ⊢ sched (cs₀ i ! ⦃pair.snd ! w,o⦄) (fs₀ i ! ⦃pair.snd ! w,o⦄) ⟦ o,pair.snd ! w | A i ⟧ :=
begin [temporal]
  have H' := one_to_one.H' C v o sch _ H,
  have hJ : ◻(J' J ! ⦃v,sch,w,o⦄),
  { replace SIM₀ := SIM₀' _ SIM₀,
    replace SIM := SIM' A C J SIM,
    apply simulation.J_inv_in_w p' q' (Next_a A) _ (J' J) SIM₀ SIM _ o _ H' w Hw },
  simp [J'] at hJ,
  have Hpo' := Hpo' p q A C cs₁ fs₁ J _ _ _ o sch Hpo (pair.snd ! w) i ; try { auto },
  apply replacement Hpo' Γ _ _,
  clear Hpo Hpo' SIM SIM₀,
  have : ◻ (⦃pair.snd ! w,sch⦄ ≃ w),
  { simp [Wtn,simulation.Wtn] at Hw,
    cases Hw with Hw₀ Hw₁,
    apply induct _ _ _ _,
    { persistent,
      henceforth, intro h',
      admit }, admit  },
  rw [this], tauto, auto,
end

lemma one_to_one
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  apply p_exists_partial_intro _ (proj $ @pair.snd evt α') _ _,
  select_witness w : temporal.one_to_one.Wtn w with Hw,
  have this := H, revert this,
  dsimp [SPEC₀,SPEC₁],
  have H' := temporal.one_to_one.H' , -- o sch,
  apply ctx_p_and_p_imp_p_and' _ _,
  apply ctx_p_and_p_imp_p_and' _ _,
  { clear_except SIM₀ Hw H,
    replace SIM₀ := SIM₀' _ SIM₀,
    have := init_in_w p' q' (Next_a A) (J' J) SIM₀ ⦃v,sch⦄ o Γ,
    intro Hq,
    replace this := this _ Hw _, simp [p'] at this,
    apply this,
    simp [q',proj_assoc], apply Hq, },
  { clear_except SIM SIM₀ Hw H,
    have H' := H' C v o sch _ H,
    replace SIM₀ := SIM₀' _ SIM₀,
    replace SIM := SIM' A C J SIM,
    have := temporal.simulation.C_imp_A_in_w p' q'
      (Next_a A) (Next_c C) (J' J) SIM₀ SIM ⦃v,sch⦄ o _ H' w Hw,
    { monotonicity only,
      simp [exists_action],
      intros e h₀ h₁, replace this := this _,
      { revert this,
        explicit { simp [Next_a,on_fun], intros h, exact ⟨_,h⟩ }, },
      simp [Next_c],
      suffices : ⟦ o,sch,v | λ (σ σ' : γ' × evt × β'), ((λ s s', s = e) on (prod.fst ∘ prod.snd)) σ σ' ∧ (C e on map_right prod.snd) σ σ' ⟧,
      revert this, action
      { simp [function.on_fun],
        intros, subst e, assumption, },
      rw ← action_and_action, simp,
      rw [action_on,action_on,coe_over_comp,proj_assoc,← init_eq_action,coe_eq],
      simp, split ; assumption } },
  { intros h i,
    replace h := h i,
    apply temporal.one_to_one.sched_ref ; auto },
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
lemma refinement
  (h : ∀ c e a, one_to_one_po' (SPEC₁ c o ⋀ SPEC₀.saf a o ⋀ ◻(J ! ⦃c,a,o⦄))
         ⟨cs₁ e,fs₁ e,C e⟩
         ⟨cs₀ e,fs₀ e,A e⟩ ⦃c,o⦄ ⦃a,o⦄)
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
end one_to_one

end temporal

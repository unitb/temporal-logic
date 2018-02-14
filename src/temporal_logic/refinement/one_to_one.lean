import .simulation

import ..scheduling
import ..spec

universe variables u u₀ u₁ u₂
open predicate nat
local infix ` ≃ `:75 := v_eq
local prefix `♯ `:0 := cast (by simp)

namespace temporal

namespace one_to_one
section
open fairness
parameters {α : Type u} {β : Type u₀} {γ : Type u₁ }
parameters {evt : Type u₂}
parameters {p : pred' (γ×α)} {q : pred' (γ×β)}
parameters (A : evt → act (γ×α)) (C : evt → act (γ×β))
parameters {cs₀ fs₀ : evt → pred' (γ×α)} {cs₁ fs₁ : evt → pred' (γ×β)}
parameters (J : pred' (γ×α×β))
parameters (Jₐ : pred' (γ×α))

def C' (e : evt) : act (evt×γ×β) :=
λ ⟨sch,s⟩ ⟨_,s'⟩, sch = e ∧ C e s s'

abbreviation ae (i : evt) : event (γ×α) := ⟨cs₀ i,fs₀ i,A i⟩
abbreviation ce (i : evt) : event (evt×γ×β) := ⟨cs₁ i!pair.snd,fs₁ i!pair.snd,C' i⟩

section specs

parameters p q cs₀ fs₀ cs₁ fs₁


def SPEC₀.saf' (v : tvar α) (o : tvar γ) (sch : tvar evt) : cpred :=
spec_saf_spec p cs₀ fs₀ A ⦃o,v⦄ sch

def SPEC₀ (v : tvar α) (o : tvar γ) : cpred :=
spec p cs₀ fs₀ A ⦃o,v⦄

def SPEC₁ (v : tvar β) (o : tvar γ) : cpred :=
spec q cs₁ fs₁ C ⦃o,v⦄

def SPEC₂ (v : tvar β) (o : tvar γ) (s : tvar evt) : cpred :=
spec_sch q cs₁ fs₁ C ⦃o,v⦄ s

end specs

parameters [inhabited α] [inhabited evt]
parameter SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J
parameter SIM
: ∀ w v o v' o' e,
  (o,w,v) ⊨ J →
  (o,w) ⊨ Jₐ →
  (o,v) ⊨ cs₁ e →
  (o,v) ⊨ fs₁ e →
  C e (o,v) (o',v') →
  ∃ w', (o,w) ⊨ cs₀ e ∧
        (o,w) ⊨ fs₀ e ∧
        A e (o,w) (o',w') ∧
        (o',w',v') ⊨ J

parameters (v : tvar β) (o : tvar γ) (sch : tvar evt)

variable (Γ : cpred)

parameters β γ

variable HJₐ : Γ ⊢ ∀∀ w, SPEC₀ w o ⟶ ◻(Jₐ ! ⦃o,w⦄)

variable Hpo : ∀ w e sch,
  one_to_one_po' (SPEC₁ v o ⋀ SPEC₀.saf' w o sch ⋀ ◻(J ! ⦃o,w,v⦄))
     (ce e) (ae e) ⦃sch,o,v⦄ ⦃o,w⦄

parameters {β γ}

section SPEC₂
variables H : Γ ⊢ SPEC₂ v o sch

open prod temporal.prod

def Next_a : act $ (γ × evt) × α :=
λ σ σ',
∃ e, σ.1.2 = e ∧
     map_left fst σ ⊨ cs₀ e ∧
     map_left fst σ ⊨ fs₀ e ∧
     (A e on map_left fst) σ σ'

def Next_c : act $ (γ × evt) × β :=
λ σ σ',
∃ e, σ.1.2 = e ∧
     map_left fst σ ⊨ cs₁ e ∧
     map_left fst σ ⊨ fs₁ e ∧
     (C e on map_left fst) σ σ'

section J
def J' : pred' ((γ × evt) × α × β) :=
J ! ⟨ prod.map_left fst ⟩

def JJₐ : pred' ((γ × evt) × α) :=
Jₐ ! ⟨ prod.map_left fst ⟩

def p' : pred' ((γ × evt) × α) :=
p ! ⟨ prod.map_left fst ⟩

def q' : pred' ((γ × evt) × β) :=
q ! ⟨ prod.map_left fst ⟩

end J

variable w : tvar α
open simulation function
noncomputable def Wtn := Wtn p' Next_a J' v ⦃o,sch⦄

variable valid_witness
: Γ ⊢ Wtn w

lemma abstract_sch (e : evt)
: Γ ⊢ sch ≃ e ⋀ cs₀ e ! ⦃o,w⦄ ⋀ fs₀ e ! ⦃o,w⦄ ⋀ ⟦ o,w | A e ⟧ ≡
      sch ≃ e ⋀ ⟦ ⦃o,sch⦄,w | Next_a ⟧ :=
begin
  lifted_pred,
  split ; intro h ; split
  ; casesm* _ ∧ _ ; try { assumption }
  ; simp [Next_a,on_fun] at * ; cc,
end

section Simulation_POs
include SIM₀
lemma SIM₀' (v : β) (o : γ × evt)
  (h : (o, v) ⊨ q')
: (∃ (w : α), (o, w) ⊨ p' ∧ (o, w, v) ⊨ J') :=
begin
  simp [q',prod.map_left] at h,
  specialize SIM₀ v o.1 h,
  revert SIM₀, intros_mono,
  simp [J',p',map], intros,
  constructor_matching* [Exists _, _ ∧ _] ;
  tauto,
end

omit SIM₀
include SIM
lemma SIM' (w : α) (v : β) (o : γ × evt) (v' : β) (o' : γ × evt)
  (h₀ : (o, w, v) ⊨ J')
  (h₃ : (o, w) ⊨ JJₐ)
  (h₄ : Next_c (o, v) (o', v'))
: (∃ w', Next_a (o,w) (o',w') ∧ (o', w', v') ⊨ J') :=
begin
  simp [J',map] at h₀,
  simp [Next_c,on_fun] at h₄,
  casesm* _ ∧ _,
  simp [JJₐ] at h₃,
  specialize SIM w v o.1 v' o'.1 o.2 h₀ _ _ _ _
  ; try { assumption },
  cases SIM with w' SIM,
  existsi [w'],
  simp [Next_a, J',on_fun,map,h₀],
  tauto,
end

include H
omit SIM
lemma H'
: Γ ⊢ simulation.SPEC₁ q' Next_c v ⦃o,sch⦄ :=
begin [temporal]
  simp [SPEC₂,simulation.SPEC₁,q'] at H ⊢,
  split, tauto,
  casesm* _ ⋀ _,
  select h : ◻p_exists _,
  henceforth! at h ⊢,
  cases h with e h,
  explicit' [Next_c,sched]
  { casesm* _ ∧ _, subst e, tauto, }
end

include SIM₀ SIM
lemma witness_imp_SPEC₀_saf
  (h : Γ ⊢ Wtn w)
: Γ ⊢ SPEC₀.saf' w o sch :=
begin [temporal]
  have hJ := J_inv_in_w p' q'
                        temporal.one_to_one.Next_a
                        temporal.one_to_one.Next_c
                        temporal.one_to_one.J'
                        temporal.one_to_one.JJₐ
                        temporal.one_to_one.SIM₀'
                        temporal.one_to_one.SIM'
                        v ⦃o,sch⦄ Γ
                        (temporal.one_to_one.H' _ H) _ h,
  have hJ' := abs_J_inv_in_w p' q'--
                        temporal.one_to_one.Next_a
                        temporal.one_to_one.J'
                        temporal.one_to_one.JJₐ
                        temporal.one_to_one.SIM₀'
                        v ⦃o,sch⦄ Γ
                        _ h ,
  simp [SPEC₀.saf',SPEC₂,Wtn,simulation.Wtn] at h ⊢ H,
  casesm* _ ⋀ _,
  split,
  { clear SIM hJ,
    select h : w ≃ _,
    select h' : q ! _,
    rw [← pair.snd_mk sch w,h],
    explicit
    { simp [Wx₀] at ⊢ h', unfold_coes,
      simp [Wx₀_f,p',J',map],
      cases SIM₀ (σ ⊨ v) (σ ⊨ o) h',
      apply_epsilon_spec, } },
  { clear SIM₀,
    select h : ◻(_ ≃ _),
    select h' : ◻(p_exists _),
    henceforth! at h h' ⊢ hJ hJ',
    explicit' [Wf,Wf_f,J',JJₐ]
    { simp [Next_a,on_fun] at h h',
      casesm* [_ ∧ _,Exists _],
      subst w', subst h'_w,
      apply_epsilon_spec,
      have : (∃ (w' : α), (o, w) ⊨ cs₀ sch ∧
      (o, w) ⊨ fs₀ sch ∧ A sch (o, w) (o', w') ∧ (o', w', v') ⊨ J), auto,
      cases this, tauto, } },
end

omit H
parameters p q cs₁ fs₁
include Hpo p

lemma SPEC₂_imp_SPEC₁
: (SPEC₂ v o sch) ⟹ (SPEC₁ v o) :=
begin [temporal]
  simp only [SPEC₁,SPEC₂,temporal.one_to_one.SPEC₁,temporal.one_to_one.SPEC₂],
  monotonicity, apply ctx_p_and_p_imp_p_and',
  { monotonicity, simp, intros x h₀ h₁ _ _,
    existsi x, tauto, },
  { intros h i h₀ h₁,
    replace h := h _ h₀ h₁,
    revert h, monotonicity, simp, }
end

lemma H_C_imp_A (e : evt)
: SPEC₂ v o sch ⋀ Wtn w ⋀ ◻(J ! ⦃o,w,v⦄) ⟹
  ◻(cs₁ e ! ⦃o,v⦄ ⋀ fs₁ e ! ⦃o,v⦄ ⋀ sch ≃ ↑e ⋀ ⟦ o,v | C e ⟧ ⟶ cs₀ e ! ⦃o,w⦄ ⋀ fs₀ e ! ⦃o,w⦄ ⋀ ⟦ o,w | A e ⟧) :=
begin [temporal]
  intro H',
  have H : temporal.one_to_one.SPEC₁ v o ⋀
           temporal.one_to_one.Wtn w ⋀
           ◻(J ! ⦃o,w,v⦄),
  { revert H',  persistent,
    intro, casesm* _ ⋀ _, split* ; try { assumption },
    apply temporal.one_to_one.SPEC₂_imp_SPEC₁ _ Γ _,
    auto, casesm* _ ⋀ _, auto, },
  clear Hpo,
  let J' := temporal.one_to_one.J',
  have SIM₀' := temporal.one_to_one.SIM₀', clear SIM₀,
  have SIM' := temporal.one_to_one.SIM',  clear SIM,
  have := C_imp_A_in_w p' _ (Next_a A) (Next_c C) J' _ SIM₀' SIM' v ⦃o,sch⦄ Γ _ w _,
  { henceforth! at this ⊢,
    simp, intros h₀ h₁ h₂ h₃, clear_except this h₀ h₁ h₂ h₃,
    suffices : sch ≃ ↑e ⋀ cs₀ e ! ⦃o,w⦄ ⋀ fs₀ e ! ⦃o,w⦄ ⋀ ⟦ o,w | A e ⟧, admit,
    rw abstract_sch, split, assumption,
    apply this _,
    simp [Next_c],
    suffices : ⟦ ⦃o,sch⦄,v | λ (σ σ' : (γ × evt) × β), (σ.fst).snd = e ∧ (C e on map_left fst) σ σ' ⟧,
    { explicit' { cc, }, },
    rw [← action_and_action,← init_eq_action,action_on'], split,
    explicit
    { simp at ⊢ h₀, assumption },
    simp [h₃], },
  clear_except H',
  simp [simulation.SPEC₁,SPEC₂,temporal.one_to_one.SPEC₂] at H' ⊢,
  cases_matching* _ ⋀ _, split,
  { simp [q'], assumption, },
  { select H' : ◻(p_exists _), clear_except H',
    henceforth at H' ⊢, cases H' with i H',
    simp [Next_c],
    suffices : ⟦ ⦃o,sch⦄,v | λ (σ σ' : (γ × evt) × β), (σ.fst).snd = i ∧ (C i on map_left fst) σ σ' ⟧,
    { explicit' { cases this, subst i, tauto, } },
    explicit' { cc }, },
  { cases_matching* _ ⋀ _, assumption, },
end

lemma Hpo' (e : evt)
: one_to_one_po (SPEC₂ v o sch ⋀ Wtn w ⋀ ◻(J ! ⦃o,w,v⦄))
/- -/ (cs₁ e ! ⦃o,v⦄)
      (fs₁ e ! ⦃o,v⦄)
      (sch ≃ ↑e ⋀ ⟦ o,v | C e ⟧)
/- -/ (cs₀ e ! ⦃o,w⦄)
      (fs₀ e ! ⦃o,w⦄)
      ⟦ o,w | A e ⟧ :=
begin
  have
  : temporal.one_to_one.SPEC₂ v o sch ⋀ temporal.one_to_one.Wtn w ⋀ ◻(J ! ⦃o,w,v⦄) ⟹
    temporal.one_to_one.SPEC₁ v o ⋀ temporal.one_to_one.SPEC₀.saf' w o sch ⋀ ◻(J ! ⦃o,w,v⦄),
  begin [temporal]
    simp, intros h₀ h₁ h₂,
    split*,
    { apply temporal.one_to_one.SPEC₂_imp_SPEC₁ Hpo _ h₀, },
    { apply temporal.one_to_one.witness_imp_SPEC₀_saf ; auto, },
    { auto }
  end,
  constructor,
  iterate 3
  { cases (Hpo w e sch),
    simp at *,
    transitivity,
    { apply this },
    { assumption }, },
  begin [temporal]
    intros Hs,
    have H_imp := temporal.one_to_one.H_C_imp_A Hpo w e _ Hs,
    henceforth! at ⊢ H_imp,
    simp at H_imp ⊢,
    exact H_imp,
  end
end

end Simulation_POs

include H SIM₀ SIM Hpo

lemma sched_ref (i : evt) (w : tvar α)
 (Hw : Γ ⊢ Wtn w)
 (h : Γ ⊢ sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) (sch ≃ ↑i ⋀ ⟦ o,v | C i ⟧))
: Γ ⊢ sched (cs₀ i ! ⦃o,w⦄) (fs₀ i ! ⦃o,w⦄)
            ⟦ o,w | A i ⟧ :=
begin [temporal]
  have H' := one_to_one.H' C v o sch _ H,
  have hJ : ◻(J' J ! ⦃⦃o,sch⦄,w,v⦄),
  { replace SIM₀ := SIM₀' _ SIM₀,
    replace SIM := SIM' A C J _ SIM,
    apply simulation.J_inv_in_w p' q' (Next_a A) _ (J' J) _ SIM₀ SIM _ ⦃o,sch⦄ _ H' w Hw, },
  simp [J'] at hJ,
  have Hpo' := temporal.one_to_one.Hpo' Hpo w i,
  apply replacement Hpo' Γ _,
  tauto, auto,
end

lemma one_to_one
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  select_witness w : temporal.one_to_one.Wtn w with Hw,
  have this := H, revert this,
  dsimp [SPEC₀,SPEC₁],
  have H' := temporal.one_to_one.H' , -- o sch,
  apply ctx_p_and_p_imp_p_and' _ _,
  apply ctx_p_and_p_imp_p_and' _ _,
  { clear_except SIM₀ Hw H,
    replace SIM₀ := temporal.one_to_one.SIM₀',
    have := init_in_w p' q' (Next_a A) (J' J) SIM₀ v ⦃o,sch⦄ Γ _ Hw,
    intro Hq,
    simp [p',q'] at this,
    auto, },
  { clear_except SIM SIM₀ Hw H,
    have H' := H' C v o sch _ H,
    replace SIM₀ := SIM₀' _ SIM₀,
    replace SIM := SIM' A C J _ SIM,
    have := temporal.simulation.C_imp_A_in_w p' q'
      (Next_a A) (Next_c C) (J' J) _ SIM₀ SIM v ⦃o,sch⦄ _ H' w Hw,
    { monotonicity!,
      simp [exists_action],
      intros e h₀ h₁ h₂ h₃, replace this := this _,
      explicit' [Next_a]
      { intros, casesm* _ ∧ _,
        constructor_matching* [Exists _,_ ∧ _] ; auto, },
      simp [Next_c],
      suffices : ⟦ ⦃o,sch⦄,v | λ (σ σ' : (γ × evt) × β), map_left prod.fst σ ⊨ fs₁ e ∧ ((λ s s', s = e) on (prod.snd ∘ prod.fst)) σ σ' ∧ (C e on map_left prod.fst) σ σ' ⟧,
      explicit'
      { intros, subst e, tauto, },
      henceforth at this,
      explicit' [Next_c]
      { tauto } } },
  { intros h i,
    replace h := h i,
    apply temporal.one_to_one.sched_ref; auto },
end
end SPEC₂

section refinement_SPEC₂
include Hpo SIM₀ SIM
parameters cs₁ fs₁ cs₀ fs₀

lemma refinement_SPEC₂
: Γ ⊢ (∃∃ sch, SPEC₂ v o sch) ⟶ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  simp, intros sch Hc,
  apply one_to_one A C J Jₐ SIM₀ SIM _ _ _ _ _  Hc,
  apply Hpo,
end
end refinement_SPEC₂

lemma refinement_SPEC₁ [schedulable evt]
: SPEC₁ v o ⟹ (∃∃ sch, SPEC₂ v o sch) :=
assume Γ,
sch_intro _ _ _ _ _ _

include SIM₀ SIM
lemma refinement [schedulable evt]
  (h : ∀ c a e sch, one_to_one_po' (SPEC₁ c o ⋀ SPEC₀.saf' a o sch ⋀ ◻(J ! ⦃o,a,c⦄))
         ⟨cs₁ e!pair.snd,fs₁ e!pair.snd,C' e⟩
         ⟨cs₀ e,fs₀ e,A e⟩ ⦃sch,o,c⦄ ⦃o,a⦄)
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  transitivity (∃∃ c sch, SPEC₂ q C cs₁ fs₁ c o sch),
  { apply p_exists_p_imp_p_exists ,
    intro v,
    apply refinement_SPEC₁, },
  { simp, intros c sch Hspec,
    specialize h c, simp [one_to_one_po'] at h,
    apply refinement_SPEC₂ A C cs₀ fs₀ cs₁ fs₁ J Jₐ SIM₀ SIM c o _ _ _,
    simp [one_to_one_po'],
    exact h,
    existsi sch, assumption },
end

end
end one_to_one

end temporal

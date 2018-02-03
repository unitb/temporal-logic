import ..scheduling
import ..fairness

import util.predicate

universe variables u u₀ u₁ u₂ u₃
open predicate nat

local infix ` ≃ `:75 := v_eq

namespace temporal

namespace many_to_many
section
open fairness
parameters {α : Type u} {β : Type u₀} {γ : Type u₁ }
parameters {aevt : Type u₂} {cevt : Type u₃}
parameters {p : pred' (γ×α)} {q : pred' (γ×β)}
parameters (A : aevt → act (γ×α)) (C : cevt → act (γ×β))
parameters {cs₀ fs₀ : aevt → pred' (γ×α)} {cs₁ fs₁ : cevt → pred' (γ×β)}
parameters (J : pred' (γ×α×β))
parameter ref : aevt → cevt → Prop
parameter wit : Π a, subtype (ref a) → cpred

open prod

def C' (e : cevt) : act (cevt×γ×β) :=
λ ⟨sch,s⟩ ⟨_,s'⟩, sch = e ∧ C e s s'

abbreviation ae (i : aevt) : event (γ×α) := ⟨cs₀ i,fs₀ i,A i⟩
abbreviation ce (i : cevt) : event (γ×β) := ⟨cs₁ i,fs₁ i,C i⟩

abbreviation ae' (i : aevt) : event (γ×α×aevt) :=
{ p := cs₀ i!⟨prod.map_right fst⟩
, q := fs₀ i!⟨prod.map_right fst⟩
, A := λ s s', s.2.2 = i ∧ (A i on prod.map_right fst) s s' }
abbreviation ce' (i : cevt) (j : aevt) : event (γ×β×cevt×aevt) :=
{ p := cs₁ i!⟨prod.map_right fst⟩
, q := fs₁ i!⟨prod.map_right fst⟩
, A := λ ⟨o,v,ce,_⟩ ⟨o',v',_,ae'⟩, ae' = j ∧ ce = i ∧ C i (o,v) (o',v') }

section specs

parameters p q cs₀ fs₀ cs₁ fs₁

def SPEC₀.saf (v : tvar α) (o : tvar γ) : cpred :=
p ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ o,v | A i ⟧)

def SPEC₀.saf' (v : tvar α) (o : tvar γ) (sch : tvar aevt) : cpred :=
p ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⊙sch ≃ ↑i ⋀ ⟦ o,v | A i ⟧)

def SPEC₀ (v : tvar α) (o : tvar γ) : cpred :=
SPEC₀.saf v o ⋀
∀∀ i, sched (cs₀ i ! ⦃o,v⦄) (fs₀ i ! ⦃o,v⦄) ⟦ o,v | A i ⟧

def SPEC₁ (v : tvar β) (o : tvar γ) : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ o,v | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) ⟦ o,v | C i ⟧

def SPEC₂ (v : tvar β) (o : tvar γ) (s : tvar cevt) : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻(∃∃ i, s ≃ ↑i ⋀ ⟦ o,v | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) (s ≃ ↑i ⋀ ⟦ o,v | C i ⟧)

end specs

parameters [inh_α : inhabited α]
           [inh_cevt : inhabited cevt]
           [inh_aevt : inhabited aevt]

parameter Hc2a : ∀ ce : cevt, ∃ ae : aevt, ref ae ce

parameter SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J
parameter SIM
: ∀ w v o v' o' ce,
  (o,w,v) ⊨ J →
  C ce (o,v) (o',v') →
  ∃ ae w', (o',w',v') ⊨ J ∧
           ref ae ce ∧
           A ae (o,w) (o',w')

section obligations

parameters (v : tvar β) (o : tvar γ)
parameters (Γ : cpred)

parameters β γ
variable Hpo : ∀ (e : aevt) (w : tvar α) (sch : tvar aevt),
  many_to_many_po'
    (subtype (ref e))
    (SPEC₁ v o ⋀ SPEC₀.saf' w o sch ⋀ ◻(J ! ⦃o,w,v⦄))
    (wit e)
    (λ e', ce e') (ae e)
    ⦃o,v⦄ ⦃o,w⦄
parameters {β γ}

section conc_sch

parameters (sch_c : tvar cevt)

variable (sch_a : tvar aevt)

section SPEC₂
variable H : Γ ⊢ SPEC₂ v o sch_c

open prod temporal.prod

def Next_a : act $ γ × aevt × α :=
λ σ σ',
∃ e, σ.2.1 = e ∧ (A e on map_right snd) σ σ'

def Next_c : act $ γ × cevt × β :=
λ σ σ',
∃ e, σ.2.1 = e ∧ (C e on map_right snd) σ σ'

section J
def J' : pred' (γ × (aevt × α) × (cevt × β)) :=
J ! ⟨ prod.map_right $ prod.map prod.snd prod.snd ⟩ ⋀
⟨ λ ⟨_, a, c⟩, ref a.1 c.1 ⟩

def p' : pred' (γ × aevt × α) :=
p ! ⟨prod.map_right prod.snd⟩

def q' : pred' (γ × cevt × β) :=
q ! ⟨prod.map_right prod.snd⟩

end J
variable w : tvar α
open function
include inh_aevt inh_α
noncomputable def Wx₀_f : tvar (β → γ → aevt × α) :=
λ v o, ε w : aevt × _, (o,w.2) ⊨ p ∧ (o,w.2,v) ⊨ J

noncomputable def Wx₀ : tvar (aevt × α) :=
Wx₀_f v o

noncomputable def Wf_f : tvar (cevt → β → γ → γ → aevt × α → aevt × α) :=
⟪ℕ, λ ce v' o o' (w : _ × _),
      ε w' : aevt × α,
             (o',w'.2,v') ⊨ J ∧
             ref w'.1 ce ∧
             A w'.1 (o,w.2) (o',w'.2) ⟫

noncomputable def Wf : tvar (aevt × α → aevt × α) :=
Wf_f sch_c (⊙v) o (⊙o)

noncomputable def Wtn (w : tvar (aevt × α)) :=
w ≃ Wx₀ ⋀ ◻(⊙w ≃ Wf w)

lemma Wx₀_def' (σ : ℕ)
: σ ⊨ Wx₀ =
  ε w : _ × α, (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J :=
by repeat { unfold_coes <|> simp [Wx₀,Wx₀_f] }

@[simp,predicate]
lemma Wx₀_def (σ : ℕ) (a b)
: (a,b) = σ ⊨ Wx₀ ↔
  a = (ε w : _ × α,    (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J).fst ∧
  b = (ε w : aevt × α, (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J).snd :=
by repeat { unfold_coes <|> simp [Wx₀,Wx₀_f,ext] }

lemma Wf_def' (σ : ℕ) (w)
: σ ⊨ Wf ⦃sch_a,w⦄ =
  ε w' : _ × α,
         (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
               ref w'.1 (σ ⊨ sch_c) ∧
               A w'.1 (σ ⊨ o,σ ⊨ w) (succ σ ⊨ o,w'.2) :=
by repeat { unfold_coes <|> simp [Wf,Wf_f] }

@[simp,predicate]
lemma Wf_def (σ : ℕ) (w) (a b)
: (a,b) = σ ⊨ Wf ⦃sch_a,w⦄ ↔
  a = (ε w' : _ × α,
         (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
               ref w'.1 (σ ⊨ sch_c) ∧
               A w'.1 (σ ⊨ o,σ ⊨ w) (succ σ ⊨ o,w'.2)).1 ∧
  b = (ε w' : aevt × α,
         (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
               ref w'.1 (σ ⊨ sch_c) ∧
               A w'.1 (σ ⊨ o,σ ⊨ w) (succ σ ⊨ o,w'.2)).2 :=
by repeat { unfold_coes <|> simp [Wf,Wf_f,ext] }

variable valid_witness
: Γ ⊢ Wtn ⦃sch_a,w⦄

lemma abstract_sch (e : aevt)
: Γ ⊢ sch_a ≃ e ⋀ ⟦ o,w | A e ⟧ ≡ sch_a ≃ e ⋀ ⟦ o,sch_a,w | Next_a ⟧ :=
begin
  lifted_pred,
  split ; intro h ; split
  ; cases h with h₀ h₁ ; try { assumption },
  { simp [Next_a,on_fun,h₀], auto, },
  { simp [Next_a,on_fun,h₀] at h₁, auto }
end

section Simulation_POs
-- include SIM₀ Hc2a
-- lemma SIM₀' (v : cevt × β) (o : γ)
--   (h : (o, v) ⊨ q')
-- : (∃ (w : aevt × α), (o, w) ⊨ p' ∧ (o, w, v) ⊨ J') :=
-- begin
--   simp [q',prod.map_left] at h,
--   specialize SIM₀ v.2 o h,
--   specialize Hc2a v.1,
--   revert SIM₀, intros_mono,
--   simp [J',p',map], intros,
--   cases Hc2a,
--   constructor_matching* [Exists _, _ ∧ _] ;
--   tauto,
-- end

-- omit SIM₀
-- include SIM
-- lemma SIM' (w : aevt × α) (v : cevt × β) (o : γ) (v' : cevt × β) (o' : γ)
--   (h₀ : (o, w, v) ⊨ J')
--   (h₁ : Next_c (o, v) (o', v'))
-- : (∃ w', Next_a (o,w) (o',w') ∧ (o', w', v') ⊨ J') :=
-- begin
--   simp [J',map] at h₀,
--   simp [Next_c,on_fun] at h₁,
--   cases h₀,
--   specialize SIM w.2 v.2 o v'.2 o' v.1 w.1 h₀_right h₀_left h₁,
--   cases SIM with w' SIM,
--   cases Hc2a v'.1 with ae',
--   existsi [(ae',w')],
--   simp [Next_a, J',on_fun,map,h₀_right],
--   tauto,
-- end

-- include H
-- omit SIM
-- lemma H'
-- : Γ ⊢ simulation.SPEC₁ q' Next_c ⦃v,sch_c⦄ o :=
-- begin [temporal]
--   simp [SPEC₂,simulation.SPEC₁,q'] at H ⊢,
--   split, tauto,
--   casesm* _ ⋀ _,
--   persistent,
--   select h : ◻p_exists _,
--   henceforth at h ⊢,
--   cases h with e h,
--   simp only [Next_c] at *,
--   explicit'
--   { cc },
-- end

-- omit H
abbreviation ref' : tvar (aevt → cevt → Prop) :=
ref

-- variable Hcorrect_sched : Γ ⊢ ◻(ref' sch_a sch_c)

include SIM₀ SIM H valid_witness

lemma J_inv_in_w
: Γ ⊢ ◻(J ! ⦃o,w,v⦄) :=
begin [temporal]
  simp [Wtn,SPEC₂] at valid_witness H,
  cases valid_witness with h₀ h₀,
  casesm* _ ⋀ _,
  apply induct _ _ _ _,
  { persistent,
    select H₀ : ◻p_exists _,
    henceforth at h₀_1 H₀ ⊢,
    explicit'
    { intro h,
      cases h₀_1, subst w',
      apply_epsilon_spec, simp, tauto, } },
  { select Hw : _ ≃ temporal.many_to_many.Wx₀,
    select Hq : q ! _,
    clear_except Hw SIM₀ Hq,
    explicit'
    { cases Hw, subst w, apply_epsilon_spec,
      simp, tauto, } }
end

lemma witness_imp_SPEC₀_saf
  (h : Γ ⊢ Wtn ⦃sch_a,w⦄)
: Γ ⊢ SPEC₀.saf' w o sch_a :=
begin [temporal]
  have hJ := temporal.many_to_many.J_inv_in_w sch_a H w valid_witness ,
  clear valid_witness,
  simp [SPEC₀.saf',SPEC₂,Wtn] at h ⊢ H,
  casesm* _ ⋀ _,
  split,
  { clear SIM,
    henceforth at hJ,
    select Hw : _ ≃ temporal.many_to_many.Wx₀,
    select h' : q ! _,
    -- rw [← pair.snd_mk sch_a w,h],
    explicit'
    { cases Hw, subst w,
      apply_epsilon_spec,
      simp, auto, } },
  { clear SIM₀,
    select h : ◻(_ ≃ _),
    select h' : ◻(p_exists _),
    persistent,
    henceforth at h h' ⊢ hJ ,
    explicit'
    { cases h, subst w', subst sch_a',
      apply_epsilon_spec, simp,
      tauto, } },
end

omit H
parameters p q cs₁ fs₁
include Hpo p
omit valid_witness

lemma SPEC₂_imp_SPEC₁
: (SPEC₂ v o sch_c) ⟹ (SPEC₁ v o) :=
begin [temporal]
  simp only [SPEC₁,SPEC₂,temporal.many_to_many.SPEC₁,temporal.many_to_many.SPEC₂],
  monotonicity, apply ctx_p_and_p_imp_p_and',
  { monotonicity, simp, intros x h₀ h₁,
    existsi x, exact h₁ },
  { intros h i h₀ h₁,
    replace h := h _ h₀ h₁,
    revert h, monotonicity, simp, }
end

section
omit Hpo
include valid_witness fs₁ cs₁ Γ H
-- #check w
-- noncomputable def sch_w : tvar aevt :=
-- ⟪ ℕ, λ (w w' : α), ε ae, A ae w w' ⟫ w (⊙w)

lemma sch_w_spec
: Γ ⊢ ◻(ref' (⊙sch_a) sch_c) :=
begin [temporal]
  have hJ := temporal.many_to_many.J_inv_in_w _ H _ valid_witness,
  simp [Wtn,SPEC₂] at valid_witness H,
  cases valid_witness with Hw' Hw,
  cases H with H H₀,
  cases H with H₁ H₂,
  persistent,
  -- have H' := temporal.many_to_many.H',
  henceforth at Hw ⊢ hJ H₂,
  explicit'
  { cases Hw, subst sch_a', apply_epsilon_spec,
    simp, apply SIM ; auto, },
end

end

include H valid_witness
lemma H_C_imp_A (e : cevt) (e' : aevt)
  -- (Hsim : ref e' e)
: Γ ⊢ ◻(sch_c ≃ ↑e ⟶ ⊙sch_a ≃ ↑e' ⟶ ⟦ o,v | C e ⟧ ⟶ ⟦ o,w | A e' ⟧) :=
begin [temporal]
  have hJ := temporal.many_to_many.J_inv_in_w sch_a H w valid_witness,
  simp [Wtn] at valid_witness,
  cases valid_witness with h₀ h₁,
  clear_except hJ SIM h₁,
  persistent,
  henceforth at *,
  explicit'
  { intros, cases h₁, subst w', subst sch_a', substs e',
    apply_epsilon_spec,
    simp, subst e,
    tauto, },
end
omit valid_witness H
/- latest idea: sch_a should be part of concrete state?
-/

lemma Hpo' (e : aevt)
: many_to_many_po'
     (subtype (ref e)) (SPEC₂ v o sch_c ⋀ Wtn ⦃sch_a,w⦄ ⋀ ◻(J ! ⦃o,w,v⦄))
     (wit e)
     (λ i, ce' i e) (ae e)
     ⦃o,v,sch_c,sch_a⦄ ⦃o,w⦄
:=
begin
  have
  : temporal.many_to_many.SPEC₂ v o sch_c ⋀ temporal.many_to_many.Wtn ⦃sch_a,w⦄ ⋀
      ◻(J ! ⦃o,w,v⦄) ⟹
    temporal.many_to_many.SPEC₁ v o ⋀ temporal.many_to_many.SPEC₀.saf' w o sch_a ⋀
      ◻(J ! ⦃o,w,v⦄),
  begin [temporal]
    simp, intros h₀ h₁ h₂, split*,
    { apply temporal.many_to_many.SPEC₂_imp_SPEC₁ Hpo _ ; try { auto }, },
    { apply temporal.many_to_many.witness_imp_SPEC₀_saf _ h₀ _ h₁, auto, },
    { auto }
  end,
  constructor,
  iterate 3
  { cases (Hpo e w sch_a),
    simp at *,
    transitivity,
    { apply this },
    { assumption } },
  clear this,
  begin [temporal]
    intros,
    casesm* _ ⋀ _,
    select Hw : temporal.many_to_many.Wtn _,
    select hJ : ◻(J ! _),
    have := temporal.many_to_many.H_C_imp_A _ _ _ _ Hw x e
    ; try { auto <|> apply temporal.many_to_many.sch_w_spec },
    clear_except this SIM₀ SIM Hw hJ,
    simp [Wtn] at Hw, cases Hw with Hw' Hw,
    persistent,
    henceforth at ⊢ this Hw hJ,
    explicit'
    { intros, cases Hw, simp only [ce'._match_2,ce'._match_1] at *,
      casesm* _ ∧ _,
      apply this _ _ ; tauto <|> cc, },
  end
end

end Simulation_POs

include H SIM₀ SIM Hpo

lemma sched_ref (i : aevt) -- (w : tvar (aevt × α))
 (Hw : Γ ⊢ Wtn ⦃sch_a,w⦄)
 (h : Γ ⊢ ∀∀ j, ref i j ⟶ sched (cs₁ j ! ⦃o,v⦄) (fs₁ j ! ⦃o,v⦄) (sch_c ≃ ↑j ⋀ ⟦ o,v | C j ⟧))
: Γ ⊢ sched (cs₀ i ! ⦃o,w⦄) (fs₀ i ! ⦃o,w⦄) ⟦ o,w | A i ⟧ :=
begin [temporal]
  have hJ : ◻(J ! ⦃o,w,v⦄),
  { apply temporal.many_to_many.J_inv_in_w ; auto },
  apply splitting (Hpo i w sch_a) _ _,
  { split, split,
    apply temporal.many_to_many.SPEC₂_imp_SPEC₁ Hpo ; auto,
    apply temporal.many_to_many.witness_imp_SPEC₀_saf ; auto,
    auto },
  intro ce, cases ce with ce Hce,
  simp only, intros H₀ H₁,
  replace h := h ce Hce H₀ H₁,
  revert h,
  monotonicity!,
  lifted_pred,
end

lemma many_to_many
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  apply p_exists_partial_intro _ (proj $ @pair.snd aevt α) _ _,
  select_witness w : temporal.many_to_many.Wtn w with Hw,
  cases w with sch_a w,
  have this := H, revert this,
  dsimp [SPEC₀,SPEC₁],
  -- have H' := temporal.many_to_many.H' , -- o sch,
  apply ctx_p_and_p_imp_p_and' _ _,
  apply ctx_p_and_p_imp_p_and' _ _,
  { clear_except SIM₀ Hw H,
    simp [Wtn,SPEC₂] at H Hw,
    casesm _ ⋀ _,
    select Hw : (_ ≃ temporal.many_to_many.Wx₀),
    clear H,
    explicit'
    { intro, cases Hw,
      subst w, apply_epsilon_spec,
      simp, auto, }, },
  { clear_except SIM SIM₀ Hw H,
    have hJ := temporal.many_to_many.J_inv_in_w _ H _ Hw,
    simp [Wtn,SPEC₂] at H Hw,
    casesm _ ⋀ _,
    monotonicity!,
    simp, intros ce h₀ h₁,
    select Hw : ◻(_ ≃ _),
    henceforth at Hw hJ,
    explicit'
    { cases Hw, subst w', subst ce,
      apply_epsilon_spec,
      simp, auto, }, },
  { intros h i,
    apply temporal.many_to_many.sched_ref
    ; repeat { auto <|> intro }, },
end
end SPEC₂
end conc_sch

section refinement_SPEC₂
include SIM₀ SIM wit Hpo inh_aevt inh_α
parameters cs₁ fs₁ cs₀ fs₀

-- variable {Γ : cpred}

lemma refinement_SPEC₂
: Γ ⊢ (∃∃ sch_c, SPEC₂ v o sch_c) ⟶ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  simp, intros sch Hc,
  apply temporal.many_to_many.many_to_many,
  auto, auto,
end

end refinement_SPEC₂

open nat function set
include inh_cevt

variables [schedulable cevt]

lemma refinement_SPEC₁
: Γ ⊢ SPEC₁ v o ⟶ (∃∃ sch, SPEC₂ v o sch) :=
begin [temporal]
  intro h,
  let r : tvar (set cevt) := ⟪ ℕ, λ s s', { e | C e s s' } ⟫ ⦃o,v⦄ ⦃⊙o,⊙v⦄,
  have hr : ◻-(r ≃ (∅ : set cevt)),
  { simp [SPEC₁] at h,
    casesm* _ ⋀ _,
    select Hact : ◻(p_exists _),
    henceforth! at Hact ⊢,
    explicit' [r]
    { rw not_eq_empty_iff_exists, exact Hact }, },
  have h' := temporal.scheduling.scheduler Γ r hr,
  cases h' with sch h',
  existsi sch,
  simp [SPEC₁,SPEC₂] at ⊢ h,
  casesm* _ ⋀ _,
  split* ; try { auto },
  { select h' : ◻(p_exists _),
    select hJ : ◻(_ ∊ _),
    persistent, henceforth at hJ h' ⊢,
    existsi sch with hh,
    split,
    { rw hh, },
    { simp [r] at hJ, clear a_1 hr r,
      explicit'
      { subst sch, assumption } } },
  { introv, intros h₀ h₁,
    rename a_3 h₂,
    replace h₂ := h₂ x h₀ h₁,
    replace a_1 := a_1 x,
    persistent,
    have : ↑x ∊ r ≡ ⟦ o,v | C x ⟧,
    { simp [r], clear a_1 a hr r,
      explicit' { refl }, },
    rw [this,this] at a_1,
    auto, }
end

end obligations
open function
include SIM₀ SIM inh_cevt inh_aevt inh_α
lemma refinement {o : tvar γ} [schedulable cevt]
  (h :   ∀ (v : tvar β) (e : aevt) (w : tvar α) (sch_a : tvar aevt),
    many_to_many_po' (subtype (ref e)) (SPEC₁ v o ⋀ SPEC₀.saf' w o sch_a ⋀ ◻(J ! ⦃o,w,v⦄)) (wit e)
      (λ (e' : subtype (ref e)), ce ↑e') (ae e)
      ⦃o,v⦄ ⦃o,w⦄)
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  transitivity (∃∃ c sch, SPEC₂ q C cs₁ fs₁ c o sch),
  { apply p_exists_p_imp_p_exists ,
    intro v,
    apply temporal.many_to_many.refinement_SPEC₁, },
  { simp, intros c sch Hspec,
    specialize h c,
    apply temporal.many_to_many.refinement_SPEC₂ c o Γ h,
    existsi sch, exact Hspec, },
end

end
end many_to_many

end temporal

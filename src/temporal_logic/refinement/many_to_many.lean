import ..scheduling
import ..fairness
import ..spec

import util.predicate

universe variables u u₀ u₁ u₂ u₃
open predicate nat

local infix ` ≃ `:75 := v_eq

namespace temporal

namespace many_to_many
section
open fairness
parameters {α : Type u} {β : Type u₀} {γ : Type u₁ }
parameters {m₀ : mch (γ×α)} {m₁ : mch (γ×β)}
local notation `p` := m₀.init
local notation `q` := m₁.init
local notation `aevt` := m₀.evt
local notation `cevt` := m₁.evt
local notation `cs₀` := m₀.cs
local notation `fs₀` := m₀.fs
local notation `cs₁` := m₁.cs
local notation `fs₁` := m₁.fs
local notation `A` := m₀.A
local notation `C` := m₁.A
local notation `ae`  := m₀.event
local notation `ce`  := m₁.event
local notation `ce'` := m₁.event' (option aevt)
-- local notation `Next₀` := m₀.effect
-- local notation `Next₁` := m₁.effect


parameters (J : pred' (γ×α×β))
parameter ref : option aevt → option cevt → Prop
parameter wit : Π a : aevt, subtype (λ c : cevt, ref a c) → cpred

open prod

def C' (e : cevt) : act (cevt×γ×β) :=
λ ⟨sch,s⟩ ⟨_,s'⟩, sch = e ∧ C e s s'


-- #check (_ × _) × _
-- abbreviation ae' (i : aevt) : event (γ×α×aevt) :=
-- { p := cs₀ i!⟨prod.map_right fst⟩
-- , q := fs₀ i!⟨prod.map_right fst⟩
-- , A := λ s s', s.2.2 = i ∧ (A i on prod.map_right fst) s s' }
-- abbreviation ce' (i : cevt) (j : aevt) : event (γ×β×(cevt×aevt)) :=
-- { p := cs₁ i!⟨prod.map_right fst⟩
-- , q := fs₁ i!⟨prod.map_right fst⟩
-- , A := λ ⟨o,v,ce,_⟩ ⟨o',v',_,ae'⟩, ae' = j ∧ ce = i ∧ C i (o,v) (o',v') }

section specs

-- parameters p q cs₀ fs₀ cs₁ fs₁

def SPEC₀.saf' (v : tvar α) (o : tvar γ) (sch : tvar (option aevt)) : cpred :=
m₀.spec_saf_sch ⦃o,v⦄ (⊙sch)

def SPEC₀ (v : tvar α) (o : tvar γ) : cpred :=
m₀.spec ⦃ o,v ⦄

def SPEC₁ (v : tvar β) (o : tvar γ) : cpred :=
m₁.spec ⦃ o,v ⦄

def SPEC₂ (v : tvar β) (o : tvar γ) (s : tvar (option cevt)) : cpred :=
m₁.spec_sch ⦃o,v⦄ s

end specs

parameters [inh_cevt : inhabited cevt]
           [inh_aevt : inhabited aevt]

-- parameter Hc2a : ∀ ce : cevt, ∃ ae : aevt, ref ae ce

-- parameter init_Jₐ : ∀ w o, (o,w) ⊨ p → (o,w) ⊨ Jₐ
-- parameter evt_Jₐ  : ∀ w o w' o' e,
--                           (o,w) ⊨ Jₐ →
--                           (o,w) ⊨ cs₀ e →
--                           (o,w) ⊨ fs₀ e →
--                           A e (o,w) (o',w') →
--                           (o',w') ⊨ Jₐ

structure refinement :=
  (SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J)
  (SIM : ∀ cev w v o v' o',
    (o,w,v) ⊨ J →
    m₁.effect cev (o,v) (o',v') →
    ∃ aev w', ref aev cev ∧
             m₀.effect aev (o,w) (o',w') ∧
             (o',w',v') ⊨ J )
  (ANIM : ∀ (e : aevt) (sch : tvar (option aevt)) (o v w),
    many_to_many_po'
      (subtype _)
      (SPEC₁ v o ⋀ SPEC₀.saf' w o sch ⋀ ◻(J ! ⦃o,w,v⦄))
      (wit e)
      (λ e', ce e') (ae e)
      ⦃o,v⦄ ⦃o,w⦄)

section obligations

parameters (v : tvar β) (o : tvar γ)
parameters (Γ : cpred)

parameter Href : refinement

parameters β γ
parameters {β γ}

section conc_sch

parameters (sch_c : tvar (option cevt))

variable (sch_a : tvar (option aevt))

section SPEC₂
variable H : Γ ⊢ SPEC₂ v o sch_c

open prod temporal.prod

-- def Next_a : act $ γ × aevt × α :=
-- λ σ σ',
-- ∃ e, σ.2.1 = e ∧
--       map_right snd σ ⊨ cs₀ e ∧
--       map_right snd σ ⊨ fs₀ e ∧
--       (A e on map_right snd) σ σ'

-- def Next_c : act $ γ × cevt × β :=
-- λ σ σ',
-- ∃ e, σ.2.1 = e ∧
--       map_right snd σ ⊨ cs₁ e ∧
--       map_right snd σ ⊨ fs₁ e ∧
--       (C e on map_right snd) σ σ'

section J
def J' : pred' (γ × (aevt × α) × (cevt × β)) :=
J ! ⟨ prod.map_right $ prod.map prod.snd prod.snd ⟩ ⋀
⟨ λ ⟨_, a, c⟩, ref a.1 c.1 ⟩

-- def JJₐ : pred' (γ × aevt × α) :=
-- Jₐ ! ⟨ prod.map_right snd ⟩

def p' : pred' (γ × aevt × α) :=
p ! ⟨prod.map_right prod.snd⟩

def q' : pred' (γ × cevt × β) :=
q ! ⟨prod.map_right prod.snd⟩

end J
variable w : tvar α
open function
include inh_aevt
-- def Wx₀_f : tvar (β → γ → aevt × α → Prop) :=
-- λ v o (w : aevt × _), (o,w.2) ⊨ p ∧ (o,w.2,v) ⊨ J

-- @[simp]
-- def Wx₀ : tvar (option aevt × α → Prop) :=
-- [| v o , λ (w : option aevt × _), (o,w.2) ⊨ p |]

-- def Wf_f : tvar (option cevt → β → γ → γ → option aevt × α → option aevt × α → Prop) :=
-- ⟪ℕ, λ ce v' o o' (w : _ × _) (w' : option aevt × α),
--              (o',w'.2,v') ⊨ J ∧
--              ref w'.1 ce ∧
--              -- (o,w.2) ⊨ cs₀ w'.1 ∧
--              -- (o,w.2) ⊨ fs₀ w'.1 ∧
--              m₀.effect w'.1 (o,w.2) (o',w'.2) ⟫
--              -- A w'.1 (o,w.2) (o',w'.2) ⟫

-- @[simp]
-- def Wf : tvar (option aevt × α → option aevt × α → Prop) :=
-- ⟪ℕ, λ (cev : option cevt) o o' (w w' : option aevt × α),
--              ref w'.1 cev ∧
--              -- (o,w.2) ⊨ cs₀ w'.1 ∧
--              -- (o,w.2) ⊨ fs₀ w'.1 ∧
--              m₀.effect w'.1 (o,w.2) (o',w'.2) ⟫
--  sch_c o (⊙o)

-- lemma Wx₀_def' (σ : ℕ)
-- : σ ⊨ Wx₀ =
--   ε w : _ × α, (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J :=
-- by repeat { unfold_coes <|> simp [Wx₀,Wx₀_f] }

-- @[simp,predicate]
-- lemma Wx₀_def (σ : ℕ) (a b)
-- : (a,b) = σ ⊨ Wx₀ ↔
--   a = (ε w : _ × α,    (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J).fst ∧
--   b = (ε w : aevt × α, (σ ⊨ o,w.2) ⊨ p ∧ (σ ⊨ o,w.2,σ ⊨ v) ⊨ J).snd :=
-- by repeat { unfold_coes <|> simp [Wx₀,Wx₀_f,ext] }

-- lemma Wf_def' (σ : ℕ) (w)
-- : σ ⊨ Wf ⦃sch_a,w⦄ =
--   ε w' : _ × α,
--          (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
--                ref w'.1 (σ ⊨ sch_c) ∧
--                (σ ⊨ o,σ ⊨ w) ⊨ cs₀ w'.1 ∧
--                (σ ⊨ o,σ ⊨ w) ⊨ fs₀ w'.1 ∧
--                A w'.1 (σ ⊨ o,σ ⊨ w) (succ σ ⊨ o,w'.2) :=
-- by repeat { unfold_coes <|> simp [Wf,Wf_f] }


-- @[simp,predicate]
-- lemma Wf_def (σ : ℕ) (sch_a w) (a b)
-- : (a,b) = (σ ⊨ Wf) (sch_a,w) ↔
--   a = (ε w' : _ × α,
--          (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
--                ref w'.1 (σ ⊨ sch_c) ∧
--                (σ ⊨ o,w) ⊨ cs₀ w'.1 ∧
--                (σ ⊨ o,w) ⊨ fs₀ w'.1 ∧
--                A w'.1 (σ ⊨ o,w) (succ σ ⊨ o,w'.2)).1 ∧
--   b = (ε w' : aevt × α,
--          (succ σ ⊨ o,w'.2,succ σ ⊨ v) ⊨ J ∧
--                ref w'.1 (σ ⊨ sch_c) ∧
--                (σ ⊨ o,w) ⊨ cs₀ w'.1 ∧
--                (σ ⊨ o,w) ⊨ fs₀ w'.1 ∧
--                A w'.1 (σ ⊨ o,w) (succ σ ⊨ o,w'.2)).2 :=
-- by repeat { unfold_coes <|> simp [Wf,Wf_f,ext] }

-- variable valid_witness
-- : Γ ⊢ Wtn ⦃sch_a,w⦄

-- lemma abstract_sch (e : aevt)
-- : Γ ⊢ sch_a ≃ e ⋀ cs₀ e ! ⦃o,w⦄ ⋀ fs₀ e ! ⦃o,w⦄ ⋀ ⟦ o,w | A e ⟧ ≡
--       sch_a ≃ e ⋀ ⟦ o,sch_a,w | Next_a ⟧ :=
-- begin
--   lifted_pred [Next_a,on_fun],
--   split ; intro h ; split
--   ; casesm* _ ∧ _ ; subst e ; tauto,
-- end

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
abbreviation ref' : tvar (option aevt → option cevt → Prop) :=
ref

@[simp]
def Next₀ : act (γ × α × option aevt) :=
λ ⟨o,w,sch_a⟩ ⟨o',w',_⟩, ∃ e, sch_a = e ∧ m₀.effect e (o,w) (o',w')

-- include valid_witness -- init_Jₐ evt_Jₐ
include H Href
-- set_option pp.implicit true

lemma J_inv_in_w'
: Γ ⊢ ∃∃ w, ◻(J ! ⦃o,w,v⦄) ⋀ SPEC₀.saf' w o sch_a :=
begin [temporal]
  -- select_witness w : temporal.many_to_many.Wtn w
  --   with Hw using J ! ⦃o,w.snd,v⦄,
  unfold SPEC₂ mch.spec_sch at H, casesm* _ ⋀ _,

  select_witness w : m₀.init ! ⦃o,w⦄ ⋀ ◻ ⟦ o,w,sch_a | temporal.many_to_many.Next₀ ⟧
    -- with h₀ h₁
    using (J ! ⦃o,w,v⦄)
  { ext, admit, -- simp_coe [to_fun_var'],
    -- simp only with lifted_fn,
    -- congr, funext, transitivity, apply to_fun_var'_lift₂,
    -- -- congr,
    -- simp [to_fun_var'_coe] with lifted_fn,
    -- congr, rw to_fun_var'_id,
    -- refl,
    },
  explicit' with a
  { apply Href.SIM₀, assumption },
  -- simp [SPEC₂] at H,
  -- rw henceforth_next_intro,
  -- dsimp [SPEC₀.saf'],
  -- -- cases valid_witness with h₀ h₀,
  -- casesm* _ ⋀ _,
  -- intros,
  -- t_induction,
  -- { -- select Hw : _ ≃ temporal.many_to_many.Wx₀,
  --   select Hq : q ! _,
  --   have SIM₀ := Href.SIM₀,
  --   explicit' with SIM₀ Hq
  --   { {  },
  --     simp, tauto, } },
  { select H₀ : p_exists _,
    -- henceforth! at h₀_1 H₀ ⊢,
    explicit' [Next₀] with H₀
    { intros h hJ,
      -- casesm* [_ ∧ _,Exists _],
      -- type_check cs₀,
      -- have : (o', h', v') ⊨ J ∧
      --        (o,w) ⊨ cs₀ sch_a' ∧ (o,w) ⊨ fs₀ sch_a' ∧
      --        A sch_a' (o, w) (o', w'),
      -- { subst H₀_w, subst w', subst sch_a',
      --   apply_epsilon_spec,
      --   simp,
      --   apply SIM ; solve_by_elim },
      -- split, tauto,
      -- casesm* _ ∧ _,
      -- apply evt_Jₐ ; apply hJₐ <|> solve_by_elim
      } },
end

-- lemma J_inv_in_w
-- : Γ ⊢ ◻(J ! ⦃o,w,v⦄) :=
-- begin [temporal]
--   cases temporal.many_to_many.J_inv_in_w' _ H _ valid_witness,
--   assumption
-- end

-- lemma abs_J_inv_in_w
-- : Γ ⊢ ◻(Jₐ ! ⦃o,w⦄) :=
-- begin [temporal]
--   cases temporal.many_to_many.J_inv_in_w' _ H _ valid_witness,
--   assumption
-- end

lemma witness_imp_SPEC₀_saf
: Γ ⊢ SPEC₀.saf' w o sch_a :=
begin [temporal]
  simp [SPEC₀.saf',Wtn] at ⊢ valid_witness,
  cases valid_witness with H₀ H₁,
  split,
  explicit' with H₀
  { tauto, },
  henceforth!,
  explicit' with H₁
  { tauto, },
end

omit H
parameters m₀ m₁
include Href
omit valid_witness

lemma SPEC₂_imp_SPEC₁
: (SPEC₂ v o sch_c) ⟹ (SPEC₁ v o) :=
begin [temporal]
  simp only [SPEC₁,SPEC₂,temporal.many_to_many.SPEC₁,temporal.many_to_many.SPEC₂],
  monotonicity, apply ctx_p_and_p_imp_p_and',
  { monotonicity, simp, intros x, intros,
    existsi x, tauto },
  { intros h i h₀ h₁,
    replace h := h _ h₀ h₁,
    revert h, monotonicity, simp, }
end

section
omit Href
include valid_witness Γ H
-- #check w
-- noncomputable def sch_w : tvar aevt :=
-- ⟪ ℕ, λ (w w' : α), ε ae, A ae w w' ⟫ w (⊙w)

-- lemma sch_w_spec
-- : Γ ⊢ ◻(ref' (⊙sch_a) sch_c) :=
-- begin [temporal]
--   have hJ  := temporal.many_to_many.J_inv_in_w _ H _ valid_witness,
--   have hJₐ := temporal.many_to_many.abs_J_inv_in_w _ H _ valid_witness,
--   simp [Wtn,SPEC₂] at valid_witness H,
--   cases valid_witness with Hw' Hw,
--   cases H with H H₀,
--   cases H with H₁ H₂,
--   henceforth! at Hw ⊢ hJ hJₐ H₂,
--   explicit' with Hw hJ hJₐ H₂
--   { cases Hw, subst sch_a', casesm* [_∧_,Exists _],
--     subst sch_c, apply_epsilon_spec,
--     simp, solve_by_elim, },
-- end

end

include H valid_witness

lemma H_C_imp_A (e : option cevt) (e' : option aevt)
  (Hsim : ref e' e)
: Γ ⊢ ◻(sch_c ≃ ↑e ⟶ ⊙sch_a ≃ ↑e' ⟶
        ⟦ o,v | Next₁ e ⟧ ⟶
        ⟦ o,w | Next₀ e' ⟧) :=
begin [temporal]
  have hJ := temporal.many_to_many.J_inv_in_w sch_a H w valid_witness,
  have hJₐ := temporal.many_to_many.abs_J_inv_in_w sch_a H w valid_witness,
  simp [Wtn] at valid_witness,
  cases valid_witness with h₀ h₁,
  cases H with H H₀,
  cases H with H₁ H₂,
  clear_except hJ hJₐ SIM h₁ H₂,
  henceforth! at *,
  explicit' with hJ hJₐ SIM h₁ H₂
  { intros, cases h₁, subst w', subst sch_c,
    subst sch_a', substs e',
    casesm* [_ ∧ _, Exists _], subst e,
    apply_epsilon_spec,
    simp, apply SIM ; solve_by_elim, },
end

omit valid_witness H

lemma Hpo' (e : aevt)
: many_to_many_po'
     _ (SPEC₂ v o sch_c ⋀ Wtn ⦃sch_a,w⦄ ⋀ ◻(J ! ⦃o,w,v⦄))
     (wit e)
     (λ i, ce' i e) (ae e)
     ⦃⦃o,v⦄,sch_c,sch_a⦄ ⦃o,w⦄
:=
begin
  have
  : temporal.many_to_many.SPEC₂ v o sch_c ⋀ temporal.many_to_many.Wtn ⦃sch_a,w⦄ ⋀
      ◻(J ! ⦃o,w,v⦄) ⟹
    temporal.many_to_many.SPEC₁ v o ⋀ temporal.many_to_many.SPEC₀.saf' w o sch_a ⋀
      ◻(J ! ⦃o,w,v⦄),
  begin [temporal]
    simp, intros h₀ h₁ h₂, split*,
    { apply temporal.many_to_many.SPEC₂_imp_SPEC₁ _ _ ; try { solve_by_elim }, },
    { apply temporal.many_to_many.witness_imp_SPEC₀_saf _ h₀ _ h₁, },
    { solve_by_elim }
  end,
  constructor,
  iterate 3
  { cases (Href.ANIM e sch_a o v w),
    simp! [ce',mch.event'] at *,
    transitivity,
    { apply this },
    { assumption } },
  clear this,
  begin [temporal]
    intros,
    casesm* _ ⋀ _,
    select Hw : temporal.many_to_many.Wtn _,
    select hJ : ◻(J ! _),
    select H  : temporal.many_to_many.SPEC₂ _ _ _,
    have := temporal.many_to_many.H_C_imp_A _ H w Hw _ e x.2,
    cases H with H H₀,
    cases H with H₁ H₂,
    clear_except this Href SIM₀ SIM Hw hJ H₂,
    simp [Wtn] at Hw, cases Hw with Hw' Hw,
    henceforth! at ⊢ Hw hJ H₂ this,
    explicit' [mch.event'] with this Hw hJ H₂
    { dsimp [ce',mch.event'], cases Hw,
      intros,
      casesm* [_ ∧ _, Exists _, sch_c = _],
      specialize this _ _ _ ; try { assumption },
      simp [and_assoc,*], exact this, },
  end
end

end Simulation_POs

include H Href

lemma sched_ref (i : aevt) -- (w : tvar (aevt × α))
 (hJ : Γ ⊢ ◻(J ! ⦃o,w,v⦄))
 (Hw : Γ ⊢ Wtn ⦃sch_a,w⦄)
 (h : Γ ⊢ ∀∀ j : cevt, ref ↑i ↑j ⟶ sched (cs₁ j ! ⦃o,v⦄) (fs₁ j ! ⦃o,v⦄) (sch_c ≃ some j ⋀ ⟦ o,v | C j ⟧))
: Γ ⊢ sched (cs₀ i ! ⦃o,w⦄) (fs₀ i ! ⦃o,w⦄) ⟦ o,w | A i ⟧ :=
begin [temporal]
  -- have hJ : ◻(J ! ⦃o,w,v⦄),
  -- { apply temporal.many_to_many.J_inv_in_w ; solve_by_elim },
  apply splitting (Href.ANIM i sch_a o v w) _ _,
  { split*,
    apply temporal.many_to_many.SPEC₂_imp_SPEC₁ _ ; assumption,
    apply temporal.many_to_many.witness_imp_SPEC₀_saf ; assumption,
    assumption },
  intro cev, cases cev with cev Hce,
  simp only, intros H₀ H₁,
  replace h := h cev Hce H₀ H₁,
  revert h,
  monotonicity!,
  explicit'
  { intros, tauto },
end

/-
  This proof works as:
  Init₂ ⇒ Init₀
  Saf₂  ⇒ Saf₀
  Spec₂ ⇒ Live₀
 -/
lemma many_to_many
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  apply p_exists_partial_intro _ (proj $ @pair.snd (option aevt) α) _ _,
  -- replace H := H.left,
  cases H.left with H₀ H₁,
  select_witness w : temporal.many_to_many.Wtn w
    with Hw using J ! ⦃o,w.snd,v⦄,
  explicit' [Wx₀] with H₀
  { apply Href.SIM₀ _ _ H₀, },
  explicit' [Wf] with H₁
  { simp_intros b hJ [and_assoc],
    have := Href.SIM _ _ _ _ _ _ hJ H₁,
    tauto, }, -- a ∧ a ↔ a
  existsi w,
  { apply m₀.spec_of_spec_saf_sch _ (⊙w.fst),
    apply temporal.many_to_many.witness_imp_SPEC₀_saf _ H,
    revert Hw, simp,
    intro, apply temporal.many_to_many.sched_ref w.fst H w.snd x,
    assumption, simp *, introv H',
    apply H.right, },
end
end SPEC₂
end conc_sch

section refinement_SPEC₂
include Href wit inh_aevt
parameters m₀ m₁

lemma refinement_SPEC₂
: Γ ⊢ (∃∃ sch_c, SPEC₂ v o sch_c) ⟶ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  simp, intros sch Hc,
  apply temporal.many_to_many.many_to_many ;
  solve_by_elim,
end

end refinement_SPEC₂

open nat function set scheduling
include inh_cevt

variables [encodable cevt]

lemma refinement_SPEC₁
: SPEC₁ v o ⟹ (∃∃ sch, SPEC₂ v o sch) :=
assume Γ,
sch_intro _ _ _

end obligations
open function
include J wit inh_cevt inh_aevt

lemma refinement' {o : tvar γ} [encodable cevt]
  (h : refinement)
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  transitivity (∃∃ c (sch : tvar (option cevt)), SPEC₂ c o sch),
  { apply p_exists_p_imp_p_exists ,
    intro v,
    apply temporal.many_to_many.refinement_SPEC₁, },
  { simp, intros c sch Hspec,
    apply temporal.many_to_many.refinement_SPEC₂ c o Γ h,
    existsi sch, exact Hspec, },
end

end
end many_to_many

end temporal

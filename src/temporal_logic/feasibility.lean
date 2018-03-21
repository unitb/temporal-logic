
import .refinement.one_to_one

universe variables u u₀ u₁ u₂

namespace temporal
namespace feasibility
open fairness predicate nat
local infix ` ≃ `:75 := v_eq
section feasibility

parameters {α : Type u}
parameters {evt : Type u₂}
parameters {p : pred' α}
parameters (A : evt → act α)
parameters {cs₀ fs₀ : evt → pred' α}
parameters (J : pred' α)
parameters [inhabited evt] [inhabited α]

parameter init_FIS : ∃ s, s ⊨ p
parameter init_INV : ∀ s, s ⊨ p → s ⊨ J
parameter DLF : ∀ s, s ⊨ J → ∃ e, s ⊨ cs₀ e ∧ s ⊨ fs₀ e
parameter evt_FIS : ∀ e s, s ⊨ J → s ⊨ cs₀ e → s ⊨ fs₀ e → ∃ s', A e s s'
parameter evt_INV : ∀ e s s', A e s s' → s ⊨ J → s' ⊨ J

def SPEC₀ (v : tvar α) : cpred :=
spec p cs₀ fs₀ A v

def p' : pred' (unit × α) :=
p ! pair.snd

def q' : pred' (unit × unit) :=
True

open prod
def A' (e : evt) : act (unit × α) :=
λ σ σ',
     (A e on snd) σ σ'

def C (e : evt) : act (unit × unit) :=
λ _ _, true

def C' (e : evt) : act (evt × unit × unit) :=
λ ⟨sch,_⟩ _, sch = e

abbreviation J' : pred' (unit × α × unit) :=
J ! pair.fst ! pair.snd

abbreviation cs₀' (e : evt) : pred' (unit × α) :=
cs₀ e ! pair.snd

abbreviation fs₀' (e : evt) : pred' (unit × α) :=
fs₀ e ! pair.snd

abbreviation cs₁ (e : evt) : pred' (unit × unit) :=
True

abbreviation fs₁ (e : evt) : pred' (unit × unit) :=
True
section
include init_FIS init_INV DLF
lemma SIM₀' (v o : unit)
  (h : (o, v) ⊨ q')
: (∃ (w : α), (o, w) ⊨ p' ∧ (o, w, v) ⊨ J') :=
by { simp [q',p'] at *,
     apply exists_imp_exists _ init_FIS,
     intros, split, assumption, apply init_INV, assumption }
end
open function
section
include evt_FIS evt_INV DLF
lemma SIM' (w : α) (v o v' o' : unit) (e : evt)
  (hJ : (o, w, v) ⊨ J')
  (_ : true)
  (_ : true)
  (_ : true)
  (hC : C e (o, v) (o', v'))
: (∃ (w' : α),
        (o,w) ⊨ cs₀' e ∧
        (o,w) ⊨ fs₀' e ∧
        A' e (o, w) (o', w') ∧
        (o', w', v') ⊨ J') :=
begin
  -- simp [comp,A',on_fun] at *,
  -- casesm* [_ ∧ _, Exists _, unit],
  -- constructor_matching* [_ ∧ _],
  -- apply exists_imp_exists _ (evt_FIS e w _),
  -- intros, split, admit, assumption,
  -- tauto,
  admit,
end

end

def o : tvar unit := ↑()

-- parameter Hpo
-- : ∀ c a e, one_to_one_po' (SPEC₀.saf a o ⋀ ◻(J ! ⦃o,a,c⦄))
--          ⟨cs₁ e,fs₁ e,C' e⟩
--          ⟨cs₀ e,fs₀ e,A' e⟩ ⦃o,c⦄ ⦃o,a⦄)

def SPEC₀.saf' (v : tvar α) (sch : tvar evt) : cpred :=
spec_saf_spec p' cs₀' fs₀' A' ⦃o,v⦄ sch

def SPEC₁ (v : tvar unit) : cpred :=
spec q' cs₁ fs₁ C ⦃o,v⦄

lemma Hpo'
 : ∀ c a e sch, one_to_one_po' (SPEC₁ c ⋀ SPEC₀.saf' a sch ⋀ ◻(J' ! ⦃o,a,c⦄))
         ⟨cs₁ e!pair.snd,fs₁ e!pair.snd,one_to_one.C' C e⟩
         ⟨cs₀' e,fs₀' e,A' e⟩ ⦃sch,o,c⦄ ⦃o,a⦄ :=
begin
  intros,
  constructor,
  { simp [tl_leads_to], },
  { simp [tl_leads_to], },
  { simp [tl_leads_to], },
  begin [temporal]
    simp [SPEC₁,q',sched,SPEC₀.saf'],
    intros _ _ _ h _, henceforth! at *,
    intros, cases h with x h,
    explicit' [C,one_to_one.C',A']
    { cc },
  end,
end

include J init_INV init_FIS evt_INV evt_FIS Hpo' DLF
lemma feasibility [schedulable evt]
: ⊩ (∃∃ v, SPEC₀ v) :=
begin [temporal]
  have := temporal.feasibility.SIM',
  have :=  @one_to_one.refinement α unit unit evt
     temporal.feasibility.p' temporal.feasibility.q'
       temporal.feasibility.A'
       temporal.feasibility.C
       temporal.feasibility.cs₀'
       temporal.feasibility.fs₀'
       temporal.feasibility.cs₁
       temporal.feasibility.fs₁
       temporal.feasibility.J' True _ _
       _ _
       temporal.feasibility.SIM₀'
       temporal.feasibility.SIM'
       o _ _ Γ _,
  { simp [one_to_one.SPEC₀,SPEC₀] at this ⊢,
    casesm* [p_exists _, _ ⋀ _],
    existsi _, solve_by_elim,
    split,
    { simp [A',p',action_on' _ _ prod.snd] at *,
      tauto, },
    { simp [A',action_on' _ _ prod.snd] at *,
      assumption, }, },
  { intros, simp, },
  { intros, simp, },
  apply temporal.feasibility.Hpo' ,
  { existsi o,
    simp [one_to_one.SPEC₁,q',C,C',sched], }
end

end feasibility
end feasibility
end temporal

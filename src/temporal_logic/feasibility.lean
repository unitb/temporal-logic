
import .refinement.one_to_one

universe variables u u₀ u₁ u₂

namespace temporal
namespace feasibility
section feasibility
open fairness predicate nat

parameters {α : Type u}
parameters {evt : Type u₂}
parameters {p : pred' α}
parameters (A : evt → act α)
parameters {cs₀ fs₀ : evt → pred' α}
parameters (J : pred' α)
parameters [inhabited evt] [inhabited α]

parameter init_FIS : ∃ s, s ⊨ p
parameter init_INV : ∀ s, s ⊨ p → s ⊨ J

parameter evt_FIS : ∀ e s, s ⊨ J → ∃ s', A e s s'
parameter evt_INV : ∀ e s s', A e s s' → s ⊨ J → s' ⊨ J

def SPEC₀.saf (v : tvar α) : cpred :=
p ! v ⋀
◻(∃∃ i, ⟦ v | A i ⟧)

def SPEC₀ (v : tvar α) : cpred :=
SPEC₀.saf v ⋀
∀∀ i, sched (cs₀ i ! v) (fs₀ i ! v) ⟦ v | A i ⟧

def p' : pred' (unit × α) :=
p ! pair.snd

def q' : pred' (unit × unit) :=
True

def A' (e : evt) : act (unit × α) :=
A e on prod.snd

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
include init_FIS init_INV
lemma SIM₀' (v o : unit)
  (h : (o, v) ⊨ q')
: (∃ (w : α), (o, w) ⊨ p' ∧ (o, w, v) ⊨ J') :=
by { simp [q',p'] at *,
     apply exists_imp_exists _ init_FIS,
     intros, split, auto,
     apply init_INV, assumption }
end
open function
section
include evt_FIS evt_INV
lemma SIM' (w : α) (v o v' o' : unit) (e : evt)
  (hJ : (o, w, v) ⊨ J')
  (hC : C e (o, v) (o', v'))
: (∃ (w' : α), A' e (o, w) (o', w') ∧ (o', w', v') ⊨ J') :=
begin
  simp [comp,A',on_fun] at *,
  apply exists_imp_exists _ (evt_FIS e w hJ),
  tauto,
end

end

def o : tvar unit := ↑()

-- parameter Hpo
-- : ∀ c a e, one_to_one_po' (SPEC₀.saf a o ⋀ ◻(J ! ⦃o,a,c⦄))
--          ⟨cs₁ e,fs₁ e,C' e⟩
--          ⟨cs₀ e,fs₀ e,A' e⟩ ⦃o,c⦄ ⦃o,a⦄)


def SPEC₀.saf' (v : tvar α) (sch : tvar evt) : cpred :=
p' ! ⦃o,v⦄ ⋀
◻(∃∃ i, sch ≃ ↑i ⋀ ⟦ o,v | A' i ⟧)

def SPEC₁ (v : tvar unit) : cpred :=
q' ! ⦃o,v⦄ ⋀
◻(∃∃ i, ⟦ o,v | C i ⟧) ⋀
∀∀ i, sched (cs₁ i ! ⦃o,v⦄) (fs₁ i ! ⦃o,v⦄) ⟦ o,v | C i ⟧

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
    simp [C',SPEC₁,sched,q',action_on _ _ prod.snd,SPEC₀.saf'],
    intros _ _ _ h _, revert h,
    monotonicity only,
    simp, intro,
    explicit' [C,one_to_one.C',A']
    { cc, },
  end
end

include J init_INV init_FIS evt_INV evt_FIS Hpo'
lemma feasibility
: ⊩ (∃∃ v, SPEC₀ v) :=
begin [temporal]
  have :=  @one_to_one.refinement α unit unit evt
     temporal.feasibility.p' temporal.feasibility.q'
       temporal.feasibility.A'
       temporal.feasibility.C
       temporal.feasibility.cs₀'
       temporal.feasibility.fs₀'
       temporal.feasibility.cs₁
       temporal.feasibility.fs₁
       temporal.feasibility.J' _ _
       temporal.feasibility.SIM₀'
       temporal.feasibility.SIM'
       o _ Γ _,
  { simp [one_to_one.SPEC₀,SPEC₀] at this ⊢,
    casesm* [p_exists _, _ ⋀ _],
    existsi _, auto,
    split,
    { simp [SPEC₀.saf,one_to_one.SPEC₀.saf,A',p',action_on' _ _ prod.snd] at *,
      assumption, },
    { simp [A',action_on' _ _ prod.snd] at *,
      assumption, }, },
  apply temporal.feasibility.Hpo' ,
  { existsi o,
    simp [one_to_one.SPEC₁,q',C,C',sched], }
end

end feasibility
end feasibility
end temporal

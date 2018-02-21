-- import temporal_logic.tactic
import temporal_logic.lemmas

universes u u₀ u₁

open predicate temporal

namespace temporal
namespace fairness

section defs

variables p q A : cpred

def wf : cpred :=
◇◻p ⟶ ◻◇A

def sf : cpred :=
◻◇p ⟶ ◻◇A

def sched : cpred :=
◇◻p ⟶ ◻◇q ⟶ ◻◇(p ⋀ q ⋀ A)

instance persistent_sched : persistent (sched p q A) :=
by { unfold sched, apply_instance }

end defs
-- TODO(Simon) replace ~> with ◻◇_ ⟶ ◻◇_

structure one_to_one_po (S p q A p' q' A' : cpred) : Prop :=
  (delay : S ⟹ (p' ⋀ q' ~> p))
  (resched : S ⟹ (p' ⋀ q' ~> q))
  (stable : S ⟹ (◻◇p ⟶ ◇◻p' ⟶ ◇◻p))
  (sim : S ⟹ ◻(p ⟶ q ⟶ A ⟶ p' ⋀ q' ⋀ A'))

structure event (α : Type u₀) :=
(p q : pred' α) (A : act α)

def one_to_one_po' {α β} (S : cpred)
: event α → event β → tvar α → tvar β → Prop
| ⟨p₀,q₀,A₀⟩ ⟨p₁,q₁,A₁⟩ v w :=
one_to_one_po S
  (p₀!v) (q₀!v) ⟦ v | A₀ ⟧
  (p₁!w) (q₁!w) ⟦ w | A₁ ⟧

namespace one_to_one
section one_to_one

parameters {S p q A : cpred}
parameters {p' q' A' : cpred}
parameters po : one_to_one_po S p q A p' q' A'
parameters Γ : cpred
parameters hS : Γ ⊢ S
private def H₀ : Γ ⊢ p' ⋀ q' ~> p :=
po.delay Γ hS

private def H₁ : Γ ⊢ ◻◇p ⟶ ◇◻p' ⟶ ◇◻p :=
po.stable Γ hS

private def H₂ : Γ ⊢ ◻(p ⟶ q ⟶ A ⟶ p' ⋀ q' ⋀ A') :=
po.sim Γ hS
private def H₃ : Γ ⊢ p' ⋀ q' ~> q :=
po.resched Γ hS

include po hS

lemma replacement
: Γ ⊢ sched p q A ⟶ sched p' q' A' :=
begin [temporal]
  simp [sched], intros,
  have swc := coincidence a_1 a_2,
  have wc : ◇◻p,
  { assume_negation, simp at h,
    have H₁ := H₁ po Γ hS,
    have H₀ := H₀ po Γ hS,
    apply H₁ _ a_1,
    apply inf_often_of_leads_to H₀ swc, },
  have sc : ◻◇q,
  { have H₃ := H₃ po Γ hS,
    apply inf_often_of_leads_to H₃ swc, },
  replace a := a wc sc, revert a,
  { have H₂ := H₂ po Γ hS,
    intros H₃, replace H₃ := coincidence wc H₃,
    henceforth! at H₃ ⊢, eventually H₃ ⊢,
    casesm* _ ⋀ _,
    apply H₂ ; assumption, },
end

end one_to_one
end one_to_one
export one_to_one (replacement)


namespace splitting
section splitting

parameters (t : Sort u)
-- TODO(Simon) Weaken proof obligation `H₀`. We can do with ◻◇_ ⟶ ◻◇ _
-- instead of _ ~> _. Use w i unless -p'
structure many_to_many_po (S : cpred) (w p q A : t → cpred) (p' q' A' : cpred) : Prop :=
  (delay : S ⟹ ∀∀ i, p' ⋀ q' ⋀ w i ~> p i ⋀ q i ⋀ w i)
  (stable : S ⟹ ∀∀ i, ◇(p i ⋀ w i) ⟶ ◇◻p' ⟶ ◇◻(p i ⋀ w i))
  (wfis : S ⟹ ◻(p' ⋀ q' ⟶ ∃∃ i, w i))
  (sim : S ⟹ ∀∀ i, ◻(p i ⟶ q i ⟶ A i ⟶ p' ⋀ q' ⋀ A'))
def many_to_many_po' {α β} (S : cpred) (w : t → cpred)
: (t → event α) → event β → tvar α → tvar β → Prop
| e ⟨p₁,q₁,A₁⟩ cv av :=
many_to_many_po S w
  (λ i, (e i).p!cv) (λ i, (e i).q!cv) (λ i, ⟦ cv | (e i).A ⟧)
  (p₁!av) (q₁!av) ⟦ av | A₁ ⟧

parameters {t}
parameters {w p q A : t → cpred}
parameters {p' q' A' S : cpred}
parameters po : many_to_many_po S w p q A p' q' A'
parameters {Γ : cpred}
parameters hS : Γ ⊢ S

-- variables H₀ : Γ ⊢ ∀∀ i, ◻◇(p' ⋀ q' ⋀ w i) ⟶ ◻◇p i ⋀ q i ⋀ w i
def H₀ : Γ ⊢ ∀∀ i, p' ⋀ q' ⋀ w i ~> p i ⋀ q i ⋀ w i :=
po.delay Γ hS

def H₁ : Γ ⊢ ∀∀ i, ◇(p i ⋀ w i) ⟶ ◇◻p' ⟶ ◇◻(p i ⋀ w i) :=
po.stable Γ hS

def H₂ : Γ ⊢ ∀∀ i, ◻(p i ⟶ q i ⟶ A i ⟶ p' ⋀ q' ⋀ A') :=
po.sim Γ hS

def H₃ : Γ ⊢ ◻(p' ⋀ q' ⟶ ∃∃ i, w i) :=
po.wfis Γ hS

include hS po H₀ H₁ H₂ H₃

open temporal
lemma splitting
: Γ ⊢ (∀∀ i, sched (p i) (q i) (A i)) ⟶ sched p' q' A' :=
begin [temporal]
  intro H₅,
  simp [sched] at *, intros hp' hq',
  have H₇ := temporal.leads_to_disj_gen temporal.fairness.splitting.H₀,
  replace H₇ := inf_often_of_leads_to H₇ _,
  replace H₇ : ∃∃ (i : t), ◇(p i ⋀ q i ⋀ w i),
  { henceforth at H₇, rw eventually_exists at H₇, },
  { cases H₇ with i H₇,
    have H₉ := temporal.fairness.splitting.H₁ i _ hp',
    have : ◻◇q i,
    { have := inf_often_of_leads_to (temporal.fairness.splitting.H₀ i) _, revert this,
      { monotonicity!, lifted_pred, show _, { intros, assumption } },
      rw_using : (p' ⋀ q' ⋀ w i) = (p' ⋀ w i ⋀ q'),
      { lifted_pred, tauto },
      apply coincidence _ hq',
      { apply stable_and_of_stable_of_stable hp',
        revert H₉, monotonicity! p_and_elim_right _ _ _, }, },
    replace this := H₅ i _ this,
    { have H₂ := temporal.fairness.splitting.H₂ i,
      replace this := coincidence H₉ this,
      henceforth! at this ⊢, eventually this ⊢,
      casesm* _ ⋀ _, apply H₂ ; assumption  },
    { revert H₉, monotonicity!, lifted_pred,
      show _, { intros, assumption } },
    { revert H₇, monotonicity!, lifted_pred }, },
  { have := coincidence hp' hq', revert this,
    have H₃ := temporal.fairness.splitting.H₃,
    monotonicity!,
    intros hp,
    have := H₃ hp,
    revert this, apply p_exists_p_imp_p_exists,
    tauto, } ,
end

end splitting
end splitting
export splitting (splitting many_to_many_po many_to_many_po')
end fairness
end temporal

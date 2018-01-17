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
◇◻p ⟶ ◻◇q ⟶ ◻◇A

instance persistent_sched : persistent (sched p q A) :=
by { unfold sched, apply_instance }

end defs
-- TODO(Simon) replace ~> with ◻◇_ ⟶ ◻◇_

structure one_to_one_po (S p q A p' q' A' : cpred) : Prop :=
  (delay : S ⟹ (p' ⋀ q' ~> p))
  (resched : S ⟹ (p' ⋀ q' ~> q))
  (stable : S ⟹ (◻◇p ⟶ ◇◻p' ⟶ ◇◻p))
  (sim : S ⟹ ◻(A ⟶ A'))

structure event (α : Type u₀) (β : Type u₁) :=
(p q : pred' α) (A : act β)

def one_to_one_po' {α β} (S : cpred)
  (e₀ : event α α) (e₁ : event β β)
  (v₀) (w₀)
: Prop :=
one_to_one_po S
  (e₀.p!v₀) (e₀.q!v₀) ⟦ v₀ | e₀.A ⟧
  (e₁.p!w₀) (e₁.q!w₀) ⟦ w₀ | e₁.A ⟧

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

private def H₂ : Γ ⊢ ◻(A ⟶ A') :=
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
    persistent, monotonicity, apply H₂, },
end

end one_to_one
section splitting

variables {t : Sort u}
variables w p q A : t → cpred
variables Γ p' q' A' : cpred

-- TODO(Simon) Weaken proof obligation `H₀`. We can do with ◻◇_ ⟶ ◻◇ _
-- instead of _ ~> _. Use w i unless -p'

-- variables H₀ : Γ ⊢ ∀∀ i, ◻◇(p' ⋀ q' ⋀ w i) ⟶ ◻◇p i ⋀ q i ⋀ w i
variables H₀ : Γ ⊢ ∀∀ i, p' ⋀ q' ⋀ w i ~> p i ⋀ q i ⋀ w i
variables H₁ : Γ ⊢ ∀∀ i, ◇(p i ⋀ w i) ⟶ ◇◻p' ⟶ ◇◻(p i ⋀ w i)
variables H₂ : Γ ⊢ ∀∀ i, ◻(A i ⟶ A')
variables H₃ : Γ ⊢ ◻(p' ⋀ q' ⟶ ∃∃ i, w i)
include H₀ H₁ H₂ H₃

open temporal
lemma splitting
: Γ ⊢ (∀∀ i, sched (p i) (q i) (A i)) ⟶ sched p' q' A' :=
begin [temporal]
  intro H₅,
  simp [sched] at *, intros hp' hq',
  have H₇ := inf_often_of_leads_to (temporal.leads_to_disj_gen  H₀) _,
  replace H₇ : ∃∃ (i : t), ◇(p i ⋀ q i ⋀ w i),
  { henceforth at H₇, rw eventually_exists at H₇, },
  { cases H₇ with i H₇,
    have H₉ := H₁ i _ hp',
    have : ◻◇q i,
    { have := inf_often_of_leads_to (H₀ i) _, revert this,
      { monotonicity only, lifted_pred },
      rw_using : (p' ⋀ q' ⋀ w i) = (p' ⋀ w i ⋀ q'),
      { lifted_pred },
      apply coincidence _ hq',
      { apply stable_and_of_stable_of_stable hp',
        revert H₉, monotonicity only p_and_elim_right _ _ _, }, },
    have := H₅ i _ this,
    { revert this, monotonicity only,
      apply H₂ i },
    { revert H₉, monotonicity only, lifted_pred, },
    { revert H₇, monotonicity only, lifted_pred }, },
  { have := coincidence hp' hq', revert this,
    monotonicity only,
    simp, intros hp hq,
    have := H₃ hp hq,
    revert this, apply p_exists_p_imp_p_exists,
    intros i hw, repeat { split <|> assumption }, } ,
end

end splitting

end fairness
end temporal

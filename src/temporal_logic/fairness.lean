-- import temporal_logic.tactic
import temporal_logic.lemmas

universes u

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
section one_to_one

variables {p q A : cpred}
variables {p' q' A' : cpred}
variables Γ : cpred

variables H₀ : Γ ⊢ p' ⋀ q' ~> p
variables H₁ : Γ ⊢ ◻◇p ⟶ ◇◻p ⋁ ◻◇-p'
variables H₂ : Γ ⊢ ◻(A ⟶ A')
variables H₃ : Γ ⊢ p' ⋀ q' ~> q
include H₀ H₁ H₂ H₃

lemma replacement
: Γ ⊢ sched p q A ⟶ sched p' q' A' :=
begin [temporal]
  simp [sched], intros,
  have swc := coincidence a_1 a_2,
  have wc : ◇◻p,
  { assume_negation, simp at h,
    rw [p_or_comm,← p_not_p_imp] at H₁, simp at H₁,
    apply H₁ _ a_1,
    apply inf_often_of_leads_to H₀ swc, },
  have sc : ◻◇q,
  { apply inf_often_of_leads_to H₃ swc, },
  replace a := a wc sc, revert a,
  { persistent, monotonicity, apply H₂, },
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

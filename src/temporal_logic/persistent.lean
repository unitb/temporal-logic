
import temporal_logic.basic

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal
open predicate
class persistent (p : cpred) : Prop :=
  (is_persistent : ◻p = p)
export persistent (is_persistent)

instance henceforth_persistent {p : cpred} : persistent (◻p) :=
by { constructor, simp }

instance not_eventually_persistent {p : cpred} : persistent (-◇p) :=
by { constructor, simp }

instance leads_to_persistent {p q : cpred} : persistent (p ~> q) :=
by { constructor, simp [tl_leads_to,is_persistent] }

instance and_persistent {p q : cpred} [persistent p] [persistent q]
: persistent (p ⋀ q) :=
by { constructor, simp [henceforth_and,is_persistent], }

instance coe_persistent (p : Prop)
: persistent (p : cpred) :=
by { constructor, cases classical.prop_complete p ; subst p ; simp, }

instance true_persistent
: persistent (True : cpred) :=
by { constructor, simp, }

instance false_persistent
: persistent (False : cpred) :=
by { constructor, simp, }

instance forall_persistent {p : α → cpred} [∀ i, persistent (p i)]
: persistent (p_forall p) :=
by { constructor, simp [henceforth_forall,is_persistent], }

instance not_exists_persistent {p : α → cpred} [∀ i, persistent (- p i)]
: persistent (- p_exists p) :=
by { constructor, simp [p_not_p_exists,henceforth_forall,is_persistent], }

instance exists_persistent {p : α → cpred} [∀ i, persistent (p i)]
: persistent (p_exists p) :=
by { constructor, apply mutual_entails,
     apply henceforth_str,
     apply p_exists_elim, intro, rw ← is_persistent (p x),
     monotonicity, apply p_exists_intro, }

instance not_forall_persistent {p : α → cpred} [∀ i, persistent (- p i)]
: persistent (- p_forall p) :=
by { constructor, simp [p_not_p_forall], apply is_persistent }

def list_persistent (xs : list cpred) :=
Π q ∈ xs, persistent q

lemma nil_persistent
: list_persistent [] :=
by { intros p h, cases h }

lemma cons_persistent (x : cpred) (xs : list $ cpred)
  [persistent x]
  (h : list_persistent xs)
: list_persistent (x :: xs) :=
by { intros p h, simp [list_persistent] at *,
     cases h ; [ subst p, skip ] ; auto, }

def with_h_asms (Γ : cpred) : Π (xs : list (cpred)) (x : cpred), Prop
 | [] x := Γ ⊢ x
 | (x :: xs) y := Γ ⊢ x → with_h_asms xs y

lemma indirect_judgement (h p : pred' β)
  (H : ∀ Γ, Γ ⊢ h → Γ ⊢ p)
: h ⊢ p :=
sorry

lemma judgement_trans (p q r : pred' β)
  (h₀ : p ⊢ q)
  (h₁ : q ⊢ r)
: p ⊢ r :=
sorry

lemma from_antecendent (xs : list (cpred)) (p : cpred)
  (h : ∀ Γ, with_h_asms Γ xs p)
: ◻ xs.foldr (⋀) True ⊢ p :=
begin
  apply indirect_judgement,
  introv h', specialize h Γ,
  induction xs with x xs,
  { simp [with_h_asms] at h, apply h },
  { simp [list.foldr,henceforth_and] at h',
    apply ih_1,
    { revert h',
      apply p_impl_revert,
      apply p_and_elim_right },
    { apply h, revert h',
      apply p_impl_revert,
      apply p_and_entails_of_entails_left,
      apply henceforth_str, } }
end

class postponable (p : cpred) : Prop :=
  (postpone : ◇p = p)
export postponable (postpone)

lemma p_imp_postpone (Γ p q : cpred) [postponable q]
  (h : tl_imp Γ p q)
: tl_imp Γ (◇p) q :=
begin
  rw ← postpone q,
  monotonicity h,
end

instance (p : cpred) : postponable (◇p) :=
by { constructor, simp [eventually_eventually] }

instance forall_postponable (p : α → cpred) [∀ i, postponable (p i)]
: postponable (p_forall p) :=
⟨ begin
    apply mutual_entails,
    { rw [p_entails_of_fun],
      introv h, rw p_forall_to_fun, intro i,
      rw ← postpone (p i), revert h, apply p_impl_revert,
      revert Γ, change (_ ⟹ _),
      monotonicity, rw [p_entails_of_fun],
      introv h, apply p_forall_revert h },
    apply eventually_weaken
  end ⟩

instance exists_postponable (p : α → cpred) [∀ i, postponable (p i)]
: postponable (p_exists p) :=
by constructor ; simp [eventually_exists,postpone]

lemma persistent_to_henceforth {p q : cpred}
  (h : ◻ p ⊢ q)
: ◻ p ⊢ ◻ q :=
sorry

instance has_coe_to_fun_henceforth (Γ p q : cpred) : has_coe_to_fun (Γ ⊢ ◻(p ⟶ q)) :=
{ F := λ _, Γ ⊢ p → Γ ⊢ q
, coe := assume h, henceforth_str (p ⟶ q) Γ h  }

instance has_coe_to_fun_leads_to (Γ p q : cpred) : has_coe_to_fun (Γ ⊢ p ~> q) :=
temporal.has_coe_to_fun_henceforth _ _ _



end temporal

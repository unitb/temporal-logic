
import temporal_logic.basic

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal
open predicate

class postponable (p : cpred) : Prop :=
  (postpone : ◇p = p)
export postponable (postpone)

instance henceforth_persistent {p : cpred} : persistent (◻p) :=
by { constructor, simp only with tl_simp }

instance persistent_not {p : cpred} [postponable p] : persistent (-p) :=
by { constructor, rw [← not_eventually, postpone p] }

instance leads_to_persistent {p q : cpred} : persistent (p ~> q) :=
by { constructor, simp [tl_leads_to,is_persistent] }

instance and_persistent {p q : cpred} [persistent p] [persistent q]
: persistent (p ⋀ q) :=
by { constructor, simp [henceforth_and,is_persistent], }

instance coe_persistent (p : Prop)
: persistent (p : cpred) :=
by { constructor, cases classical.prop_complete p ; subst p ; simp with tl_simp, }

instance false_persistent
: persistent (False : cpred) :=
by { constructor, simp only with tl_simp, }

instance forall_persistent {p : α → cpred} [∀ i, persistent (p i)]
: persistent (p_forall p) :=
by { constructor, simp [henceforth_forall,is_persistent], }


instance exists_persistent {p : α → cpred} [∀ i, persistent (p i)]
: persistent (p_exists p) :=
by { constructor, apply mutual_entails,
     apply henceforth_str,
     apply p_exists_elim, intro, rw ← is_persistent (p x),
     monotonicity, apply p_exists_intro, }

instance (p : cpred) : postponable (◇p) :=
by { constructor, simp [eventually_eventually] }

instance postponable_not {p : cpred} [persistent p] : postponable (-p) :=
by { constructor, rw [← not_henceforth, is_persistent p] }

instance or_postponable {p q : cpred} [postponable p] [postponable q]
: postponable (p ⋁ q) :=
by { constructor, simp [eventually_or,postpone], }

instance imp_postponable {p q : cpred} [persistent p] [postponable q]
: postponable (p ⟶ q) :=
by { simp [p_imp_iff_p_not_p_or], apply_instance }

instance coe_postponable (p : Prop)
: postponable (p : cpred) :=
by { constructor, cases classical.prop_complete p ; subst p ; simp with tl_simp, }

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

-- instance not_forall_persistent {p : α → cpred} [∀ i, persistent (- p i)]
-- : persistent (- p_forall p) :=
-- by { constructor, simp [p_not_p_forall], apply is_persistent }

inductive list_persistent : list cpred → Prop
 | nil_persistent : list_persistent []
 | cons_persistent (x : cpred) (xs : list $ cpred)
   [persistent x]
   (h : list_persistent xs)
 : list_persistent (x :: xs)

export list_persistent (nil_persistent)

def with_h_asms (Γ : cpred) : Π (xs : list (cpred)) (x : cpred), Prop
 | [] x := Γ ⊢ x
 | (x :: xs) y := Γ ⊢ x → with_h_asms xs y

lemma indirect_judgement (h p : pred' β)
  (H : ∀ Γ, Γ ⊢ h → Γ ⊢ p)
: h ⊢ p :=
by { apply H, lifted_pred keep, assumption }

lemma judgement_trans (p q r : pred' β)
  (h₀ : p ⊢ q)
  (h₁ : q ⊢ r)
: p ⊢ r :=
by { lifted_pred keep,
     apply h₁.apply,
     apply h₀.apply _ a }

lemma p_imp_postpone (Γ p q : cpred)
  [persistent Γ]
  [postponable q]
  (h : ctx_impl Γ p q)
: ctx_impl Γ (◇p) q :=
begin
  rw ← postpone q,
  monotonicity h,
end

lemma persistent_to_henceforth {p q : cpred}
  [persistent p]
  (h : p ⊢ q)
: p ⊢ ◻ q :=
by { rw ← is_persistent p,
     lifted_pred keep, intro i,
     apply h.apply _ (a i), }

lemma henceforth_deduction {Γ p q : cpred}
  (h : Γ ⊢ ◻(p ⟶ q))
: Γ ⊢ p → Γ ⊢ q :=
henceforth_str (p ⟶ q) Γ h

instance has_coe_to_fun_henceforth (Γ p q : cpred) : has_coe_to_fun (Γ ⊢ ◻(p ⟶ q)) :=
{ F := λ _, Γ ⊢ p → Γ ⊢ q
, coe :=  henceforth_deduction }

instance has_coe_to_fun_leads_to (Γ p q : cpred) : has_coe_to_fun (Γ ⊢ p ~> q) :=
temporal.has_coe_to_fun_henceforth _ _ _



end temporal

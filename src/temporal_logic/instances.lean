
import .scheduling
import data.equiv

universes u v u' v'

namespace temporal
open function

instance schedulable_empty : schedulable empty :=
{ f := λ _, 0
, inj := by { intros _ _, casesm* empty, }  }

instance schedulable_unit : schedulable unit :=
{ f := λ _, 0
, inj := by { intros _ _, casesm* unit, simp }  }

instance schedulable_bool : schedulable bool :=
{ f := bool.rec 0 1
, inj := by { intros _ _, casesm* bool ; simp }  }

instance schedulable_nat : schedulable ℕ :=
{ f := id
, inj := injective_id }
open equiv

lemma equiv.inj {α β} (h : α ≃ β) : injective h :=
by { apply injective_of_left_inverse, apply h.left_inv }

instance schedulable_int : schedulable ℤ :=
{ f := int_equiv_nat
, inj := equiv.inj _ }

instance schedulable_fin (n : ℕ) : schedulable (fin n) :=
{ f := fin.val
, inj := by { intros _ _, apply fin.eq_of_veq } }

variables {α : Type u} {β : Type v} {η : α → Type u'}
variables {α' : Type u'} {β' : Type v'}

section inductive_construction

variables [schedulable α]
variables [schedulable β]
variables [∀ x, schedulable (η x)]

def sum.map (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
| (sum.inr x) := sum.inr (g x)
| (sum.inl x) := sum.inl (f x)

open equiv scheduling.schedulable

instance schedulable_sum : schedulable (α ⊕ β) :=
{ f := nat_sum_nat_equiv_nat ∘ sum.map scheduling.schedulable.f scheduling.schedulable.f
, inj := by { apply injective_comp, apply equiv.inj,
              intros _ _, casesm* _ ⊕ _ ; simp [sum.map] ; apply inj, } }

instance schedulable_option : schedulable (option α) :=
{ f := f ∘ option_equiv_sum_unit α
, inj :=
begin
  apply injective_comp,
  { apply inj },
  { apply equiv.inj, },
end
}

instance schedulable_list : schedulable (list α) :=
{ f := f ∘ list_nat_equiv_nat ∘ list.map f
, inj :=
begin
  apply injective_comp,
  { apply inj },
  apply injective_comp,
  { apply equiv.inj, },
  { intros xs,
    induction xs ; intro ys ; cases ys ; simp,
    intros, split,
    apply inj _ a,
    solve_by_elim },
end
}

instance schedulable_prod : schedulable (α × β) :=
{ f := nat_prod_nat_equiv_nat ∘ prod.map scheduling.schedulable.f scheduling.schedulable.f
, inj := by { apply injective_comp,
              { apply equiv.inj },
              intros _ _, casesm* _ × _,
              simp [prod.map], intros,
              split ; apply inj ; solve_by_elim } }

def index_pair : sigma η → ℕ × ℕ
 | ⟨x,y⟩ := (f x,f y)

instance schedulable_sigma : schedulable (sigma η) :=
{ f := nat_prod_nat_equiv_nat ∘ index_pair
, inj := by { apply injective_comp,
              { apply equiv.inj },
              intros _ _, casesm* sigma _,
              simp [index_pair],
              intros,
              have : a₁_fst = a₂_fst := inj _ (by solve_by_elim),
              subst a₂_fst, simp,
              exact inj _ (by solve_by_elim) }  }

end inductive_construction

section from_other_class

open fintype

local attribute [instance] classical.prop_decidable

noncomputable instance fintype_schedulable [fintype α] : schedulable α :=
{ f := (λ x, (trunc.out (equiv_fin α) x).val)
, inj := by { intros _ _ h, simp at h,
              replace h := fin.eq_of_veq h,
              apply equiv.inj _ h, } }

class countable_type (α : Type u) :=
(enum : trunc $ α ≃ ℕ)

noncomputable instance countable_type_schedulable [countable_type α] : schedulable α :=
{ f := (λ x, trunc.out (countable_type.enum α) x)
, inj := by { intros _ _ h, simp at h, exact h, } }

end from_other_class

end temporal

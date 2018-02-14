
import .fairness

universe variables u u₀ u₁ u₂

namespace temporal

open predicate fairness

variables {α : Type u} {evt : Type u₀}
variables (p : pred' α)
variables (cs fs : evt → pred' α)
variables (A : evt → act α)

@[simp]
def spec_saf_spec (v : tvar α) (sch : tvar evt) : cpred :=
p ! v ⋀
◻(∃∃ e, sch ≃ ↑e ⋀ cs e ! v ⋀ fs e ! v ⋀ ⟦ v | A e ⟧)

@[simp]
def spec (v : tvar α) : cpred :=
p ! v ⋀
◻(∃∃ e, cs e ! v ⋀ fs e ! v ⋀ ⟦ v | A e ⟧) ⋀
∀∀ e, sched (cs e ! v) (fs e ! v) ⟦ v | A e ⟧

@[simp]
def spec_sch (v : tvar α) (sch : tvar evt) : cpred :=
p ! v ⋀
◻(∃∃ e, sch ≃ ↑e ⋀ cs e ! v ⋀ fs e ! v ⋀ ⟦ v | A e ⟧) ⋀
∀∀ e, sched (cs e ! v) (fs e ! v) (sch ≃ e ⋀ ⟦ v | A e ⟧)


end temporal

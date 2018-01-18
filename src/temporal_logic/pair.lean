import temporal_logic.basic

universe variables u u₀ u₁ u₂

namespace temporal
open predicate

section pair

variables {α' : Type u} {β' : Type u₀} {γ' : Type u₁}
variables (x : tvar α') (y : tvar β') (z : tvar γ')

@[simp]
lemma pair_model (i : ℕ) :
i ⊨ ⦃x,y⦄ = (i ⊨ y,i ⊨ x) :=
by { cases x, cases y, refl }

@[reducible]
def pair.fst : var (α' × β') α' :=
⟨ @prod.fst α' β' ⟩

@[simp]
def pair.fst_mk (x : tvar α') (y : tvar β')
: pair.fst ! ⦃y,x⦄ = x :=
by lifted_pred

@[simp]
def pair.fst_mk' (x : tvar α') (y : tvar β')
: ⟨ @prod.fst α' β' ⟩ ! ⦃y,x⦄ = x :=
pair.fst_mk _ _

@[simp]
def pair.snd_mk' (x : tvar α') (y : tvar β')
: ⟨ @prod.snd α' β' ⟩ ! ⦃y,x⦄ = y :=
by lifted_pred

@[simp]
def prod.map_left {α β γ} (f : α → β) : α × γ → β × γ
 | (x,y) := (f x, y)

@[simp]
def prod.map_right {α β γ} (f : β → γ) : α × β → α × γ
 | (x,y) := (x,f y)
open temporal.prod

@[simp]
lemma map_right_proj_pair (f : α' → γ')
: ⟨map_right f⟩ ! ⦃x,y⦄ = ⦃⟨f⟩ ! x, y⦄ :=
by ext i ; simp [map_right]

@[simp]
lemma map_left_proj_pair (f : α' → γ')
: ⟨map_left f⟩ ! ⦃y,x⦄ = ⦃y, ⟨f⟩ ! x⦄ :=
by ext i ; simp [map_left]

end pair

end temporal

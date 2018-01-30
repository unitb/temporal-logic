import temporal_logic.basic

universe variables u u₀ u₁ u₂

namespace temporal
open predicate

section pair

variables {α' : Type u} {β' : Type u₀} {γ' : Type u₁} {ω : Type u₂}
variables (x : tvar α') (y : tvar β') (z : tvar γ')

@[simp]
lemma pair_model (i : ℕ) :
i ⊨ ⦃x,y⦄ = (i ⊨ x,i ⊨ y) :=
by { cases x, cases y, refl }

@[reducible]
def pair.fst : var (α' × β') α' :=
⟨ @prod.fst α' β' ⟩

@[reducible]
def pair.snd : var (α' × β') β' :=
⟨ @prod.snd α' β' ⟩

@[simp]
def pair.fst_mk (x : tvar α') (y : tvar β')
: pair.fst ! ⦃x,y⦄ = x :=
by lifted_pred

@[simp]
def pair.fst_mk' (x : tvar α') (y : tvar β')
: ⟨ @prod.fst α' β' ⟩ ! ⦃x,y⦄ = x :=
pair.fst_mk _ _

@[simp]
def pair.snd_mk (x : tvar α') (y : tvar β')
: pair.snd ! ⦃x,y⦄ = y :=
by lifted_pred

@[simp]
def pair.snd_mk' (x : tvar α') (y : tvar β')
: ⟨ @prod.snd α' β' ⟩ ! ⦃x,y⦄ = y :=
by lifted_pred

@[simp]
def prod.map_left {α β γ} (f : α → β) : α × γ → β × γ
 | (x,y) := (f x, y)

@[simp]
def prod.map_right {α β γ} (f : β → γ) : α × β → α × γ
 | (x,y) := (x,f y)
open temporal.prod

@[simp]
lemma map_right_proj_pair (f : β' → γ')
: ⟨map_right f⟩ ! ⦃x,y⦄ = ⦃x, ⟨f⟩ ! y⦄ :=
by ext i ; simp [map_right]

@[simp]
lemma map_left_proj_pair (f : α' → γ')
: ⟨map_left f⟩ ! ⦃x,y⦄ = ⦃⟨f⟩ ! x, y⦄ :=
by ext i ; simp [map_left]

@[simp]
lemma map_proj_pair (f : α' → γ') (g : β' → ω)
: ⟨prod.map f g⟩ ! ⦃x,y⦄ = ⦃⟨f⟩ ! x,⟨g⟩ ! y⦄ :=
by ext i ; simp [prod.map]

@[simp]
lemma eta_pair (w : tvar (α' × β'))
: ⦃pair.fst ! w, pair.snd ! w⦄ = w :=
by ext i ; simp [prod.map]

@[simp]
lemma next_pair (v₀ : tvar α') (v₁ : tvar β')
: ⊙⦃v₀,v₁⦄ = ⦃⊙v₀,⊙v₁⦄ :=
by lifted_pred [next]
end pair

end temporal

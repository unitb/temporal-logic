import temporal_logic.basic

universe variables u u₀ u₁ u₂

namespace temporal
open predicate

section pair

variables {α : Type u} {β : Type u₀} {γ : Type u₁} {ω : Type u₂}
variables (x : tvar α) (y : tvar β) (z : tvar γ)

@[tl_simp, simp]
lemma pair_model (i : ℕ) :
i ⊨ ⦃x,y⦄ = (i ⊨ x,i ⊨ y) :=
by { cases x, cases y, refl }

@[reducible]
def pair.fst : var (α × β) α :=
⟨ @prod.fst α β ⟩

@[reducible]
def pair.snd : var (α × β) β :=
⟨ @prod.snd α β ⟩

abbreviation tvar.fst (p : var γ (α × β)) : var γ α :=
pair.fst!p

abbreviation tvar.snd (p : var γ (α × β)) : var γ β :=
pair.snd!p

@[tl_simp, simp]
def pair.fst_mk (x : tvar α) (y : tvar β)
: pair.fst ! ⦃x,y⦄ = x :=
by lifted_pred

@[tl_simp, simp]
def pair.fst_mk' (x : tvar α) (y : tvar β)
: ⟨ @prod.fst α β ⟩ ! ⦃x,y⦄ = x :=
pair.fst_mk _ _

@[tl_simp, simp]
def pair.snd_mk (x : tvar α) (y : tvar β)
: pair.snd ! ⦃x,y⦄ = y :=
by lifted_pred

@[tl_simp, simp]
def pair.snd_mk' (x : tvar α) (y : tvar β)
: ⟨ @prod.snd α β ⟩ ! ⦃x,y⦄ = y :=
by lifted_pred

@[tl_simp, simp]
def prod.map_left {α β γ} (f : α → β) : α × γ → β × γ
 | (x,y) := (f x, y)

@[tl_simp, simp]
def prod.map_right {α β γ} (f : β → γ) : α × β → α × γ
 | (x,y) := (x,f y)
open temporal.prod

@[tl_simp, simp]
lemma map_right_proj_pair (f : β → γ)
: ⟨map_right f⟩ ! ⦃x,y⦄ = ⦃x, ⟨f⟩ ! y⦄ :=
by ext i ; simp [map_right] with tl_simp

@[tl_simp, simp]
lemma map_left_proj_pair (f : α → γ)
: ⟨map_left f⟩ ! ⦃x,y⦄ = ⦃⟨f⟩ ! x, y⦄ :=
by ext i ; simp [map_left] with tl_simp

@[tl_simp, simp]
lemma map_proj_pair (f : α → γ) (g : β → ω)
: ⟨prod.map f g⟩ ! ⦃x,y⦄ = ⦃⟨f⟩ ! x,⟨g⟩ ! y⦄ :=
by ext i ; simp [prod.map] with tl_simp

@[tl_simp, simp]
lemma eta_pair (w : tvar (α × β))
: ⦃w.fst, w.snd⦄ = w :=
by ext i ; simp [prod.map] with tl_simp

@[tl_simp, simp]
lemma next_pair (v₀ : tvar α) (v₁ : tvar β)
: ⊙⦃v₀,v₁⦄ = ⦃⊙v₀,⊙v₁⦄ :=
by lifted_pred [next]

@[tl_simp, simp, predicate]
lemma to_fun_var_pair (f : tvar α → tvar β) (g : tvar α → tvar γ) (w : tvar α)
: to_fun_var (λ w : tvar α, ⦃f w,g w⦄) w = ⦃to_fun_var f w,to_fun_var g w⦄ :=
by { lifted_pred, simp! }

end pair

end temporal

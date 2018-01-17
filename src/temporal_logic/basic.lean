
import util.predicate

@[user_attribute]
meta def strengthening_attr : user_attribute :=
{ name := `strengthening
, descr := "
Strenghtening lemmas to facilitate the stripping of small details in application.
Expected shape `∀ p : pred' α, ⊩ f p ⟶ g p`
" }

local attribute [-simp] or.comm or.left_comm or.assoc and.comm and.left_comm and.assoc

namespace tactic.interactive
open lean interactive.types
open interactive lean.parser tactic
open list (hiding map) has_map predicate
local postfix *:9001 := many

meta def TL_unfold (cs : parse ident*) (loc : parse location) : tactic unit :=
do unfold_coes loc, unfold (cs ++ [`var.apply,`pred'.mk]) loc

end tactic.interactive

namespace temporal

open predicate

universe variables u u₀ u₁ u₂

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

@[reducible]
def tvar := var ℕ

@[reducible]
def cpred := tvar Prop

def act (β : Sort u) := β → β → Prop

def action (a : act α) (v : tvar α) : cpred :=
⟨ λ i, a (v.apply i) (v.apply $ i.succ) ⟩

def eventually (p : cpred) : cpred :=
⟨ λ i, ∃ j, p.apply (i+j) ⟩
def henceforth (p : cpred) : cpred :=
⟨ λ i, ∀ j, p.apply (i+j) ⟩
def next (p : tvar α) : tvar α :=
⟨ λ i, p.apply (i.succ) ⟩

def pair {α β} (x : tvar α) (y : tvar β) : tvar (α × β) :=
lifted₂ prod.mk x y

notation `⦃` x `,` l:(foldl `,` (h t, pair h t) x `⦄`)  := l

prefix `⊙`:90 := next
prefix `◇`:95 := eventually -- \di
prefix `◻`:95 := henceforth -- \sqw
notation `⟦ `:max v ` : `:50 R ` ⟧`:0 := action R v
notation `⟦ `:max v `,` v' ` : `:50 R ` ⟧`:0 := action R (pair v v')
notation `⟦ `:max v₀ `,` v₁ `,` v₂ ` : `:50 R ` ⟧`:0 := action R (pair v₀ (pair v₁ v₂))
notation `⟦ `:max v₀ `,` v₁ `,` v₂ `,` v₃ ` : `:50 R ` ⟧`:0 := action R (pair v₀ (pair v₁ (pair v₂ v₃)))

def tl_leads_to (p q : cpred) : cpred :=
◻(p ⟶ ◇q)

infix ` ~> `:55 := tl_leads_to

@[reducible]
def tl_imp (h p q : cpred) : Prop :=
ctx_impl (◻ h) p q

lemma tl_imp_intro (h : cpred) {p q : cpred}
  (h' : ◻h ⟹ (p ⟶ q))
: tl_imp h p q :=
begin
  constructor, intro,
  exact (h' True).apply σ trivial,
end

lemma tl_imp_elim (h : cpred) {p q : cpred}
  (h' : tl_imp h p q)
: ◻h ⟹ (p ⟶ q) :=
begin
  intro, revert Γ,
  apply intro_p_imp h',
end

lemma tl_imp_intro' (h : cpred) {p q : cpred}
  (h' : p ⟹ q)
: tl_imp h p q :=
h' _

@[simp]
lemma hence_true : ◻(True : cpred) = True :=
begin
  funext1,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

lemma tl_imp_elim' {p q : cpred}
  (h : tl_imp True p q)
: p ⟹ q :=
begin
  simp [tl_imp,ctx_impl] at h,
  apply h,
end

@[strengthening]
lemma eventually_weaken (p : cpred)
: (p ⟹ ◇ p) :=
begin
  pointwise with τ h,
  unfold eventually,
  existsi 0,
  apply h
end
open stream

@[strengthening]
lemma next_entails_eventually (p : cpred)
: ⊙p ⟹ ◇p :=
sorry

@[strengthening]
lemma henceforth_entails_next (p : cpred)
: ◻p ⟹ ⊙p :=
sorry

@[strengthening]
lemma henceforth_str (p : cpred) :
  (◻p ⟹ p) :=
begin
  pointwise with τ h, apply h 0
end

local infix ` <$> ` := fun_app_to_var
local infix ` <*> ` := combine_var

lemma init_eq_action {p : α → Prop} (v : tvar α)
: ⟨p⟩ ! v = ⟦ v : λ s s', p s ⟧ :=
by { cases v, refl }

lemma coe_eq (v : tvar α) (x : α)
: ⟨λ y, y = x⟩ ! v = v ≃ x :=
by { cases v, refl }

lemma init_eq_action' {p : pred' α} (v : tvar α)
: (p ! v) = ⟦ v : λ s s', p.apply s ⟧ :=
by { cases v, cases p, refl }

lemma next_eq_action {p : α → Prop} (v : tvar α)
: ⊙(p <$> v) = ⟦ v : λ s s' : α, p s' ⟧ :=
by { cases v, refl }

lemma next_eq_action' {p : pred' α} (v : tvar α)
: ⊙(p ! v) = ⟦ v : λ s s' : α, p.apply s' ⟧ :=
by { cases v, cases p, refl }

lemma not_action {A : act α} (v : tvar α)
: -⟦ v : A ⟧ = ⟦ v : λ s s', ¬ A s s' ⟧ :=
rfl

lemma action_imp (p q : act α) (v : tvar α)
: (⟦ v : λ s s' : α, p s s' → q s s' ⟧ : cpred) = ⟦ v : p ⟧ ⟶ ⟦ v : q ⟧ :=
rfl

lemma action_and_action (p q : act α) (v : tvar α)
: ⟦ v : p ⟧ ⋀ ⟦ v : q ⟧ = ⟦ v : λ s s' : α, p s s' ∧ q s s' ⟧ :=
rfl

lemma action_or_action (p q : act α) (v : tvar α)
: ⟦ v : p ⟧ ⋁ ⟦ v : q ⟧ = ⟦ v : λ s s' : α, p s s' ∨ q s s' ⟧ :=
rfl

lemma action_false (v : tvar α)
: (⟦ v : λ _ _, false ⟧ : cpred) = False :=
by { funext x, refl }

variables {Γ : cpred}

lemma unlift_action (A : act α) (v : tvar α)
  (h : ∀ σ σ', A σ σ')
: Γ ⊢ ⟦ v : A ⟧ :=
begin
  constructor, simp_intros [action],
  apply h
end

lemma henceforth_next_intro (p : cpred)
: ◻p = ◻(p ⋀ ⊙p) := sorry

@[simp]
lemma eventually_eventually (p : cpred) : ◇◇ p = ◇ p :=
begin
  funext k,
  split
  ; unfold eventually
  ; intro h
  ; cases h with i h,
  { cases h with j h,
    existsi (i+j),
    simp at h, apply h, },
  { existsi (0 : ℕ),
    existsi i,
    apply h }
end

@[simp]
lemma henceforth_henceforth (p : cpred) : ◻◻ p = ◻ p :=
begin
  funext _,
  split
  ; intro h,
  { intro i,
    have h' := h i 0,
    simp [drop_drop] at h',
    apply h' },
  { intros i j,
    simp [drop_drop],
    apply h }
end

/- True / False -/

@[simp]
lemma hence_false : ◻(False : cpred) = False :=
begin
  funext _,
  split ; intro h,
  { cases h 0 },
  { cases h }
end

@[simp]
lemma event_false : ◇(False : cpred) = False :=
begin
  funext _,
  split ; intro h,
  { cases h with _ h, cases h },
  { cases h }
end

@[simp]
lemma eventually_true : ◇(True : cpred) = True :=
begin
  funext1,
  split ; intro h,
  { trivial },
  { apply exists.intro 0, trivial }
end

/- monotonicity -/

@[monotonic]
lemma eventually_tl_imp_eventually {h p q : cpred}
  (f : tl_imp h p q)
: tl_imp h (◇p) (◇q) :=
begin
  unfold tl_imp ctx_impl at ⊢ f,
  pointwise f with τ h',
  apply exists_imp_exists,
  intro i,
  apply f,
  rw ← henceforth_henceforth at h',
  apply h',
end

@[monotonic]
lemma eventually_entails_eventually {p q : cpred}
  (f : p ⟹ q)
: (◇p) ⟹ (◇q) :=
begin
  apply tl_imp_elim',
  monotonicity (tl_imp_intro' _ f),
end

lemma eventually_imp_eventually {p q : cpred} {Γ}
 (f : Γ ⊢ ◻ (p ⟶ q))
: Γ ⊢ (◇p) ⟶ (◇q) :=
begin
  constructor, introv hΓ,
  apply exists_imp_exists,
  intro i,
  apply f.apply _ hΓ,
end

@[monotonic]
lemma henceforth_tl_imp_henceforth {h p q : cpred}
  (f : tl_imp h p q)
: tl_imp h (◻p) (◻q) :=
begin
  unfold tl_imp ctx_impl at *,
  pointwise f with i h',
  simp [henceforth], intro_mono i,
  apply f ,
  rw ← henceforth_henceforth at h',
  apply  h',
end

@[monotonic]
lemma henceforth_entails_henceforth {p q : cpred}
  (f : p ⟹ q)
: (◻p) ⟹ (◻q) :=
begin
  refine tl_imp_elim' _,
  monotonicity (tl_imp_intro' _ f),
end

lemma henceforth_imp_henceforth {p q : cpred} {Γ}
  (h : Γ ⊢ ◻ (p ⟶ q))
: Γ ⊢ (◻p) ⟶ (◻q) :=
begin
  pointwise h with τ,
  specialize h τ, simp [henceforth] at ⊢ h,
  introv h₀ h₁,
  auto,
end

lemma inf_often_entails_inf_often {p q : cpred} (f : p ⟹ q)
: ◻◇p ⟹ ◻◇q :=
by monotonicity f

lemma stable_entails_stable {p q : cpred} (f : p ⟹ q)
: ◇◻p ⟹ ◇◻q :=
by monotonicity f

lemma henceforth_and (p q : cpred)
: ◻(p ⋀ q) = ◻p ⋀ ◻q :=
begin
  funext1,
  repeat { split ; intros }
  ; intros i ; try { simp, split },
  { apply (a i).left },
  { apply (a i).right },
  { apply a.left },
  { apply a.right },
end

lemma henceforth_forall (P : α → cpred)
: ◻(∀∀ x, P x) = ∀∀ x, ◻P x :=
begin
  funext1,
  simp [henceforth,p_forall],
  rw forall_swap,
end

@[simp]
lemma not_eventually (p : cpred)
: (-◇p) = (◻-p) :=
begin
  funext1,
  simp [henceforth,not_forall_iff_exists_not,eventually],
end

lemma eventually_exists (P : α → cpred)
: ◇(∃∃ x, P x) = ∃∃ x, ◇P x :=
begin
  funext1,
  unfold eventually p_exists,
  split
  ; intro H
  ; cases H with i H
  ; cases H with j H
  ; exact ⟨_,_,H⟩ ,
end

lemma one_point_elim {t} (Γ p : cpred) (v : tvar t)
  (h : ∀ x : t, Γ ⊢ (↑x ≃ v) ⟶ p)
: Γ ⊢ p :=
begin
  rw [← p_forall_to_fun] at h,
  constructor,
  intros i h',
  apply h.apply  i h' (v.apply $ i),
  simp,
end

end temporal

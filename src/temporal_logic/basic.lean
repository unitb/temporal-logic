
import util.predicate
import util.meta.tactic

@[user_attribute]
meta def strengthening_attr : user_attribute :=
{ name := `strengthening
, descr := "
Strenghtening lemmas to facilitate the stripping of small details in application.
Expected shape `∀ p : pred' α, ⊩ f p ⟶ g p`
" }

run_cmd mk_simp_attr `tl_simp [`simp]
run_cmd
do ns ← attribute.get_instances `simp,
   let ns : list name := ns.filter (λ n, name.is_prefix_of `predicate n),
   n ← tactic.mk_const (mk_simp_attr_decl_name `tl_simp),
   ns.mmap' (λ n, user_attribute.set simp_attr.tl_simp n () tt),
   return ()

namespace tactic.interactive
open lean interactive.types
open interactive lean.parser tactic
open list (hiding map) functor predicate
local postfix *:9001 := many

meta def TL_unfold (cs : parse ident*) (loc : parse location) : tactic unit :=
do unfold_coes loc, unfold (cs ++ [`var.apply,`pred'.mk]) loc

end tactic.interactive

namespace temporal

open predicate nat

universes u u₀ u₁ u₂ u₃

variables {α : Sort u₀} {β : Sort u₁} {γ : Sort u₂} {φ : Sort u₃}

@[reducible]
def tvar := var ℕ

@[reducible]
def cpred := tvar Prop

abbreviation act (β : Sort u) := β → β → Prop

def action (a : act α) (v : tvar α) : cpred :=
⟨ λ i, a (v.apply i) (v.apply $ i.succ) ⟩

def eventually (p : cpred) : cpred :=
⟨ λ i, ∃ j, p.apply (i+j) ⟩
def henceforth (p : cpred) : cpred :=
⟨ λ i, ∀ j, p.apply (i+j) ⟩
def next (p : tvar α) : tvar α :=
⟨ λ i, p.apply (i.succ) ⟩

@[lifted_fn, reducible]
def pair {α β} (x : tvar α) (y : tvar β) : tvar (α × β) :=
lifted₂ prod.mk x y

notation `⦃` x₀ `,` x₁ `⦄` := pair x₀ x₁
notation `⦃` x₀ `,` x₁ `,` x₂ `⦄` := pair x₀ (pair x₁ x₂)
notation `⦃` x₀ `,` x₁ `,` x₂ `,` x₃ `⦄` := pair x₀ (pair x₁ (pair x₂ x₃))
notation `⦃` x₀ `,` x₁ `,` x₂ `,` x₃ `,` x₄ `⦄` := pair x₀ (pair x₁ (pair x₂ (pair x₃ x₄)))
-- notation `⦃` x `,` l:(foldl `,` (h t, pair h t) x `⦄`)  := l

prefix `⊙`:90 := next
prefix `◇`:95 := eventually -- \di
prefix `◻`:95 := henceforth -- \sqw
notation `⟦ `:max v ` | `:50 R ` ⟧`:0 := action R v
notation `⟦ `:max v `,` v' ` | `:50 R ` ⟧`:0 := action R (pair v v')
notation `⟦ `:max v₀ `,` v₁ `,` v₂ ` | `:50 R ` ⟧`:0 := action R (pair v₀ (pair v₁ v₂))
notation `⟦ `:max v₀ `,` v₁ `,` v₂ `,` v₃ ` | `:50 R ` ⟧`:0 := action R (pair v₀ (pair v₁ (pair v₂ v₃)))

def tl_leads_to (p q : cpred) : cpred :=
◻(p ⟶ ◇q)

infix ` ~> `:55 := tl_leads_to


def to_fun_var (f : var γ α → var γ β) : var γ (α → β) :=
⟨ λ i x, (f ↑x).apply i ⟩

def to_fun_var' (f : tvar α → tvar α → tvar β) : tvar (α → α → β) :=
⟨ λ i x y, (f x y).apply i ⟩

class persistent (p : cpred) : Prop :=
  (is_persistent : ◻p = p)
export persistent (is_persistent)

lemma tl_imp_intro (h : cpred) [persistent h] {p q : cpred}
  (h' : h ⟹ (p ⟶ q))
: ctx_impl h p q :=
begin
  constructor, intro,
  exact (h' True).apply σ trivial,
end

lemma tl_imp_elim (h : cpred) [persistent h] {p q : cpred}
  (h' : ctx_impl h p q)
: h ⟹ (p ⟶ q) :=
begin
  intro, revert Γ,
  apply intro_p_imp h',
end

lemma tl_imp_intro' (h : cpred) [persistent h] {p q : cpred}
  (h' : p ⟹ q)
: ctx_impl h p q :=
h' _

@[tl_simp, simp]
lemma hence_true : ◻(True : cpred) = True :=
begin
  ext1,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

@[tl_simp, simp]
lemma next_true : ⊙True = True :=
by lifted_pred

@[tl_simp, simp]
lemma next_false : ⊙False = False :=
by lifted_pred [next]

instance true_persistent
: persistent (True : cpred) :=
by { constructor, simp with tl_simp, }

lemma tl_imp_elim' {p q : cpred}
  (h : ctx_impl True p q)
: p ⟹ q :=
begin
  simp [ctx_impl] at h,
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
by { lifted_pred [eventually], intro, existsi 1, assumption }

@[strengthening]
lemma henceforth_entails_next (p : cpred)
: ◻p ⟹ ⊙p :=
by { lifted_pred [eventually], intro h, apply h 1 }

@[strengthening]
lemma henceforth_str (p : cpred) :
  (◻p ⟹ p) :=
begin
  pointwise with τ h, apply h 0
end

local infix ` <$> ` := fun_app_to_var
local infix ` <*> ` := combine_var

lemma init_eq_action {p : α → Prop} (v : tvar α)
: ⟨p⟩ ! v = ⟦ v | λ s s', p s ⟧ :=
by { cases v, refl }

lemma coe_eq (v : tvar α) (x : α)
: ⟨λ y, y = x⟩ ! v = v ≃ x :=
by { cases v, refl }

lemma init_eq_action' {p : pred' α} (v : tvar α)
: (p ! v) = ⟦ v | λ s s', p.apply s ⟧ :=
by { cases v, cases p, refl }

lemma next_eq_action {p : α → Prop} (v : tvar α)
: ⊙(p <$> v) = ⟦ v | λ s s' : α, p s' ⟧ :=
by { cases v, refl }

lemma action_eq {A : act α} (v : tvar α)
: ⟦ v | A ⟧ = (A : tvar (act α)) v (⊙v) :=
by { cases v, refl }

lemma next_eq_action' {p : pred' α} (v : tvar α)
: ⊙(p ! v) = ⟦ v | λ s s' : α, p.apply s' ⟧ :=
by { cases v, cases p, refl }

lemma not_action {A : act α} (v : tvar α)
: -⟦ v | A ⟧ = ⟦ v | λ s s', ¬ A s s' ⟧ :=
rfl

lemma action_imp (p q : act α) (v : tvar α)
: (⟦ v | λ s s' : α, p s s' → q s s' ⟧ : cpred) = ⟦ v | p ⟧ ⟶ ⟦ v | q ⟧ :=
rfl

lemma action_and_action (p q : act α) (v : tvar α)
: ⟦ v | p ⟧ ⋀ ⟦ v | q ⟧ = ⟦ v | λ s s' : α, p s s' ∧ q s s' ⟧ :=
rfl

lemma action_or_action (p q : act α) (v : tvar α)
: ⟦ v | p ⟧ ⋁ ⟦ v | q ⟧ = ⟦ v | λ s s' : α, p s s' ∨ q s s' ⟧ :=
rfl

lemma action_false (v : tvar α)
: (⟦ v | λ _ _, false ⟧ : cpred) = False :=
by { funext x, refl }

variables {Γ : cpred}

lemma unlift_action (A : act α) (v : tvar α)
  (h : ∀ σ σ', A σ σ')
: Γ ⊢ ⟦ v | A ⟧ :=
begin
  constructor, simp_intros [action],
  apply h
end

@[tl_simp, simp]
lemma eventually_eventually (p : cpred) : ◇◇ p = ◇ p :=
begin
  ext k,
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

@[tl_simp, simp]
lemma henceforth_henceforth (p : cpred) : ◻◻ p = ◻ p :=
begin
  ext _,
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

lemma henceforth_next_intro (p : cpred)
: ◻p = ◻(p ⋀ ⊙p) :=
by { lifted_pred, split ; intros h i,
     { split, apply h i, specialize h (succ i),
       simp [add_succ] at h, simp [next,h], },
     { apply (h i).left }}

/- True / False -/

@[tl_simp, simp]
lemma hence_false : ◻(False : cpred) = False :=
begin
  ext _,
  split ; intro h,
  { cases h 0 },
  { cases h }
end

@[tl_simp, simp]
lemma event_false : ◇(False : cpred) = False :=
begin
  ext _,
  split ; intro h,
  { cases h with _ h, cases h },
  { cases h }
end

@[tl_simp, simp]
lemma eventually_true : ◇(True : cpred) = True :=
begin
  ext1,
  split ; intro h,
  { trivial },
  { apply exists.intro 0, trivial }
end

/- monotonicity -/

@[monotonic]
lemma eventually_tl_imp_eventually {h p q : cpred}
  [persistent h]
  (f : ctx_impl h p q)
: ctx_impl h (◇p) (◇q) :=
begin
  unfold ctx_impl at ⊢ f,
  rw ← is_persistent h at *,
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
  monotonicity (f _),
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
  [persistent h]
  (f : ctx_impl h p q)
: ctx_impl h (◻p) (◻q) :=
begin
  unfold ctx_impl at *,
  rw ← is_persistent h,
  pointwise f with i h',
  simp [henceforth], intro_mono i,
  apply f ,
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
  solve_by_elim,
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
  ext1,
  repeat { split ; intros }
  ; intros i ; try { simp, split },
  { apply (a i).left },
  { apply (a i).right },
  { apply a.left },
  { apply a.right },
end

lemma eventually_or (p q : cpred)
: ◇(p ⋁ q) = ◇p ⋁ ◇q :=
begin
  ext1,
  simp [eventually,exists_or],
end

lemma henceforth_forall (P : α → cpred)
: ◻(∀∀ x, P x) = ∀∀ x, ◻P x :=
begin
  ext1,
  simp [henceforth,p_forall],
  rw forall_swap,
end

@[tl_simp, simp]
lemma not_henceforth (p : cpred) : (- ◻p) = (◇-p) :=
begin
  ext1,
  simp [henceforth,not_forall_iff_exists_not,eventually],
end

@[tl_simp, simp]
lemma not_eventually (p : cpred)
: (-◇p) = (◻-p) :=
begin
  ext1,
  simp [henceforth,not_forall_iff_exists_not,eventually],
end

@[tl_simp, simp, predicate]
lemma models_to_fun_var (σ : γ) (x : var γ α → var γ β)
: σ ⊨ to_fun_var x = λ i, σ ⊨ x i :=
by { refl }

@[tl_simp, simp, predicate]
lemma models_to_fun_var' (σ : ℕ) (f : tvar (α → α → β))
: σ ⊨ to_fun_var' (λ x, var_seq $ var_seq f x) = σ ⊨ f :=
by { casesm* tvar _, dunfold to_fun_var', simp_coes [var_seq], }

@[tl_simp, simp, predicate, lifted_fn]
lemma to_fun_var_fn_coe_proj (f : var γ α) (g : var β φ → var β γ) (w : var β φ)
: to_fun_var (λ w, f ! g w) w = f ! to_fun_var g w :=
by { funext, lifted_pred, simp!, }

@[tl_simp, simp, predicate, lifted_fn]
lemma to_fun_var_fn_coe (g : var β (φ → γ)) (w : var β φ)
: to_fun_var (λ w, g w) w = g w :=
by { funext, lifted_pred, simp!, }

@[tl_simp, simp, predicate, lifted_fn]
lemma to_fun_var_fn_coe' (f : tvar (α → α → β)) (w w' : tvar α)
: ⇑(to_fun_var' $ λ w w', f w w') w w' = f w w' :=
by { lifted_pred, simp! [to_fun_var'], }

@[lifted_fn]
lemma to_fun_var_lift₁ (f : φ → β) (g : var γ α → var γ φ) (w : var γ α)
: (to_fun_var (λ (w : var γ α), lifted₁ f (g w))) w = lifted₁ f (to_fun_var g w) :=
by { lifted_pred, simp! }

@[lifted_fn]
lemma to_fun_var_lift₂ {σ} (f : φ → σ → β)
  (g₀ : var γ α → var γ φ)
  (g₁ : var γ α → var γ σ) (w : var γ α)
: (to_fun_var (λ (w : var γ α), lifted₂ f (g₀ w) (g₁ w))) w =
  lifted₂ f (to_fun_var g₀ w) (to_fun_var g₁ w) :=
by { lifted_pred, simp }

@[lifted_fn]
lemma to_fun_var_coe (w : var γ α) (v : var γ β)
: to_fun_var (λ (w : var γ α), v) w = v :=
by { lifted_pred, simp }

@[lifted_fn]
lemma to_fun_var_id (w : var γ α)
: to_fun_var (λ w : var γ α, w) w = w :=
by { lifted_pred, simp }

@[lifted_fn]
lemma to_fun_var'_fn_coe (f : var φ β) (g : tvar α → tvar α → tvar φ) (w w' : tvar α)
: (to_fun_var' (λ (w w' : tvar α), f ! g w w')) w w' = f ! to_fun_var' g w w'  :=
by { lifted_pred, simp! [to_fun_var'], }

@[lifted_fn]
lemma to_fun_var'_coe (w w' : tvar α) (v : tvar β)
: (to_fun_var' (λ (w w' : tvar α), v)) w w' = v :=
by { lifted_pred, simp! [to_fun_var'], }

@[lifted_fn]
lemma to_fun_var'_id (w w' : tvar α)
: to_fun_var' (λ w w' : tvar α, w) w w' = w :=
by { lifted_pred, simp! [to_fun_var',next], }

@[lifted_fn]
lemma to_fun_var'_id' (w w' : tvar α)
: to_fun_var' (λ w w' : tvar α, w') w w' = w' :=
by { lifted_pred, simp! [to_fun_var'], }

@[lifted_fn]
lemma to_fun_var'_lift₂ {σ} (f : φ → σ → β)
  (g₀ : tvar α → tvar α → tvar φ)
  (g₁ : tvar α → tvar α → tvar σ) (w w' : tvar α)
: to_fun_var' (λ (w w' : tvar α), lifted₂ f (g₀ w w') (g₁ w w')) w w' =
  lifted₂ f (to_fun_var' g₀ w w') (to_fun_var' g₁ w w') :=
by { lifted_pred, simp! [to_fun_var'], }

@[tl_simp, simp, predicate]
lemma models_coe (σ : α) (x : β)
: σ ⊨ ↑x = x :=
by { refl }

@[tl_simp, simp, predicate]
lemma models_action (A : act α) (v : tvar α) (i : ℕ)
: i ⊨ ⟦ v | A ⟧ ↔ A (i ⊨ v) (succ i ⊨ v) :=
by { refl }

@[tl_simp, simp, predicate]
lemma models_next (p : tvar α) (t : ℕ)
: t ⊨ ⊙p = succ t ⊨ p :=
by refl

lemma induct' (p : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ ◻ (p ⟶ ◻p) :=
begin
  constructor,
  intros τ hΓ k hp i,
  induction i with i,
  assumption,
  have := h.apply τ hΓ (k+i) (cast (by simp) i_ih),
  simp [next] at this,
  simp [add_succ,this],
end

lemma induct (p : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ ⊙p))
: Γ ⊢ p ⟶ ◻p :=
henceforth_str (p ⟶ ◻p) Γ (induct' _ h)

lemma induct_evt' (p q : cpred) {Γ}
  (h : Γ ⊢ ◻ (p ⟶ -q ⟶ ⊙p ⋁ ⊙q))
: Γ ⊢ ◻ (p ⟶ ◇q ⋁ ◻p) :=
begin
  lifted_pred using h,
  simp only [henceforth] with tl_simp at *,
  intros,
  simp [or_iff_not_imp,eventually],
  intros hnq k,
  induction k with k,
  { simp [a] },
  { simp [add_succ],
    specialize h _ k_ih (hnq _),
    rw [or_comm,or_iff_not_imp] at h,
    apply h, rw [← add_succ,← add_succ],
    apply hnq }
end

lemma eventually_exists (P : α → cpred)
: ◇(∃∃ x, P x) = ∃∃ x, ◇P x :=
begin
  ext1,
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

section witness
variables x₀ : tvar α
variables f : tvar (α → α)
variables (i : ℕ)

open classical nat

private def w : ℕ → α
 | 0 := i ⊨ x₀
 | (succ j) := (i + j ⊨ f) (w j)

lemma fwd_witness
: ⊩ ∃∃ w, w ≃ x₀ ⋀ ◻( ⊙w ≃ f w ) :=
begin
  lifted_pred,
  existsi (⟨ λ i, w x₀ f x (i - x) ⟩ : tvar α),
  simp [nat.sub_self,w],
  intro i,
  have h : x + i ≥ x := nat.le_add_right _ _,
  simp [next,nat.add_sub_cancel_left,succ_sub h,w],
end

end witness

def nelist (α : Type*) := { xs : list α // xs.empty = ff }

def nelist.head {α : Type*} : nelist α → α
 | ⟨ x::xs, _ ⟩ := x

def nelist.tail {α : Type*} : nelist α → option (nelist α)
 | ⟨ x::x'::xs, _ ⟩ := some ⟨ x'::xs, rfl ⟩
 | ⟨ _ :: [], _ ⟩ := none

def nelist.uncons {α : Type*} : nelist α → α ⊕ (α × nelist α)
 | ⟨ x::x'::xs, _ ⟩ := sum.inr (x,⟨x'::xs,rfl⟩)
 | ⟨ x :: [], _ ⟩ := sum.inl x

def nelist.single {α : Type*} : α → nelist α
 | x := ⟨ x :: [] ,rfl ⟩

def nelist.cons {α : Type*} : α → nelist α → nelist α
 | x ⟨ xs, _⟩ := ⟨ x::xs,rfl ⟩

noncomputable def epsilon [nonempty α] (p : tvar (α → Prop)) : tvar α :=
⟨ λ i, classical.epsilon $ i ⊨ p ⟩

end temporal

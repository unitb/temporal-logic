
import .fairness

universe variables u u₀ u₁ u₂

namespace temporal

open predicate fairness

variables {α : Type u}

structure mch' (evt : Type u₀) (α : Type u) :=
  (init : pred' α)
  (cs fs : evt → pred' α)
  (A : option evt → act α)

namespace mch'

variable {evt : Type u₀}
variables (m : mch' evt α)
local notation `cs` := m.cs
local notation `fs` := m.fs
local notation `p` := m.init
local notation `A` := m.A

def effect : option evt → α → α → Prop
 | none v v' := A none v v'
 | (some e) v v' := v ⊨ cs e ∧ v ⊨ fs e ⋀ A (some e) v v'

local notation `Next` := m.effect

protected def event (e : evt) : event α :=
⟨ cs e, fs e, A e ⟩

def event' (aevt : Type u₀) (e : evt) (e' : aevt) : event (α × evt × aevt) :=
⟨ cs e ! pair.fst
, fs e ! pair.fst
, λ ⟨s,ce,_⟩ ⟨s',_,ae'⟩, ae' = e' ∧ ce = e ∧ A e s s' ⟩

-- abbreviation ce' (i : cevt) (j : aevt) : event (γ×β×(cevt×aevt)) :=
-- { p := cs₁ i!⟨prod.map_right fst⟩
-- , q := fs₁ i!⟨prod.map_right fst⟩
-- , A := λ ⟨o,v,ce,_⟩ ⟨o',v',_,ae'⟩, ae' = j ∧ ce = i ∧ C i (o,v) (o',v') }

@[simp, tl_simp]
def spec_saf_spec (v : tvar α) (sch : tvar evt) : cpred :=
p ! v ⋀
◻(∃∃ e, ⟦ v | m.effect e ⟧ )

@[simp, tl_simp]
def spec (v : tvar α) : cpred :=
p ! v ⋀
◻(∃∃ e, ⟦ v | m.effect e ⟧ ) ⋀
∀∀ e, sched (cs e ! v) (fs e ! v) ⟦ v | A e ⟧

@[simp, tl_simp]
def spec_sch (v : tvar α) (sch : tvar (option evt)) : cpred :=
p ! v ⋀
◻(∃∃ e : option evt, sch ≃ ↑e ⋀ ⟦ v | m.effect e ⟧) ⋀
∀∀ e : evt, sched (cs e ! v) (fs e ! v) (sch ≃ some e ⋀ ⟦ v | A ↑e ⟧)

structure invariant (J : pred' α) : Prop :=
  (init : p ⟹ J)
  (step : ∀ e s s', Next e s s' → s ⊨ J → s' ⊨ J)

end mch'

structure mch (α : Type u) :=
  {evt : Type u₀}
  (init : pred' α)
  (cs fs : evt → pred' α)
  (A : option evt → act α)

namespace mch
variables (m : mch α)
local notation `evt` := m.evt
local notation `cs` := m.cs
local notation `fs` := m.fs
local notation `p` := m.init
local notation `A` := m.A

def effect : option evt → α → α → Prop
 | none v v' := A none v v'
 | (some e) v v' := v ⊨ cs e ∧ v ⊨ fs e ⋀ A (some e) v v'

local notation `Next` := m.effect

lemma act_of_effect {v v' : α} {e : option evt}
  (h : Next e v v')
: A e v v' :=
by { cases e ; revert h ; simp [effect], }

protected def event (e : evt) : event α :=
⟨ cs e, fs e, A e ⟩

def event' (aevt : Type u₀) (e : evt) (e' : aevt) : event (α × option evt × aevt) :=
⟨ cs e ! pair.fst
, fs e ! pair.fst
, λ ⟨s,ce,_⟩ ⟨s',_,ae'⟩, ae' = e' ∧ ce = e ∧ A e s s' ⟩

-- abbreviation ce' (i : cevt) (j : aevt) : event (γ×β×(cevt×aevt)) :=
-- { p := cs₁ i!⟨prod.map_right fst⟩
-- , q := fs₁ i!⟨prod.map_right fst⟩
-- , A := λ ⟨o,v,ce,_⟩ ⟨o',v',_,ae'⟩, ae' = j ∧ ce = i ∧ C i (o,v) (o',v') }

@[simp, tl_simp]
def spec_saf_sch (v : tvar α) (sch : tvar (option evt)) : cpred :=
p ! v ⋀
◻(∃∃ e : option evt, sch ≃ ↑e ⋀ ⟦ v | m.effect e ⟧)

@[simp, tl_simp]
def spec (v : tvar α) : cpred :=
p ! v ⋀
◻(∃∃ e, ⟦ v | m.effect e ⟧ ) ⋀
∀∀ e, sched (cs e ! v) (fs e ! v) ⟦ v | A e ⟧

@[simp, tl_simp]
def spec_sch (v : tvar α) (sch : tvar (option evt)) : cpred :=
p ! v ⋀
◻(∃∃ e : option evt, sch ≃ ↑e ⋀ ⟦ v | m.effect e ⟧) ⋀
∀∀ e : evt, sched (cs e ! v) (fs e ! v) (sch ≃ some e ⋀ ⟦ v | A e ⟧)

structure invariant (J : pred' α) : Prop :=
  (init : p ⟹ J)
  (step : ∀ e s s', Next e s s' → s ⊨ J → s' ⊨ J)

variable {Γ : cpred}

lemma spec_sch_of_spec_saf_sch (v : tvar α) (sch : tvar (option evt))
  (h : Γ ⊢ m.spec_saf_sch v sch)
  (h' : Γ ⊢ ∀∀ (e : m.evt), sched (m.cs e ! v) (m.fs e ! v) (sch ≃ ↑(some e) ⋀ ⟦ v | m.A (some e) ⟧))
: Γ ⊢ m.spec_sch v sch :=
begin [temporal]
  simp at *,
  split ; assumption,
end

lemma spec_of_spec_sch (v : tvar α) (sch : tvar (option evt))
  (h : Γ ⊢ m.spec_sch v sch)
: Γ ⊢ m.spec v :=
begin [temporal]
  simp at *,
  revert h,
  apply ctx_p_and_p_imp_p_and',
  apply ctx_p_and_p_imp_p_and_right',
  { monotonicity, apply p_exists_p_imp_p_exists,
    simp, },
  { apply p_forall_p_imp_p_forall,
    intro, apply sched_imp_sched, simp },
end

lemma spec_of_spec_saf_sch (v : tvar α) (sch : tvar (option evt))
  (h : Γ ⊢ m.spec_saf_sch v sch)
  (h' : Γ ⊢ ∀∀ (e : m.evt), sched (m.cs e ! v) (m.fs e ! v) ⟦ v | m.A (some e) ⟧)
: Γ ⊢ m.spec v :=
begin [temporal]
  simp at *,
  split,
  { revert h,
    apply ctx_p_and_p_imp_p_and_right',
    monotonicity,
    apply p_exists_p_imp_p_exists,
    simp  },
  assumption,
end

end mch

end temporal

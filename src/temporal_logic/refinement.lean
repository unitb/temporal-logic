
import temporal_logic.fairness
import temporal_logic.pair
import temporal_logic.lemmas

universe variables u u₀ u₁ u₂
open predicate nat

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

local attribute [-simp] or.comm or.left_comm or.assoc and.comm and.left_comm and.assoc

namespace temporal

namespace simulation
section

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters (p : pred' (α'×γ')) (q : pred' (β'×γ'))
parameters (A : act (α'×γ')) (C : act (β'×γ'))
parameters (J : pred' (α'×β'×γ'))

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> C ⟧

parameters [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ w v o v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

section witness
variables (i : ℕ)

open classical

private noncomputable def w : ℕ → α'
 | 0 := (ε w', (w',i ⊨ o) ⊨ p ∧ (w', i ⊨ v, i ⊨ o) ⊨ J)
 | (succ j) := (ε w', A (w j,i+j ⊨ o) (w',i + succ j ⊨ o) ∧
                      (w', i + succ j ⊨ v, i + succ j ⊨ o) ⊨ J)

noncomputable def witness : tvar (tvar α') := ⟨ λ i, ⟨ λ j, @w i (j-i) ⟩ ⟩

end witness

parameters Γ : cpred
parameters H : Γ ⊢ SPEC₁ v o

include SIM₀

lemma init_in_w
: Γ ⊢ ∀∀ w, ↑w ≃ witness ⟶ q;;⦃o,v⦄ ⟶ p;;⦃o,w⦄ :=
begin
  lifted_pred [witness,nat.sub_self,w] ,
  intro Hq,
  apply_epsilon_spec, simp,
  intros, assumption,
end

include H SIM
lemma J_inv_in_w
: Γ ⊢ ∀∀ w, ↑w ≃ witness ⟶ ◻(J ;; ⦃o,v,w⦄) :=
begin
  lifted_pred keep,
  intro i, simp [witness],
  simp [nat.add_sub_cancel_left,w],
  induction i with i,
  { simp [w],
    apply_epsilon_spec (SIM₀ _ _ _),
    simp,
    have := H.left.apply _ a, simp at this,
    exact this },
  { simp [w],
    specialize @SIM _ (x + i ⊨ v) (x + i ⊨ o) (x + succ i ⊨ v) (x + succ i ⊨ o) ih_1,
    apply_epsilon_spec (SIM _), simp,
    replace H := (H.apply _ a).right i,
    simp at H, simp [add_succ,H], },
end

lemma C_imp_A_in_w
: Γ ⊢ ∀∀ w, ↑w ≃ witness ⟶ ◻(⟦ ⦃o,v⦄ <> C ⟧ ⟶ ⟦ ⦃o,w⦄ <> A ⟧) :=
begin [temporal]
  intros w Hw,
  have := J_inv_in_w p q A C J SIM₀ @SIM v o Γ H,
  replace this := this w Hw,
  revert this,
  apply henceforth_imp_henceforth ,
  revert Hw w,
  explicit {
    simp, intros i,
    have : σ ≤ σ + i, { simp [nat.zero_le], },
    simp [witness,nat.add_sub_cancel_left,nat.succ_sub this,w],
    intros hJ hC,
    apply_epsilon_spec, simp,
    intros, assumption, },
end

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  existsi witness p A J v o with Hw,
  simp [SPEC₀], split,
  { have := init_in_w p q A J SIM₀ v o Γ,
    apply this witness₀ _ _, rw Hw,
    apply H.left },
  { have := C_imp_A_in_w p q A C J SIM₀ @SIM v o Γ H,
    replace this := this witness₀ Hw,
    have := H.right, revert this,
    monotonicity only, apply this  }
end

omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation p q A C J SIM₀ @SIM _ _ _ h,
end

end
end simulation

export simulation (simulation simulation')

section witness_construction

parameters {α' : Sort u}
parameters {p J : pred' α'}
parameters {A : act α'}

parameters H₀ : p ⟹ J
parameters FIS₀ : ∃ σ, σ ⊨ p
parameters FIS : ∀ σ, σ ⊨ J → ∃ σ', A σ σ'
parameters INV : ∀ σ σ', σ ⊨ J → A σ σ' → σ' ⊨ J

open classical simulation

include H₀ INV

def A' : plift α' × unit → plift α' × unit → Prop :=
A on (plift.down ∘ prod.fst)

parameters [_inst : inhabited α']

include FIS₀ FIS _inst
lemma witness_construction
: ⊩ ∃∃ v, p ;; v ⋀ ◻⟦ v <> A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (plift α' × unit) α' := ↑(@plift.down α') ;; pair.fst,
  let p' : pred' (plift α' × unit) := p ;; prj,
  have _inst : inhabited (plift α') := ⟨ plift.up (default α') ⟩,
  let J' : pred' (plift α' × unit × unit) := J ;; ↑(@plift.down α') ;; pair.fst,
  have := @simulation _ _ _ p' (@True $ unit × unit) (A' H₀ INV) C J' _ _ _ o o Γ _,
  begin [temporal]
    revert this,
    let f : tvar (plift α') → tvar α' := λ v, ↑(λ x : plift α', x.down) ;; v,
    let SPEC := @SPEC₀ _ _ p' (A' H₀ INV),
    let SPEC' := λ (v : tvar α'), p ;; v ⋀ ◻⟦ v <> A ⟧,
    apply p_exists_imp_p_exists' (λ w, SPEC w o) SPEC' f,
    intro, simp only [SPEC,f,SPEC',SPEC₀,p',prj,proj_assoc,pair.fst_mk,A'],
    monotonicity, rw [action_on,coe_over_comp,proj_assoc,pair.fst_mk'],
    refl,
  end,
  { intros,
    revert FIS₀,
    apply exists_imp_exists' plift.up,
    introv h, split, simp [p',h],
    simp [J'], apply ew_str H₀ _ h, },
  { introv hJ hC, simp [J'] at hJ,
    have := FIS (w.down) hJ, revert this,
    apply exists_imp_exists' plift.up,
    introv hA, simp [A'], split,
    { apply hA },
    { apply INV _ _ hJ hA  } },
  { simp [SPEC₁,C], }
end

end witness_construction

namespace refinement
section
open fairness
parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {evt : Type u₂}
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters (A : evt → act (α'×γ')) (C : evt → act (β'×γ'))
parameters {cs₀ fs₀ : evt → pred' (α'×γ')} {cs₁ fs₁ : evt → pred' (β'×γ')}
parameters (J : pred' (α'×β'×γ'))

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ ⦃o,v⦄ <> A i ⟧) ⋀
∀∀ i, sched (cs₀ i ;; ⦃o,v⦄) (fs₀ i ;; ⦃o,v⦄) ⟦ ⦃o,v⦄ <> A i ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ ⦃o,v⦄ <> C i ⟧) ⋀
∀∀ i, sched (cs₁ i ;; ⦃o,v⦄) (fs₁ i ;; ⦃o,v⦄) ⟦ ⦃o,v⦄ <> C i ⟧

def SPEC₂ (v : tvar β') (o : tvar γ') (s : tvar evt) : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻(∃∃ i, s ≃ ↑i ⋀ ⟦ ⦃o,v⦄ <> C i ⟧) ⋀
∀∀ i, sched (cs₁ i ;; ⦃o,v⦄) (fs₁ i ;; ⦃o,v⦄) (s ≃ ↑i ⋀ ⟦ ⦃o,v⦄ <> C i ⟧)

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ w v o v' o' e,
  (w,v,o) ⊨ J →
  C e (v,o) (v',o') →
  ∃ w', A e (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ') (sch : tvar evt)

parameters (Γ : cpred)
parameters H : Γ ⊢ SPEC₂ v o sch

def cv := ⦃o,v⦄
variable Hdelay : Γ ⊢ ∀∀ e w, cs₀ e;;⦃o,w⦄ ⋀ fs₀ e;;⦃o,w⦄ ~> cs₁ e;;cv
variable Hresched : Γ ⊢ ∀∀ e w, cs₀ e;;⦃o,w⦄ ⋀ fs₀ e;;⦃o,w⦄ ~> fs₁ e;;cv
variable Hstable : Γ ⊢ ∀∀ e w, ◻◇(cs₁ e;;cv) ⟶ ◇◻(cs₁ e;;cv) ⋁ ◻◇-(cs₀ e;;⦃o,w⦄)

open simulation (witness init_in_w C_imp_A_in_w) prod temporal.prod

def Next_a :=
λ σ σ', ∃ e, A e σ σ'

def Next_c :=
λ σ σ' : (evt × β') × γ', ∃ e, σ.1.1 = e ∧ (C e on map_left snd) σ σ'

section J
parameter evt
def J' : pred' (α' × (evt × β') × γ') :=
J ;; ((prod.map_right $ prod.map_left prod.snd) : (α' × (evt × β') × γ') → (α' × β' × γ'))

parameter q
def q' : pred' ((evt × β') × γ') :=
q ;; (prod.map_left prod.snd : (evt × β') × γ' → β' × γ')

end J

section Simulation_POs
include SIM₀
lemma SIM₀' (v : evt × β') (o : γ')
  (h : (v, o) ⊨ q')
: (∃ (w : α'), (w, o) ⊨ p ∧ (w, v, o) ⊨ J') :=
begin
  simp [q',prod.map_left] at h,
  specialize SIM₀ v.2 o h,
  revert SIM₀, intros_mono,
  simp [J'],
end
omit SIM₀
include SIM
lemma SIM' (w : α') (v : evt × β') (o : γ') (v' : evt × β') (o' : γ')
  (h₀ : (w, v, o) ⊨ J')
  (h₁ : Next_c (v, o) (v', o'))
: (∃ (w' : α'), Next_a (w, o) (w', o') ∧ (w', v', o') ⊨ J') :=
sorry
omit SIM
lemma H'
: Γ ⊢ simulation.SPEC₁ q' Next_c ⦃v,sch⦄ o :=
sorry

end Simulation_POs

include H SIM₀ SIM Hstable Hdelay Hresched

lemma one_to_one
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  -- type_check witness p (Next_a A) J' ⦃sch,v⦄ o ,
  existsi witness p (Next_a A) (J' evt J) ⦃v,sch⦄ o with Hw,
  -- existsi witness p (Next_a A) J v o with Hw,
  have this := H, revert this,
  dsimp [SPEC₀,SPEC₁],
  -- type_check ctx_imp_entails_p_imp _ _,
  replace SIM := SIM' A C J SIM,
  replace SIM₀ := SIM₀' _ SIM₀,
  replace H := H' evt q C v o sch Γ,
  apply ctx_p_and_p_imp_p_and' _ _,
  apply ctx_p_and_p_imp_p_and' _ _,
  { clear_except SIM₀ Hw H,
    have := init_in_w p (q' evt q) (Next_a A) (J' evt J) SIM₀ ⦃v,sch⦄ o Γ,
    intro Hq,
    apply this witness₀ Hw _,
    simp [q',proj_assoc], apply Hq, },
  { clear_except SIM SIM₀ Hw H,
    have := C_imp_A_in_w p (q' evt q) (Next_a A) (Next_c C) (J' evt J) SIM₀ SIM ⦃v,sch⦄ o Γ H,
    { replace this := this witness₀ Hw,
      monotonicity only,
      simp [exists_action],
      intros e h₀ h₁, apply this _,
      simp [Next_c],
      suffices : ⟦ ⦃o,⦃v,sch⦄⦄ <> λ (σ σ' : (evt × β') × γ'), ((λ s s', s = e) on (prod.fst ∘ prod.fst)) σ σ' ∧ (C e on map_left snd) σ σ' ⟧,
      revert this, action
      { simp [function.on_fun],
      intros, subst e, assumption, },
      rw ← action_and_action, simp,
      rw [action_on,action_on,coe_over_comp,proj_assoc,← init_eq_action,coe_eq],
      simp, split ; assumption } },
  { intros h i,
    apply replacement Γ _ _ _ _ (h i),
    apply Hdelay i _,
    apply Hstable i _,
    admit,
    apply Hresched i _, },
end

omit H
lemma data_refinement'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
sorry

end
end refinement

end temporal

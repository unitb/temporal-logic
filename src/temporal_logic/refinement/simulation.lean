
import temporal_logic.fairness
import temporal_logic.pair
import temporal_logic.lemmas

universe variables u u₀ u₁ u₂
open predicate nat

namespace temporal

namespace simulation
section

parameters {α : Type u} {β : Type u₀} {γ : Type u₁ }
parameters (p : pred' (γ×α)) (q : pred' (γ×β))
parameters (A : act (γ×α)) (C : act (γ×β))
parameters (J : pred' (γ×α×β))

variables (x : tvar α) (y : tvar β) (z : tvar γ)

def SPEC₀ (v : tvar α) (o : tvar γ) : cpred :=
p ! ⦃ o,v ⦄ ⋀
◻⟦ o,v | A ⟧

def SPEC₁ (v : tvar β) (o : tvar γ) : cpred :=
q ! ⦃ o,v ⦄ ⋀
◻⟦ o,v | C ⟧

parameters [inhabited α]
parameter SIM₀ : ∀ v o, (o,v) ⊨ q → ∃ w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J
parameter SIM
: ∀ w v o v' o',
  (o,w,v) ⊨ J →
  C (o,v) (o',v') →
  ∃ w', A (o,w) (o',w') ∧
        (o',w',v') ⊨ J

parameters (v : tvar β) (o : tvar γ)

parameters Γ : cpred
parameters H : Γ ⊢ SPEC₁ v o

noncomputable def Wx₀_f : tvar (β → γ → α) :=
λ v o, ε w, (o,w) ⊨ p ∧ (o,w,v) ⊨ J

noncomputable def Wx₀ : tvar α :=
Wx₀_f v o

noncomputable def Wf_f : tvar (β → γ → γ → α → α) :=
λ v' o o' w, ε w', A (o,w) (o',w') ∧
                   (o',w',v') ⊨ J

noncomputable def Wf : tvar (α → α) :=
Wf_f (⊙v) o (⊙o)

noncomputable def Wtn (w : tvar α) :=
w ≃ Wx₀ ⋀ ◻(⊙w ≃ Wf w)

include SIM₀

lemma init_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ q!⦃o,v⦄ ⟶ p!⦃o,w⦄ :=
begin
  lifted_pred [nat.sub_self,Wtn] ,
  introv Hq, intros, simp [Hq,Wx₀,Wx₀_f],
  unfold_coes, simp [Wx₀,Wx₀_f],
  apply_epsilon_spec,
end
set_option trace.app_builder true
include H SIM
lemma J_inv_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(J ! ⦃o,w,v⦄) :=
begin [temporal]
  introv Hw,
  apply induct _ _ _ _,
  { replace Hw := Hw.right,
    simp, rw Hw,
    replace H := H.right,
    henceforth at H ⊢ , revert H,
    explicit
    { repeat { unfold_coes <|> simp [Wf,Wf_f] },
      intros, apply_epsilon_spec,  } },
  { replace Hw := Hw.left,
    rw [Hw,Wx₀,Wx₀_f],
    replace H := H.left,
    explicit {
    { unfold_coes, simp at ⊢ H,
      apply_epsilon_spec, } } },
end

lemma C_imp_A_in_w
: Γ ⊢ ∀∀ w, Wtn w ⟶ ◻(⟦ o,v | C ⟧ ⟶ ⟦ o,w | A ⟧) :=
begin [temporal]
  intros w Hw,
  have := J_inv_in_w p q A C J SIM₀ @SIM v o Γ H,
  replace this := this w Hw,
  simp [action_eq],
  rw [Hw.right],
  clear H Hw,
  henceforth at ⊢ this,
  revert this,
  explicit {
    repeat { simp [Wf,Wf_f] <|> unfold_coes },
    intros,
    apply_epsilon_spec, },
end

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  select_witness w : temporal.simulation.Wtn w with Hw,
  have := H, revert this,
  simp only [SPEC₀,SPEC₁],
  apply ctx_p_and_p_imp_p_and',
  { apply temporal.simulation.init_in_w _ Hw },
  { type_check_result "foo",
    replace Hw := temporal.simulation.C_imp_A_in_w _ Hw,
    monotonicity only,
    apply Hw, },
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

namespace witness_construction
section witness_construction

parameters {α : Sort u}
parameters {p J : pred' α}
parameters {A : act α}

parameters H₀ : p ⟹ J
parameters FIS₀ : ∃ σ, σ ⊨ p
parameters FIS : ∀ σ, σ ⊨ J → ∃ σ', A σ σ'
parameters INV : ∀ σ σ', σ ⊨ J → A σ σ' → σ' ⊨ J

open classical simulation

include H₀ INV

def A' : act $ unit × plift α :=
A on (plift.down ∘ prod.snd)

parameters [_inst : inhabited α]

include FIS₀ FIS _inst
lemma witness_construction
: ⊩ ∃∃ v, p ! v ⋀ ◻⟦ v | A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (unit × plift α) α := ⟨plift.down⟩ ! pair.snd,
  let p' : pred' (unit × plift α) := p ! prj,
  have _inst : inhabited (plift α) := ⟨ plift.up (default α) ⟩,
  let J' : pred' (unit × plift α × unit) := J ! ⟨plift.down⟩ ! pair.fst ! pair.snd,
  have := @simulation _ _ _ _ (@True $ unit × unit) (A' H₀ INV) C J' _ _ _ o o Γ _,
  begin [temporal]
    revert this,
    let f : tvar (plift α) → tvar α := λ v, ⟨plift.down⟩ ! v,
    let SPEC := @SPEC₀ _ _ p' (A' H₀ INV),
    let SPEC' := λ (v : tvar α), p ! v ⋀ ◻⟦ v | A ⟧,
    apply p_exists_imp_p_exists' (λ w, SPEC w o) SPEC' f,
    intro, simp only [SPEC,f,SPEC',SPEC₀,p',prj,proj_assoc,pair.snd_mk,A'],
    monotonicity, rw [action_on,coe_over_comp,proj_assoc,pair.snd_mk'],
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
end witness_construction

end temporal

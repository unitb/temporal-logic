
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

-- parameters [inhabited α]
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

def Wx₀ : tvar (α → Prop) :=
[| o, λ w, (o,w) ⊨ p |]

def Wf : tvar (α → α → Prop) :=
⟪ ℕ, λ o o' w w', A (o,w) (o',w') ⟫ o (⊙o)

def Wtn (w : tvar α) :=
Wx₀ w ⋀ ◻(Wf w ⊙w)

include SIM₀

variables w : tvar α
-- variables Hw : Γ ⊢ Wtn w
-- include Hw

include H SIM
-- omit Hw

#check to_fun_var
#check to_fun_var'

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin [temporal]
  cases H with H₀ Hnext,
  -- ⊢ ⇑(⇑(to_fun_var' (λ (w w_1 : tvar α), ⇑(⇑Wf w) w_1)) w) w' = ⇑(⇑Wf w) w'
  select_witness w : temporal.simulation.Wtn w
    with Hw hJ
    using (J!⦃o,w,v⦄), { },
  explicit' [SPEC₀,Wx₀] with H₀
    { solve_by_elim, } ,
  -- intros,
  explicit' [Wf] with Hnext
  { intros, apply SIM ; assumption, },
  existsi w, revert Hw,
  simp only [SPEC₀,SPEC₁,Wtn],
  apply ctx_p_and_p_imp_p_and',
  explicit' [Wx₀] {  },
  mono!,
  explicit' [Wf] {  },
end

omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation p q A C J SIM₀ @SIM _ _ _ h ,
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

open classical simulation function

include H₀ INV

def A' : act $ unit × plift α :=
A on (plift.down ∘ prod.snd)

-- parameters [_inst : inhabited α]

include FIS₀ FIS
lemma witness_construction
: ⊩ ∃∃ v, p ! v ⋀ ◻⟦ v | A ⟧ :=
begin
  intro,
  let o : tvar unit := ↑(),
  let C : unit × unit → unit × unit → Prop := λ _ _, true,
  let prj : var (unit × plift α) α := ⟨plift.down⟩ ! pair.snd,
  let p' : pred' (unit × plift α) := p ! prj,
  -- cases FIS₀ with w Hw,
  -- have _inst : inhabited (plift α) := ⟨ plift.up w ⟩,
  let J' : pred' (unit × plift α × unit) := J ! ⟨plift.down⟩ ! pair.fst ! pair.snd,
  have := @simulation _ _ _ p' (@True $ unit × unit) (A' H₀ INV) C J' _ _ o o Γ _,
  -- ; try { auto },
  -- have := @simulation _ _ _ _ (@True $ unit × unit) (A' H₀ INV) C J' True _inst _ _ o o Γ _,
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
    apply exists_imp_exists' plift.up _ FIS₀,
    introv Hw, split, simp [p',Hw],
    simp [J'], apply ew_str H₀ _ Hw, },
  { introv hJ hC, simp [J'] at hJ,
    -- existsi w,
    have := FIS _ hJ, revert this,
    apply exists_imp_exists' plift.up,
    simp [A',function.comp,on_fun], introv hA, split,
    { apply hA },
    { apply INV _ _ hJ hA  } },
  { simp only [SPEC₁,C] with tl_simp, }
end

end witness_construction
end witness_construction

end temporal

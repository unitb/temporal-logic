
import temporal_logic.fairness
import temporal_logic.lemmas

universe variables u u₀ u₁ u₂
open predicate nat

variables {α : Sort u₀} {β : Type u₁} {γ : Sort u₂}

namespace temporal

section pair

variables {α' : Type u} {β' : Type u₀} {γ' : Type u₁}
variables (x : tvar α') (y : tvar β') (z : tvar γ')

def pair : tvar (α' × β') :=
lifted₂ prod.mk x y

notation `⦃` x `,` l:(foldl `,` (h t, pair h t) x `⦄`)  := l

@[simp]
lemma pair_model (i : ℕ) :
i ⊨ ⦃x,y⦄ = (i ⊨ y,i ⊨ x) :=
by { cases x, cases y, refl }

@[reducible]
def pair.fst : var (α' × β') α' :=
↑(@prod.fst α' β')

@[simp]
def pair.fst_mk (x : tvar α') (y : tvar β')
: pair.fst ;; ⦃y,x⦄ = x :=
by lifted_pred

-- @[simp]
def pair.fst_mk' (x : tvar α') (y : tvar β')
: ↑(@prod.fst α' β') ;; ⦃y,x⦄ = x :=
pair.fst_mk _ _

end pair

namespace simulation
section

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters {A : act (α'×γ')} {C : act (β'×γ')}
parameters {J : pred' (α'×β'×γ')}

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> C ⟧

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ {w v o} v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

parameters {Γ : cpred}
parameters H : Γ ⊢ SPEC₁ v o

section witness
variables (i : ℕ) (Hi : i ⊨ Γ)
include H Hi

open classical

private noncomputable def ww : Π j : ℕ, { w : α' // j ≥ i → (w,j ⊨ v,j ⊨ o) ⊨ J }
 | j :=
if h : j > i then
     have h₀ : j ≥ 1,
       by { apply succ_le_of_lt,
            apply nat.lt_of_le_of_lt (nat.zero_le i) h },
     have h₁ : i ≤ j - 1,
       by { rw ← add_le_to_le_sub _ ; assumption },
     have Hdec : j - 1 < j,
       by { apply nat.sub_lt_of_pos_le, apply zero_lt_one,
            assumption },
     let hw := (ww (j-1)).property h₁ in
     have Hstep : C (j - 1 ⊨ v, j - 1 ⊨ o) (j ⊨ v, j ⊨ o),
       begin
         clear_except H Hi h₀ h₁ h, replace H := (H.apply _ Hi).right ((j-1) - i),
         simp at H, rw [← nat.add_sub_assoc,nat.add_sub_cancel_left,← succ_sub] at H
         ; apply H <|> assumption,
       end,
     let x := some (SIM (j ⊨ v) (j ⊨ o) hw Hstep) in
     have h₁ : j ≥ i → (x, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM (j ⊨ v) (j ⊨ o) hw Hstep)).right,
     ⟨x,h₁⟩
else if h' : i ≤ j then
     have h : i = j,
       by { apply le_antisymm h', apply le_of_not_gt, assumption },
     have h₀ : (j ⊨ v, j ⊨ o) ⊨ q,
          begin
            clear_except H Hi h,
            have := H.left.apply _ Hi, simp at this,
            subst i, apply this,
          end,
     let x₀ := some (SIM₀ (j ⊨ v) (j ⊨ o) h₀) in
     have h₁ : j ≥ i → (x₀, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM₀ (j ⊨ v) (j ⊨ o) h₀)).right,
     ⟨x₀,h₁⟩
else
  have h₁ : j ≥ i → (default α', j ⊨ v, j ⊨ o) ⊨ J,
    by { intro, exfalso, apply h', assumption, },
  ⟨default α',h₁⟩

private noncomputable def ww' (j : ℕ) := (ww i Hi j).val

end witness
include H SIM₀ SIM

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin
  simp [SPEC₀],
  lifted_pred keep,
  let w := ww' SIM₀ @SIM v o H _ a,
  existsi (⟨ w ⟩ : tvar α'),
  split,
  intro i,
  { simp,
    generalize h : w (x + i) = z,
    have h' : succ (x + i) > x,
    { apply lt_succ_of_le, apply nat.le_add_right },
    simp [w], rw [ww',ww], simp [dif_pos h'],
    rw ← h,
    apply_some_spec, simp, intros, assumption, },
  { dsimp [w,ww'], rw ww, simp,
    apply_some_spec,
    simp, intros, assumption, },
end
omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation SIM₀ @SIM _ _ h,
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

open classical

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
    { apply INV _ _ hJ hA  },
    { apply hA } },
  { simp [SPEC₁,C], }
end

end witness_construction

section simulation

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters {A : act (α'×γ')} {C : act (β'×γ')}
parameters {J : pred' (α'×β'×γ')}

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> A ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> C ⟧

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ {w v o} v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

parameters {Γ : cpred}
parameters H : Γ ⊢ SPEC₁ v o

section witness
variables (i : ℕ) (Hi : i ⊨ Γ)
include H Hi

open classical

private noncomputable def ww : Π j : ℕ, { w : α' // j ≥ i → (w,j ⊨ v,j ⊨ o) ⊨ J }
 | j :=
if h : j > i then
     have h₀ : j ≥ 1,
       by { apply succ_le_of_lt,
            apply nat.lt_of_le_of_lt (nat.zero_le i) h },
     have h₁ : i ≤ j - 1,
       by { rw ← add_le_to_le_sub _ ; assumption },
     have Hdec : j - 1 < j,
       by { apply nat.sub_lt_of_pos_le, apply zero_lt_one,
            assumption },
     let hw := (ww (j-1)).property h₁ in
     have Hstep : C (j - 1 ⊨ v, j - 1 ⊨ o) (j ⊨ v, j ⊨ o),
       begin
         clear_except H Hi h₀ h₁ h, replace H := (H.apply _ Hi).right ((j-1) - i),
         simp at H, rw [← nat.add_sub_assoc,nat.add_sub_cancel_left,← succ_sub] at H
         ; apply H <|> assumption,
       end,
     let x := some (SIM (j ⊨ v) (j ⊨ o) hw Hstep) in
     have h₁ : j ≥ i → (x, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM (j ⊨ v) (j ⊨ o) hw Hstep)).right,
     ⟨x,h₁⟩
else if h' : i ≤ j then
     have h : i = j,
       by { apply le_antisymm h', apply le_of_not_gt, assumption },
     have h₀ : (j ⊨ v, j ⊨ o) ⊨ q,
          begin
            clear_except H Hi h,
            have := H.left.apply _ Hi, simp at this,
            subst i, apply this,
          end,
     let x₀ := some (SIM₀ (j ⊨ v) (j ⊨ o) h₀) in
     have h₁ : j ≥ i → (x₀, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM₀ (j ⊨ v) (j ⊨ o) h₀)).right,
     ⟨x₀,h₁⟩
else
  have h₁ : j ≥ i → (default α', j ⊨ v, j ⊨ o) ⊨ J,
    by { intro, exfalso, apply h', assumption, },
  ⟨default α',h₁⟩

private noncomputable def ww' (j : ℕ) := (ww i Hi j).val

end witness
include H SIM₀ SIM

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin
  simp [SPEC₀],
  lifted_pred keep,
  let w := ww' SIM₀ @SIM v o H _ a,
  existsi (⟨ w ⟩ : tvar α'),
  split,
  intro i,
  { simp,
    generalize h : w (x + i) = z,
    have h' : succ (x + i) > x,
    { apply lt_succ_of_le, apply nat.le_add_right },
    simp [w], rw [ww',ww], simp [dif_pos h'],
    rw ← h,
    apply_some_spec, simp, intros, assumption, },
  { dsimp [w,ww'], rw ww, simp,
    apply_some_spec,
    simp, intros, assumption, },
end
omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation SIM₀ @SIM _ _ h,
end

end simulation

section witness_construction

parameters {α' : Sort u}
parameters {p J : pred' α'}
parameters {A : act α'}

parameters H₀ : p ⟹ J
parameters FIS₀ : ∃ σ, σ ⊨ p
parameters FIS : ∀ σ, σ ⊨ J → ∃ σ', A σ σ'
parameters INV : ∀ σ σ', σ ⊨ J → A σ σ' → σ' ⊨ J

open classical

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
    { apply INV _ _ hJ hA  },
    { apply hA } },
  { simp [SPEC₁,C], }
end

end witness_construction

namespace refinement
section

parameters {α' : Type u} {β' : Type u₀} {γ' : Type u₁ }
parameters {p : pred' (α'×γ')} {q : pred' (β'×γ')}
parameters {A : ℕ → act (α'×γ')} {C : ℕ → act (β'×γ')}
parameters {g : ℕ → pred' (α'×γ')} {g' : ℕ → pred' (β'×γ')}
parameters {J : pred' (α'×β'×γ')}

variables (x : tvar α') (y : tvar β') (z : tvar γ')

def SPEC₀ (v : tvar α') (o : tvar γ') : cpred :=
p ;; ⦃ o,v ⦄ ⋀
◻(∃∃ i, ⟦ ⦃o,v⦄ <> A i ⟧) ⋀
∀∀ i : ℕ, wf (g i ;; ⦃o,v⦄) ⟦ ⦃o,v⦄ <> A i ⟧

def SPEC₁ (v : tvar β') (o : tvar γ') : cpred :=
q ;; ⦃ o,v ⦄ ⋀
◻⟦ ⦃o,v⦄ <> C ⟧

parameter [inhabited α']
parameter SIM₀ : ∀ v o, (v,o) ⊨ q → ∃ w, (w,o) ⊨ p ∧ (w,v,o) ⊨ J
parameter SIM
: ∀ {w v o} v' o',
  (w,v,o) ⊨ J →
  C (v,o) (v',o') →
  ∃ w', A (w,o) (w',o') ∧
        (w',v',o') ⊨ J

parameters (v : tvar β') (o : tvar γ')

parameters {Γ : cpred}
parameters H : Γ ⊢ SPEC₁ v o

section witness
variables (i : ℕ) (Hi : i ⊨ Γ)
include H Hi

open classical

private noncomputable def ww : Π j : ℕ, { w : α' // j ≥ i → (w,j ⊨ v,j ⊨ o) ⊨ J }
 | j :=
if h : j > i then
     have h₀ : j ≥ 1,
       by { apply succ_le_of_lt,
            apply nat.lt_of_le_of_lt (nat.zero_le i) h },
     have h₁ : i ≤ j - 1,
       by { rw ← add_le_to_le_sub _ ; assumption },
     have Hdec : j - 1 < j,
       by { apply nat.sub_lt_of_pos_le, apply zero_lt_one,
            assumption },
     let hw := (ww (j-1)).property h₁ in
     have Hstep : C (j - 1 ⊨ v, j - 1 ⊨ o) (j ⊨ v, j ⊨ o),
       begin
         clear_except H Hi h₀ h₁ h, replace H := (H.apply _ Hi).right ((j-1) - i),
         simp at H, rw [← nat.add_sub_assoc,nat.add_sub_cancel_left,← succ_sub] at H
         ; apply H <|> assumption,
       end,
     let x := some (SIM (j ⊨ v) (j ⊨ o) hw Hstep) in
     have h₁ : j ≥ i → (x, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM (j ⊨ v) (j ⊨ o) hw Hstep)).right,
     ⟨x,h₁⟩
else if h' : i ≤ j then
     have h : i = j,
       by { apply le_antisymm h', apply le_of_not_gt, assumption },
     have h₀ : (j ⊨ v, j ⊨ o) ⊨ q,
          begin
            clear_except H Hi h,
            have := H.left.apply _ Hi, simp at this,
            subst i, apply this,
          end,
     let x₀ := some (SIM₀ (j ⊨ v) (j ⊨ o) h₀) in
     have h₁ : j ≥ i → (x₀, j ⊨ v, j ⊨ o) ⊨ J,
       from assume _, (some_spec (SIM₀ (j ⊨ v) (j ⊨ o) h₀)).right,
     ⟨x₀,h₁⟩
else
  have h₁ : j ≥ i → (default α', j ⊨ v, j ⊨ o) ⊨ J,
    by { intro, exfalso, apply h', assumption, },
  ⟨default α',h₁⟩

private noncomputable def ww' (j : ℕ) := (ww i Hi j).val

end witness
include H SIM₀ SIM

lemma simulation
: Γ ⊢ ∃∃ w, SPEC₀ w o :=
begin
  simp [SPEC₀],
  lifted_pred keep,
  let w := ww' SIM₀ @SIM v o H _ a,
  existsi (⟨ w ⟩ : tvar α'),
  split,
  intro i,
  { simp,
    generalize h : w (x + i) = z,
    have h' : succ (x + i) > x,
    { apply lt_succ_of_le, apply nat.le_add_right },
    simp [w], rw [ww',ww], simp [dif_pos h'],
    rw ← h,
    apply_some_spec, simp, intros, assumption, },
  { dsimp [w,ww'], rw ww, simp,
    apply_some_spec,
    simp, intros, assumption, },
end
omit H
lemma simulation'
: (∃∃ c, SPEC₁ c o) ⟹ (∃∃ a, SPEC₀ a o) :=
begin [temporal]
  rw p_exists_p_imp,
  intros x h,
  apply simulation SIM₀ @SIM _ _ h,
end

end
end refinement

end temporal

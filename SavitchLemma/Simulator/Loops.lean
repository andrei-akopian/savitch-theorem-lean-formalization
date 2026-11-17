module

public import SavitchLemma.Simulator.Initialize

@[expose] public section

/-!
# Simulator loop combinators

Defines component binding and finite-state loops used by the transition checker.
-/

namespace SavitchLemma

/-! ## General monadic bind & stateful loop combinators -/

/-- Bind a component returning `E₁` into a continuation returning `E₂` with fixed
internal state `Q₂`. -/
def bindComponent {Q₁ Q₂ InputAlphabet Γ : Type*} {k : ℕ} {E₁ E₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k E₁)
    (M₂ : E₁ → TMComponent Q₂ InputAlphabet Γ k E₂) :
    TMComponent (Q₁ ⊕ (E₁ × Q₂)) InputAlphabet Γ k E₂ where
  start := .inl M₁.start
  step s inSym workSyms :=
    match s with
    | .inl q₁ =>
      (M₁.step q₁ inSym workSyms).mapState fun
        | .inl q₁' => .inl (.inl q₁')
        | .inr e₁ => .inl (.inr (e₁, (M₂ e₁).start))
    | .inr (e₁, q₂) =>
      ((M₂ e₁).step q₂ inSym workSyms).mapState fun
        | .inl q₂' => .inl (.inr (e₁, q₂'))
        | .inr e₂ => .inr e₂

theorem bindComponent_reachesExit {Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ} {E₁ E₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k E₁)
    (M₂ : E₁ → TMComponent Q₂ InputAlphabet Γ k E₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ tapes₂ : Fin k → OneSidedTape Γ} {in₀ in₁ in₂ : Fin (n + 2)}
    {e₁ : E₁} {e₂ : E₂}
    (h₁ : M₁.ReachesExit input bound tapes₀ in₀ e₁ tapes₁ in₁)
    (h₂ : (M₂ e₁).ReachesExit input bound tapes₁ in₁ e₂ tapes₂ in₂) :
    (bindComponent M₁ M₂).ReachesExit input bound tapes₀ in₀ e₂ tapes₂ in₂ := by
  have hLift₁ : ∀ a b : OneSidedTMConfig (Q₁ ⊕ E₁) Γ k n,
      Relation.ReflTransGen
        (fun x y => M₁.CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (bindComponent M₁ M₂).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q₁ => .inl (.inl q₁)
         | .inr e => .inl (.inr (e, (M₂ e).start)), a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q₁ => .inl (.inl q₁)
         | .inr e => .inl (.inr (e, (M₂ e).start)), b.inputHead, b.workTapes⟩ := by
    intro a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (Sum.inl q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inl q, by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, TMAction.mapState, hState, hScanned, hNext]
      · simpa [bindComponent, TMAction.mapState, hState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hState, hScanned] using hTps
  have hLift₂ : ∀ a b : OneSidedTMConfig (Q₂ ⊕ E₂) Γ k n,
      Relation.ReflTransGen
        (fun x y => (M₂ e₁).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (bindComponent M₁ M₂).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q₂ => .inl (.inr (e₁, q₂))
         | .inr e => .inr e, a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q₂ => .inl (.inr (e₁, q₂))
         | .inr e => .inr e, b.inputHead, b.workTapes⟩ := by
    intro a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (Sum.inr (e₁, q)), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inr (e₁, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, TMAction.mapState, hState, hScanned, hNext]
      · simpa [bindComponent, TMAction.mapState, hState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hState, hScanned] using hTps
  exact (hLift₁ _ _ h₁).trans (hLift₂ _ _ h₂)

/-- Loop carrying a finite state `State` between iterations. -/
def loopWithState {State Q InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (init : State) (body : State → TMComponent Q InputAlphabet Γ k (State ⊕ Exit)) :
    TMComponent (State × Q) InputAlphabet Γ k Exit where
  start := (init, (body init).start)
  step st inSym workSyms :=
    ((body st.1).step st.2 inSym workSyms).mapState fun
      | .inl q' => .inl (st.1, q')
      | .inr (.inl st') => .inl (st', (body st').start)
      | .inr (.inr e) => .inr e

theorem loopWithState_reachesExit {State Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (init : State) (body : State → TMComponent Q InputAlphabet Γ k (State ⊕ Exit))
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (Inv : State → (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (measure : State → (Fin k → OneSidedTape Γ) → Fin (n + 2) → ℕ)
    (Post : Exit → (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (hStep : ∀ st tapes inHead, Inv st tapes inHead →
      (∃ st' tapes' inHead',
        (body st).ReachesExit input bound tapes inHead (.inl st') tapes' inHead' ∧
        Inv st' tapes' inHead' ∧
        measure st' tapes' inHead' < measure st tapes inHead) ∨
      (∃ e tapes' inHead',
        (body st).ReachesExit input bound tapes inHead (.inr e) tapes' inHead' ∧
        Post e tapes' inHead')) :
    ∀ tapes inHead, Inv init tapes inHead →
      ∃ e tapes' inHead',
        (loopWithState init body).ReachesExit input bound tapes inHead e tapes' inHead' ∧
        Post e tapes' inHead' := by
  have hLift : ∀ st, ∀ a b : OneSidedTMConfig (Q ⊕ (State ⊕ Exit)) Γ k n,
      Relation.ReflTransGen
        (fun x y => (body st).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (loopWithState init body).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q => .inl (st, q)
         | .inr (.inl st') => .inl (st', (body st').start)
         | .inr (.inr e) => .inr e, a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q => .inl (st, q)
         | .inr (.inl st') => .inl (st', (body st').start)
         | .inr (.inr e) => .inr e, b.inputHead, b.workTapes⟩ := by
    intro st a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (st, q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((State × Q) ⊕ Exit) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(st, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [loopWithState, TMAction.mapState, hState, hScanned, hNext]
        cases ((body st).step q (readInput input prev.inputHead) prev.scannedWork).nextState with
        | inl q' => rfl
        | inr e => cases e <;> rfl
      · simpa [loopWithState, TMAction.mapState, hState, hScanned] using hInM
      · simpa [loopWithState, TMAction.mapState, hState, hScanned] using hTps
  intro tapes inHead hInitInv
  have hWF : ∀ m st tapes inHead, measure st tapes inHead = m → Inv st tapes inHead →
      ∃ e tapes' inHead',
        Relation.ReflTransGen
          (fun x y => (loopWithState init body).CompStep input x y ∧
            (∀ t, (x.workTapes t).head < bound t) ∧
            (∀ t, (y.workTapes t).head < bound t))
          ⟨.inl (st, (body st).start), inHead, tapes⟩
          ⟨.inr e, inHead', tapes'⟩ ∧
        Post e tapes' inHead' := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro st tapes inHead hm hInvCur
      rcases hStep st tapes inHead hInvCur with
        ⟨stMid, tapesMid, inMid, hCont, hInvMid, hDec⟩ | ⟨e, tapesEnd, inEnd, hDone, hPost⟩
      · have hLifted := hLift st _ _ hCont
        have hm' : measure stMid tapesMid inMid < m := hm ▸ hDec
        obtain ⟨e, tapesEnd, inEnd, hRest, hPost⟩ :=
          ih (measure stMid tapesMid inMid) hm' stMid tapesMid inMid rfl hInvMid
        exact ⟨e, tapesEnd, inEnd, hLifted.trans hRest, hPost⟩
      · exact ⟨e, tapesEnd, inEnd, hLift st _ _ hDone, hPost⟩
  exact hWF (measure init tapes inHead) init tapes inHead rfl hInitInv

end SavitchLemma

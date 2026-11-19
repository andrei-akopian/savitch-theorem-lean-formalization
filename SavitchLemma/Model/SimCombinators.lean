module

public import SavitchLemma.Model.ConcreteEncoding
public import SavitchLemma.RegisterTape.Initialization
public import SavitchLemma.Model.TMCombinators
public import SavitchLemma.Tape.Comparison

@[expose] public section

/-!
# Combinators, multi-tape helpers, and bit-relation trackers for the Savitch simulator

This module collects lightweight reusable infrastructure shared by `SimInit`,
`StepChecker`, `AcceptChecker`, and `SavitchSimulator`:
- `mkWorkAction` and `compStep_head_override` / `compStep_exit_override`
- small tape atoms (`stepRightAtom`, `writeEndMarkStayAtom`)
- generic control combinators (`repeatUnit`, `bindComponent`, `loopWithState`)
- bit decoding (`decodeBitsOpt`), the 5-bit relational DFA (`BitRelState`,
  `relMatchesInputMove`), and work-tape scan accumulators (`HeadMatchState`, `TapeSummary`).
-/

namespace SavitchLemma

/-! ## General multi-tape action & override helpers -/

/-- Build a stationary-input `TMAction` directly from per-tape writes and moves. -/
def mkWorkAction {Q : Type*} {k : ℕ} (next : Q)
    (writeFn : Fin k → SimSym) (moveFn : Fin k → TapeMove) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write := writeFn
  workMove := moveFn

theorem OneSidedTape.updateAndMove_stay_self (t : OneSidedTape SimSym) :
    t.updateAndMove (t.cells t.head) .stay = some t := by
  simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]
  cases t
  simp only [OneSidedTape.mk.injEq, and_true]
  funext i
  split_ifs with h
  · rw [h]
  · rfl

theorem compStep_head_override {Q Exit InputAlphabet : Type*} {k n : ℕ}
    (M : TMComponent Q InputAlphabet SimSym k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes nextTapes finalTapes : Fin k → OneSidedTape SimSym)
    (inHead finalInHead : Fin (n + 2)) (e : Exit)
    (q q' : Q)
    (hHeads : ∀ j, (initTapes j).head < bound j)
    (hNextHeads : ∀ j, (nextTapes j).head < bound j)
    (hInMove : moveHead (n + 2) inHead
      (M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).inputMove = some inHead)
    (hUpd : ∀ j, (initTapes j).updateAndMove
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).write j)
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
      some (nextTapes j))
    (hNextState : (M.step q (readInput input inHead)
      (fun j => (initTapes j).cells (initTapes j).head)).nextState = .inl q')
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', inHead, nextTapes⟩ ⟨.inr e, finalInHead, finalTapes⟩) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, inHead, initTapes⟩ ⟨.inr e, finalInHead, finalTapes⟩ := by
  refine Relation.ReflTransGen.head ⟨?_, hHeads, hNextHeads⟩ hRest
  exact ⟨q, rfl, hNextState.symm, inHead, hInMove, rfl, hUpd⟩

theorem compStep_exit_override {Q Exit InputAlphabet : Type*} {k n : ℕ}
    (M : TMComponent Q InputAlphabet SimSym k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes nextTapes : Fin k → OneSidedTape SimSym)
    (inHead : Fin (n + 2)) (e : Exit) (q : Q)
    (hHeads : ∀ j, (initTapes j).head < bound j)
    (hNextHeads : ∀ j, (nextTapes j).head < bound j)
    (hInMove : moveHead (n + 2) inHead
      (M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).inputMove = some inHead)
    (hUpd : ∀ j, (initTapes j).updateAndMove
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).write j)
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
      some (nextTapes j))
    (hNextState : (M.step q (readInput input inHead)
      (fun j => (initTapes j).cells (initTapes j).head)).nextState = .inr e) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, inHead, initTapes⟩ ⟨.inr e, inHead, nextTapes⟩ := by
  refine Relation.ReflTransGen.single ⟨?_, hHeads, hNextHeads⟩
  exact ⟨q, rfl, hNextState.symm, inHead, hInMove, rfl, hUpd⟩

/-! ## Small single-tape atoms -/

/-- One-step atom advancing a single tape `t` one cell to the right without changing its cell. -/
def stepRightAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) scanned (fun j => if j = t then .right else .stay)

theorem stepRightAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (contents : List SimSym) (pos : ℕ) (hBound : pos + 1 < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ ft,
      (stepRightAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft contents (pos + 1) := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using by omega
    · exact hOtherBounds j hj
  have hMove : moveOneSidedHead pos .right = some (pos + 1) := by simp [moveOneSidedHead]
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_keep .right hMove
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [stepRightAtom, mkWorkAction] using hUpdT
    · simp only [stepRightAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (stepRightAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH rfl hUpd rfl, hFT⟩

/-- Append `.endMark` onto tape `t` without moving its head. -/
def writeEndMarkStayAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) (fun j => if j = t then .endMark else scanned j) (fun _ => .stay)

theorem writeEndMarkStayAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref : List SimSym) (hBound : pref.length < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) pref pref.length) :
    ∃ ft,
      (writeEndMarkStayAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ [.endMark]) pref.length := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using hBound
    · exact hOtherBounds j hj
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_append_move rfl .endMark .stay rfl
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [writeEndMarkStayAtom, mkWorkAction] using hUpdT
    · simp only [writeEndMarkStayAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (writeEndMarkStayAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH (by simp [writeEndMarkStayAtom, mkWorkAction, moveHead]) hUpd rfl, hFT⟩

/-! ## Repeat, monadic bind, and stateful loop combinators -/

/-- Repeat a `Unit`-exiting component `m` times sequentially. -/
def repeatUnit {Q InputAlphabet : Type*} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit) :
    TMComponent (Fin (m + 1) × Q) InputAlphabet SimSym 5 Unit where
  start := (⟨0, Nat.zero_lt_succ m⟩, M.start)
  step st inSym scanned :=
    if h : st.1.val < m then
      (M.step st.2 inSym scanned).mapState fun
        | .inl q' => .inl (st.1, q')
        | .inr () => .inl (⟨st.1.val + 1, by omega⟩, M.start)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem repeatUnit_reachesExit {Q InputAlphabet : Type*} {n : ℕ} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (Inv : ℕ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop)
    (hStep : ∀ i, i < m → ∀ tapes ih, Inv i tapes ih →
      ∃ tapes' ih',
        M.ReachesExit input bound tapes ih () tapes' ih' ∧ Inv (i + 1) tapes' ih') :
    ∀ tapes ih, Inv 0 tapes ih →
      (∀ t, (tapes t).head < bound t) →
      ∃ tapes' ih',
        (repeatUnit m M).ReachesExit input bound tapes ih () tapes' ih' ∧
        Inv m tapes' ih' := by
  intro tapes ih hInv0 hH0
  have hLift : ∀ (i : ℕ) (hi : i < m), ∀ a b,
      (∃ q₀, a.state = .inl q₀) →
      Relation.ReflTransGen
        (fun x y => M.CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j)) a b →
      Relation.ReflTransGen
        (fun x y => (repeatUnit m M).CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j))
        ⟨.inl (⟨i, by omega⟩, match a.state with | .inl q => q | .inr () => M.start),
          a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q => .inl (⟨i, by omega⟩, q)
         | .inr () => .inl (⟨i + 1, by omega⟩, M.start),
          b.inputHead, b.workTapes⟩ := by
    intro i hi a b ha hR
    induction hR with
    | refl =>
      rcases ha with ⟨q₀, hq₀⟩
      simp [hq₀]
      exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ihR =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail (by simpa [hState] using ihR) ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (⟨i, by omega⟩, q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig (Fin (m + 1) × Q ⊕ Unit) SimSym 5 n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(⟨i, by omega⟩, q), by simp, ?_, ihC, ?_, hInC, ?_⟩
      · simp only [repeatUnit, hi, ↓reduceDIte, TMAction.mapState, hScanned, hNext]
        cases (M.step q (readInput input prev.inputHead) prev.scannedWork).nextState <;> rfl
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hInM
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hTps
  have hLoop : ∀ rem i (hi : i + rem = m) tps ihC,
      Inv i tps ihC → (∀ j, (tps j).head < bound j) →
      ∃ tps' ih',
        Relation.ReflTransGen
          (fun x y => (repeatUnit m M).CompStep input x y ∧
            (∀ j, (x.workTapes j).head < bound j) ∧
            (∀ j, (y.workTapes j).head < bound j))
          ⟨.inl (⟨i, by omega⟩, M.start), ihC, tps⟩
          ⟨.inr (), ih', tps'⟩ ∧
        Inv m tps' ih' := by
    intro rem
    induction rem with
    | zero =>
      intro i hi tps ihC hInvI hHI
      have hEqM : i = m := by omega
      subst i
      refine ⟨tps, ihC, Relation.ReflTransGen.single ⟨?_, hHI, hHI⟩, hInvI⟩
      refine ⟨(⟨m, Nat.lt_succ_self m⟩, M.start), rfl, ?_, ihC, ?_, rfl, ?_⟩
      · simp [repeatUnit, mkWorkAction]
      · simp [repeatUnit, mkWorkAction, moveHead]
      · intro j
        simp only [repeatUnit, Nat.lt_irrefl, ↓reduceDIte, mkWorkAction]
        exact OneSidedTape.updateAndMove_stay_self _
    | succ r ihR =>
      intro i hi tps ihC hInvI hHI
      obtain ⟨tpsMid, ihMid, hRunM, hInvMid⟩ := hStep i (by omega) tps ihC hInvI
      have hLifted := hLift i (by omega) _ _ ⟨M.start, rfl⟩ hRunM
      have hHMid : ∀ j, (tpsMid j).head < bound j := by
        cases hRunM with
        | tail _ hLast => exact hLast.2.2
      obtain ⟨tpsEnd, ihEnd, hRest, hInvEnd⟩ := ihR (i + 1) (by omega) tpsMid ihMid hInvMid hHMid
      exact ⟨tpsEnd, ihEnd, hLifted.trans hRest, hInvEnd⟩
  exact hLoop m 0 (Nat.zero_add m) tapes ih hInv0 hH0

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
          ({ state := match prev.state with
             | .inl q₁ => .inl (.inl q₁)
             | .inr e => .inl (.inr (e, (M₂ e).start)),
             inputHead := prev.inputHead, workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inl q, by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, hScanned, TMAction.mapState, hNext]
        cases (M₁.step q (readInput input prev.inputHead) prev.scannedWork).nextState <;> rfl
      · simpa [bindComponent, TMAction.mapState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hScanned] using hTps
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
          ({ state := match prev.state with
             | .inl q₂ => .inl (.inr (e₁, q₂))
             | .inr e => .inr e,
             inputHead := prev.inputHead, workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inr (e₁, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, hScanned, TMAction.mapState, hNext]
        cases ((M₂ e₁).step q (readInput input prev.inputHead) prev.scannedWork).nextState <;> rfl
      · simpa [bindComponent, TMAction.mapState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hScanned] using hTps
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
          ({ state := match prev.state with
             | .inl q' => .inl (st, q')
             | .inr (.inl st') => .inl (st', (body st').start)
             | .inr (.inr e) => .inr e,
             inputHead := prev.inputHead, workTapes := prev.workTapes } :
            OneSidedTMConfig ((State × Q) ⊕ Exit) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(st, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [loopWithState, hScanned, TMAction.mapState, hNext]
        cases ((body st).step q (readInput input prev.inputHead) prev.scannedWork).nextState with
        | inl q' => rfl
        | inr e => cases e <;> rfl
      · simpa [loopWithState, TMAction.mapState, hScanned] using hInM
      · simpa [loopWithState, TMAction.mapState, hScanned] using hTps
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

/-! ## Bit decoding and finite-state comparison trackers -/

theorem true_mem_iff_bitsToNat_pos (bs : List Bool) :
    true ∈ bs ↔ 0 < bitsToNat bs := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    cases b
    · have h1 : (true ∈ false :: bs) ↔ true ∈ bs := by simp
      rw [h1, ih]
      simp only [bitsToNat]
      cases bitsToNat bs <;> simp
    · simp [bitsToNat]

theorem true_not_mem_iff_bitsToNat_zero (bs : List Bool) :
    true ∉ bs ↔ bitsToNat bs = 0 := by
  rw [true_mem_iff_bitsToNat_pos]
  omega

/-- Decode `m` bits (LSB-first) into an element of a finite type `U`, returning
`none` when the decoded integer is at least `Fintype.card U`. -/
noncomputable def decodeBitsOpt (m : ℕ) (U : Type*) [Fintype U]
    (f : Fin m → Bool) : Option U :=
  let v := bitsToNat (List.ofFn f)
  if h : v < Fintype.card U then
    some ((Fintype.equivFin U).symm ⟨v, h⟩)
  else
    none

theorem decodeBitsOpt_eq_some_iff {m : ℕ} {U : Type*} [Fintype U]
    (hPow : Fintype.card U + 1 ≤ 2 ^ m) (f : Fin m → Bool) (u : U) :
    decodeBitsOpt m U f = some u ↔
      natToBits m (Fintype.equivFin U u).val = List.ofFn f := by
  unfold decodeBitsOpt
  dsimp only
  constructor
  · intro hDec
    split_ifs at hDec with hLt
    simp only [Option.some.injEq] at hDec
    have hVal : (Fintype.equivFin U u).val = bitsToNat (List.ofFn f) := by
      rw [← hDec, Equiv.apply_symm_apply]
    rw [hVal]
    have hId := natToBits_bitsToNat (List.ofFn f)
    simpa [List.length_ofFn] using hId
  · intro hBits
    have hValLt : (Fintype.equivFin U u).val < 2 ^ m := by
      have h1 := (Fintype.equivFin U u).isLt
      omega
    have hNat := congrArg bitsToNat hBits
    rw [bitsToNat_natToBits_of_lt hValLt] at hNat
    have hLt : bitsToNat (List.ofFn f) < Fintype.card U := by
      rw [← hNat]
      exact (Fintype.equivFin U u).isLt
    simp only [hLt, ↓reduceDIte, Option.some.injEq]
    apply (Fintype.equivFin U).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext hNat.symm

/-- Finite-state DFA tracker comparing two equal-length LSB-first bit streams
`u` (A) and `v` (B) for equality (`v = u`), increment (`v = u + 1`), and decrement
(`u = v + 1`) simultaneously in one left-to-right pass. -/
structure BitRelState where
  eqOk : Bool
  incOk : Bool
  incCarry : Bool
  decOk : Bool
  decCarry : Bool
  deriving DecidableEq

def BitRelState.equivProd : BitRelState ≃ Bool × Bool × Bool × Bool × Bool where
  toFun s := (s.eqOk, s.incOk, s.incCarry, s.decOk, s.decCarry)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨_, _, _, _, _⟩; rfl

instance : Fintype BitRelState :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool × Bool) BitRelState.equivProd.symm

def BitRelState.init : BitRelState :=
  ⟨true, true, true, true, true⟩

def BitRelState.step (st : BitRelState) (a b : Bool) : BitRelState where
  eqOk := st.eqOk && (a == b)
  incOk := st.incOk && (b == xor a st.incCarry)
  incCarry := a && st.incCarry
  decOk := st.decOk && (a == xor b st.decCarry)
  decCarry := b && st.decCarry

def BitRelState.runList (st : BitRelState) (u v : List Bool) : BitRelState :=
  (u.zip v).foldl (fun s p => s.step p.1 p.2) st

theorem BitRelState.runList_eqOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    (st.runList u v).eqOk = true ↔ (st.eqOk = true ∧ u = v) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil => simp [BitRelState.runList]
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change ((st.step a b).runList us vs).eqOk = true ↔ st.eqOk = true ∧ a :: us = b :: vs
      rw [ih (st.step a b) vs hLen]
      simp [BitRelState.step, Bool.and_eq_true, List.cons.injEq]
      tauto

theorem BitRelState.runList_incOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    ((st.runList u v).incOk && !(st.runList u v).incCarry) = true ↔
      (st.incOk = true ∧ bitsToNat v = bitsToNat u + st.incCarry.toNat) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil =>
      simp only [BitRelState.runList, List.zip_nil_right, List.foldl_nil, bitsToNat, Nat.zero_add,
        Bool.and_eq_true, Bool.not_eq_true']
      cases st.incOk <;> cases st.incCarry <;> simp
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change (((st.step a b).runList us vs).incOk &&
        !((st.step a b).runList us vs).incCarry) = true ↔
        st.incOk = true ∧ bitsToNat (b :: vs) = bitsToNat (a :: us) + st.incCarry.toNat
      rw [ih (st.step a b) vs hLen]
      simp only [BitRelState.step, Bool.and_eq_true, bitsToNat]
      cases st.incOk <;> cases a <;> cases b <;> cases st.incCarry <;> simp <;> omega

theorem BitRelState.runList_decOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    ((st.runList u v).decOk && !(st.runList u v).decCarry) = true ↔
      (st.decOk = true ∧ bitsToNat u = bitsToNat v + st.decCarry.toNat) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil =>
      simp only [BitRelState.runList, List.zip_nil_right, List.foldl_nil, bitsToNat, Nat.zero_add,
        Bool.and_eq_true, Bool.not_eq_true']
      cases st.decOk <;> cases st.decCarry <;> simp
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change (((st.step a b).runList us vs).decOk &&
        !((st.step a b).runList us vs).decCarry) = true ↔
        st.decOk = true ∧ bitsToNat (a :: us) = bitsToNat (b :: vs) + st.decCarry.toNat
      rw [ih (st.step a b) vs hLen]
      simp only [BitRelState.step, Bool.and_eq_true, bitsToNat]
      cases st.decOk <;> cases a <;> cases b <;> cases st.decCarry <;> simp <;> omega

theorem BitRelState.init_runList (u v : List Bool) (hLen : u.length = v.length) :
    let r := BitRelState.init.runList u v
    (r.eqOk = true ↔ bitsToNat u = bitsToNat v) ∧
    ((r.incOk && !r.incCarry) = true ↔ bitsToNat v = bitsToNat u + 1) ∧
    ((r.decOk && !r.decCarry) = true ↔ bitsToNat u = bitsToNat v + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitRelState.runList_eqOk BitRelState.init u v hLen]
    simp only [BitRelState.init, true_and]
    constructor
    · intro h; subst h; rfl
    · intro h
      have h1 := natToBits_bitsToNat u
      have h2 := natToBits_bitsToNat v
      rw [hLen] at h1
      rw [h] at h1
      exact h1.symm.trans h2
  · simpa [BitRelState.init] using BitRelState.runList_incOk BitRelState.init u v hLen
  · simpa [BitRelState.init] using BitRelState.runList_decOk BitRelState.init u v hLen

/-- Finite-state predicate checking whether `rel` witnesses `moveHead (n+2) h₁ mv = some h₂`
given `inSym = readInput input h₁`. -/
def relMatchesInputMove {InputAlphabet : Type*} (inSym : InputSymbol InputAlphabet)
    (rel : BitRelState) (mv : TapeMove) : Bool :=
  match mv with
  | .left =>
    match inSym with
    | .leftEnd => false
    | _ => rel.decOk && !rel.decCarry
  | .stay => rel.eqOk
  | .right =>
    match inSym with
    | .rightEnd => false
    | _ => rel.incOk && !rel.incCarry

theorem relMatchesInputMove_iff {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (h₁ : Fin (n + 2)) (h₂val : ℕ)
    (u v : List Bool) (hLen : u.length = v.length)
    (hU : bitsToNat u = h₁.val) (hV : bitsToNat v = h₂val)
    (mv : TapeMove) :
    relMatchesInputMove (readInput input h₁) (BitRelState.init.runList u v) mv = true ↔
      ∃ h₂ : Fin (n + 2), moveHead (n + 2) h₁ mv = some h₂ ∧ h₂.val = h₂val := by
  obtain ⟨hEq, hInc, hDec⟩ := BitRelState.init_runList u v hLen
  cases mv with
  | left =>
    unfold relMatchesInputMove readInput
    split_ifs with h0 hR
    · simp [moveHead, h0]
    · simp only [moveHead, hDec, hU, hV]
      have hPos : 0 < h₁.val := by omega
      simp only [hPos, ↓reduceDIte]
      constructor
      · intro h
        refine ⟨⟨h₁.val - 1, by omega⟩, rfl, by simp; omega⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val - 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
    · simp only [moveHead, hDec, hU, hV]
      have hPos : 0 < h₁.val := by omega
      simp only [hPos, ↓reduceDIte]
      constructor
      · intro h
        refine ⟨⟨h₁.val - 1, by omega⟩, rfl, by simp; omega⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val - 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
  | stay =>
    unfold relMatchesInputMove moveHead
    simp only [hEq, hU, hV, Option.some.injEq]
    constructor
    · intro h; exact ⟨h₁, rfl, h⟩
    · rintro ⟨_, rfl, hVal⟩; exact hVal
  | right =>
    unfold relMatchesInputMove readInput
    split_ifs with h0 hR
    · have hLt : h₁.val + 1 < n + 2 := by omega
      simp only [moveHead, hLt, ↓reduceDIte, hInc, hU, hV]
      constructor
      · intro h; exact ⟨⟨h₁.val + 1, hLt⟩, rfl, by simp [h]⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val + 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
    · simp [moveHead, hR]
    · have hLt : h₁.val + 1 < n + 2 := by omega
      simp only [moveHead, hLt, ↓reduceDIte, hInc, hU, hV]
      constructor
      · intro h; exact ⟨⟨h₁.val + 1, hLt⟩, rfl, by simp [h]⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val + 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega

/-- Position relative to the current tape head during an `S`-cell sweep. -/
inductive HeadMatchState where
  | before
  | atHead
  | pastHead
  deriving DecidableEq

def HeadMatchState.equivFin : HeadMatchState ≃ Fin 3 where
  toFun | .before => 0 | .atHead => 1 | .pastHead => 2
  invFun | 0 => .before | 1 => .atHead | _ => .pastHead
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype HeadMatchState := Fintype.ofEquiv (Fin 3) HeadMatchState.equivFin.symm

/-- Finite summary of checking one serialized work-tape block between `tArgA` and `tArgB`. -/
structure TapeSummary (Γ : Type*) where
  ok : Bool
  scanned : Γ
  written : Γ
  leftValid : Bool
  stayValid : Bool
  rightValid : Bool

instance {Γ : Type*} [Fintype Γ] : Fintype (TapeSummary Γ) :=
  Fintype.ofEquiv (Bool × Γ × Γ × Bool × Bool × Bool)
    { toFun := fun ⟨ok, s, w, l, st, r⟩ => ⟨ok, s, w, l, st, r⟩
      invFun := fun t => (t.ok, t.scanned, t.written, t.leftValid, t.stayValid, t.rightValid)
      left_inv := fun ⟨_, _, _, _, _, _⟩ => rfl
      right_inv := fun t => by cases t; rfl }

def TapeSummary.matchesAction {Γ : Type*} [DecidableEq Γ] (ts : TapeSummary Γ)
    (w : Γ) (mv : TapeMove) : Bool :=
  ts.ok && decide (ts.written = w) &&
    match mv with
    | .left => ts.leftValid
    | .stay => ts.stayValid
    | .right => ts.rightValid

end SavitchLemma

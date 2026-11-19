module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import SavitchLemma.Model.MachineDefinitions

import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# A finite-capacity multitape nondeterministic machine

Internal proof machinery relating the external one-sided machine definitions in
`SavitchLemma.Model.MachineDefinitions` to fixed-capacity (`BoundedTape`,
`TMConfig`, `AcceptsWithinCapacity`) computations.  For each fixed input and
capacity, bounded configurations form a finite type (`tmConfig_finite`,
`tmConfig_card`), which provides the IDs used by the abstract register machine.
-/

namespace SavitchLemma

/-- A work tape restricted to `S` cells. -/
structure BoundedTape (Γ : Type*) (S : ℕ) where
  cells : Fin S → Γ
  head : Fin S

/-- A bounded tape is equivalent to its cells and head position. -/
def BoundedTape.equivProd {Γ : Type*} (S : ℕ) :
    BoundedTape Γ S ≃ ( (Fin S → Γ) × Fin S) where
  toFun tape := (tape.cells, tape.head)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv tape := by cases tape; rfl
  right_inv pair := by cases pair; rfl

instance BoundedTape.fintype {Γ : Type*} [Fintype Γ] (S : ℕ) : Fintype (BoundedTape Γ S) :=
  Fintype.ofEquiv ((Fin S → Γ) × Fin S) (BoundedTape.equivProd S).symm

/-- The cells currently containing a nonblank symbol. -/
noncomputable def BoundedTape.nonblankCells {Γ : Type*} {S : ℕ}
    (tape : BoundedTape Γ S) (blank : Γ) : Finset (Fin S) := by
  classical
  exact Finset.univ.filter (fun i => tape.cells i ≠ blank)

/-- The current nonblank portion of a bounded tape uses at most its capacity. -/
theorem BoundedTape.nonblankCells_card_le {Γ : Type*} {S : ℕ}
    (tape : BoundedTape Γ S) (blank : Γ) :
    (tape.nonblankCells blank).card ≤ S := by
  classical
  calc
    (tape.nonblankCells blank).card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = S := by simp

/-- The head and every cell it can scan lie inside the `S`-cell segment. -/
theorem BoundedTape.head_prefix_size {Γ : Type*} {S : ℕ} (tape : BoundedTape Γ S) :
    tape.head.val + 1 ≤ S := Nat.succ_le_of_lt tape.head.isLt

/-- Every successful finite head move agrees with the corresponding one-sided
unbounded head move. -/
theorem moveHead_toOneSided {S : ℕ} (position : Fin S) (movement : TapeMove)
    {next : Fin S} (hMove : moveHead S position movement = some next) :
    moveOneSidedHead position.val movement = some next.val := by
  cases movement with
  | left =>
    simp [moveHead] at hMove
    rcases hMove with ⟨hPos, hEq⟩
    have hVal := congrArg Fin.val hEq
    simpa [moveOneSidedHead, hPos] using hVal
  | stay =>
    simp [moveHead] at hMove
    have hVal := congrArg Fin.val hMove
    simpa [moveOneSidedHead] using hVal
  | right =>
    simp [moveHead] at hMove
    rcases hMove with ⟨hPos, hEq⟩
    have hVal := congrArg Fin.val hEq
    simpa [moveOneSidedHead] using hVal

/-- Write the scanned cell and move the work-tape head. -/
def BoundedTape.updateAndMove {Γ : Type*} {S : ℕ} (tape : BoundedTape Γ S)
    (symbol : Γ) (movement : TapeMove) : Option (BoundedTape Γ S) := do
  match moveHead S tape.head movement with
  | none => none
  | some head => some ⟨fun i => if i = tape.head then symbol else tape.cells i, head⟩

/-- Extend a bounded tape with blank cells to obtain a one-sided infinite tape. -/
def BoundedTape.toOneSided {Γ : Type*} {S : ℕ} (tape : BoundedTape Γ S)
    (blank : Γ) : OneSidedTape Γ where
  cells i := if h : i < S then tape.cells ⟨i, h⟩ else blank
  head := tape.head.val

/-- Restrict a one-sided tape whose head lies in the first `S` cells. -/
def OneSidedTape.toBounded {Γ : Type*} (tape : OneSidedTape Γ) (S : ℕ)
    (hHead : tape.head < S) : BoundedTape Γ S where
  cells := fun i => tape.cells i.val
  head := ⟨tape.head, hHead⟩

/-- A successful bounded-tape update agrees with the one-sided infinite-tape
update after extending the finite tape by blanks. -/
theorem BoundedTape.updateAndMove_toOneSided {Γ : Type*} {S : ℕ}
    (tape next : BoundedTape Γ S) (blank symbol : Γ) (movement : TapeMove)
    (hStep : tape.updateAndMove symbol movement = some next) :
    (tape.toOneSided blank).updateAndMove symbol movement =
      some (next.toOneSided blank) := by
  cases hMove : moveHead S tape.head movement with
  | none => simp [BoundedTape.updateAndMove, hMove] at hStep
  | some nextHead =>
    have hNext : next = ⟨fun i => if i = tape.head then symbol else tape.cells i, nextHead⟩ := by
      have h := hStep
      simp [BoundedTape.updateAndMove, hMove] at h
      exact h.symm
    have hInfiniteMove := moveHead_toOneSided tape.head movement hMove
    change (match moveOneSidedHead tape.head.val movement with
      | none => none
      | some head =>
        some ⟨fun i => if i = tape.head.val then symbol else (tape.toOneSided blank).cells i,
          head⟩) = some (next.toOneSided blank)
    simp only [hInfiniteMove]
    simp only [Option.some.injEq]
    rw [hNext]
    rw [OneSidedTape.mk.injEq]
    constructor
    · funext i
      by_cases hi : i < S
      · by_cases hHead : i = tape.head.val
        · subst i
          simp [BoundedTape.toOneSided, hi]
        · have hFinNe : (⟨i, hi⟩ : Fin S) ≠ tape.head := by
            intro h
            apply hHead
            exact congrArg Fin.val h
          simp [BoundedTape.toOneSided, hi, hHead, hFinNe]
      · have hNe : i ≠ tape.head.val := by omega
        simp [BoundedTape.toOneSided, hi, hNe]
    · rfl

/-- A one-sided head move with both endpoints inside the finite segment is a
successful bounded head move. -/
theorem moveHead_toBounded {S : ℕ} (position : ℕ) (hPosition : position < S)
    (movement : TapeMove) {next : ℕ} (hMove : moveOneSidedHead position movement = some next)
    (hNext : next < S) :
    moveHead S ⟨position, hPosition⟩ movement = some ⟨next, hNext⟩ := by
  cases movement with
  | left =>
    simp [moveOneSidedHead] at hMove
    rcases hMove with ⟨hPositive, hNextEq⟩
    simp [moveHead, hPositive]
    exact hNextEq
  | stay =>
    simp [moveOneSidedHead] at hMove
    subst next
    simp [moveHead]
  | right =>
    simp [moveOneSidedHead] at hMove
    subst next
    simp [moveHead, hNext]

/-- Restricting a one-sided tape after an update that stays within capacity
produces the corresponding bounded-tape update. -/
theorem OneSidedTape.updateAndMove_toBounded {Γ : Type*} (tape next : OneSidedTape Γ)
    (capacity : ℕ) (hHead : tape.head < capacity) (hNext : next.head < capacity)
    (symbol : Γ) (movement : TapeMove)
    (hStep : tape.updateAndMove symbol movement = some next) :
    (tape.toBounded capacity hHead).updateAndMove symbol movement =
      some (next.toBounded capacity hNext) := by
  cases hMove : moveOneSidedHead tape.head movement with
  | none => simp [OneSidedTape.updateAndMove, hMove] at hStep
  | some nextHead =>
    have hUpdated : next =
        ⟨fun i => if i = tape.head then symbol else tape.cells i, nextHead⟩ := by
      have h := hStep
      simp [OneSidedTape.updateAndMove, hMove] at h
      exact h.symm
    have hNextHead : nextHead < capacity := by
      have h := congrArg OneSidedTape.head hUpdated
      simpa [h] using hNext
    have hBoundedMove := moveHead_toBounded tape.head hHead movement hMove hNextHead
    subst next
    simp only [BoundedTape.updateAndMove, OneSidedTape.toBounded, hBoundedMove,
      Option.some.injEq]
    rw [BoundedTape.mk.injEq]
    constructor
    · funext i
      by_cases hVal : i.val = tape.head
      · have hEq : i = ⟨tape.head, hHead⟩ := Fin.ext hVal
        simp [hEq]
      · have hNe : i ≠ (⟨tape.head, hHead⟩ : Fin capacity) := by
          intro hEq
          apply hVal
          exact congrArg Fin.val hEq
        simp [hNe, hVal]
    · rfl

/-- A machine configuration on a fixed input and fixed work-tape capacity. -/
structure TMConfig (Q Γ : Type*) (k n S : ℕ) where
  state : Q
  inputHead : Fin (n + 2)
  workTapes : Fin k → BoundedTape Γ S

/-- The symbols currently scanned on all bounded work tapes. -/
def TMConfig.scannedWork {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) : Fin k → Γ :=
  fun tape => (cfg.workTapes tape).cells (cfg.workTapes tape).head

/-- Extend all bounded work tapes by blank cells. -/
def TMConfig.toOneSided {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) (blank : Γ) : OneSidedTMConfig Q Γ k n where
  state := cfg.state
  inputHead := cfg.inputHead
  workTapes := fun tape => (cfg.workTapes tape).toOneSided blank

/-- A one-sided configuration fits in the first `S` cells when all heads stay
below `S` and every cell at or beyond `S` is blank. -/
def OneSidedTMConfig.FitsCapacity {Q Γ : Type*} {k n : ℕ}
    (cfg : OneSidedTMConfig Q Γ k n) (blank : Γ) (S : ℕ) : Prop :=
  ∀ tape : Fin k, (cfg.workTapes tape).head < S ∧
    ∀ i : ℕ, S ≤ i → (cfg.workTapes tape).cells i = blank

theorem OneSidedTMConfig.FitsCapacity.headsWithin {Q Γ : Type*} {k n S : ℕ}
    {cfg : OneSidedTMConfig Q Γ k n} {blank : Γ} (hFit : cfg.FitsCapacity blank S) :
    cfg.HeadsWithin S :=
  fun tape => (hFit tape).1

/-- Restrict a one-sided configuration whose work heads all lie below `S`. -/
def OneSidedTMConfig.toBounded {Q Γ : Type*} {k n : ℕ}
    (cfg : OneSidedTMConfig Q Γ k n) (S : ℕ) (hHeads : cfg.HeadsWithin S) :
    TMConfig Q Γ k n S where
  state := cfg.state
  inputHead := cfg.inputHead
  workTapes := fun tape => (cfg.workTapes tape).toBounded S (hHeads tape)

/-- Restricting a one-sided configuration preserves the scanned work symbols. -/
theorem OneSidedTMConfig.toBounded_scannedWork {Q Γ : Type*} {k n S : ℕ}
    (cfg : OneSidedTMConfig Q Γ k n) (hHeads : cfg.HeadsWithin S) :
    (cfg.toBounded S hHeads).scannedWork = cfg.scannedWork := by
  funext tape
  rfl

/-- Extending a bounded configuration produces a one-sided configuration that
fits the same capacity. -/
theorem TMConfig.toOneSided_fitsCapacity {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) (blank : Γ) :
    (cfg.toOneSided blank).FitsCapacity blank S := by
  intro tape
  constructor
  · exact (cfg.workTapes tape).head.isLt
  · intro i hi
    simp [TMConfig.toOneSided, BoundedTape.toOneSided, Nat.not_lt_of_ge hi]

/-- Extending a bounded tape preserves the symbol under its head. -/
theorem BoundedTape.toOneSided_readHead {Γ : Type*} {S : ℕ}
    (tape : BoundedTape Γ S) (blank : Γ) :
    (tape.toOneSided blank).cells (tape.toOneSided blank).head = tape.cells tape.head := by
  simp [BoundedTape.toOneSided]

/-- The symbols scanned on each work tape are preserved by extension. -/
theorem TMConfig.toOneSided_scannedWork {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) (blank : Γ) :
    (cfg.toOneSided blank).scannedWork = cfg.scannedWork := by
  funext tape
  exact BoundedTape.toOneSided_readHead (cfg.workTapes tape) blank

/-- Every work-tape head in a configuration is within the declared capacity. -/
theorem TMConfig.workHeadsWithinCapacity {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) : ∀ tape : Fin k, (cfg.workTapes tape).head.val < S :=
  fun tape => (cfg.workTapes tape).head.isLt

/-- The size of the scanned prefix of the work tapes in a configuration.  On
each one-sided tape this includes every square from the origin to its head. -/
def TMConfig.scannedPrefix {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) : ℕ :=
  Finset.univ.sup (fun tape : Fin k => (cfg.workTapes tape).head.val + 1)

/-- Every configuration at capacity `S` scans at most `S` squares per tape. -/
theorem TMConfig.scannedPrefix_le_capacity {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) : cfg.scannedPrefix ≤ S := by
  unfold TMConfig.scannedPrefix
  apply Finset.sup_le
  intro tape _
  exact BoundedTape.head_prefix_size (cfg.workTapes tape)

/-- A configuration is a finite product of its control, input head, and work
tapes. -/
def TMConfig.equivProd {Q Γ : Type*} (k n S : ℕ) :
    TMConfig Q Γ k n S ≃ Q × Fin (n + 2) × (Fin k → BoundedTape Γ S) where
  toFun cfg := (cfg.state, cfg.inputHead, cfg.workTapes)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv cfg := by cases cfg; rfl
  right_inv data := by cases data with | mk state rest => cases rest; rfl

instance TMConfig.fintype {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    (k n S : ℕ) : Fintype (TMConfig Q Γ k n S) :=
  Fintype.ofEquiv (Q × Fin (n + 2) × (Fin k → BoundedTape Γ S))
    (TMConfig.equivProd k n S).symm

/-- The initially blank work tapes and leftmost input-head position. -/
def MultitapeNTM.initialConfig {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (capacity : ℕ) (hCapacity : 0 < capacity) : TMConfig Q Γ k n capacity where
  state := M.startState
  inputHead := ⟨0, by omega⟩
  workTapes := fun _ => ⟨fun _ => M.blank, ⟨0, hCapacity⟩⟩

/-- One nondeterministic transition, constrained to the fixed input and
finite work-tape capacity. -/
def MultitapeNTM.step {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (capacity : ℕ)
    (cfg next : TMConfig Q Γ k n capacity) : Prop :=
  ∃ action,
    action ∈ M.transitions cfg.state (readInput input cfg.inputHead) cfg.scannedWork ∧
    next.state = action.nextState ∧
    ∃ inputHead, moveHead (n + 2) cfg.inputHead action.inputMove = some inputHead ∧
      next.inputHead = inputHead ∧
      ∀ tape : Fin k,
        (cfg.workTapes tape).updateAndMove (action.write tape) (action.workMove tape) =
          some (next.workTapes tape)

/-- A bounded machine step is a valid one-sided infinite-tape step after
extending all bounded tapes with blanks. -/
theorem MultitapeNTM.step_lifts_toOneSided {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (cfg next : TMConfig Q Γ k n capacity)
    (hStep : M.step input capacity cfg next) :
    M.oneSidedStep input (cfg.toOneSided M.blank) (next.toOneSided M.blank) := by
  rcases hStep with ⟨action, hAction, hState, inputHead, hMove, hInputHead, hTapes⟩
  refine ⟨action, ?_, hState, inputHead, hMove, hInputHead, ?_⟩
  · rw [TMConfig.toOneSided_scannedWork]
    exact hAction
  · intro tape
    exact BoundedTape.updateAndMove_toOneSided (cfg.workTapes tape)
      (next.workTapes tape) M.blank (action.write tape) (action.workMove tape) (hTapes tape)

/-- Every finite bounded run has the corresponding one-sided infinite-tape
run. -/
theorem MultitapeNTM.boundedRun_lifts_toOneSided {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) {initial final : TMConfig Q Γ k n capacity}
    (hRun : Relation.ReflTransGen (M.step input capacity) initial final) :
    Relation.ReflTransGen (M.oneSidedStep input)
      (initial.toOneSided M.blank) (final.toOneSided M.blank) := by
  induction hRun with
  | refl => exact Relation.ReflTransGen.refl
  | @tail previous current hPrevious hStep ih =>
    exact Relation.ReflTransGen.tail ih
      (M.step_lifts_toOneSided input capacity previous current hStep)

/-- Extending the bounded initial configuration yields the one-sided initial
configuration. -/
theorem MultitapeNTM.initialConfig_toOneSided {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (capacity : ℕ) (hCapacity : 0 < capacity) :
    (M.initialConfig (n := n) capacity hCapacity).toOneSided M.blank =
      M.oneSidedInitialConfig := by
  simp only [MultitapeNTM.initialConfig, MultitapeNTM.oneSidedInitialConfig,
    TMConfig.toOneSided, BoundedTape.toOneSided]
  congr 1
  funext _
  congr 1
  funext i
  split <;> rfl

/-- Restricting the one-sided initial configuration recovers the bounded initial
configuration. -/
theorem MultitapeNTM.oneSidedInitialConfig_toBounded {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (capacity : ℕ) (hCapacity : 0 < capacity) :
    (M.oneSidedInitialConfig (n := n)).toBounded capacity (fun _ => hCapacity) =
      M.initialConfig capacity hCapacity := by
  rfl

/-- Every finite bounded run lifts to a one-sided run staying within `capacity`. -/
theorem MultitapeNTM.boundedRun_lifts_within {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) {initial final : TMConfig Q Γ k n capacity}
    (hRun : Relation.ReflTransGen (M.step input capacity) initial final) :
    Relation.ReflTransGen
      (fun a b => M.oneSidedStep input a b ∧ a.HeadsWithin capacity ∧ b.HeadsWithin capacity)
      (initial.toOneSided M.blank) (final.toOneSided M.blank) := by
  induction hRun with
  | refl => exact Relation.ReflTransGen.refl
  | @tail previous current hPrevious hStep ih =>
    refine Relation.ReflTransGen.tail ih ⟨?_, ?_, ?_⟩
    · exact M.step_lifts_toOneSided input capacity previous current hStep
    · exact (previous.toOneSided_fitsCapacity M.blank).headsWithin
    · exact (current.toOneSided_fitsCapacity M.blank).headsWithin

/-- Restricting a one-sided step whose endpoints stay below `capacity` gives a
bounded step. -/
theorem MultitapeNTM.oneSidedStep_restricts_toBounded {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) {cfg next : OneSidedTMConfig Q Γ k n}
    (hStep : M.oneSidedStep input cfg next)
    (hCfg : cfg.HeadsWithin capacity) (hNext : next.HeadsWithin capacity) :
    M.step input capacity (cfg.toBounded capacity hCfg) (next.toBounded capacity hNext) := by
  rcases hStep with ⟨action, hAction, hState, inputHead, hMove, hInputHead, hTapes⟩
  refine ⟨action, ?_, hState, inputHead, hMove, hInputHead, ?_⟩
  · rw [OneSidedTMConfig.toBounded_scannedWork]
    exact hAction
  · intro tape
    exact OneSidedTape.updateAndMove_toBounded (cfg.workTapes tape) (next.workTapes tape)
      capacity (hCfg tape) (hNext tape) (action.write tape) (action.workMove tape) (hTapes tape)

/-- Every one-sided run whose configurations stay within `capacity` restricts
to a bounded run. -/
theorem MultitapeNTM.oneSidedRun_restricts_toBounded {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) {initial final : OneSidedTMConfig Q Γ k n}
    (hInitial : initial.HeadsWithin capacity)
    (hRun : Relation.ReflTransGen
      (fun a b => M.oneSidedStep input a b ∧ a.HeadsWithin capacity ∧ b.HeadsWithin capacity)
      initial final) :
    ∃ hFinal : final.HeadsWithin capacity,
      Relation.ReflTransGen (M.step input capacity)
        (initial.toBounded capacity hInitial) (final.toBounded capacity hFinal) := by
  induction hRun with
  | refl => exact ⟨hInitial, Relation.ReflTransGen.refl⟩
  | @tail previous current hPrevious hStep ih =>
    rcases ih with ⟨hPrevHeads, hPrevRun⟩
    rcases hStep with ⟨hOneStep, _, hCurrHeads⟩
    refine ⟨hCurrHeads, Relation.ReflTransGen.tail hPrevRun ?_⟩
    exact M.oneSidedStep_restricts_toBounded input capacity hOneStep hPrevHeads hCurrHeads

/-- A space-bounded one-sided accepting run is also an unbounded accepting run. -/
theorem MultitapeNTM.acceptsOneSided_of_acceptsOneSidedWithin
    {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (hAccept : M.AcceptsOneSidedWithin input capacity) :
    M.AcceptsOneSided input := by
  rcases hAccept with ⟨final, hRun, hAcc⟩
  have hRun' : Relation.ReflTransGen (M.oneSidedStep input) M.oneSidedInitialConfig final := by
    clear hAcc
    induction hRun with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hStep ih => exact Relation.ReflTransGen.tail ih hStep.1
  exact ⟨final, hRun', hAcc⟩

/-- Acceptance using only a work-tape segment of `capacity` cells. -/
def MultitapeNTM.AcceptsWithinCapacity {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (capacity : ℕ) (hCapacity : 0 < capacity) : Prop :=
  ∃ final : TMConfig Q Γ k n capacity,
    Relation.ReflTransGen (M.step input capacity)
      (M.initialConfig capacity hCapacity) final ∧ M.accepting final.state

/-- One-sided space-`capacity` acceptance coincides with bounded-capacity
acceptance whenever `0 < capacity`. -/
theorem MultitapeNTM.acceptsOneSidedWithin_iff_acceptsWithinCapacity
    {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (hCapacity : 0 < capacity) :
    M.AcceptsOneSidedWithin input capacity ↔ M.AcceptsWithinCapacity input capacity hCapacity := by
  constructor
  · rintro ⟨final, hRun, hAcc⟩
    obtain ⟨hFinal, hBoundedRun⟩ :=
      M.oneSidedRun_restricts_toBounded input capacity (fun _ => hCapacity) hRun
    rw [M.oneSidedInitialConfig_toBounded capacity hCapacity] at hBoundedRun
    exact ⟨final.toBounded capacity hFinal, hBoundedRun, hAcc⟩
  · rintro ⟨final, hRun, hAcc⟩
    have hLifted := M.boundedRun_lifts_within input capacity hRun
    rw [M.initialConfig_toOneSided capacity hCapacity] at hLifted
    exact ⟨final.toOneSided M.blank, hLifted, hAcc⟩

/-- Deterministic one-sided transitions have at most one successor. -/
theorem MultitapeDTM.oneSidedStep_deterministic {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    {cfg next₁ next₂ : OneSidedTMConfig Q Γ k n}
    (h₁ : D.oneSidedStep input cfg next₁) (h₂ : D.oneSidedStep input cfg next₂) :
    next₁ = next₂ := by
  rcases h₁ with ⟨a₁, ha₁, hS₁, ih₁, hM₁, hIH₁, hT₁⟩
  rcases h₂ with ⟨a₂, ha₂, hS₂, ih₂, hM₂, hIH₂, hT₂⟩
  have haEq : a₁ = a₂ := by
    simp only [MultitapeDTM.toNTM] at ha₁ ha₂
    cases hTrans : D.transition cfg.state (readInput input cfg.inputHead) cfg.scannedWork with
    | none => simp [hTrans] at ha₁
    | some a =>
      simp [hTrans] at ha₁ ha₂
      exact ha₁.trans ha₂.symm
  subst haEq
  have hihEq : ih₁ = ih₂ := by
    have hSome : some ih₁ = some ih₂ := hM₁.symm.trans hM₂
    exact Option.some.inj hSome
  rcases next₁ with ⟨s₁, i₁, w₁⟩
  rcases next₂ with ⟨s₂, i₂, w₂⟩
  dsimp at hS₁ hS₂ hIH₁ hIH₂ hT₁ hT₂
  congr 1
  · exact hS₁.trans hS₂.symm
  · exact hIH₁.trans (hihEq.trans hIH₂.symm)
  · funext tape
    have hSome : some (w₁ tape) = some (w₂ tape) := (hT₁ tape).symm.trans (hT₂ tape)
    exact Option.some.inj hSome

/-- The bounded configuration space is finite. -/
theorem tmConfig_finite (Q Γ : Type*) (k n S : ℕ)
    [Fintype Q] [Fintype Γ] : Finite (TMConfig Q Γ k n S) := Finite.of_fintype _

/-- Cardinality of the bounded configuration space. -/
theorem tmConfig_card (Q Γ : Type*) (k n S : ℕ)
    [Fintype Q] [Fintype Γ] :
    Fintype.card (TMConfig Q Γ k n S) =
      Fintype.card Q * (n + 2) * ((Fintype.card Γ ^ S) * S) ^ k := by
  have hTape : Fintype.card (BoundedTape Γ S) = Fintype.card Γ ^ S * S := by
    rw [Fintype.card_congr (BoundedTape.equivProd S)]
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [Fintype.card_congr (TMConfig.equivProd k n S)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [hTape]
  simp [Nat.mul_assoc]

end SavitchLemma

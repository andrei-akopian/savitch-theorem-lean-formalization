module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Relation

import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# A finite-capacity multitape nondeterministic machine

Work tapes are represented by a cell function `Fin S → Γ` and a head position
in `Fin S`.  A computation at capacity `S` cannot move a work-tape head beyond
those `S` cells.  For each fixed input and capacity, configurations form a
finite type, which will later provide the IDs used by the abstract register
machine.
-/

namespace SavitchLemma

/-- A head movement by one cell, or no movement. -/
inductive TapeMove where
  | left
  | stay
  | right

/-- The read-only input tape has explicit end-marker symbols. -/
inductive InputSymbol (InputAlphabet : Type*) where
  | leftEnd
  | symbol (value : InputAlphabet)
  | rightEnd

/-- Read one cell of the input tape.  Positions `0` and `n + 1` hold the
left and right markers; the input symbols occupy positions `1` through `n`. -/
def readInput {InputAlphabet : Type*} {n : ℕ} (input : Fin n → InputAlphabet)
    (position : Fin (n + 2)) : InputSymbol InputAlphabet :=
  if hLeft : position.val = 0 then
    .leftEnd
  else if hRight : position.val = n + 1 then
    .rightEnd
  else
    .symbol (input ⟨position.val - 1, by omega⟩)

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

/-- Move a head without leaving its finite tape segment. -/
def moveHead (S : ℕ) (position : Fin S) : TapeMove → Option (Fin S)
  | .left =>
    if h : 0 < position.val then
      some ⟨position.val - 1, by omega⟩
    else
      none
  | .stay => some position
  | .right =>
    if h : position.val + 1 < S then
      some ⟨position.val + 1, h⟩
    else
      none

/-- Write the scanned cell and move the work-tape head. -/
def BoundedTape.updateAndMove {Γ : Type*} {S : ℕ} (tape : BoundedTape Γ S)
    (symbol : Γ) (movement : TapeMove) : Option (BoundedTape Γ S) := do
  match moveHead S tape.head movement with
  | none => none
  | some head => some ⟨fun i => if i = tape.head then symbol else tape.cells i, head⟩

/-- A machine configuration on a fixed input and fixed work-tape capacity. -/
structure TMConfig (Q Γ : Type*) (k n S : ℕ) where
  state : Q
  inputHead : Fin (n + 2)
  workTapes : Fin k → BoundedTape Γ S

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

/-- One possible nondeterministic transition action. -/
structure TMAction (Q Γ : Type*) (k : ℕ) where
  nextState : Q
  inputMove : TapeMove
  write : Fin k → Γ
  workMove : Fin k → TapeMove

/-- A multitape nondeterministic machine with finite-state data.  `transitions`
returns a finite list, so each machine step has finite branching. -/
structure MultitapeNTM (Q InputAlphabet Γ : Type*) (k : ℕ)
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ] where
  startState : Q
  blank : Γ
  accepting : Q → Prop
  transitions : Q → InputSymbol InputAlphabet → (Fin k → Γ) → List (TMAction Q Γ k)

/-- The initially blank work tapes and leftmost input-head position. -/
def MultitapeNTM.initialConfig {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (capacity : ℕ) (hCapacity : 0 < capacity) : TMConfig Q Γ k n capacity where
  state := M.startState
  inputHead := ⟨0, by omega⟩
  workTapes := fun _ => ⟨fun _ => M.blank, ⟨0, hCapacity⟩⟩

/-- The symbols currently scanned on all work tapes. -/
def TMConfig.scannedWork {Q Γ : Type*} {k n S : ℕ}
    (cfg : TMConfig Q Γ k n S) : Fin k → Γ :=
  fun tape => (cfg.workTapes tape).cells (cfg.workTapes tape).head

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

/-- Acceptance using only a work-tape segment of `capacity` cells. -/
def MultitapeNTM.AcceptsWithinCapacity {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (capacity : ℕ) (hCapacity : 0 < capacity) : Prop :=
  ∃ final : TMConfig Q Γ k n capacity,
    Relation.ReflTransGen (M.step input capacity)
      (M.initialConfig capacity hCapacity) final ∧ M.accepting final.state

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

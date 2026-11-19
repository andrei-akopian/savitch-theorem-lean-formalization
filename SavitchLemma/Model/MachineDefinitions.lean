module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Multitape Turing machine definitions for external review

This file isolates the **trusted definitions** needed to read and audit the
statement of Savitch's Theorem (`savitch_theorem_one_full` and its measurable
variants in `SavitchLemma/MainTheorem.lean`):

- Tape movement (`TapeMove`), input tape with end-markers (`InputSymbol`, `readInput`),
  and one-sided infinite work tapes (`OneSidedTape`, `moveOneSidedHead`,
  `OneSidedTape.updateAndMove`).
- Configurations (`OneSidedTMConfig`, `OneSidedTMConfig.HeadsWithin`) and
  nondeterministic / deterministic multitape Turing machines (`MultitapeNTM`,
  `MultitapeDTM`).
- Unbounded and space-bounded acceptance (`AcceptsOneSided`,
  `AcceptsOneSidedWithin`, `AcceptsLanguageWithinSpace`) and tape-constructible
  ("measurable") space functions (`HaltsScanningExactly`, `IsMeasurable`).

All internal proof machinery—finite-capacity `BoundedTape` / `TMConfig`,
lifting/restriction equivalences, and configuration-count formulas—lives in
`SavitchLemma/Model/MachineModel.lean` and downstream modules.
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

/-- Head movement on a finite tape of `S` cells (used for the `n + 2`-cell
input tape).  Moving off either end returns `none`. -/
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

/-- The usual one-sided infinite work tape. -/
structure OneSidedTape (Γ : Type*) where
  cells : ℕ → Γ
  head : ℕ

/-- Head movement on a one-sided infinite work tape.  Moving left at the origin `0`
is disallowed (`none`). -/
def moveOneSidedHead (position : ℕ) : TapeMove → Option ℕ
  | .left => if 0 < position then some (position - 1) else none
  | .stay => some position
  | .right => some (position + 1)

/-- Write one symbol and move on a one-sided infinite tape. -/
def OneSidedTape.updateAndMove {Γ : Type*} (tape : OneSidedTape Γ)
    (symbol : Γ) (movement : TapeMove) : Option (OneSidedTape Γ) :=
  match moveOneSidedHead tape.head movement with
  | none => none
  | some head => some ⟨fun i => if i = tape.head then symbol else tape.cells i, head⟩

/-- A machine configuration on a read-only input of length `n` and `k`
one-sided infinite work tapes. -/
structure OneSidedTMConfig (Q Γ : Type*) (k n : ℕ) where
  state : Q
  inputHead : Fin (n + 2)
  workTapes : Fin k → OneSidedTape Γ

/-- The symbols scanned on the one-sided work tapes. -/
def OneSidedTMConfig.scannedWork {Q Γ : Type*} {k n : ℕ}
    (cfg : OneSidedTMConfig Q Γ k n) : Fin k → Γ :=
  fun tape => (cfg.workTapes tape).cells (cfg.workTapes tape).head

/-- All work-tape heads in a one-sided configuration lie strictly below `S`
(equivalently, only cells `0 .. S - 1` are ever visited on one-sided tapes
starting at `0`). -/
def OneSidedTMConfig.HeadsWithin {Q Γ : Type*} {k n : ℕ}
    (cfg : OneSidedTMConfig Q Γ k n) (S : ℕ) : Prop :=
  ∀ tape : Fin k, (cfg.workTapes tape).head < S

/-- One possible transition action. -/
structure TMAction (Q Γ : Type*) (k : ℕ) where
  nextState : Q
  inputMove : TapeMove
  write : Fin k → Γ
  workMove : Fin k → TapeMove

/-- A multitape nondeterministic Turing machine with finite-state data.
`transitions` returns a finite list, so each machine step has finite branching. -/
structure MultitapeNTM (Q InputAlphabet Γ : Type*) (k : ℕ)
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ] where
  startState : Q
  blank : Γ
  accepting : Q → Prop
  transitions : Q → InputSymbol InputAlphabet → (Fin k → Γ) → List (TMAction Q Γ k)

/-- One nondeterministic transition on one-sided infinite work tapes. -/
def MultitapeNTM.oneSidedStep {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (cfg next : OneSidedTMConfig Q Γ k n) : Prop :=
  ∃ action,
    action ∈ M.transitions cfg.state (readInput input cfg.inputHead) cfg.scannedWork ∧
    next.state = action.nextState ∧
    ∃ inputHead, moveHead (n + 2) cfg.inputHead action.inputMove = some inputHead ∧
      next.inputHead = inputHead ∧
      ∀ tape : Fin k,
        (cfg.workTapes tape).updateAndMove (action.write tape) (action.workMove tape) =
          some (next.workTapes tape)

/-- The initial configuration on one-sided infinite work tapes (all heads at `0`,
all work cells blank). -/
def MultitapeNTM.oneSidedInitialConfig {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) : OneSidedTMConfig Q Γ k n where
  state := M.startState
  inputHead := ⟨0, by omega⟩
  workTapes := fun _ => ⟨fun _ => M.blank, 0⟩

/-- Acceptance on unbounded one-sided work tapes. -/
def MultitapeNTM.AcceptsOneSided {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet) : Prop :=
  ∃ final : OneSidedTMConfig Q Γ k n,
    Relation.ReflTransGen (M.oneSidedStep input) M.oneSidedInitialConfig final ∧
    M.accepting final.state

/-- Acceptance on one-sided work tapes with all heads staying below `capacity`. -/
def MultitapeNTM.AcceptsOneSidedWithin {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) : Prop :=
  ∃ final : OneSidedTMConfig Q Γ k n,
    Relation.ReflTransGen
      (fun a b => M.oneSidedStep input a b ∧ a.HeadsWithin capacity ∧ b.HeadsWithin capacity)
      M.oneSidedInitialConfig final ∧ M.accepting final.state

/-- A language `A` is accepted by `M` within storage `L(n)` when every input in `A`
has an accepting run with all work-tape heads `< L(n)`, and `M` accepts no input
outside `A` (even on unbounded tapes). -/
def MultitapeNTM.AcceptsLanguageWithinSpace {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ) : Prop :=
  (∀ n (input : Fin n → InputAlphabet), A n input → M.AcceptsOneSidedWithin input (L n)) ∧
  (∀ n (input : Fin n → InputAlphabet), M.AcceptsOneSided input → A n input)

/-- A deterministic multitape Turing machine has at most one transition per
state and scanned symbols. -/
structure MultitapeDTM (Q InputAlphabet Γ : Type*) (k : ℕ)
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ] where
  startState : Q
  blank : Γ
  accepting : Q → Prop
  transition : Q → InputSymbol InputAlphabet → (Fin k → Γ) → Option (TMAction Q Γ k)

/-- View a deterministic multitape machine as a nondeterministic one. -/
def MultitapeDTM.toNTM {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) : MultitapeNTM Q InputAlphabet Γ k where
  startState := D.startState
  blank := D.blank
  accepting := D.accepting
  transitions q inSym workSyms := (D.transition q inSym workSyms).toList

/-- One-sided acceptance for a deterministic machine. -/
def MultitapeDTM.AcceptsOneSided {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet) : Prop :=
  D.toNTM.AcceptsOneSided input

/-- One-sided space-bounded acceptance for a deterministic machine. -/
def MultitapeDTM.AcceptsOneSidedWithin {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) : Prop :=
  D.toNTM.AcceptsOneSidedWithin input capacity

/-- Deterministic language acceptance within storage `L(n)`. -/
def MultitapeDTM.AcceptsLanguageWithinSpace {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ) : Prop :=
  D.toNTM.AcceptsLanguageWithinSpace A L

/-- One step of a deterministic machine on one-sided tapes. -/
def MultitapeDTM.oneSidedStep {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (cfg next : OneSidedTMConfig Q Γ k n) : Prop :=
  D.toNTM.oneSidedStep input cfg next

/-- A 1-tape deterministic run witnesses exact space `S` if every visited head
position is below `S`, some visited head position reaches `S - 1`, and the final
configuration has no defined transition. -/
def MultitapeDTM.HaltsScanningExactly {Q InputAlphabet Γ : Type*}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ 1) {n : ℕ}
    (input : Fin n → InputAlphabet) (S : ℕ) : Prop :=
  ∃ final : OneSidedTMConfig Q Γ 1 n,
    Relation.ReflTransGen
      (fun a b => D.oneSidedStep input a b ∧ a.HeadsWithin S ∧ b.HeadsWithin S)
      D.toNTM.oneSidedInitialConfig final ∧
    D.transition final.state (readInput input final.inputHead) final.scannedWork = none ∧
    (0 < S → ∃ mid : OneSidedTMConfig Q Γ 1 n,
      Relation.ReflTransGen
        (fun a b => D.oneSidedStep input a b ∧ a.HeadsWithin S ∧ b.HeadsWithin S)
        D.toNTM.oneSidedInitialConfig mid ∧
      (mid.workTapes 0).head + 1 = S)

/-- A space function `L` is measurable over `InputAlphabet` when a single-work-tape
deterministic Turing machine halts after scanning `L(n)` work squares on every
input of length `n`. -/
def IsMeasurable (InputAlphabet : Type*) [Fintype InputAlphabet] (L : ℕ → ℕ) : Prop :=
  ∃ (Q Γ : Type) (_ : Fintype Q) (_ : Fintype Γ)
    (D : MultitapeDTM Q InputAlphabet Γ 1),
    ∀ (n : ℕ) (input : Fin n → InputAlphabet), D.HaltsScanningExactly input (L n)

end SavitchLemma

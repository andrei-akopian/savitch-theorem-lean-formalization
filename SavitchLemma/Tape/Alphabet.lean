module

public import Mathlib.Data.Fintype.Basic
public import SavitchLemma.Model.ConcreteEncoding
public import SavitchLemma.Model.TMCombinators

@[expose] public section

/-!
# Tape alphabet and matching

Defines `SimSym` and the `TapeMatches` invariant between a one-sided tape and a finite symbol list.
-/

namespace SavitchLemma

/-- Tape alphabet for the concrete 5-tape Savitch simulator. -/
inductive SimSym where
  | blank
  | leftMark
  | bit (b : Bool)
  | tag (b : Bool)
  | sep
  | srcSep
  | endMark
  deriving DecidableEq

/-- Explicit equivalence between `SimSym` and `Fin 9`. -/
def SimSym.equivFin : SimSym ≃ Fin 9 where
  toFun
    | .blank => 0
    | .leftMark => 1
    | .bit false => 2
    | .bit true => 3
    | .tag false => 4
    | .tag true => 5
    | .sep => 6
    | .srcSep => 7
    | .endMark => 8
  invFun
    | 0 => .blank
    | 1 => .leftMark
    | 2 => .bit false
    | 3 => .bit true
    | 4 => .tag false
    | 5 => .tag true
    | 6 => .sep
    | 7 => .srcSep
    | 8 => .endMark
  left_inv x := by cases x with | bit b => cases b <;> rfl | tag b => cases b <;> rfl | _ => rfl
  right_inv i := by revert i; decide

instance : Fintype SimSym := Fintype.ofEquiv (Fin 9) SimSym.equivFin.symm

/-- A one-sided tape matches a finite symbol list `contents` with head at `pos`. -/
def TapeMatches (tape : OneSidedTape SimSym) (contents : List SimSym) (pos : ℕ) : Prop :=
  tape.head = pos ∧ ∀ i : ℕ, tape.cells i = contents[i]?.getD .blank

theorem list_set_append_mid {α : Type*} (pref : List α) (x : α) (suf : List α) (y : α) :
    (pref ++ x :: suf).set pref.length y = pref ++ y :: suf := by
  induction pref with
  | nil => rfl
  | cons a as ih => simp [List.set_cons_succ, ih]

theorem list_get_append_mid {α : Type*} (pref : List α) (x : α) (suf : List α) :
    (pref ++ x :: suf)[pref.length]'(by simp) = x := by
  induction pref with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem TapeMatches.head_eq {tape : OneSidedTape SimSym} {contents : List SimSym} {pos : ℕ}
    (h : TapeMatches tape contents pos) : tape.head = pos := h.1

theorem TapeMatches.read {tape : OneSidedTape SimSym} {contents : List SimSym} {pos : ℕ}
    (h : TapeMatches tape contents pos) :
    tape.cells tape.head = contents[pos]?.getD .blank := by
  rw [h.1]
  exact h.2 pos

theorem TapeMatches.read_lt {tape : OneSidedTape SimSym} {contents : List SimSym} {pos : ℕ}
    (h : TapeMatches tape contents pos) (hLt : pos < contents.length) :
    tape.cells tape.head = contents[pos] := by
  rw [h.read, List.getElem?_eq_getElem hLt]
  rfl

theorem TapeMatches.initial :
    TapeMatches ⟨fun _ => .blank, 0⟩ [] 0 :=
  ⟨rfl, fun i => by simp⟩

theorem TapeMatches.update_set {tape : OneSidedTape SimSym} {contents : List SimSym}
    {pos : ℕ} (h : TapeMatches tape contents pos) (sym : SimSym) (mv : TapeMove)
    {nextPos : ℕ} (hMove : moveOneSidedHead pos mv = some nextPos)
    (hLt : pos < contents.length) :
    ∃ nextTape, tape.updateAndMove sym mv = some nextTape ∧
      TapeMatches nextTape (contents.set pos sym) nextPos := by
  have hMove' : moveOneSidedHead tape.head mv = some nextPos := by rw [h.1]; exact hMove
  refine ⟨⟨fun i => if i = tape.head then sym else tape.cells i, nextPos⟩, ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove']
  · intro i
    dsimp only
    rw [h.1]
    by_cases hi : i = pos
    · subst hi
      simp [List.getElem?_set_self hLt]
    · simp only [hi, ↓reduceIte]
      rw [h.2 i, List.getElem?_set_ne (Ne.symm hi)]

theorem TapeMatches.update_append {tape : OneSidedTape SimSym} {contents : List SimSym}
    (h : TapeMatches tape contents contents.length) (sym : SimSym) :
    ∃ nextTape, tape.updateAndMove sym .right = some nextTape ∧
      TapeMatches nextTape (contents ++ [sym]) (contents.length + 1) := by
  have hMove : moveOneSidedHead tape.head .right = some (contents.length + 1) := by
    simp [moveOneSidedHead, h.1]
  refine ⟨⟨fun i => if i = tape.head then sym else tape.cells i, contents.length + 1⟩,
    ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove]
  · intro i
    dsimp only
    rw [h.1]
    by_cases hi : i = contents.length
    · subst hi
      simp
    · simp only [hi, ↓reduceIte]
      rw [h.2 i]
      by_cases hLt : i < contents.length
      · rw [List.getElem?_append_left hLt]
      · have hGt : contents.length < i := by omega
        have hNone1 : contents[i]? = none := List.getElem?_eq_none (by omega)
        have hNone2 : (contents ++ [sym])[i]? = none := by
          apply List.getElem?_eq_none
          simp; omega
        rw [hNone1, hNone2]

theorem TapeMatches.update_append_left {tape : OneSidedTape SimSym} {contents : List SimSym}
    (h : TapeMatches tape contents contents.length) (hPos : 1 ≤ contents.length) (sym : SimSym) :
    ∃ nextTape, tape.updateAndMove sym .left = some nextTape ∧
      TapeMatches nextTape (contents ++ [sym]) (contents.length - 1) := by
  have hMove : moveOneSidedHead tape.head .left = some (contents.length - 1) := by
    simp [moveOneSidedHead, h.1, show contents.length ≠ 0 by omega]
  refine ⟨⟨fun i => if i = tape.head then sym else tape.cells i, contents.length - 1⟩,
    ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove]
  · intro i
    dsimp only
    rw [h.1]
    by_cases hi : i = contents.length
    · subst hi
      simp
    · simp only [hi, ↓reduceIte]
      rw [h.2 i]
      by_cases hLt : i < contents.length
      · rw [List.getElem?_append_left hLt]
      · have hGt : contents.length < i := by omega
        have hNone1 : contents[i]? = none := List.getElem?_eq_none (by omega)
        have hNone2 : (contents ++ [sym])[i]? = none := by
          apply List.getElem?_eq_none
          simp; omega
        rw [hNone1, hNone2]

theorem TapeMatches.update_keep {tape : OneSidedTape SimSym} {contents : List SimSym}
    {pos : ℕ} (h : TapeMatches tape contents pos) (mv : TapeMove)
    {nextPos : ℕ} (hMove : moveOneSidedHead pos mv = some nextPos) :
    ∃ nextTape, tape.updateAndMove (tape.cells tape.head) mv = some nextTape ∧
      TapeMatches nextTape contents nextPos := by
  have hMove' : moveOneSidedHead tape.head mv = some nextPos := by rw [h.1]; exact hMove
  refine ⟨⟨fun i => if i = tape.head then tape.cells tape.head else tape.cells i, nextPos⟩,
    ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove']
  · intro i
    dsimp only
    by_cases hi : i = tape.head
    · subst hi
      simpa using h.2 tape.head
    · simp only [hi, ↓reduceIte]
      exact h.2 i

end SavitchLemma

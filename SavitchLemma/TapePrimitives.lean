module

public import Mathlib.Data.Fintype.Basic
public import SavitchLemma.ConcreteEncoding
public import SavitchLemma.TMCombinators

@[expose] public section

/-!
# Concrete tape alphabet and verified multi-tape primitives

This module defines the 9-symbol alphabet `SimSym` used by the deterministic
Savitch simulator on a 5-tape workspace, the `TapeMatches` invariant relating a
`OneSidedTape SimSym` to a finite `List SimSym`, and small verified `TMComponent`
subroutines (rewinding, clearing, copying, incrementing, decrementing, and
comparing bit blocks).
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

/-- Helper to construct a `TMAction` that modifies only one work tape `t`
(leaving the input head and all other work tapes stationary and unchanged). -/
def singleTapeAction {Q : Type*} {k : ℕ} (next : Q) (t : Fin k)
    (writeSym : SimSym) (mv : TapeMove) (scanned : Fin k → SimSym) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write i := if i = t then writeSym else scanned i
  workMove i := if i = t then mv else .stay

/-- Helper to construct a `TMAction` that modifies two distinct work tapes `t₁, t₂`. -/
def twoTapeAction {Q : Type*} {k : ℕ} (next : Q) (t₁ t₂ : Fin k)
    (w₁ w₂ : SimSym) (m₁ m₂ : TapeMove) (scanned : Fin k → SimSym) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write i := if i = t₁ then w₁ else if i = t₂ then w₂ else scanned i
  workMove i := if i = t₁ then m₁ else if i = t₂ then m₂ else .stay

theorem singleTapeAction_apply {Q : Type*} {k : ℕ} (next : Q) (t : Fin k)
    (writeSym : SimSym) (mv : TapeMove)
    (tapes : Fin k → OneSidedTape SimSym)
    {nextTape : OneSidedTape SimSym}
    (hUpd : (tapes t).updateAndMove writeSym mv = some nextTape) :
    ∀ i : Fin k,
      (tapes i).updateAndMove
        ((singleTapeAction next t writeSym mv (fun j => (tapes j).cells (tapes j).head)).write i)
        ((singleTapeAction next t writeSym mv (fun j => (tapes j).cells (tapes j).head)).workMove i) =
      some (if i = t then nextTape else tapes i) := by
  intro i
  by_cases hi : i = t
  · subst hi
    simpa [singleTapeAction] using hUpd
  · simp only [singleTapeAction]
    simp only [hi, ↓reduceIte]
    cases hT : tapes i with
    | mk cells head =>
      simp [OneSidedTape.updateAndMove, moveOneSidedHead]
      funext j
      by_cases hj : j = head <;> simp [hj]

theorem twoTapeAction_apply {Q : Type*} {k : ℕ} (next : Q) (t₁ t₂ : Fin k)
    (hNe : t₁ ≠ t₂) (w₁ w₂ : SimSym) (m₁ m₂ : TapeMove)
    (tapes : Fin k → OneSidedTape SimSym)
    {nt₁ nt₂ : OneSidedTape SimSym}
    (hUpd₁ : (tapes t₁).updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : (tapes t₂).updateAndMove w₂ m₂ = some nt₂) :
    ∀ i : Fin k,
      (tapes i).updateAndMove
        ((twoTapeAction next t₁ t₂ w₁ w₂ m₁ m₂ (fun j => (tapes j).cells (tapes j).head)).write i)
        ((twoTapeAction next t₁ t₂ w₁ w₂ m₁ m₂ (fun j => (tapes j).cells (tapes j).head)).workMove i) =
      some (if i = t₁ then nt₁ else if i = t₂ then nt₂ else tapes i) := by
  intro i
  by_cases h1 : i = t₁
  · subst h1
    simpa [twoTapeAction] using hUpd₁
  · by_cases h2 : i = t₂
    · subst h2
      simpa [twoTapeAction, hNe.symm] using hUpd₂
    · simp only [twoTapeAction, h1, h2, ↓reduceIte]
      cases hT : tapes i with
      | mk cells head =>
        simp [OneSidedTape.updateAndMove, moveOneSidedHead]
        funext j
        by_cases hj : j = head <;> simp [hj]

theorem singleTape_atom_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → SimSym → (Exit × SimSym × TapeMove))
    (t : Fin k) (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hHeads : ∀ j, (tapes j).head < bound j)
    {nextTape : OneSidedTape SimSym}
    (hUpd : (tapes t).updateAndMove
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).2.1
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).2.2 = some nextTape)
    (hNextHead : nextTape.head < bound t) :
    (TMComponent.atom fun inSym scanned =>
      let res := f inSym (scanned t)
      singleTapeAction res.1 t res.2.1 res.2.2 scanned).ReachesExit input bound tapes inHead
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).1
      (fun j => if j = t then nextTape else tapes j) inHead := by
  let res := f (readInput input inHead) ((tapes t).cells (tapes t).head)
  have hAtom := TMComponent.atom_reachesExit
    (fun inSym scanned =>
      let res := f inSym (scanned t)
      singleTapeAction res.1 t res.2.1 res.2.2 scanned)
    input bound tapes inHead hHeads inHead
    (by simp [singleTapeAction, moveHead])
    (fun j => if j = t then nextTape else tapes j)
    (fun j => singleTapeAction_apply res.1 t res.2.1 res.2.2 tapes hUpd j)
    (fun j => by
      by_cases hj : j = t
      · subst hj; simpa using hNextHead
      · simp only [hj, ↓reduceIte]; exact hHeads j)
  exact hAtom

theorem twoTape_atom_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → SimSym → SimSym →
      (Exit × SimSym × SimSym × TapeMove × TapeMove))
    (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hHeads : ∀ j, (tapes j).head < bound j)
    {nt₁ nt₂ : OneSidedTape SimSym}
    (hUpd₁ : (tapes t₁).updateAndMove
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.1
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.2.1 = some nt₁)
    (hUpd₂ : (tapes t₂).updateAndMove
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.1
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.2.2 = some nt₂)
    (hHead₁ : nt₁.head < bound t₁) (hHead₂ : nt₂.head < bound t₂) :
    (TMComponent.atom fun inSym scanned =>
      let res := f inSym (scanned t₁) (scanned t₂)
      twoTapeAction res.1 t₁ t₂ res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 scanned).ReachesExit
      input bound tapes inHead
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).1
      (fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else tapes j) inHead := by
  let res := f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
    ((tapes t₂).cells (tapes t₂).head)
  have hAtom := TMComponent.atom_reachesExit
    (fun inSym scanned =>
      let res := f inSym (scanned t₁) (scanned t₂)
      twoTapeAction res.1 t₁ t₂ res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 scanned)
    input bound tapes inHead hHeads inHead
    (by simp [twoTapeAction, moveHead])
    (fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else tapes j)
    (fun j => twoTapeAction_apply res.1 t₁ t₂ hNe
      res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 tapes hUpd₁ hUpd₂ j)
    (fun j => by
      by_cases h1 : j = t₁
      · subst h1; simpa using hHead₁
      · by_cases h2 : j = t₂
        · subst h2; simpa [h1] using hHead₂
        · simp only [h1, h2, ↓reduceIte]; exact hHeads j)
  exact hAtom

/-- Initialize cell `0` on all `k` work tapes to `.leftMark` and move each head
to cell `1`. -/
def initLeftMarksComp (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  TMComponent.atom fun _ _ =>
    { nextState := ()
      inputMove := .stay
      write := fun _ => .leftMark
      workMove := fun _ => .right }

theorem initLeftMarksComp_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ) (hBound : ∀ t, 2 ≤ bound t)
    (inHead : Fin (n + 2)) :
    (initLeftMarksComp InputAlphabet k).ReachesExit input bound
      (fun _ => ⟨fun _ => .blank, 0⟩) inHead ()
      (fun _ => ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩) inHead := by
  apply TMComponent.atom_reachesExit
  · intro t; exact Nat.lt_of_lt_of_le (by decide) (hBound t)
  · simp [moveHead]
  · intro t
    simp [OneSidedTape.updateAndMove, moveOneSidedHead]
  · intro t; exact Nat.lt_of_lt_of_le (by decide) (hBound t)

theorem tapeMatches_after_leftMark :
    TapeMatches ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩ [.leftMark] 1 := by
  refine ⟨rfl, fun i => ?_⟩
  cases i with
  | zero => simp
  | succ i' => simp

/-- Rewind tape `t` left until `.leftMark`, then step right once to cell `1`. -/
def rewindStepFn {InputAlphabet : Type*} (_ : InputSymbol InputAlphabet) :
    SimSym → ((Unit ⊕ Unit) × SimSym × TapeMove)
  | .leftMark => (.inr (), .leftMark, .right)
  | sym => (.inl (), sym, .left)

def rewindComp (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent Unit InputAlphabet SimSym k (Unit ⊕ Unit) :=
  TMComponent.atom fun inSym scanned =>
    let res := rewindStepFn inSym (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned

def rewindTape (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  (rewindComp InputAlphabet t).loop

theorem rewindTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (contents : List SimSym) (_hNonEmpty : 1 ≤ contents.length)
    (hLeftMark : contents[0] = .leftMark)
    (hNoOtherLeft : ∀ i, 1 ≤ i → i < contents.length → contents[i]? ≠ some .leftMark)
    (hBound : contents.length ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (pos : ℕ) (_hPos : 1 ≤ pos) (hPosLt : pos < contents.length)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ finalTapes,
      (rewindTape InputAlphabet t).ReachesExit input bound initTapes inHead () finalTapes inHead ∧
      TapeMatches (finalTapes t) contents 1 ∧
      (∀ j, j ≠ t → finalTapes j = initTapes j) := by
  let Inv : (Fin k → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ t → tapes j = initTapes j) ∧
    ∃ p, p < contents.length ∧ TapeMatches (tapes t) contents p
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (rewindComp InputAlphabet t).ReachesExit input bound tapes ih (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧ (tapes' t).head < (tapes t).head) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (rewindComp InputAlphabet t).ReachesExit input bound tapes ih (.inr e) tapes' ih' ∧
        ih' = inHead ∧ TapeMatches (tapes' t) contents 1 ∧
        (∀ j, j ≠ t → tapes' j = initTapes j)) := by
    intro tapes ih hInv
    rcases hInv with ⟨hIhEq, hOthers, p, hpLt, hpMatch⟩
    subst ih
    have hHeadBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; rw [hpMatch.head_eq]; exact Nat.lt_of_lt_of_le hpLt hBound
      · rw [hOthers j hj]; exact hOtherBounds j hj
    cases p with
    | zero =>
      have hRead : (tapes t).cells (tapes t).head = .leftMark := by
        rw [hpMatch.read_lt hpLt]
        exact hLeftMark
      have hMove : moveOneSidedHead 0 .right = some 1 := rfl
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .leftMark .right hMove hpLt
      have hSetSame : contents.set 0 .leftMark = contents := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp [hLeftMark]
          | succ i' => simp
      rw [hSetSame] at hNextMatch
      right
      refine ⟨(), fun j => if j = t then nextTape else tapes j, inHead, ?_, rfl, ?_, ?_⟩
      · have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet) rewindStepFn
          t input bound tapes inHead hHeadBounds
          (by simpa [rewindStepFn, hRead] using hUpd)
          (by rw [hNextMatch.head_eq]; omega)
        simpa [rewindComp, rewindStepFn, hRead] using hAtom
      · simpa using hNextMatch
      · intro j hj
        simp [hj, hOthers j hj]
    | succ p' =>
      have hSymNe : contents[p' + 1] ≠ .leftMark := by
        have h := hNoOtherLeft (p' + 1) (by omega) hpLt
        rw [List.getElem?_eq_getElem hpLt] at h
        simpa using h
      have hRead : (tapes t).cells (tapes t).head = contents[p' + 1] :=
        hpMatch.read_lt hpLt
      have hNotLeft : (tapes t).cells (tapes t).head ≠ .leftMark := by
        rw [hRead]; exact hSymNe
      have hMove : moveOneSidedHead (p' + 1) .left = some p' := by
        simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_keep .left hMove
      have hFnEq : rewindStepFn (readInput input inHead) ((tapes t).cells (tapes t).head) =
          (.inl (), (tapes t).cells (tapes t).head, .left) := by
        cases hC : (tapes t).cells (tapes t).head
        · rfl
        · exact (hNotLeft hC).elim
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      left
      refine ⟨fun j => if j = t then nextTape else tapes j, inHead, ?_, ?_, ?_⟩
      · have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet) rewindStepFn
          t input bound tapes inHead hHeadBounds
          (by simpa [hFnEq] using hUpd)
          (by rw [hNextMatch.head_eq]; omega)
        simpa [rewindComp, hFnEq] using hAtom
      · refine ⟨rfl, fun j hj => by simp [hj, hOthers j hj], p', by omega, by simpa using hNextMatch⟩
      · simp [hpMatch.head_eq, hNextMatch.head_eq]
  have hInitInv : Inv initTapes inHead :=
    ⟨rfl, fun _ _ => rfl, pos, hPosLt, hMatch⟩
  obtain ⟨_, finalTapes, _, hLoop, rfl, hFinalMatch, hOthers⟩ :=
    TMComponent.loop_reachesExit (rewindComp InputAlphabet t) input bound Inv
      (fun tapes _ => (tapes t).head)
      (fun _ tapes ih => ih = inHead ∧ TapeMatches (tapes t) contents 1 ∧
        (∀ j, j ≠ t → tapes j = initTapes j))
      hStep initTapes inHead hInitInv
  exact ⟨finalTapes, hLoop, hFinalMatch, hOthers⟩

/-- Generic single-tape scan loop on tape `t`: each step reads the scanned symbol
on `t` and either continues (`.inl ()`) or exits (`.inr e`) with a write and move. -/
def scanTape {InputAlphabet : Type*} {k : ℕ} {Exit : Type*} (t : Fin k)
    (f : SimSym → (Unit ⊕ Exit) × SimSym × TapeMove) :
    TMComponent Unit InputAlphabet SimSym k Exit :=
  (TMComponent.atom fun _ scanned =>
    let res := f (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned).loop

theorem scanTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (t : Fin k) (f : SimSym → (Unit ⊕ Exit) × SimSym × TapeMove)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (Inv : OneSidedTape SimSym → Prop)
    (measure : OneSidedTape SimSym → ℕ)
    (Post : Exit → OneSidedTape SimSym → Prop)
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hStep : ∀ tape, Inv tape → tape.head < bound t →
      ∃ nextTape,
        tape.updateAndMove (f (tape.cells tape.head)).2.1 (f (tape.cells tape.head)).2.2 =
          some nextTape ∧
        nextTape.head < bound t ∧
        ((f (tape.cells tape.head)).1 = .inl () → Inv nextTape ∧ measure nextTape < measure tape) ∧
        (∀ e, (f (tape.cells tape.head)).1 = .inr e → Post e nextTape))
    (hInit : Inv (initTapes t)) (hInitBound : (initTapes t).head < bound t) :
    ∃ e finalTape,
      (scanTape (InputAlphabet := InputAlphabet) t f).ReachesExit input bound
        initTapes inHead e (fun j => if j = t then finalTape else initTapes j) inHead ∧
      Post e finalTape := by
  let FullInv : (Fin k → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧ (∀ j, j ≠ t → tapes j = initTapes j) ∧
    Inv (tapes t) ∧ (tapes t).head < bound t
  let Body := TMComponent.atom (InputAlphabet := InputAlphabet) fun _ scanned =>
    let res := f (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned
  have hBodyStep : ∀ tapes ih, FullInv tapes ih →
      (∃ tapes' ih', Body.ReachesExit input bound tapes ih (.inl ()) tapes' ih' ∧
        FullInv tapes' ih' ∧ measure (tapes' t) < measure (tapes t)) ∨
      (∃ e : Exit, ∃ tapes' ih', Body.ReachesExit input bound tapes ih (.inr e) tapes' ih' ∧
        ih' = inHead ∧ (∀ j, j ≠ t → tapes' j = initTapes j) ∧ Post e (tapes' t)) := by
    intro tapes ih hInv
    rcases hInv with ⟨hIhEq, hOthers, hInvT, hHeadT⟩
    subst ih
    have hHeadBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; exact hHeadT
      · rw [hOthers j hj]; exact hOtherBounds j hj
    obtain ⟨nextTape, hUpd, hNextHead, hInl, hInr⟩ := hStep (tapes t) hInvT hHeadT
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ s => f s) t input bound tapes inHead hHeadBounds hUpd hNextHead
    cases hExit : (f ((tapes t).cells (tapes t).head)).1 with
    | inl u =>
      cases u
      rw [hExit] at hAtom
      obtain ⟨hInvNext, hMeas⟩ := hInl hExit
      left
      refine ⟨fun j => if j = t then nextTape else tapes j, inHead, hAtom, ?_, ?_⟩
      · refine ⟨rfl, fun j hj => by simp [hj, hOthers j hj], ?_⟩
        simpa using And.intro hInvNext hNextHead
      · simpa using hMeas
    | inr e =>
      rw [hExit] at hAtom
      right
      refine ⟨e, fun j => if j = t then nextTape else tapes j, inHead, hAtom, rfl, ?_, ?_⟩
      · intro j hj; simp [hj, hOthers j hj]
      · simpa using hInr e hExit
  obtain ⟨e, finalTapes, _, hLoop, rfl, hOthers, hPost⟩ :=
    TMComponent.loop_reachesExit Body input bound FullInv
      (fun tapes _ => measure (tapes t))
      (fun e tapes ih => ih = inHead ∧ (∀ j, j ≠ t → tapes j = initTapes j) ∧ Post e (tapes t))
      hBodyStep initTapes inHead ⟨rfl, fun _ _ => rfl, hInit, hInitBound⟩
  have hTapesEq : finalTapes = fun j => if j = t then finalTapes t else initTapes j := by
    funext j
    by_cases hj : j = t
    · subst hj; simp
    · simp [hj, hOthers j hj]
  rw [hTapesEq] at hLoop
  exact ⟨e, finalTapes t, hLoop, hPost⟩

/-- Scan tape `t` right until `.endMark` (overwriting cells `≥ 1` with `.blank`,
keeping `.leftMark` at cell `0`), then rewind to cell `1`. -/
def clearRightStep : SimSym → (Unit ⊕ Unit) × SimSym × TapeMove
  | .endMark => (.inr (), .blank, .stay)
  | _ => (.inl (), .blank, .right)

def clearTape (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent (Unit ⊕ Unit) InputAlphabet SimSym k Unit :=
  (scanTape (InputAlphabet := InputAlphabet) t clearRightStep).seq (rewindTape InputAlphabet t)

theorem clearTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (prefixSyms : List SimSym) (hBound : prefixSyms.length + 2 ≤ bound t)
    (hNoEnd : ∀ s ∈ prefixSyms, s ≠ .endMark)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) (.leftMark :: prefixSyms ++ [.endMark]) 1) :
    ∃ finalTape,
      (clearTape InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then finalTape else initTapes j) inHead ∧
      TapeMatches finalTape [.leftMark] 1 := by
  let orig : List SimSym := .leftMark :: prefixSyms ++ [.endMark]
  let L := orig.length
  have hL : L = prefixSyms.length + 2 := by
    simp [L, orig]
  let blankList : List SimSym := (List.replicate L SimSym.blank).set 0 .leftMark
  let Inv : OneSidedTape SimSym → Prop := fun tape =>
    ∃ p, 1 ≤ p ∧ p < L ∧
      TapeMatches tape ((List.replicate p SimSym.blank).set 0 .leftMark ++ orig.drop p) p
  let Post : Unit → OneSidedTape SimSym → Prop := fun _ tape => TapeMatches tape blankList (L - 1)
  have hStep : ∀ tape, Inv tape → tape.head < bound t →
      ∃ nextTape,
        tape.updateAndMove (clearRightStep (tape.cells tape.head)).2.1
          (clearRightStep (tape.cells tape.head)).2.2 = some nextTape ∧
        nextTape.head < bound t ∧
        ((clearRightStep (tape.cells tape.head)).1 = .inl () →
          Inv nextTape ∧ (L - nextTape.head) < (L - tape.head)) ∧
        (∀ e, (clearRightStep (tape.cells tape.head)).1 = .inr e → Post e nextTape) := by
    intro tape ⟨p, hp1, hpLt, hpMatch⟩ hHeadLt
    let curList : List SimSym := (List.replicate p SimSym.blank).set 0 .leftMark ++ orig.drop p
    have hCurLen : curList.length = L := by
      simp [curList, L]
      omega
    have hpCur : p < curList.length := by rw [hCurLen]; exact hpLt
    have hRead : tape.cells tape.head = orig[p] := by
      rw [hpMatch.read_lt hpCur]
      have hPrefLen : ((List.replicate p SimSym.blank).set 0 .leftMark).length = p := by simp
      have hGe : ((List.replicate p SimSym.blank).set 0 .leftMark).length ≤ p := hPrefLen.le
      simp [curList, List.getElem_append_right hGe, hPrefLen]
    by_cases hpLast : p = L - 1
    · have hpVal : p = prefixSyms.length + 1 := by omega
      have hEnd : orig[p] = .endMark := by
        simp only [orig, hpVal, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        simp
      have hReadEnd : tape.cells tape.head = .endMark := hRead.trans hEnd
      have hMove : moveOneSidedHead p .stay = some p := rfl
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .blank .stay hMove hpCur
      have hSetEq : curList.set p .blank = blankList := by
        apply List.ext_getElem
        · simp [hCurLen, blankList]
        · intro i hi1 hi2
          have hiL : i < L := by simpa [hCurLen] using hi1
          by_cases hip : i = p
          · simp [hip, blankList, List.getElem_set_ne (by omega : 0 ≠ p)]
          · rw [List.getElem_set_ne (Ne.symm hip)]
            have hiLtP : i < p := by omega
            have hiPref : i < ((List.replicate p SimSym.blank).set 0 .leftMark).length := by
              simp; omega
            simp only [curList, List.getElem_append_left hiPref]
            by_cases hi0 : i = 0
            · subst hi0; simp [blankList]
            · simp [blankList, List.getElem_set_ne (Ne.symm hi0)]
      rw [hSetEq, hpLast] at hNextMatch
      refine ⟨nextTape, by simpa [clearRightStep, hReadEnd] using hUpd,
        by rw [hNextMatch.head_eq]; omega, ?_, ?_⟩
      · intro hBad; simp [clearRightStep, hReadEnd] at hBad
      · intro e _; simpa [Post] using hNextMatch
    · have hpLtLast : p < prefixSyms.length + 1 := by omega
      have hNotEnd : orig[p] ≠ .endMark := by
        have hMem : orig[p] ∈ prefixSyms := by
          have hp0 : p - 1 < prefixSyms.length := by omega
          have hEq : orig[p] = prefixSyms[p - 1] := by
            cases p with
            | zero => omega
            | succ p' =>
              simp only [orig, List.cons_append, List.getElem_cons_succ]
              rw [List.getElem_append_left (by omega)]
              rfl
          rw [hEq]
          exact List.getElem_mem hp0
        exact hNoEnd _ hMem
      have hReadNotEnd : tape.cells tape.head ≠ .endMark := by rw [hRead]; exact hNotEnd
      have hFnEq : clearRightStep (tape.cells tape.head) = (.inl (), .blank, .right) := by
        cases hC : tape.cells tape.head
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hReadNotEnd hC).elim
      have hMove : moveOneSidedHead p .right = some (p + 1) := by simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .blank .right hMove hpCur
      have hSetEq : curList.set p .blank =
          (List.replicate (p + 1) SimSym.blank).set 0 .leftMark ++ orig.drop (p + 1) := by
        apply List.ext_getElem
        · simp [hCurLen, L]
          omega
        · intro i hi1 hi2
          have hiL : i < L := by simpa [hCurLen] using hi1
          by_cases hip : i = p
          · subst hip
            rw [List.getElem_set_self (by simpa [List.length_set] using hpCur)]
            have hPrefLen : ((List.replicate (i + 1) SimSym.blank).set 0 .leftMark).length = i + 1 := by simp
            rw [List.getElem_append_left (by omega : i < ((List.replicate (i + 1) SimSym.blank).set 0 .leftMark).length)]
            rw [List.getElem_set_ne (by omega : 0 ≠ i), List.getElem_replicate]
          · rw [List.getElem_set_ne (Ne.symm hip)]
            by_cases hiLtP : i < p
            · have hiLt1 : i < ((List.replicate p SimSym.blank).set 0 .leftMark).length := by simp; omega
              have hiLt2 : i < ((List.replicate (p + 1) SimSym.blank).set 0 .leftMark).length := by simp; omega
              rw [List.getElem_append_left hiLt1, List.getElem_append_left hiLt2]
              by_cases hi0 : i = 0
              · subst hi0; simp
              · simp [List.getElem_set_ne (Ne.symm hi0)]
            · have hiGtP : p < i := by omega
              have hGe1 : ((List.replicate p SimSym.blank).set 0 .leftMark).length ≤ i := by simp; omega
              have hGe2 : ((List.replicate (p + 1) SimSym.blank).set 0 .leftMark).length ≤ i := by simp; omega
              rw [List.getElem_append_right hGe1, List.getElem_append_right hGe2]
              simp only [List.length_set, List.length_replicate, List.getElem_drop]
              congr 1
              omega
      rw [hSetEq] at hNextMatch
      refine ⟨nextTape, by simpa [hFnEq] using hUpd, by rw [hNextMatch.head_eq]; omega, ?_, ?_⟩
      · intro _
        refine ⟨⟨p + 1, by omega, by omega, hNextMatch⟩, ?_⟩
        rw [hpMatch.head_eq, hNextMatch.head_eq]
        omega
      · intro e hBad; simp [hFnEq] at hBad
  have hInitInv : Inv (initTapes t) := by
    refine ⟨1, by omega, by omega, ?_⟩
    simpa [orig] using hMatch
  have hInitHead : (initTapes t).head < bound t := by
    rw [hMatch.head_eq]; omega
  obtain ⟨_, midTape, hScan, hMidMatch⟩ := scanTape_reachesExit (Exit := Unit) t clearRightStep
    input bound initTapes inHead Inv (fun tape => L - tape.head) Post
    hOtherBounds hStep hInitInv hInitHead
  obtain ⟨finalTapes, hR, hFM, hO⟩ := rewindTape_reachesExit t input bound blankList
    (by simp [blankList]; omega) (by simp [blankList])
    (fun i hi1 hi2 => by
      have hiL : i < L := by simpa [blankList] using hi2
      simp [blankList, hiL, List.getElem_set_ne (by omega : 0 ≠ i)])
    (by simp [blankList]; omega)
    (fun j => if j = t then midTape else initTapes j) inHead
    (fun j hj => by simp [hj, hOtherBounds j hj]) (L - 1) (by omega)
    (by simp [blankList]; omega) (by simpa using hMidMatch)
  have hFM' : TapeMatches (finalTapes t) [.leftMark] 1 := by
    refine ⟨hFM.1, fun i => ?_⟩
    rw [hFM.2 i]
    cases i with
    | zero => simp [blankList, show 0 < L by omega]
    | succ i' =>
      by_cases hiL : i' + 1 < L
      · simp [blankList, hiL, List.getElem_set_ne (by omega : 0 ≠ i' + 1)]
      · have hNone : blankList[i' + 1]? = none := List.getElem?_eq_none (by simp [blankList]; omega)
        simp [hNone]
  have hFinalEq : finalTapes = fun j => if j = t then finalTapes t else initTapes j := by
    funext j
    by_cases hj : j = t
    · subst hj; simp
    · simp [hj, hO j hj]
  rw [hFinalEq] at hR
  exact ⟨finalTapes t, (TMComponent.seq_reachesExit _ _ input bound hScan hR), hFM'⟩

/-- Prepend one internal `CompStep` onto a `ReachesExit` derivation. -/
theorem compStep_head_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (bound : Fin k → ℕ)
    {q q' : Q} {tapes tapes' finalTapes : Fin k → OneSidedTape Γ}
    {ih ih' finalIh : Fin (n + 2)} {e : Exit}
    (hHeads : ∀ j, (tapes j).head < bound j)
    (hHeads' : ∀ j, (tapes' j).head < bound j)
    (hNext : (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).nextState =
      .inl q')
    (hInMove : moveHead (n + 2) ih
      (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).inputMove =
        some ih')
    (hWork : ∀ j, (tapes j).updateAndMove
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).write j)
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).workMove j) =
        some (tapes' j))
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q', ih', tapes'⟩ ⟨.inr e, finalIh, finalTapes⟩) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, ih, tapes⟩ ⟨.inr e, finalIh, finalTapes⟩ := by
  refine Relation.ReflTransGen.head ⟨?_, hHeads, hHeads'⟩ hRest
  exact ⟨q, rfl, hNext.symm, ih', hInMove, rfl, hWork⟩

/-- Finish a `ReachesExit` derivation in one `CompStep` to `.inr e`. -/
theorem compStep_exit_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (bound : Fin k → ℕ)
    {q : Q} {tapes tapes' : Fin k → OneSidedTape Γ}
    {ih ih' : Fin (n + 2)} {e : Exit}
    (hHeads : ∀ j, (tapes j).head < bound j)
    (hHeads' : ∀ j, (tapes' j).head < bound j)
    (hNext : (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).nextState =
      .inr e)
    (hInMove : moveHead (n + 2) ih
      (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).inputMove =
        some ih')
    (hWork : ∀ j, (tapes j).updateAndMove
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).write j)
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).workMove j) =
        some (tapes' j)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, ih, tapes⟩ ⟨.inr e, ih', tapes'⟩ := by
  refine Relation.ReflTransGen.single ⟨?_, hHeads, hHeads'⟩
  exact ⟨q, rfl, hNext.symm, ih', hInMove, rfl, hWork⟩

/-- Helper to prepend one single-tape `CompStep` when the tape array overrides
tape `t` with `tape` / `nextTape`. -/
theorem singleTape_compStep_head_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (tape nextTape finalTape : OneSidedTape SimSym)
    (q q' : Q) {ih finalIh : Fin (n + 2)} {e : Exit}
    {w : SimSym} {mv : TapeMove}
    (hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j)
    (hNextHead : nextTape.head < bound t)
    (hUpd : tape.updateAndMove w mv = some nextTape)
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', ih, fun j => if j = t then nextTape else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t then finalTape else initTapes j⟩)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
      singleTapeAction (Sum.inl q') t w mv
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t then tape else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t then finalTape else initTapes j⟩ := by
  refine compStep_head_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_ hRest
  · by_cases hj : j = t
    · subst hj; simpa using hNextHead
    · simp only [hj, ↓reduceIte]; exact by simpa [hj] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [singleTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := singleTapeAction_apply (Sum.inl q' : Q ⊕ Exit) t w mv
      (fun y => if y = t then tape else initTapes y) (by simpa using hUpd) j
    by_cases hj : j = t
    · subst hj; simpa using hApp
    · simpa [hj] using hApp

theorem singleTape_compStep_exit_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (tape nextTape : OneSidedTape SimSym)
    (q : Q) {ih : Fin (n + 2)} {e : Exit}
    {w : SimSym} {mv : TapeMove}
    (hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j)
    (hNextHead : nextTape.head < bound t)
    (hUpd : tape.updateAndMove w mv = some nextTape)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
      singleTapeAction (Sum.inr e) t w mv
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t then tape else initTapes j⟩
      ⟨.inr e, ih, fun j => if j = t then nextTape else initTapes j⟩ := by
  refine compStep_exit_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_
  · by_cases hj : j = t
    · subst hj; simpa using hNextHead
    · simp only [hj, ↓reduceIte]; exact by simpa [hj] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [singleTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := singleTapeAction_apply (Sum.inr e : Q ⊕ Exit) t w mv
      (fun y => if y = t then tape else initTapes y) (by simpa using hUpd) j
    by_cases hj : j = t
    · subst hj; simpa using hApp
    · simpa [hj] using hApp

theorem twoTape_compStep_head_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym)
    (tape₁ tape₂ nt₁ nt₂ ft₁ ft₂ : OneSidedTape SimSym)
    (q q' : Q) {ih finalIh : Fin (n + 2)} {e : Exit}
    {w₁ w₂ : SimSym} {m₁ m₂ : TapeMove}
    (hHeads : ∀ j, (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j)
    (hNH₁ : nt₁.head < bound t₁) (hNH₂ : nt₂.head < bound t₂)
    (hUpd₁ : tape₁.updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : tape₂.updateAndMove w₂ m₂ = some nt₂)
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', ih, fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j⟩)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
      twoTapeAction (Sum.inl q') t₁ t₂ w₁ w₂ m₁ m₂
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j⟩ := by
  refine compStep_head_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_ hRest
  · by_cases h1 : j = t₁
    · subst h1; simpa using hNH₁
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hNH₂
      · simp only [h1, h2, ↓reduceIte]; exact by simpa [h1, h2] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [twoTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := twoTapeAction_apply (Sum.inl q' : Q ⊕ Exit) t₁ t₂ hNe w₁ w₂ m₁ m₂
      (fun y => if y = t₁ then tape₁ else if y = t₂ then tape₂ else initTapes y)
      (by simpa using hUpd₁) (by simpa [hNe.symm] using hUpd₂) j
    by_cases h1 : j = t₁
    · subst h1; simpa using hApp
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hApp
      · simpa [h1, h2] using hApp

theorem twoTape_compStep_exit_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym)
    (tape₁ tape₂ nt₁ nt₂ : OneSidedTape SimSym)
    (q : Q) {ih : Fin (n + 2)} {e : Exit}
    {w₁ w₂ : SimSym} {m₁ m₂ : TapeMove}
    (hHeads : ∀ j, (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j)
    (hNH₁ : nt₁.head < bound t₁) (hNH₂ : nt₂.head < bound t₂)
    (hUpd₁ : tape₁.updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : tape₂.updateAndMove w₂ m₂ = some nt₂)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
      twoTapeAction (Sum.inr e) t₁ t₂ w₁ w₂ m₁ m₂
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j⟩
      ⟨.inr e, ih, fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else initTapes j⟩ := by
  refine compStep_exit_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_
  · by_cases h1 : j = t₁
    · subst h1; simpa using hNH₁
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hNH₂
      · simp only [h1, h2, ↓reduceIte]; exact by simpa [h1, h2] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [twoTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := twoTapeAction_apply (Sum.inr e : Q ⊕ Exit) t₁ t₂ hNe w₁ w₂ m₁ m₂
      (fun y => if y = t₁ then tape₁ else if y = t₂ then tape₂ else initTapes y)
      (by simpa using hUpd₁) (by simpa [hNe.symm] using hUpd₂) j
    by_cases h1 : j = t₁
    · subst h1; simpa using hApp
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hApp
      · simpa [h1, h2] using hApp

/-- Rewind the input head to `.leftEnd` (position `0`) without modifying any
work tapes. -/
def rewindInputBody (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k (Unit ⊕ Unit) :=
  TMComponent.atom fun inSym scanned =>
    match inSym with
    | .leftEnd => TMAction.mk (Sum.inr ()) TapeMove.stay scanned (fun _ => TapeMove.stay)
    | _ => TMAction.mk (Sum.inl ()) TapeMove.left scanned (fun _ => TapeMove.stay)

def rewindInput (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  (rewindInputBody InputAlphabet k).loop

private theorem stay_all_tapes {k : ℕ} (tapes : Fin k → OneSidedTape SimSym) :
    ∀ j : Fin k,
      (tapes j).updateAndMove ((tapes j).cells (tapes j).head) .stay = some (tapes j) := by
  intro j
  cases hT : tapes j with
  | mk cells head =>
    simp only [OneSidedTape.updateAndMove, moveOneSidedHead]
    congr 1
    simp only [OneSidedTape.mk.injEq, and_true]
    funext i
    by_cases hi : i = head <;> simp [hi]

theorem rewindInput_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym)
    (hBounds : ∀ j, (tapes j).head < bound j) (inHead : Fin (n + 2)) :
    (rewindInput InputAlphabet k).ReachesExit input bound tapes inHead ()
      tapes ⟨0, by omega⟩ := by
  have hInd : ∀ p, ∀ ih : Fin (n + 2), ih.val = p →
      (rewindInput InputAlphabet k).ReachesExit input bound tapes ih () tapes ⟨0, by omega⟩ := by
    intro p
    induction p with
    | zero =>
      intro ih hPos
      have hIh0 : ih = ⟨0, by omega⟩ := Fin.ext hPos
      have hRead : readInput input ih = .leftEnd := by simp [readInput, hPos]
      have hStepEq : (rewindInput InputAlphabet k).step () (readInput input ih)
          (fun j => (tapes j).cells (tapes j).head) =
          TMAction.mk (Sum.inr ()) TapeMove.stay
            (fun j => (tapes j).cells (tapes j).head) (fun _ => TapeMove.stay) := by
        simp [rewindInput, rewindInputBody, TMComponent.loop, TMComponent.atom, hRead,
          TMAction.mapState]
      refine compStep_exit_reachesExit (rewindInput InputAlphabet k) input bound hBounds hBounds
        (by rw [hStepEq])
        (by rw [hStepEq]; simp [moveHead, hIh0])
        (fun j => by rw [hStepEq]; exact stay_all_tapes tapes j)
    | succ p' ihRec =>
      intro ih hPos
      have hNotLeft : readInput input ih ≠ .leftEnd := by
        simp [readInput, hPos]
        split <;> simp
      have hStepEq : (rewindInput InputAlphabet k).step () (readInput input ih)
          (fun j => (tapes j).cells (tapes j).head) =
          TMAction.mk (Sum.inl ()) TapeMove.left
            (fun j => (tapes j).cells (tapes j).head) (fun _ => TapeMove.stay) := by
        simp only [rewindInput, rewindInputBody, TMComponent.loop, TMComponent.atom,
          TMAction.mapState]
      have hLt : p' < n + 2 := by have := ih.isLt; omega
      have hMove : moveHead (n + 2) ih .left = some ⟨p', hLt⟩ := by
        simp [moveHead, hPos]
      exact compStep_head_reachesExit (rewindInput InputAlphabet k) input bound hBounds hBounds
        (by rw [hStepEq]) (by rw [hStepEq]; exact hMove)
        (fun j => by rw [hStepEq]; exact stay_all_tapes tapes j)
        (ihRec ⟨p', hLt⟩ rfl)
  exact hInd inHead.val inHead rfl

/-- Decrement an LSB-first binary number on tape `t` (`[.leftMark] ++ bits ++ [.endMark]`).
Returns `true` if the value was positive (and decrements it by 1); returns `false`
if the value was `0` (leaving it `0`). In both cases tape `t` ends at cell `1`. -/
inductive DecState where
  | scanZero
  | rewindTrue
  | restore
  deriving DecidableEq

def DecState.equivFin : DecState ≃ Fin 3 where
  toFun | .scanZero => 0 | .rewindTrue => 1 | .restore => 2
  invFun | 0 => .scanZero | 1 => .rewindTrue | _ => .restore
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype DecState := Fintype.ofEquiv (Fin 3) DecState.equivFin.symm

def decScratch (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent DecState InputAlphabet SimSym k Bool where
  start := .scanZero
  step s _ scanned :=
    match s with
    | .scanZero =>
      match scanned t with
      | .bit false => singleTapeAction (.inl .scanZero) t (.bit true) .right scanned
      | .bit true => singleTapeAction (.inl .rewindTrue) t (.bit false) .left scanned
      | sym => singleTapeAction (.inl .restore) t sym .left scanned
    | .rewindTrue =>
      match scanned t with
      | .leftMark => singleTapeAction (.inr true) t .leftMark .right scanned
      | sym => singleTapeAction (.inl .rewindTrue) t sym .left scanned
    | .restore =>
      match scanned t with
      | .leftMark => singleTapeAction (.inr false) t .leftMark .right scanned
      | _ => singleTapeAction (.inl .restore) t (.bit false) .left scanned

/-- Decrement an LSB-first bit list by one (all-zeros wraps to all-ones). -/
def decBits : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: decBits bs

theorem decBits_length (bs : List Bool) : (decBits bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [decBits, ih]

theorem bitsToNat_decBits {bs : List Bool} (hHasTrue : true ∈ bs) :
    bitsToNat (decBits bs) + 1 = bitsToNat bs := by
  induction bs with
  | nil => simp at hHasTrue
  | cons b bs ih =>
    cases b
    · rcases List.mem_cons.mp hHasTrue with hEq | hMem
      · cases hEq
      · have ih' := ih hMem
        simp [decBits, bitsToNat]
        have hPos : 1 ≤ bitsToNat bs := by
          have : 0 < bitsToNat bs := by
            by_contra h0
            have hZ : bitsToNat bs = 0 := by omega
            have : ∀ l, bitsToNat l = 0 → true ∉ l := by
              intro l hl
              induction l with
              | nil => simp
              | cons x xs ihx =>
                cases x
                · have hxs : bitsToNat xs = 0 := by simpa [bitsToNat] using hl
                  intro hMem'
                  rcases List.mem_cons.mp hMem' with hEq | hIn
                  · cases hEq
                  · exact ihx hxs hIn
                · simp [bitsToNat] at hl
            exact this bs hZ hMem
          omega
        omega
    · simp [decBits, bitsToNat]
      omega

private theorem decScratch_rewindTrue {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (bits : List Bool) (hBound : bits.length + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j) :
    ∀ pos, pos < bits.length + 2 →
      ∀ tape, TapeMatches tape (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) pos →
      Relation.ReflTransGen
        (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
          (∀ j, (a.workTapes j).head < bound j) ∧
          (∀ j, (b.workTapes j).head < bound j))
        ⟨.inl .rewindTrue, inHead, fun j => if j = t then tape else initTapes j⟩
        ⟨.inr true, inHead, fun j => if j = t then ⟨tape.cells, 1⟩ else initTapes j⟩ := by
  let contents : List SimSym := SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]
  have hLen : contents.length = bits.length + 2 := by simp [contents]
  intro pos
  induction pos with
  | zero =>
    intro hLt tape hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le hLt hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; exact hLt)]
      simp
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch.update_set .leftMark .right hMove (by rw [hLen]; exact hLt)
    have hNextEq : nextTape = ⟨tape.cells, 1⟩ := by
      have hCells : nextTape.cells = tape.cells := by
        funext i
        rw [hNextMatch.2 i, hMatch.2 i]
        by_cases hi : i = 0
        · subst hi; simp
        · simp
      have hHead : nextTape.head = 1 := hNextMatch.head_eq
      cases nextTape
      simp only [OneSidedTape.mk.injEq]
      exact ⟨hCells, hHead⟩
    rw [hNextEq] at hUpd hNextMatch
    exact singleTape_compStep_exit_override (decScratch InputAlphabet t) t input bound
      initTapes tape ⟨tape.cells, 1⟩ .rewindTrue hHeadBounds
      (by simp; omega)
      (by simpa using hUpd)
      (by simp [decScratch, hRead])
  | succ p ih =>
    intro hLt tape hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le hLt hBound
      · simpa [hj] using hOtherBounds j hj
    have hReadNotLeft : tape.cells tape.head ≠ .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; exact hLt)]
      simp only [List.cons_append, List.getElem_cons_succ]
      by_cases hp : p < bits.length
      · rw [List.getElem_append_left (by simp [hp])]
        simp
      · have hpEq : p = bits.length := by omega
        rw [List.getElem_append_right (by simp [hpEq])]
        simp [hpEq]
    have hMove : moveOneSidedHead (p + 1) .left = some p := by simp [moveOneSidedHead]
    obtain ⟨nextTape, hUpd, hNextMatch⟩ := hMatch.update_keep .left hMove
    have hNextCells : nextTape.cells = tape.cells := by
      funext i
      rw [hNextMatch.2 i, hMatch.2 i]
    have hRest := ih (by omega) nextTape hNextMatch
    have hTargetEq : (⟨nextTape.cells, 1⟩ : OneSidedTape SimSym) = ⟨tape.cells, 1⟩ := by
      rw [hNextCells]
    rw [hTargetEq] at hRest
    have hStepEq : (decScratch InputAlphabet t).step .rewindTrue (readInput input inHead)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
        singleTapeAction (Sum.inl DecState.rewindTrue) t
          (tape.cells tape.head) .left
          (fun j => (if j = t then tape else initTapes j).cells
            (if j = t then tape else initTapes j).head) := by
      simp only [decScratch, ↓reduceIte]
    exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape ⟨tape.cells, 1⟩ .rewindTrue .rewindTrue hHeadBounds
      (by rw [hNextMatch.head_eq]; omega) hUpd hRest hStepEq

private theorem decScratch_restore {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (m : ℕ) (hBound : m + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j) :
    ∀ pos, pos ≤ m →
      ∀ tape, TapeMatches tape
        (SimSym.leftMark :: List.replicate pos (SimSym.bit true) ++
          List.replicate (m - pos) (SimSym.bit false) ++ [SimSym.endMark]) pos →
      ∃ finalTape,
        Relation.ReflTransGen
          (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .restore, inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr false, inHead, fun j => if j = t then finalTape else initTapes j⟩ ∧
        TapeMatches finalTape (SimSym.leftMark :: List.replicate m (SimSym.bit false) ++ [SimSym.endMark]) 1 := by
  intro pos
  induction pos with
  | zero =>
    intro _ tape hMatch
    have hLen : (SimSym.leftMark :: List.replicate 0 (SimSym.bit true) ++
        List.replicate (m - 0) (SimSym.bit false) ++ [SimSym.endMark]).length = m + 2 := by simp
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : 0 < m + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; omega)]
      simp
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch.update_set .leftMark .right hMove (by rw [hLen]; omega)
    have hSetEq :
        (SimSym.leftMark :: List.replicate 0 (SimSym.bit true) ++
          List.replicate (m - 0) (SimSym.bit false) ++ [SimSym.endMark]).set 0 .leftMark =
        SimSym.leftMark :: List.replicate m (SimSym.bit false) ++ [SimSym.endMark] := by
      simp
    rw [hSetEq] at hNextMatch
    refine ⟨nextTape, ?_, hNextMatch⟩
    exact singleTape_compStep_exit_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
      hUpd (by simp [decScratch, hRead])
  | succ p ih =>
    intro hpLe tape hMatch
    let pref : List SimSym := SimSym.leftMark :: List.replicate p (SimSym.bit true)
    let suf : List SimSym := List.replicate (m - (p + 1)) (SimSym.bit false) ++ [SimSym.endMark]
    have hPrefLen : pref.length = p + 1 := by simp [pref]
    have hCurEq : SimSym.leftMark :: List.replicate (p + 1) (SimSym.bit true) ++
        List.replicate (m - (p + 1)) (SimSym.bit false) ++ [SimSym.endMark] =
        pref ++ SimSym.bit true :: suf := by
      simp [pref, suf, List.replicate_succ', List.append_assoc]
    have hpLt : p + 1 < (pref ++ SimSym.bit true :: suf).length := by
      rw [← hPrefLen]; simp
    have hMatch' : TapeMatches tape (pref ++ SimSym.bit true :: suf) pref.length := by
      rw [hPrefLen, ← hCurEq]; exact hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : p + 1 < m + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit true := by
      rw [hMatch'.read_lt (by simp)]
      exact list_get_append_mid pref (.bit true) suf
    have hMove : moveOneSidedHead (p + 1) .left = some p := by simp [moveOneSidedHead]
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch'.update_set (.bit false) .left (by rw [hPrefLen]; exact hMove) (by simp)
    rw [list_set_append_mid] at hNextMatch
    have hNextEq : pref ++ SimSym.bit false :: suf =
        SimSym.leftMark :: List.replicate p (SimSym.bit true) ++
          List.replicate (m - p) (SimSym.bit false) ++ [SimSym.endMark] := by
      have hRep : List.replicate (m - p) (SimSym.bit false) =
          SimSym.bit false :: List.replicate (m - (p + 1)) (SimSym.bit false) := by
        rw [show m - p = (m - (p + 1)) + 1 by omega, List.replicate_succ]
      simp [pref, suf, hRep, List.append_assoc]
    rw [hNextEq] at hNextMatch
    obtain ⟨finalTape, hRest, hFinalMatch⟩ := ih (by omega) nextTape hNextMatch
    refine ⟨finalTape, ?_, hFinalMatch⟩
    exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape finalTape .restore .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
      hUpd hRest (by simp [decScratch, hRead])

theorem decScratch_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (bits : List Bool) (hBound : bits.length + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) 1) :
    ∃ res finalTape bits',
      bits'.length = bits.length ∧
      (decScratch InputAlphabet t).ReachesExit input bound initTapes inHead res
        (fun j => if j = t then finalTape else initTapes j) inHead ∧
      TapeMatches finalTape (SimSym.leftMark :: bits'.map SimSym.bit ++ [SimSym.endMark]) 1 ∧
      (res = true ↔ true ∈ bits) ∧
      (res = true → bitsToNat bits' + 1 = bitsToNat bits) ∧
      (res = false → bits' = bits) := by
  have hScan : ∀ (suf pref : List Bool),
      pref = List.replicate pref.length false →
      pref.length + suf.length = bits.length →
      ∀ tape, TapeMatches tape
        (SimSym.leftMark :: ((List.replicate pref.length true ++ suf).map SimSym.bit) ++ [SimSym.endMark])
        (1 + pref.length) →
      ∃ res finalTape bits',
        bits'.length = bits.length ∧
        Relation.ReflTransGen
          (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .scanZero, inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = t then finalTape else initTapes j⟩ ∧
        TapeMatches finalTape (SimSym.leftMark :: bits'.map SimSym.bit ++ [SimSym.endMark]) 1 ∧
        (res = true ↔ true ∈ pref ++ suf) ∧
        (res = true → bitsToNat bits' + 1 = bitsToNat (pref ++ suf)) ∧
        (res = false → bits' = pref ++ suf) := by
    intro suf
    induction suf with
    | nil =>
      intro pref hPrefFalse hLenSum tape hTapMatch
      have hLenPref : pref.length = bits.length := by simpa using hLenSum
      let prefSyms : List SimSym :=
        SimSym.leftMark :: List.replicate pref.length (SimSym.bit true)
      have hPrefLen : prefSyms.length = 1 + pref.length := by simp [prefSyms]; omega
      have hListEq :
          SimSym.leftMark :: ((List.replicate pref.length true ++ []).map SimSym.bit) ++ [SimSym.endMark] =
          prefSyms ++ SimSym.endMark :: [] := by
        simp [prefSyms, List.map_replicate]
      have hTapMatch' : TapeMatches tape (prefSyms ++ SimSym.endMark :: []) prefSyms.length := by
        rw [hPrefLen, ← hListEq]; exact hTapMatch
      have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
        intro j
        by_cases hj : j = t
        · subst hj; simpa [hTapMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + pref.length < bits.length + 2) hBound
        · simpa [hj] using hOtherBounds j hj
      have hRead : tape.cells tape.head = .endMark := by
        rw [hTapMatch'.read_lt (by simp)]
        exact list_get_append_mid prefSyms .endMark []
      have hMove : moveOneSidedHead (1 + pref.length) .left = some pref.length := by
        simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hTapMatch.update_keep .left hMove
      have hNextMatch' : TapeMatches nextTape
          (SimSym.leftMark :: List.replicate pref.length (SimSym.bit true) ++
            List.replicate (bits.length - pref.length) (SimSym.bit false) ++ [SimSym.endMark])
          pref.length := by
        simpa [hLenPref, List.map_replicate] using hNextMatch
      obtain ⟨finalTape, hRest, hFinalMatch⟩ :=
        decScratch_restore t input bound bits.length hBound initTapes inHead hOtherBounds
          pref.length (by omega) nextTape hNextMatch'
      refine ⟨false, finalTape, pref, hLenPref, ?_, ?_, ?_, ?_, ?_⟩
      · exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape finalTape .scanZero .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
          hUpd hRest (by simp [decScratch, hRead])
      · have hMap : pref.map SimSym.bit = List.replicate bits.length (SimSym.bit false) := by
          conv_lhs => rw [hPrefFalse]
          rw [hLenPref, List.map_replicate]
        rw [hMap]
        exact hFinalMatch
      · have hNotMem : true ∉ pref := by
          conv => rhs; rw [hPrefFalse]
          simp
        simp [hNotMem]
      · intro hBad; cases hBad
      · intro _; simp
    | cons b bs ih =>
      intro pref hPrefFalse hLenSum tape hTapMatch
      let prefSyms : List SimSym :=
        SimSym.leftMark :: List.replicate pref.length (SimSym.bit true)
      let sufSyms : List SimSym := bs.map SimSym.bit ++ [SimSym.endMark]
      have hPrefLen : prefSyms.length = 1 + pref.length := by simp [prefSyms]; omega
      have hListEq :
          SimSym.leftMark :: ((List.replicate pref.length true ++ (b :: bs)).map SimSym.bit) ++ [SimSym.endMark] =
          prefSyms ++ SimSym.bit b :: sufSyms := by
        simp [prefSyms, sufSyms, List.map_replicate, List.append_assoc]
      have hTapMatch' : TapeMatches tape (prefSyms ++ SimSym.bit b :: sufSyms) prefSyms.length := by
        rw [hPrefLen, ← hListEq]; exact hTapMatch
      have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
        intro j
        by_cases hj : j = t
        · subst hj; simpa [hTapMatch.head_eq] using Nat.lt_of_lt_of_le (by simp at hLenSum; omega : 1 + pref.length < bits.length + 2) hBound
        · simpa [hj] using hOtherBounds j hj
      have hRead : tape.cells tape.head = .bit b := by
        rw [hTapMatch'.read_lt (by simp)]
        exact list_get_append_mid prefSyms (.bit b) sufSyms
      cases b with
      | true =>
        let resBits := List.replicate pref.length true ++ false :: bs
        have hResLen : resBits.length = bits.length := by
          simp [resBits]; simp at hLenSum; omega
        have hMove : moveOneSidedHead (1 + pref.length) .left = some pref.length := by
          simp [moveOneSidedHead]
        obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
          hTapMatch'.update_set (.bit false) .left (by rw [hPrefLen]; exact hMove) (by simp)
        rw [list_set_append_mid] at hNextMatch
        have hNextEq : prefSyms ++ SimSym.bit false :: sufSyms =
            SimSym.leftMark :: resBits.map SimSym.bit ++ [SimSym.endMark] := by
          simp [prefSyms, sufSyms, resBits, List.map_replicate, List.append_assoc]
        rw [hNextEq] at hNextMatch
        have hRew := decScratch_rewindTrue t input bound resBits (by rw [hResLen]; exact hBound)
          initTapes inHead hOtherBounds pref.length (by simp at hLenSum; omega) nextTape hNextMatch
        have hFinalMatch : TapeMatches ⟨nextTape.cells, 1⟩
            (SimSym.leftMark :: resBits.map SimSym.bit ++ [SimSym.endMark]) 1 := by
          refine ⟨rfl, fun i => hNextMatch.2 i⟩
        have hStep := singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape ⟨nextTape.cells, 1⟩ .scanZero .rewindTrue hHeadBounds
          (by rw [hNextMatch.head_eq]; simp at hLenSum; omega)
          hUpd hRew (by simp [decScratch, hRead])
        refine ⟨true, ⟨nextTape.cells, 1⟩, resBits, hResLen, hStep, hFinalMatch, ?_, ?_, ?_⟩
        · simp
        · intro _
          have hDecRep : ∀ m (r : List Bool),
              decBits (List.replicate m false ++ true :: r) =
                List.replicate m true ++ false :: r := by
            intro m r
            induction m with
            | zero => simp [decBits]
            | succ m ihm => simp [List.replicate_succ, decBits, ihm]
          have hDecEq : decBits (pref ++ true :: bs) = resBits := by
            calc
              decBits (pref ++ true :: bs)
                = decBits (List.replicate pref.length false ++ true :: bs) := by rw [← hPrefFalse]
              _ = resBits := hDecRep pref.length bs
          rw [← hDecEq]
          exact bitsToNat_decBits (by simp)
        · intro hBad; cases hBad
      | false =>
        have hMove : moveOneSidedHead (1 + pref.length) .right = some (1 + (pref.length + 1)) := by
          simp [moveOneSidedHead]; omega
        obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
          hTapMatch'.update_set (.bit true) .right (by rw [hPrefLen]; exact hMove) (by simp)
        rw [list_set_append_mid] at hNextMatch
        have hNextEq : prefSyms ++ SimSym.bit true :: sufSyms =
            SimSym.leftMark :: ((List.replicate (pref ++ [false]).length true ++ bs).map SimSym.bit) ++
              [SimSym.endMark] := by
          simp [prefSyms, sufSyms, List.replicate_succ', List.map_replicate, List.append_assoc]
        rw [hNextEq] at hNextMatch
        have hPrefNext : pref ++ [false] = List.replicate (pref ++ [false]).length false := by
          conv_lhs => rw [hPrefFalse]
          simp [List.replicate_succ']
        have hNextMatch' : TapeMatches nextTape
            (SimSym.leftMark :: ((List.replicate (pref ++ [false]).length true ++ bs).map SimSym.bit) ++
              [SimSym.endMark])
            (1 + (pref ++ [false]).length) := by
          simpa [Nat.add_assoc] using hNextMatch
        obtain ⟨res, finalTape, resBits, hRLen, hRest, hFM, hResIff, hDec, hKeep⟩ :=
          ih (pref ++ [false]) hPrefNext (by simp; simp at hLenSum; omega) nextTape hNextMatch'
        have hPrefAssoc : (pref ++ [false]) ++ bs = pref ++ false :: bs := by simp
        rw [hPrefAssoc] at hResIff hDec hKeep
        refine ⟨res, finalTape, resBits, hRLen, ?_, hFM, hResIff, hDec, hKeep⟩
        exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape finalTape .scanZero .scanZero hHeadBounds
          (by rw [hNextMatch.head_eq]; simp at hLenSum; omega)
          hUpd hRest (by simp [decScratch, hRead])
  rcases hScan bits [] rfl (by simp) (initTapes t) (by simpa using hMatch) with
    ⟨res, finalTape, bits', hLen', hRun', hFM', hResIff, hDec, hKeep⟩
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j
    by_cases hj : j = t <;> simp [hj]
  rw [hTapesSelf] at hRun'
  exact ⟨res, finalTape, bits', hLen', hRun', hFM',
    by simpa using hResIff, by simpa using hDec, by simpa using hKeep⟩

/-- Body of `cmpBitScan`: compares symbols on tapes `t₁` and `t₂` bit by bit until
either a mismatch occurs or both tapes reach `.endMark`. -/
def cmpBitScanBody (InputAlphabet : Type*) {k : ℕ} (t₁ t₂ : Fin k) :
    TMComponent Unit InputAlphabet SimSym k (Unit ⊕ Bool) :=
  TMComponent.atom fun _ scanned =>
    match scanned t₁, scanned t₂ with
    | .bit b₁, .bit b₂ =>
      if b₁ = b₂ then
        twoTapeAction (.inl ()) t₁ t₂ (.bit b₁) (.bit b₂) .right .right scanned
      else
        twoTapeAction (.inr false) t₁ t₂ (.bit b₁) (.bit b₂) .stay .stay scanned
    | .endMark, .endMark =>
      twoTapeAction (.inr true) t₁ t₂ .endMark .endMark .stay .stay scanned
    | s₁, s₂ =>
      twoTapeAction (.inr false) t₁ t₂ s₁ s₂ .stay .stay scanned

def cmpBitScan (InputAlphabet : Type*) {k : ℕ} (t₁ t₂ : Fin k) :
    TMComponent Unit InputAlphabet SimSym k Bool :=
  (cmpBitScanBody InputAlphabet t₁ t₂).loop

/-- Compare two bit tapes `t₁` and `t₂` (`[.leftMark] ++ bits ++ [.endMark]`) of equal
length and rewind both heads back to cell `1`. -/
def compareBitTapes (InputAlphabet : Type*) {k : ℕ} (t₁ t₂ : Fin k) :=
  (cmpBitScan InputAlphabet t₁ t₂).branch
    (((rewindTape InputAlphabet t₁).seq (rewindTape InputAlphabet t₂)).mapExit fun _ => true)
    (((rewindTape InputAlphabet t₁).seq (rewindTape InputAlphabet t₂)).mapExit fun _ => false)

private theorem cmpBitScan_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (nBits : ℕ) (hBound₁ : nBits + 2 ≤ bound t₁) (hBound₂ : nBits + 2 ≤ bound t₂)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t₁ → j ≠ t₂ → (initTapes j).head < bound j) :
    ∀ (suf₁ suf₂ pref₁ pref₂ : List Bool),
      suf₁.length = suf₂.length →
      pref₁.length = pref₂.length →
      pref₁.length + suf₁.length = nBits →
      ∀ tape₁ tape₂,
        TapeMatches tape₁
          (SimSym.leftMark :: (pref₁ ++ suf₁).map SimSym.bit ++ [SimSym.endMark])
          (1 + pref₁.length) →
        TapeMatches tape₂
          (SimSym.leftMark :: (pref₂ ++ suf₂).map SimSym.bit ++ [SimSym.endMark])
          (1 + pref₂.length) →
        ∃ pos ft₁ ft₂,
          1 ≤ pos ∧ pos ≤ nBits + 1 ∧
          (cmpBitScan InputAlphabet t₁ t₂).ReachesExit input bound
            (fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j) inHead
            (decide (suf₁ = suf₂))
            (fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j) inHead ∧
          TapeMatches ft₁
            (SimSym.leftMark :: (pref₁ ++ suf₁).map SimSym.bit ++ [SimSym.endMark]) pos ∧
          TapeMatches ft₂
            (SimSym.leftMark :: (pref₂ ++ suf₂).map SimSym.bit ++ [SimSym.endMark]) pos := by
  intro suf₁
  induction suf₁ with
  | nil =>
    intro suf₂ pref₁ pref₂ hSufLen hPrefLen hSum tape₁ tape₂ hM₁ hM₂
    cases suf₂ with
    | cons _ _ => simp at hSufLen
    | nil =>
      have hLen₁ : (SimSym.leftMark :: (pref₁ ++ []).map SimSym.bit ++ [SimSym.endMark]).length =
          nBits + 2 := by simp at hSum; simp; omega
      have hLen₂ : (SimSym.leftMark :: (pref₂ ++ []).map SimSym.bit ++ [SimSym.endMark]).length =
          nBits + 2 := by simp at hSum; simp; omega
      have hHeads : ∀ j,
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = t₁
        · subst h1; simpa [hM₁.head_eq] using Nat.lt_of_lt_of_le (by simp at hSum; omega : 1 + pref₁.length < nBits + 2) hBound₁
        · by_cases h2 : j = t₂
          · subst h2; simpa [h1, hM₂.head_eq] using Nat.lt_of_lt_of_le (by simp at hSum; omega : 1 + pref₂.length < nBits + 2) hBound₂
          · simpa [h1, h2] using hOtherBounds j h1 h2
      have hRead₁ : tape₁.cells tape₁.head = .endMark := by
        rw [hM₁.read_lt (by rw [hLen₁]; simp at hSum; omega)]
        simp only [List.append_nil, Nat.add_comm 1, List.cons_append, List.getElem_cons_succ]
        simp
      have hRead₂ : tape₂.cells tape₂.head = .endMark := by
        rw [hM₂.read_lt (by rw [hLen₂]; simp at hSum; omega)]
        simp only [List.append_nil, Nat.add_comm 1, List.cons_append, List.getElem_cons_succ]
        simp
      have hMove₁ : moveOneSidedHead (1 + pref₁.length) .stay = some (1 + pref₁.length) := rfl
      have hMove₂ : moveOneSidedHead (1 + pref₂.length) .stay = some (1 + pref₂.length) := rfl
      obtain ⟨ft₁, hUpd₁, hFM₁⟩ := hM₁.update_keep .stay hMove₁
      obtain ⟨ft₂, hUpd₂, hFM₂⟩ := hM₂.update_keep .stay hMove₂
      have hStepEq : (cmpBitScan InputAlphabet t₁ t₂).step () (readInput input inHead)
          (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
            (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
          twoTapeAction (.inr true) t₁ t₂ .endMark .endMark .stay .stay
            (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
              (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) := by
        simp only [cmpBitScan, cmpBitScanBody, TMComponent.loop, TMComponent.atom, TMAction.mapState,
          ↓reduceIte, hNe.symm, hRead₁, hRead₂]
        rfl
      refine ⟨1 + pref₁.length, ft₁, ft₂, by omega, by simp at hSum; omega, ?_, hFM₁, ?_⟩
      · exact twoTape_compStep_exit_override (cmpBitScan InputAlphabet t₁ t₂) t₁ t₂ hNe
          input bound initTapes tape₁ tape₂ ft₁ ft₂ () hHeads
          (by rw [hFM₁.head_eq]; simp at hSum; omega)
          (by rw [hFM₂.head_eq]; simp at hSum; omega)
          (by simpa [hRead₁] using hUpd₁) (by simpa [hRead₂] using hUpd₂) hStepEq
      · simpa [hPrefLen] using hFM₂
  | cons b₁ bs₁ ih =>
    intro suf₂ pref₁ pref₂ hSufLen hPrefLen hSum tape₁ tape₂ hM₁ hM₂
    cases suf₂ with
    | nil => simp at hSufLen
    | cons b₂ bs₂ =>
      have hHeads : ∀ j,
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = t₁
        · subst h1; simpa [hM₁.head_eq] using Nat.lt_of_lt_of_le (by simp at hSum; omega : 1 + pref₁.length < nBits + 2) hBound₁
        · by_cases h2 : j = t₂
          · subst h2; simpa [h1, hM₂.head_eq] using Nat.lt_of_lt_of_le (by simp at hSum; omega : 1 + pref₂.length < nBits + 2) hBound₂
          · simpa [h1, h2] using hOtherBounds j h1 h2
      have hRead₁ : tape₁.cells tape₁.head = .bit b₁ := by
        rw [hM₁.read_lt (by simp; simp at hSum; omega)]
        simp only [Nat.add_comm 1, List.cons_append, List.getElem_cons_succ, List.append_assoc,
          List.map_append, List.map_cons]
        simp
      have hRead₂ : tape₂.cells tape₂.head = .bit b₂ := by
        rw [hM₂.read_lt (by simp; simp at hSum; omega)]
        simp only [Nat.add_comm 1, List.cons_append, List.getElem_cons_succ, List.append_assoc,
          List.map_append, List.map_cons]
        simp
      by_cases hEqB : b₁ = b₂
      · subst hEqB
        have hMove₁ : moveOneSidedHead (1 + pref₁.length) .right =
            some (1 + (pref₁ ++ [b₁]).length) := by simp [moveOneSidedHead]; omega
        have hMove₂ : moveOneSidedHead (1 + pref₂.length) .right =
            some (1 + (pref₂ ++ [b₁]).length) := by simp [moveOneSidedHead]; omega
        obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM₁.update_keep .right hMove₁
        obtain ⟨nt₂, hUpd₂, hNM₂⟩ := hM₂.update_keep .right hMove₂
        have hAssoc₁ : (pref₁ ++ b₁ :: bs₁) = (pref₁ ++ [b₁]) ++ bs₁ := by simp
        have hAssoc₂ : (pref₂ ++ b₁ :: bs₂) = (pref₂ ++ [b₁]) ++ bs₂ := by simp
        rw [hAssoc₁] at hNM₁
        rw [hAssoc₂] at hNM₂
        obtain ⟨pos, ft₁, ft₂, hP1, hP2, hRest, hFM₁, hFM₂⟩ := ih bs₂ (pref₁ ++ [b₁]) (pref₂ ++ [b₁])
          (by simp at hSufLen; omega) (by simp [hPrefLen]) (by simp; simp at hSum; omega)
          nt₁ nt₂ hNM₁ hNM₂
        rw [← hAssoc₁] at hFM₁
        rw [← hAssoc₂] at hFM₂
        have hStepEq : (cmpBitScan InputAlphabet t₁ t₂).step () (readInput input inHead)
            (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
              (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
            twoTapeAction (.inl ()) t₁ t₂ (.bit b₁) (.bit b₁) .right .right
              (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) := by
          simp only [cmpBitScan, cmpBitScanBody, TMComponent.loop, TMComponent.atom, TMAction.mapState,
            ↓reduceIte, hNe.symm, hRead₁, hRead₂]
          rfl
        have hDecEq : decide ((b₁ :: bs₁) = (b₁ :: bs₂)) = decide (bs₁ = bs₂) := by simp
        rw [← hDecEq] at hRest
        refine ⟨pos, ft₁, ft₂, hP1, hP2, ?_, hFM₁, hFM₂⟩
        exact twoTape_compStep_head_override (cmpBitScan InputAlphabet t₁ t₂) t₁ t₂ hNe
          input bound initTapes tape₁ tape₂ nt₁ nt₂ ft₁ ft₂ () () hHeads
          (by rw [hNM₁.head_eq]; simp at hSum; simp; omega)
          (by rw [hNM₂.head_eq]; simp [hPrefLen] at hSum; simp; omega)
          (by simpa [hRead₁] using hUpd₁) (by simpa [hRead₂] using hUpd₂) hRest hStepEq
      · have hMove₁ : moveOneSidedHead (1 + pref₁.length) .stay = some (1 + pref₁.length) := rfl
        have hMove₂ : moveOneSidedHead (1 + pref₂.length) .stay = some (1 + pref₂.length) := rfl
        obtain ⟨ft₁, hUpd₁, hFM₁⟩ := hM₁.update_keep .stay hMove₁
        obtain ⟨ft₂, hUpd₂, hFM₂⟩ := hM₂.update_keep .stay hMove₂
        have hStepEq : (cmpBitScan InputAlphabet t₁ t₂).step () (readInput input inHead)
            (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
              (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
            twoTapeAction (.inr false) t₁ t₂ (.bit b₁) (.bit b₂) .stay .stay
              (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) := by
          simp only [cmpBitScan, cmpBitScanBody, TMComponent.loop, TMComponent.atom, TMAction.mapState,
            ↓reduceIte, hNe.symm, hRead₁, hRead₂, hEqB]
          rfl
        have hDecFalse : decide ((b₁ :: bs₁) = (b₂ :: bs₂)) = false := by simp [hEqB]
        rw [hDecFalse]
        refine ⟨1 + pref₁.length, ft₁, ft₂, by omega, by simp at hSum; omega, ?_, hFM₁, ?_⟩
        · exact twoTape_compStep_exit_override (cmpBitScan InputAlphabet t₁ t₂) t₁ t₂ hNe
            input bound initTapes tape₁ tape₂ ft₁ ft₂ () hHeads
            (by rw [hFM₁.head_eq]; simp at hSum; omega)
            (by rw [hFM₂.head_eq]; simp at hSum; omega)
            (by simpa [hRead₁] using hUpd₁) (by simpa [hRead₂] using hUpd₂) hStepEq
        · simpa [hPrefLen] using hFM₂

theorem compareBitTapes_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (bits₁ bits₂ : List Bool) (hSameLen : bits₁.length = bits₂.length)
    (hBound₁ : bits₁.length + 2 ≤ bound t₁)
    (hBound₂ : bits₂.length + 2 ≤ bound t₂)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t₁ → j ≠ t₂ → (initTapes j).head < bound j)
    (hMatch₁ : TapeMatches (initTapes t₁)
      (SimSym.leftMark :: bits₁.map SimSym.bit ++ [SimSym.endMark]) 1)
    (hMatch₂ : TapeMatches (initTapes t₂)
      (SimSym.leftMark :: bits₂.map SimSym.bit ++ [SimSym.endMark]) 1) :
    ∃ ft₁ ft₂,
      (compareBitTapes InputAlphabet t₁ t₂).ReachesExit input bound initTapes inHead
        (decide (bits₁ = bits₂))
        (fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j) inHead ∧
      TapeMatches ft₁ (SimSym.leftMark :: bits₁.map SimSym.bit ++ [SimSym.endMark]) 1 ∧
      TapeMatches ft₂ (SimSym.leftMark :: bits₂.map SimSym.bit ++ [SimSym.endMark]) 1 := by
  have hTapesSelf : (fun j => if j = t₁ then initTapes t₁
      else if j = t₂ then initTapes t₂ else initTapes j) = initTapes := by
    funext j
    by_cases h1 : j = t₁
    · subst h1; simp
    · by_cases h2 : j = t₂
      · subst h2; simp [hNe.symm]
      · simp [h1, h2]
  obtain ⟨pos, mt₁, mt₂, hPos1, hPosLe, hScan, hMM₁, hMM₂⟩ :=
    cmpBitScan_reachesExit t₁ t₂ hNe input bound bits₁.length hBound₁
      (by omega) initTapes inHead hOtherBounds bits₁ bits₂ [] [] hSameLen rfl (by simp)
      (initTapes t₁) (initTapes t₂) hMatch₁ hMatch₂
  rw [hTapesSelf] at hScan
  simp only [List.nil_append] at hMM₁ hMM₂
  let c₁ := SimSym.leftMark :: bits₁.map SimSym.bit ++ [SimSym.endMark]
  let c₂ := SimSym.leftMark :: bits₂.map SimSym.bit ++ [SimSym.endMark]
  have hNoLeft : ∀ (bs : List Bool) i, 1 ≤ i →
      i < (SimSym.leftMark :: bs.map SimSym.bit ++ [SimSym.endMark]).length →
      (SimSym.leftMark :: bs.map SimSym.bit ++ [SimSym.endMark])[i]? ≠ some SimSym.leftMark := by
    intro bs i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < bs.length
      · rw [List.getElem_append_left (by simp [hi])]
        simp
      · have hiEq : i' = bs.length := by omega
        rw [List.getElem_append_right (by simp [hiEq])]
        simp [hiEq]
  have hMidBounds : ∀ j, j ≠ t₁ →
      ((fun j => if j = t₁ then mt₁ else if j = t₂ then mt₂ else initTapes j) j).head < bound j := by
    intro j hj1
    by_cases hj2 : j = t₂
    · subst hj2; simpa [hj1, hMM₂.head_eq] using Nat.lt_of_lt_of_le (by omega : pos < bits₂.length + 2) hBound₂
    · simpa [hj1, hj2] using hOtherBounds j hj1 hj2
  obtain ⟨tapes₁, hRew₁, hFM₁, hOth₁⟩ := rewindTape_reachesExit t₁ input bound c₁ (by simp [c₁])
    rfl (hNoLeft bits₁) (by simp [c₁]; exact hBound₁) _ inHead hMidBounds pos hPos1
    (by simp [c₁]; omega) (by simpa [c₁] using hMM₁)
  have hMid₂Bounds : ∀ j, j ≠ t₂ → (tapes₁ j).head < bound j := by
    intro j hj2
    by_cases hj1 : j = t₁
    · subst hj1; simpa [hFM₁.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 < bits₁.length + 2) hBound₁
    · rw [hOth₁ j hj1]; simpa [hj1, hj2] using hOtherBounds j hj1 hj2
  have hT₁t₂ : tapes₁ t₂ = mt₂ := by simpa [hNe.symm] using hOth₁ t₂ hNe.symm
  obtain ⟨tapes₂, hRew₂, hFM₂, hOth₂⟩ := rewindTape_reachesExit t₂ input bound c₂ (by simp [c₂])
    rfl (hNoLeft bits₂) (by simp [c₂]; exact hBound₂) tapes₁ inHead hMid₂Bounds pos hPos1
    (by simp [c₂]; omega) (by rw [hT₁t₂]; simpa [c₂] using hMM₂)
  have hSeq := ((rewindTape InputAlphabet t₁).seq_reachesExit (rewindTape InputAlphabet t₂)
    input bound hRew₁ hRew₂)
  have hTapes₂Eq : tapes₂ = fun j => if j = t₁ then tapes₁ t₁
      else if j = t₂ then tapes₂ t₂ else initTapes j := by
    funext j
    by_cases hj1 : j = t₁
    · simp [hj1, hOth₂ t₁ hNe]
    · by_cases hj2 : j = t₂
      · simp [hj2, hNe.symm]
      · simp [hj1, hj2, hOth₂ j hj2, hOth₁ j hj1]
  rw [hTapes₂Eq] at hSeq
  refine ⟨tapes₁ t₁, tapes₂ t₂, ?_, hFM₁, hFM₂⟩
  refine (cmpBitScan InputAlphabet t₁ t₂).branch_reachesExit _ _ input bound
    (decide (bits₁ = bits₂)) hScan ?_
  cases hD : decide (bits₁ = bits₂)
  · simpa using TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hSeq
  · simpa using TMComponent.mapExit_reachesExit _ (fun _ => true) input bound hSeq

/-- Read a fixed-width block of `m` bits simultaneously from tapes `t₁` and `t₂`,
advancing both heads by `m` without modifying any tape cells. -/
def readFixedBits (InputAlphabet : Type*) {k : ℕ} (m : ℕ) (t₁ t₂ : Fin k) :
    TMComponent (Fin (m + 1) × (Fin m → Bool) × (Fin m → Bool)) InputAlphabet SimSym k
      (Option ((Fin m → Bool) × (Fin m → Bool))) where
  start := (⟨0, Nat.zero_lt_succ m⟩, fun _ => false, fun _ => false)
  step s _ scanned :=
    let idx := s.1
    let a₁ := s.2.1
    let a₂ := s.2.2
    if h : idx.val < m then
      match scanned t₁, scanned t₂ with
      | .bit b₁, .bit b₂ =>
        let a₁' : Fin m → Bool := fun j => if j.val = idx.val then b₁ else a₁ j
        let a₂' : Fin m → Bool := fun j => if j.val = idx.val then b₂ else a₂ j
        if hNext : idx.val + 1 = m then
          twoTapeAction (.inr (some (a₁', a₂'))) t₁ t₂ (.bit b₁) (.bit b₂) .right .right scanned
        else
          twoTapeAction (.inl (⟨idx.val + 1, by omega⟩, a₁', a₂'))
            t₁ t₂ (.bit b₁) (.bit b₂) .right .right scanned
      | s₁, s₂ =>
        twoTapeAction (.inr none) t₁ t₂ s₁ s₂ .stay .stay scanned
    else
      twoTapeAction (.inr (some (a₁, a₂))) t₁ t₂ (scanned t₁) (scanned t₂) .stay .stay scanned

theorem readFixedBits_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (m : ℕ) (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (pref₁ suf₁ pref₂ suf₂ : List SimSym) (slice₁ slice₂ : List Bool)
    (hLen₁ : slice₁.length = m) (hLen₂ : slice₂.length = m)
    (hBound₁ : pref₁.length + m < bound t₁) (hBound₂ : pref₂.length + m < bound t₂)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t₁ → j ≠ t₂ → (initTapes j).head < bound j)
    (hMatch₁ : TapeMatches (initTapes t₁) (pref₁ ++ slice₁.map SimSym.bit ++ suf₁) pref₁.length)
    (hMatch₂ : TapeMatches (initTapes t₂) (pref₂ ++ slice₂.map SimSym.bit ++ suf₂) pref₂.length) :
    ∃ ft₁ ft₂,
      (readFixedBits InputAlphabet m t₁ t₂).ReachesExit input bound initTapes inHead
        (some (fun i : Fin m => slice₁[i.val]'(by omega),
               fun i : Fin m => slice₂[i.val]'(by omega)))
        (fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j) inHead ∧
      TapeMatches ft₁ (pref₁ ++ slice₁.map SimSym.bit ++ suf₁) (pref₁.length + m) ∧
      TapeMatches ft₂ (pref₂ ++ slice₂.map SimSym.bit ++ suf₂) (pref₂.length + m) ∧
      ft₁.cells = (initTapes t₁).cells ∧
      ft₂.cells = (initTapes t₂).cells := by
  cases m with
  | zero =>
    have hHeads : ∀ j, (initTapes j).head < bound j := by
      intro j
      by_cases h1 : j = t₁
      · subst h1; simpa [hMatch₁.head_eq] using hBound₁
      · by_cases h2 : j = t₂
        · subst h2; simpa [hMatch₂.head_eq] using hBound₂
        · exact hOtherBounds j h1 h2
    have hMove₁ : moveOneSidedHead pref₁.length .stay = some pref₁.length := rfl
    have hMove₂ : moveOneSidedHead pref₂.length .stay = some pref₂.length := rfl
    obtain ⟨ft₁, hUpd₁, hFM₁⟩ := hMatch₁.update_keep .stay hMove₁
    obtain ⟨ft₂, hUpd₂, hFM₂⟩ := hMatch₂.update_keep .stay hMove₂
    have hCells₁ : ft₁.cells = (initTapes t₁).cells := by funext i; exact (hFM₁.2 i).trans (hMatch₁.2 i).symm
    have hCells₂ : ft₂.cells = (initTapes t₂).cells := by funext i; exact (hFM₂.2 i).trans (hMatch₂.2 i).symm
    refine ⟨ft₁, ft₂, ?_, hFM₁, hFM₂, hCells₁, hCells₂⟩
    have hFunEq : (fun i : Fin 0 => slice₁[i.val]'(by omega), fun i : Fin 0 => slice₂[i.val]'(by omega)) =
        ((fun _ => false : Fin 0 → Bool), (fun _ => false : Fin 0 → Bool)) := by
      ext i <;> exact i.elim0
    rw [hFunEq]
    refine compStep_exit_reachesExit (readFixedBits InputAlphabet 0 t₁ t₂) input bound hHeads
      (fun j => ?_) (by simp [readFixedBits]; rfl) (by simp [readFixedBits, twoTapeAction, moveHead])
      (fun j => ?_)
    · by_cases h1 : j = t₁
      · subst h1; simpa [hFM₁.head_eq] using hBound₁
      · by_cases h2 : j = t₂
        · subst h2; simpa [h1, hFM₂.head_eq] using hBound₂
        · simpa [h1, h2] using hOtherBounds j h1 h2
    · simp only [readFixedBits, Nat.lt_irrefl, ↓reduceDIte]
      have hApp := twoTapeAction_apply
        (Sum.inr (some (fun _ => false, fun _ => false)) :
          (Fin 1 × (Fin 0 → Bool) × (Fin 0 → Bool)) ⊕ Option ((Fin 0 → Bool) × (Fin 0 → Bool)))
        t₁ t₂ hNe ((initTapes t₁).cells (initTapes t₁).head)
        ((initTapes t₂).cells (initTapes t₂).head) .stay .stay initTapes hUpd₁ hUpd₂ j
      by_cases h1 : j = t₁
      · subst h1; simpa using hApp
      · by_cases h2 : j = t₂
        · subst h2; simpa [h1] using hApp
        · simpa [h1, h2] using hApp
  | succ m' =>
    have hLoop : ∀ rem, rem ≤ m' + 1 →
        ∀ (a₁ a₂ : Fin (m' + 1) → Bool)
          (tape₁ tape₂ : OneSidedTape SimSym),
          let idx := (m' + 1) - rem
          (∀ j : Fin (m' + 1), j.val < idx → a₁ j = slice₁[j.val]'(by omega)) →
          (∀ j : Fin (m' + 1), j.val < idx → a₂ j = slice₂[j.val]'(by omega)) →
          TapeMatches tape₁ (pref₁ ++ slice₁.map SimSym.bit ++ suf₁) (pref₁.length + idx) →
          TapeMatches tape₂ (pref₂ ++ slice₂.map SimSym.bit ++ suf₂) (pref₂.length + idx) →
          0 < rem →
          ∃ ft₁ ft₂,
            Relation.ReflTransGen
              (fun a b => (readFixedBits InputAlphabet (m' + 1) t₁ t₂).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl (⟨idx, by omega⟩, a₁, a₂), inHead,
                fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j⟩
              ⟨.inr (some (fun i : Fin (m' + 1) => slice₁[i.val]'(by omega),
                           fun i : Fin (m' + 1) => slice₂[i.val]'(by omega))),
                inHead,
                fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j⟩ ∧
            TapeMatches ft₁ (pref₁ ++ slice₁.map SimSym.bit ++ suf₁) (pref₁.length + (m' + 1)) ∧
            TapeMatches ft₂ (pref₂ ++ slice₂.map SimSym.bit ++ suf₂) (pref₂.length + (m' + 1)) ∧
            ft₁.cells = tape₁.cells ∧
            ft₂.cells = tape₂.cells := by
      intro rem
      induction rem with
      | zero => intro _ _ _ _ _ _ _ _ _ hPos; omega
      | succ r ih =>
        intro hLe a₁ a₂ tape₁ tape₂ idx ha₁ ha₂ hM₁ hM₂ _
        have hIdxLt : idx < m' + 1 := by simp [idx]; omega
        have hHeads : ∀ j,
            (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j := by
          intro j
          by_cases h1 : j = t₁
          · subst h1; simpa [hM₁.head_eq] using Nat.lt_trans (by omega : pref₁.length + idx < pref₁.length + (m' + 1)) hBound₁
          · by_cases h2 : j = t₂
            · subst h2; simpa [h1, hM₂.head_eq] using Nat.lt_trans (by omega : pref₂.length + idx < pref₂.length + (m' + 1)) hBound₂
            · simpa [h1, h2] using hOtherBounds j h1 h2
        let b₁ := slice₁[idx]'(by omega)
        let b₂ := slice₂[idx]'(by omega)
        have hRead₁ : tape₁.cells tape₁.head = .bit b₁ := by
          have hM₁' : TapeMatches tape₁ (pref₁ ++ (slice₁.map SimSym.bit ++ suf₁))
              (pref₁.length + idx) := by simpa [List.append_assoc] using hM₁
          rw [hM₁'.read_lt (by simp; omega)]
          simp [List.getElem_append_right, List.getElem_append_left, hLen₁, hIdxLt, b₁]
        have hRead₂ : tape₂.cells tape₂.head = .bit b₂ := by
          have hM₂' : TapeMatches tape₂ (pref₂ ++ (slice₂.map SimSym.bit ++ suf₂))
              (pref₂.length + idx) := by simpa [List.append_assoc] using hM₂
          rw [hM₂'.read_lt (by simp; omega)]
          simp [List.getElem_append_right, List.getElem_append_left, hLen₂, hIdxLt, b₂]
        have hMove₁ : moveOneSidedHead (pref₁.length + idx) .right = some (pref₁.length + (idx + 1)) := by
          simp [moveOneSidedHead]; omega
        have hMove₂ : moveOneSidedHead (pref₂.length + idx) .right = some (pref₂.length + (idx + 1)) := by
          simp [moveOneSidedHead]; omega
        obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM₁.update_keep .right hMove₁
        obtain ⟨nt₂, hUpd₂, hNM₂⟩ := hM₂.update_keep .right hMove₂
        have hC₁ : nt₁.cells = tape₁.cells := by funext i; exact (hNM₁.2 i).trans (hM₁.2 i).symm
        have hC₂ : nt₂.cells = tape₂.cells := by funext i; exact (hNM₂.2 i).trans (hM₂.2 i).symm
        let a₁' : Fin (m' + 1) → Bool := fun j => if j.val = idx then b₁ else a₁ j
        let a₂' : Fin (m' + 1) → Bool := fun j => if j.val = idx then b₂ else a₂ j
        have ha₁' : ∀ j : Fin (m' + 1), j.val < idx + 1 → a₁' j = slice₁[j.val]'(by omega) := by
          intro j hj
          by_cases hjEq : j.val = idx
          · simp [a₁', hjEq, b₁]
          · simp [a₁', hjEq]; exact ha₁ j (by omega)
        have ha₂' : ∀ j : Fin (m' + 1), j.val < idx + 1 → a₂' j = slice₂[j.val]'(by omega) := by
          intro j hj
          by_cases hjEq : j.val = idx
          · simp [a₂', hjEq, b₂]
          · simp [a₂', hjEq]; exact ha₂ j (by omega)
        cases r with
        | zero =>
          have hLast : idx + 1 = m' + 1 := by simp [idx]
          have hA₁Eq : a₁' = fun i : Fin (m' + 1) => slice₁[i.val]'(by omega) := by
            funext i; exact ha₁' i (by omega)
          have hA₂Eq : a₂' = fun i : Fin (m' + 1) => slice₂[i.val]'(by omega) := by
            funext i; exact ha₂' i (by omega)
          have hStepEq : (readFixedBits InputAlphabet (m' + 1) t₁ t₂).step
              (⟨idx, by omega⟩, a₁, a₂) (readInput input inHead)
              (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
              twoTapeAction
                (Sum.inr (some (fun i : Fin (m' + 1) => slice₁[i.val]'(by omega),
                                fun i : Fin (m' + 1) => slice₂[i.val]'(by omega))))
                t₁ t₂ (.bit b₁) (.bit b₂) .right .right
                (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                  (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) := by
            simp only [readFixedBits, hIdxLt, ↓reduceDIte, ↓reduceIte, hNe.symm, hRead₁, hRead₂, hLast]
            rw [← hA₁Eq, ← hA₂Eq]
          rw [hLast] at hNM₁ hNM₂
          refine ⟨nt₁, nt₂, ?_, hNM₁, hNM₂, hC₁, hC₂⟩
          exact twoTape_compStep_exit_override (readFixedBits InputAlphabet (m' + 1) t₁ t₂)
            t₁ t₂ hNe input bound initTapes tape₁ tape₂ nt₁ nt₂ (⟨idx, by omega⟩, a₁, a₂)
            hHeads (by rw [hNM₁.head_eq]; exact hBound₁) (by rw [hNM₂.head_eq]; exact hBound₂)
            (by simpa [hRead₁] using hUpd₁) (by simpa [hRead₂] using hUpd₂) hStepEq
        | succ r' =>
          have hNotLast : idx + 1 ≠ m' + 1 := by simp [idx]; omega
          have hIdxNext : m' + 1 - (r' + 1) = idx + 1 := by simp [idx]; omega
          rw [← hIdxNext] at ha₁' ha₂' hNM₁ hNM₂
          obtain ⟨ft₁, ft₂, hRest, hFM₁, hFM₂, hFC₁, hFC₂⟩ :=
            ih (by omega) a₁' a₂' nt₁ nt₂ ha₁' ha₂' hNM₁ hNM₂ (by omega)
          have hStepEq : (readFixedBits InputAlphabet (m' + 1) t₁ t₂).step
              (⟨idx, by omega⟩, a₁, a₂) (readInput input inHead)
              (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
              twoTapeAction
                (Sum.inl (⟨m' + 1 - (r' + 1), by omega⟩, a₁', a₂'))
                t₁ t₂ (.bit b₁) (.bit b₂) .right .right
                (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
                  (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) := by
            simp only [readFixedBits, hIdxLt, ↓reduceDIte, ↓reduceIte, hNe.symm, hRead₁, hRead₂, hNotLast]
            simp only [hIdxNext]
            rfl
          refine ⟨ft₁, ft₂, ?_, hFM₁, hFM₂, hFC₁.trans hC₁, hFC₂.trans hC₂⟩
          exact twoTape_compStep_head_override (readFixedBits InputAlphabet (m' + 1) t₁ t₂)
            t₁ t₂ hNe input bound initTapes tape₁ tape₂ nt₁ nt₂ ft₁ ft₂
            (⟨idx, by omega⟩, a₁, a₂) (⟨m' + 1 - (r' + 1), by omega⟩, a₁', a₂') hHeads
            (by rw [hNM₁.head_eq, hIdxNext]; omega)
            (by rw [hNM₂.head_eq, hIdxNext]; omega)
            (by simpa [hRead₁] using hUpd₁) (by simpa [hRead₂] using hUpd₂) hRest hStepEq
    have hTapesSelf : (fun j => if j = t₁ then initTapes t₁
        else if j = t₂ then initTapes t₂ else initTapes j) = initTapes := by
      funext j
      by_cases h1 : j = t₁
      · subst h1; simp
      · by_cases h2 : j = t₂
        · subst h2; simp [hNe.symm]
        · simp [h1, h2]
    obtain ⟨ft₁, ft₂, hRun, hFM₁, hFM₂, hFC₁, hFC₂⟩ := hLoop (m' + 1) le_rfl
      (fun _ => false) (fun _ => false) (initTapes t₁) (initTapes t₂)
      (fun j hj => by simp at hj) (fun j hj => by simp at hj)
      (by simpa using hMatch₁) (by simpa using hMatch₂) (by omega)
    simp only [Nat.sub_self] at hRun
    rw [hTapesSelf] at hRun
    exact ⟨ft₁, ft₂, hRun, hFM₁, hFM₂, hFC₁, hFC₂⟩

end SavitchLemma

module

public import SavitchLemma.RegisterTape.Layout

@[expose] public section

/-!
# Register copying

Copies a register bit block to a work tape and proves the corresponding exit behavior.
-/

namespace SavitchLemma

/-- Copy the `bits` block from a register on `tRegs` (head initially on its `.tag _` cell)
onto `dst` (head initially at cell `1`), terminating with `tRegs` back on that `.tag _`
cell and `dst` rewound to cell `1` holding `[.leftMark] ++ bits ++ [.endMark]`. -/
inductive CopyRegState where
  | stepTag
  | copyLoop
  | rewRegs
  deriving DecidableEq

def CopyRegState.equivFin : CopyRegState ≃ Fin 3 where
  toFun | .stepTag => 0 | .copyLoop => 1 | .rewRegs => 2
  invFun | 0 => .stepTag | 1 => .copyLoop | _ => .rewRegs
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype CopyRegState := Fintype.ofEquiv (Fin 3) CopyRegState.equivFin.symm

theorem TapeMatches.update_append_move {tape : OneSidedTape SimSym} {contents : List SimSym}
    {pos : ℕ} (h : TapeMatches tape contents pos) (hPos : pos = contents.length)
    (sym : SimSym) (mv : TapeMove) {nextPos : ℕ} (hMove : moveOneSidedHead pos mv = some nextPos) :
    ∃ nextTape, tape.updateAndMove sym mv = some nextTape ∧
      TapeMatches nextTape (contents ++ [sym]) nextPos := by
  have hMove' : moveOneSidedHead tape.head mv = some nextPos := by rw [h.1]; exact hMove
  refine ⟨⟨fun i => if i = tape.head then sym else tape.cells i, nextPos⟩, ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove']
  · intro i
    dsimp only
    rw [h.1, hPos]
    by_cases hi : i = contents.length
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      rw [h.2 i]
      by_cases hLt : i < contents.length
      · rw [List.getElem?_append_left hLt]
      · have hNone1 : contents[i]? = none := List.getElem?_eq_none (by omega)
        have hNone2 : (contents ++ [sym])[i]? = none := by
          apply List.getElem?_eq_none; simp; omega
        rw [hNone1, hNone2]

def copyRegBody (InputAlphabet : Type*) (dst : Fin 5) :
    TMComponent CopyRegState InputAlphabet SimSym 5 Unit where
  start := .stepTag
  step s _ scanned :=
    match s with
    | .stepTag =>
      twoTapeAction (.inl .copyLoop) tRegs dst (scanned tRegs) (scanned dst) .right .stay scanned
    | .copyLoop =>
      match scanned tRegs with
      | .bit b =>
        twoTapeAction (.inl .copyLoop) tRegs dst (.bit b) (.bit b) .right .right scanned
      | sym =>
        twoTapeAction (.inl .rewRegs) tRegs dst sym .endMark .left .stay scanned
    | .rewRegs =>
      match scanned tRegs with
      | .tag b =>
        twoTapeAction (.inr ()) tRegs dst (.tag b) (scanned dst) .stay .stay scanned
      | sym =>
        twoTapeAction (.inl .rewRegs) tRegs dst sym (scanned dst) .left .stay scanned

def copyRegBitsTo (InputAlphabet : Type*) (dst : Fin 5) :=
  (copyRegBody InputAlphabet dst).seq (rewindTape InputAlphabet dst)

private theorem copyRegBody_rewRegs {InputAlphabet : Type*} {n : ℕ}
    (dst : Fin 5) (hNe : tRegs ≠ dst)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool) (bits : List Bool) (tailSym : SimSym)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : pref.length + bits.length + 2 ≤ bound tRegs)
    (hBoundDst : bits.length + 2 ≤ bound dst)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ dst → (initTapes j).head < bound j) :
    ∀ pos, pos ≤ bits.length →
      ∀ tapeReg tapeDst,
        TapeMatches tapeReg
          (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
          (pref.length + pos) →
        TapeMatches tapeDst
          (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark])
          (1 + bits.length) →
        Relation.ReflTransGen
          (fun a b => (copyRegBody InputAlphabet dst).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .rewRegs, inHead,
            fun j => if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j⟩
          ⟨.inr (), inHead,
            fun j => if j = tRegs then ⟨tapeReg.cells, pref.length⟩
                     else if j = dst then tapeDst else initTapes j⟩ := by
  intro pos
  induction pos with
  | zero =>
    intro _ tapeReg tapeDst hMReg hMDst
    have hMReg' : TapeMatches tapeReg
        (pref ++ SimSym.tag b :: (bits.map SimSym.bit ++ tailSym :: suf)) pref.length := by
      simpa [List.append_assoc] using hMReg
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg'.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + bits.length + 2) hBoundReg
      · by_cases h2 : j = dst
        · subst h2; simpa [h1, hMDst.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + bits.length < bits.length + 2) hBoundDst
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hRead : tapeReg.cells tapeReg.head = .tag b := by
      rw [hMReg'.read_lt (by simp)]
      exact list_get_append_mid pref (.tag b) _
    have hMoveR : moveOneSidedHead pref.length .stay = some pref.length := rfl
    have hMoveD : moveOneSidedHead (1 + bits.length) .stay = some (1 + bits.length) := rfl
    obtain ⟨ftR, hUpdR, hFMR⟩ := hMReg'.update_keep .stay hMoveR
    obtain ⟨ftD, hUpdD, hFMD⟩ := hMDst.update_keep .stay hMoveD
    have hEqR : ftR = ⟨tapeReg.cells, pref.length⟩ := by
      have hCells : ftR.cells = tapeReg.cells := by funext i; exact (hFMR.2 i).trans (hMReg'.2 i).symm
      cases ftR; simp only [OneSidedTape.mk.injEq]; exact ⟨hCells, hFMR.head_eq⟩
    have hEqD : ftD = tapeDst := by
      have hCells : ftD.cells = tapeDst.cells := by funext i; exact (hFMD.2 i).trans (hMDst.2 i).symm
      have hHead : ftD.head = tapeDst.head := hFMD.head_eq.trans hMDst.head_eq.symm
      cases ftD; cases tapeDst; simp only [OneSidedTape.mk.injEq]; exact ⟨hCells, hHead⟩
    rw [hEqR] at hUpdR
    rw [hEqD] at hUpdD
    have hStepEq : (copyRegBody InputAlphabet dst).step .rewRegs (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
          (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) =
        twoTapeAction (.inr ()) tRegs dst (.tag b) (tapeDst.cells tapeDst.head) .stay .stay
          (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
            (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) := by
      simp only [copyRegBody, ↓reduceIte, hNe.symm, hRead]
    exact twoTape_compStep_exit_override (copyRegBody InputAlphabet dst) tRegs dst hNe
      input bound initTapes tapeReg tapeDst ⟨tapeReg.cells, pref.length⟩ tapeDst .rewRegs
      hHeads (by simp; omega) (by rw [hMDst.head_eq]; omega)
      (by simpa [hRead] using hUpdR) hUpdD hStepEq
  | succ p ih =>
    intro hpLe tapeReg tapeDst hMReg hMDst
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length + (p + 1) < pref.length + bits.length + 2) hBoundReg
      · by_cases h2 : j = dst
        · subst h2; simpa [h1, hMDst.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + bits.length < bits.length + 2) hBoundDst
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hNotTag : ∀ x : Bool, tapeReg.cells tapeReg.head ≠ .tag x := by
      intro x
      have hMReg' : TapeMatches tapeReg
          (pref ++ SimSym.tag b :: (bits.map SimSym.bit ++ tailSym :: suf))
          (pref.length + (p + 1)) := by simpa [List.append_assoc] using hMReg
      rw [hMReg'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + (p + 1))]
      have hSub : pref.length + (p + 1) - pref.length = p + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      have hpLt : p < (bits.map SimSym.bit).length := by simp; omega
      simp [List.getElem_append_left hpLt]
    have hMoveR : moveOneSidedHead (pref.length + (p + 1)) .left = some (pref.length + p) := by
      simp [moveOneSidedHead]
    have hMoveD : moveOneSidedHead (1 + bits.length) .stay = some (1 + bits.length) := rfl
    obtain ⟨ntR, hUpdR, hNMR⟩ := hMReg.update_keep .left hMoveR
    obtain ⟨ntD, hUpdD, hNMD⟩ := hMDst.update_keep .stay hMoveD
    have hCellsR : ntR.cells = tapeReg.cells := by funext i; exact (hNMR.2 i).trans (hMReg.2 i).symm
    have hEqD : ntD = tapeDst := by
      have hCells : ntD.cells = tapeDst.cells := by funext i; exact (hNMD.2 i).trans (hMDst.2 i).symm
      have hHead : ntD.head = tapeDst.head := hNMD.head_eq.trans hMDst.head_eq.symm
      cases ntD; cases tapeDst; simp only [OneSidedTape.mk.injEq]; exact ⟨hCells, hHead⟩
    rw [hEqD] at hUpdD
    have hRest := ih (by omega) ntR tapeDst hNMR hMDst
    have hTargetR : (⟨ntR.cells, pref.length⟩ : OneSidedTape SimSym) = ⟨tapeReg.cells, pref.length⟩ := by
      rw [hCellsR]
    rw [hTargetR] at hRest
    have hStepEq : (copyRegBody InputAlphabet dst).step .rewRegs (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
          (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) =
        twoTapeAction (.inl .rewRegs) tRegs dst (tapeReg.cells tapeReg.head)
          (tapeDst.cells tapeDst.head) .left .stay
          (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
            (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) := by
      simp only [copyRegBody, ↓reduceIte, hNe.symm]
    exact twoTape_compStep_head_override (copyRegBody InputAlphabet dst) tRegs dst hNe
      input bound initTapes tapeReg tapeDst ntR tapeDst ⟨tapeReg.cells, pref.length⟩ tapeDst
      .rewRegs .rewRegs hHeads (by rw [hNMR.head_eq]; omega) (by rw [hMDst.head_eq]; omega)
      hUpdR hUpdD hRest hStepEq

private theorem copyRegBody_copyLoop {InputAlphabet : Type*} {n : ℕ}
    (dst : Fin 5) (hNe : tRegs ≠ dst)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool) (bits : List Bool) (tailSym : SimSym)
    (hTailNotBit : ∀ x : Bool, tailSym ≠ .bit x)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : pref.length + bits.length + 2 ≤ bound tRegs)
    (hBoundDst : bits.length + 2 ≤ bound dst)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ dst → (initTapes j).head < bound j) :
    ∀ (sufB prefB : List Bool),
      prefB ++ sufB = bits →
      ∀ tapeReg tapeDst,
        TapeMatches tapeReg
          (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
          (pref.length + 1 + prefB.length) →
        TapeMatches tapeDst
          (SimSym.leftMark :: prefB.map SimSym.bit)
          (1 + prefB.length) →
        ∃ ftD,
          Relation.ReflTransGen
            (fun a b => (copyRegBody InputAlphabet dst).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .copyLoop, inHead,
              fun j => if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j⟩
            ⟨.inr (), inHead,
              fun j => if j = tRegs then ⟨tapeReg.cells, pref.length⟩
                       else if j = dst then ftD else initTapes j⟩ ∧
          TapeMatches ftD (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) (1 + bits.length) := by
  intro sufB
  induction sufB with
  | nil =>
    intro prefB hPB tapeReg tapeDst hMReg hMDst
    have hPB' : prefB = bits := by simpa using hPB
    subst hPB'
    have hMReg' : TapeMatches tapeReg
        ((pref ++ SimSym.tag b :: prefB.map SimSym.bit) ++ tailSym :: suf)
        (pref ++ SimSym.tag b :: prefB.map SimSym.bit).length := by
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using hMReg
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg'.head_eq] using Nat.lt_of_lt_of_le (by simp; omega : (pref ++ SimSym.tag b :: prefB.map SimSym.bit).length < pref.length + prefB.length + 2) hBoundReg
      · by_cases h2 : j = dst
        · subst h2; simpa [h1, hMDst.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + prefB.length < prefB.length + 2) hBoundDst
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hRead : tapeReg.cells tapeReg.head = tailSym := by
      rw [hMReg'.read_lt (by simp)]
      exact list_get_append_mid (pref ++ SimSym.tag b :: prefB.map SimSym.bit) tailSym suf
    have hMoveR : moveOneSidedHead (pref.length + 1 + prefB.length) .left =
        some (pref.length + prefB.length) := by simp [moveOneSidedHead]
    have hMoveD : moveOneSidedHead (1 + prefB.length) .stay = some (1 + prefB.length) := rfl
    obtain ⟨ntR, hUpdR, hNMR⟩ := hMReg.update_keep .left hMoveR
    obtain ⟨ntD, hUpdD, hNMD⟩ := hMDst.update_append_move (by simp; omega) .endMark .stay hMoveD
    have hCellsR : ntR.cells = tapeReg.cells := by funext i; exact (hNMR.2 i).trans (hMReg.2 i).symm
    have hNMD' : TapeMatches ntD
        (SimSym.leftMark :: prefB.map SimSym.bit ++ [SimSym.endMark]) (1 + prefB.length) := by
      simpa [List.append_assoc] using hNMD
    have hRew := copyRegBody_rewRegs dst hNe input bound pref suf b prefB tailSym initTapes inHead
      hBoundReg hBoundDst hOtherBounds prefB.length le_rfl ntR ntD hNMR hNMD'
    have hTargetR : (⟨ntR.cells, pref.length⟩ : OneSidedTape SimSym) = ⟨tapeReg.cells, pref.length⟩ := by
      rw [hCellsR]
    rw [hTargetR] at hRew
    have hStepEq : (copyRegBody InputAlphabet dst).step .copyLoop (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
          (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) =
        twoTapeAction (.inl .rewRegs) tRegs dst tailSym .endMark .left .stay
          (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
            (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) := by
      simp only [copyRegBody, ↓reduceIte, hRead]
    refine ⟨ntD, ?_, hNMD'⟩
    exact twoTape_compStep_head_override (copyRegBody InputAlphabet dst) tRegs dst hNe
      input bound initTapes tapeReg tapeDst ntR ntD ⟨tapeReg.cells, pref.length⟩ ntD
      .copyLoop .rewRegs hHeads (by rw [hNMR.head_eq]; omega) (by rw [hNMD'.head_eq]; omega)
      (by simpa [hRead] using hUpdR) hUpdD hRew hStepEq
  | cons x xs ih =>
    intro prefB hPB tapeReg tapeDst hMReg hMDst
    have hLenSum : prefB.length + (xs.length + 1) = bits.length := by
      have := congrArg List.length hPB
      simpa using this
    have hMReg' : TapeMatches tapeReg
        (pref ++ SimSym.tag b :: (bits.map SimSym.bit ++ tailSym :: suf))
        (pref.length + 1 + prefB.length) := by simpa [List.append_assoc] using hMReg
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg'.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length + 1 + prefB.length < pref.length + bits.length + 2) hBoundReg
      · by_cases h2 : j = dst
        · subst h2; simpa [h1, hMDst.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + prefB.length < bits.length + 2) hBoundDst
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hRead : tapeReg.cells tapeReg.head = .bit x := by
      rw [hMReg'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + 1 + prefB.length)]
      have hSub : pref.length + 1 + prefB.length - pref.length = prefB.length + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      rw [List.getElem_append_left (by simp; omega)]
      simp [← hPB]
    have hMoveR : moveOneSidedHead (pref.length + 1 + prefB.length) .right =
        some (pref.length + 1 + (prefB ++ [x]).length) := by simp [moveOneSidedHead]; omega
    have hMoveD : moveOneSidedHead (1 + prefB.length) .right = some (1 + (prefB ++ [x]).length) := by
      simp [moveOneSidedHead]; omega
    obtain ⟨ntR, hUpdR, hNMR⟩ := hMReg.update_keep .right hMoveR
    obtain ⟨ntD, hUpdD, hNMD⟩ := hMDst.update_append_move (by simp; omega) (.bit x) .right hMoveD
    have hCellsR : ntR.cells = tapeReg.cells := by funext i; exact (hNMR.2 i).trans (hMReg.2 i).symm
    have hNMD' : TapeMatches ntD (SimSym.leftMark :: (prefB ++ [x]).map SimSym.bit)
        (1 + (prefB ++ [x]).length) := by
      simpa [List.append_assoc] using hNMD
    obtain ⟨ftD, hRest, hFMD⟩ := ih (prefB ++ [x]) (by simpa using hPB) ntR ntD hNMR hNMD'
    have hTargetR : (⟨ntR.cells, pref.length⟩ : OneSidedTape SimSym) = ⟨tapeReg.cells, pref.length⟩ := by
      rw [hCellsR]
    rw [hTargetR] at hRest
    have hStepEq : (copyRegBody InputAlphabet dst).step .copyLoop (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
          (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) =
        twoTapeAction (.inl .copyLoop) tRegs dst (.bit x) (.bit x) .right .right
          (fun j => (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).cells
            (if j = tRegs then tapeReg else if j = dst then tapeDst else initTapes j).head) := by
      simp [copyRegBody, ↓reduceIte, hRead]
    refine ⟨ftD, ?_, hFMD⟩
    exact twoTape_compStep_head_override (copyRegBody InputAlphabet dst) tRegs dst hNe
      input bound initTapes tapeReg tapeDst ntR ntD ⟨tapeReg.cells, pref.length⟩ ftD
      .copyLoop .copyLoop hHeads (by rw [hNMR.head_eq]; simp; omega) (by rw [hNMD'.head_eq]; simp; omega)
      (by simpa [hRead] using hUpdR) hUpdD hRest hStepEq

theorem copyRegBitsTo_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (dst : Fin 5) (hNe : tRegs ≠ dst)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool) (bits : List Bool) (tailSym : SimSym)
    (hTailNotBit : ∀ x : Bool, tailSym ≠ .bit x)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : pref.length + bits.length + 2 ≤ bound tRegs)
    (hBoundDst : bits.length + 2 ≤ bound dst)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ dst → (initTapes j).head < bound j)
    (hMatchReg : TapeMatches (initTapes tRegs)
      (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf) pref.length)
    (hMatchDst : TapeMatches (initTapes dst) [SimSym.leftMark] 1) :
    ∃ ftD,
      (copyRegBitsTo InputAlphabet dst).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRegs then initTapes tRegs else if j = dst then ftD else initTapes j)
        inHead ∧
      TapeMatches ftD (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) 1 := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases h1 : j = tRegs
    · subst h1; simpa [hMatchReg.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + bits.length + 2) hBoundReg
    · by_cases h2 : j = dst
      · subst h2; simpa [hMatchDst.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 < bits.length + 2) hBoundDst
      · exact hOtherBounds j h1 h2
  have hMoveR : moveOneSidedHead pref.length .right = some (pref.length + 1) := by
    simp [moveOneSidedHead]
  have hMoveD : moveOneSidedHead 1 .stay = some 1 := rfl
  obtain ⟨ntR, hUpdR, hNMR⟩ := hMatchReg.update_keep .right hMoveR
  obtain ⟨ntD, hUpdD, hNMD⟩ := hMatchDst.update_keep .stay hMoveD
  have hCellsR : ntR.cells = (initTapes tRegs).cells := by
    funext i; exact (hNMR.2 i).trans (hMatchReg.2 i).symm
  have hEqD : ntD = initTapes dst := by
    have hCells : ntD.cells = (initTapes dst).cells := by
      funext i; exact (hNMD.2 i).trans (hMatchDst.2 i).symm
    have hHead : ntD.head = (initTapes dst).head := hNMD.head_eq.trans hMatchDst.head_eq.symm
    cases hD : initTapes dst
    simp only [hD] at hCells hHead
    cases ntD; simp only [OneSidedTape.mk.injEq]; exact ⟨hCells, hHead⟩
  rw [hEqD] at hUpdD
  obtain ⟨mtD, hLoop, hMMD⟩ := copyRegBody_copyLoop dst hNe input bound pref suf b bits tailSym
    hTailNotBit initTapes inHead hBoundReg hBoundDst hOtherBounds bits [] rfl ntR (initTapes dst)
    (by simpa using hNMR) (by simpa using hMatchDst)
  have hBackReg : (⟨ntR.cells, pref.length⟩ : OneSidedTape SimSym) = initTapes tRegs := by
    have hHead : (initTapes tRegs).head = pref.length := hMatchReg.head_eq
    cases hR : initTapes tRegs
    simp only [hR] at hCellsR hHead
    simp only [OneSidedTape.mk.injEq]; exact ⟨hCellsR, hHead.symm⟩
  rw [hBackReg] at hLoop
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs
      else if j = dst then initTapes dst else initTapes j) = initTapes := by
    funext j
    by_cases h1 : j = tRegs
    · subst h1; simp
    · by_cases h2 : j = dst
      · subst h2; simp [hNe.symm]
      · simp [h1, h2]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs
      else if j = dst then initTapes dst else initTapes j).head < bound j := by
    intro j
    rw [congrFun hTapesSelf j]
    exact hHeads j
  have hStepEq : (copyRegBody InputAlphabet dst).step .stepTag (readInput input inHead)
      (fun j => (if j = tRegs then initTapes tRegs else if j = dst then initTapes dst else initTapes j).cells
        (if j = tRegs then initTapes tRegs else if j = dst then initTapes dst else initTapes j).head) =
      twoTapeAction (.inl .copyLoop) tRegs dst
        ((initTapes tRegs).cells (initTapes tRegs).head)
        ((initTapes dst).cells (initTapes dst).head) .right .stay
        (fun j => (if j = tRegs then initTapes tRegs else if j = dst then initTapes dst else initTapes j).cells
          (if j = tRegs then initTapes tRegs else if j = dst then initTapes dst else initTapes j).head) := by
    simp only [copyRegBody, ↓reduceIte, hNe.symm]
  have hBody : (copyRegBody InputAlphabet dst).ReachesExit input bound initTapes inHead ()
      (fun j => if j = tRegs then initTapes tRegs else if j = dst then mtD else initTapes j) inHead := by
    have hRun := twoTape_compStep_head_override (copyRegBody InputAlphabet dst) tRegs dst hNe
      input bound initTapes (initTapes tRegs) (initTapes dst) ntR (initTapes dst)
      (initTapes tRegs) mtD .stepTag .copyLoop hHeadsOv
      (by rw [hNMR.head_eq]; omega) (by rw [hMatchDst.head_eq]; omega)
      hUpdR hUpdD hLoop hStepEq
    rw [hTapesSelf] at hRun
    exact hRun
  let cD := SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]
  have hNoLeftD : ∀ i, 1 ≤ i → i < cD.length → cD[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [cD, List.length_cons, List.length_append, List.length_map, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp [cD]; omega)]
      simp only [cD, List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < bits.length
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = bits.length := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  have hRewBounds : ∀ j, j ≠ dst →
      ((fun j => if j = tRegs then initTapes tRegs else if j = dst then mtD else initTapes j) j).head <
        bound j := by
    intro j hj
    by_cases hj1 : j = tRegs
    · subst hj1; simpa [hMatchReg.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + bits.length + 2) hBoundReg
    · simpa [hj1, hj] using hOtherBounds j hj1 hj
  obtain ⟨finalTapes, hRew, hFMD, hOth⟩ := rewindTape_reachesExit dst input bound cD (by simp [cD])
    rfl hNoLeftD (by simp [cD]; exact hBoundDst) _ inHead hRewBounds (1 + bits.length) (by omega)
    (by simp [cD]; omega) (by simpa [cD, hNe.symm] using hMMD)
  have hFinalEq : finalTapes = fun j => if j = tRegs then initTapes tRegs
      else if j = dst then finalTapes dst else initTapes j := by
    funext j
    by_cases hj2 : j = dst
    · simp [hj2, hNe.symm]
    · rw [hOth j hj2]
      simp [hj2]
  rw [hFinalEq] at hRew
  exact ⟨finalTapes dst, (copyRegBody InputAlphabet dst).seq_reachesExit
    (rewindTape InputAlphabet dst) input bound hBody hRew, hFMD⟩

theorem natToBits_zero (m : ℕ) : natToBits m 0 = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [natToBits, List.replicate_succ, ih]

theorem natToBits_one {W : ℕ} (hW : 1 ≤ W) :
    natToBits W 1 = true :: List.replicate (W - 1) false := by
  cases W with
  | zero => omega
  | succ W' =>
    simp [natToBits, natToBits_zero]

end SavitchLemma

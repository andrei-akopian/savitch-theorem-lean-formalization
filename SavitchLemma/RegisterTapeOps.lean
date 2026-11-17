module

public import SavitchLemma.AcceptingZD
public import SavitchLemma.TapePrimitives

@[expose] public section

/-!
# Register-tape layout and primitives on the 5-tape workspace

This module implements and verifies the `TMComponent` operations on Tape 1 (`tRegs`),
which stores the `r` working registers (`0..r-1`) and the source register (`r`) of
`ZDConfig r N` in `[.leftMark]`-delimited unary/binary layout, as well as the
template-driven `D0` initialization of Tape 1 from `1^W` on Tapes 2 and 3.
-/

namespace SavitchLemma

/-- Tape 0 holds the space ruler `[.leftMark, .bit true (× S), .endMark]`. -/
def tRuler : Fin 5 := 0

/-- Tape 1 holds the Savitch register array. -/
def tRegs : Fin 5 := 1

/-- Tape 2 holds argument A (`1^W` during D0, or `x` during step checking). -/
def tArgA : Fin 5 := 2

/-- Tape 3 holds argument B (`1^W` during D0, or `y` during step checking). -/
def tArgB : Fin 5 := 3

/-- Tape 4 serves as a unary/binary decrement scratch tape. -/
def tScratch : Fin 5 := 4

/-- Encode one working register `(tag, bits)` as `[.tag tag] ++ bits ++ [.sep]`. -/
def encodeRegEntry (b : Bool) (bs : List Bool) : List SimSym :=
  SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]

/-- Encode a prefix of working registers starting with `.leftMark`. -/
def encodeRegsPrefix (work : List (Bool × List Bool)) : List SimSym :=
  SimSym.leftMark :: work.flatMap (fun r => encodeRegEntry r.1 r.2)

/-- Encode the distinguished source register at the right end of Tape 1. -/
def encodeSrcEntry (src : List Bool) : List SimSym :=
  SimSym.srcSep :: SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark]

/-- Full contents of Tape 1 for working registers `work` and source bits `src`. -/
def encodeRegsTape (work : List (Bool × List Bool)) (src : List Bool) : List SimSym :=
  encodeRegsPrefix work ++ encodeSrcEntry src

/-- Extract the `r` working registers of `cfg : ZDConfig r N` as `W`-bit lists. -/
def encodeZDRegs {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List (Bool × List Bool) :=
  List.ofFn fun j : Fin r => (cfg.tag j.castSucc, natToBits W (cfg.x j.castSucc).val)

/-- Extract the source register `Fin.last r` of `cfg : ZDConfig r N` as a `W`-bit list. -/
def encodeZDSrc {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List Bool :=
  natToBits W (cfg.x (Fin.last r)).val

/-- Complete Tape 1 representation of `cfg : ZDConfig r N`. -/
def zdRegsContents {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List SimSym :=
  encodeRegsTape (encodeZDRegs W cfg) (encodeZDSrc W cfg)

@[simp]
theorem encodeRegEntry_length (b : Bool) (bs : List Bool) :
    (encodeRegEntry b bs).length = bs.length + 2 := by
  simp [encodeRegEntry]

@[simp]
theorem encodeSrcEntry_length (src : List Bool) :
    (encodeSrcEntry src).length = src.length + 3 := by
  simp [encodeSrcEntry]

theorem encodeRegsPrefix_nil : encodeRegsPrefix [] = [SimSym.leftMark] := rfl

theorem encodeRegsPrefix_snoc (work : List (Bool × List Bool)) (r : Bool × List Bool) :
    encodeRegsPrefix (work ++ [r]) = encodeRegsPrefix work ++ encodeRegEntry r.1 r.2 := by
  simp [encodeRegsPrefix, List.flatMap_append]

theorem encodeRegsPrefix_append (pref suf : List (Bool × List Bool)) :
    encodeRegsPrefix (pref ++ suf) =
      encodeRegsPrefix pref ++ suf.flatMap (fun r => encodeRegEntry r.1 r.2) := by
  simp [encodeRegsPrefix, List.flatMap_append]

theorem encodeRegsTape_split (pref suf : List (Bool × List Bool))
    (b : Bool) (bs src : List Bool) :
    encodeRegsTape (pref ++ (b, bs) :: suf) src =
      encodeRegsPrefix pref ++
        SimSym.tag b :: bs.map SimSym.bit ++
          [SimSym.sep] ++
          suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++
          encodeSrcEntry src := by
  simp [encodeRegsTape, encodeRegsPrefix, encodeRegEntry, List.flatMap_append, List.append_assoc]

theorem encodeRegsPrefix_length (W : ℕ) (work : List (Bool × List Bool))
    (hLen : ∀ r ∈ work, r.2.length = W) :
    (encodeRegsPrefix work).length = 1 + work.length * (W + 2) := by
  induction work with
  | nil => simp [encodeRegsPrefix]
  | cons r rs ih =>
    have hHead : r.2.length = W := hLen r (by simp)
    have hTail : ∀ x ∈ rs, x.2.length = W := fun x hx => hLen x (by simp [hx])
    simp only [encodeRegsPrefix, List.flatMap_cons, List.length_cons, List.length_append,
      encodeRegEntry_length, hHead]
    have ih' := ih hTail
    simp only [encodeRegsPrefix, List.length_cons] at ih'
    rw [Nat.succ_mul]
    omega

theorem encodeRegsTape_length (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W) :
    (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) := by
  simp [encodeRegsTape, encodeRegsPrefix_length W work hWork, hSrc]

theorem encodeZDRegs_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    (encodeZDRegs W cfg).length = r := by
  simp [encodeZDRegs]

theorem encodeZDRegs_bit_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    ∀ e ∈ encodeZDRegs W cfg, e.2.length = W := by
  intro e he
  simp only [encodeZDRegs, List.mem_ofFn] at he
  rcases he with ⟨j, rfl⟩
  simp [natToBits_length]

theorem encodeZDSrc_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    (encodeZDSrc W cfg).length = W := by
  simp [encodeZDSrc, natToBits_length]

theorem encodeRegEntry_no_leftMark (b : Bool) (bs : List Bool) :
    SimSym.leftMark ∉ encodeRegEntry b bs := by
  simp [encodeRegEntry]

theorem encodeSrcEntry_no_leftMark (src : List Bool) :
    SimSym.leftMark ∉ encodeSrcEntry src := by
  simp [encodeSrcEntry]

theorem encodeRegsTape_no_other_leftMark (work : List (Bool × List Bool)) (src : List Bool) :
    ∀ i, 1 ≤ i → i < (encodeRegsTape work src).length →
      (encodeRegsTape work src)[i]? ≠ some SimSym.leftMark := by
  intro i hi1 hiLt
  cases i with
  | zero => omega
  | succ i' =>
    rw [List.getElem?_eq_getElem hiLt]
    intro hEq
    have hEq' : (encodeRegsTape work src)[i' + 1] = SimSym.leftMark := Option.some.inj hEq
    simp only [encodeRegsTape, encodeRegsPrefix, List.cons_append, List.getElem_cons_succ] at hEq'
    have hInTail : SimSym.leftMark ∈
        work.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src :=
      hEq' ▸ List.getElem_mem _
    simp only [List.mem_append, List.mem_flatMap] at hInTail
    rcases hInTail with ⟨r, _, hMemR⟩ | hMemSrc
    · exact encodeRegEntry_no_leftMark r.1 r.2 hMemR
    · exact encodeSrcEntry_no_leftMark src hMemSrc

theorem encodeRegsTape_head_leftMark (work : List (Bool × List Bool)) (src : List Bool) :
    (encodeRegsTape work src)[0]'(by simp [encodeRegsTape, encodeRegsPrefix]) = SimSym.leftMark :=
  rfl

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

/-- Reset all working registers to the left of the current register on `tRegs`
to untagged `firstCode = 1` (`[true] ++ replicate (W - 1) false`), leaving `tRegs` at cell `1`. -/
inductive ResetLeftState where
  | stepInit
  | goLeft
  | wipeBits
  | fixLSB
  | backToTag
  deriving DecidableEq

def ResetLeftState.equivFin : ResetLeftState ≃ Fin 5 where
  toFun
    | .stepInit => 0 | .goLeft => 1 | .wipeBits => 2 | .fixLSB => 3 | .backToTag => 4
  invFun
    | 0 => .stepInit | 1 => .goLeft | 2 => .wipeBits | 3 => .fixLSB | _ => .backToTag
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype ResetLeftState := Fintype.ofEquiv (Fin 5) ResetLeftState.equivFin.symm

def resetLeftRegs (InputAlphabet : Type*) :
    TMComponent ResetLeftState InputAlphabet SimSym 5 Unit where
  start := .stepInit
  step s _ scanned :=
    match s with
    | .stepInit => singleTapeAction (.inl .goLeft) tRegs (scanned tRegs) .left scanned
    | .goLeft =>
      match scanned tRegs with
      | .leftMark => singleTapeAction (.inr ()) tRegs .leftMark .right scanned
      | .sep => singleTapeAction (.inl .wipeBits) tRegs .sep .left scanned
      | sym => singleTapeAction (.inl .goLeft) tRegs sym .left scanned
    | .wipeBits =>
      match scanned tRegs with
      | .bit _ => singleTapeAction (.inl .wipeBits) tRegs (.bit false) .left scanned
      | .tag _ => singleTapeAction (.inl .fixLSB) tRegs (.tag false) .right scanned
      | sym => singleTapeAction (.inl .goLeft) tRegs sym .left scanned
    | .fixLSB =>
      singleTapeAction (.inl .backToTag) tRegs (.bit true) .left scanned
    | .backToTag =>
      singleTapeAction (.inl .goLeft) tRegs (scanned tRegs) .left scanned

private theorem resetLeftRegs_wipeBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (b : Bool) (bits : List Bool) (hBitsLen : bits.length = W)
    (pref suf : List SimSym) (hPrefPos : 1 ≤ pref.length)
    (Post : OneSidedTape SimSym → Prop)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + W + 2 ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ encodeRegEntry false (natToBits W 1) ++ suf) (pref.length - 1) →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
        Post ft) :
    ∀ pos, pos ≤ bits.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            ((bits.take pos).map SimSym.bit ++
              List.replicate (bits.length - pos) (SimSym.bit false) ++
              SimSym.sep :: suf))
          (pref.length + pos) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .wipeBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          Post ft := by
  intro pos
  induction pos with
  | zero =>
    intro _ tape hM
    let tailTail := List.replicate W (SimSym.bit false) ++ SimSym.sep :: suf
    have hMEq : pref ++ SimSym.tag b ::
        ((bits.take 0).map SimSym.bit ++
          List.replicate (bits.length - 0) (SimSym.bit false) ++ SimSym.sep :: suf) =
        pref ++ SimSym.tag b :: tailTail := by
      simp [tailTail, hBitsLen]
    have hM' : TapeMatches tape (pref ++ SimSym.tag b :: tailTail) pref.length := by
      rw [← hMEq]
      simpa using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid pref (.tag b) tailTail
    have hMove₁ : moveOneSidedHead pref.length .right = some (pref.length + 1) := by
      simp [moveOneSidedHead]
    obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_set (.tag false) .right hMove₁ (by simp)
    rw [list_set_append_mid] at hNM₁
    have hW1 : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
    rcases hW1 with ⟨W', hWEq⟩
    have hRepSplit : tailTail = SimSym.bit false :: (List.replicate W' (SimSym.bit false) ++ SimSym.sep :: suf) := by
      simp [tailTail, hWEq, List.replicate_succ]
    let pref₂ := pref ++ [SimSym.tag false]
    let suf₂ := List.replicate W' (SimSym.bit false) ++ SimSym.sep :: suf
    have hPref₂Len : pref₂.length = pref.length + 1 := by simp [pref₂]
    have hNM₁' : TapeMatches nt₁ (pref₂ ++ SimSym.bit false :: suf₂) pref₂.length := by
      rw [hPref₂Len]
      simpa [pref₂, suf₂, hRepSplit, List.append_assoc] using hNM₁
    have hMove₂ : moveOneSidedHead (pref.length + 1) .left = some pref.length := by
      simp [moveOneSidedHead]
    obtain ⟨nt₂, hUpd₂, hNM₂⟩ :=
      hNM₁'.update_set (.bit true) .left (by rw [hPref₂Len]; exact hMove₂) (by simp)
    rw [list_set_append_mid] at hNM₂
    have hEntryEq : pref₂ ++ SimSym.bit true :: suf₂ =
        pref ++ encodeRegEntry false (natToBits W 1) ++ suf := by
      have hOne := natToBits_one (by omega : 1 ≤ W' + 1)
      simp only [encodeRegEntry, hWEq, hOne, Nat.add_sub_cancel]
      simp [pref₂, suf₂, List.map_replicate, List.append_assoc]
    rw [hEntryEq] at hNM₂
    have hMove₃ : moveOneSidedHead pref.length .left = some (pref.length - 1) := by
      simp [moveOneSidedHead, show pref.length ≠ 0 by omega]
    obtain ⟨nt₃, hUpd₃, hNM₃⟩ := hNM₂.update_keep .left hMove₃
    obtain ⟨ft, hGo, hRes⟩ := hAfter nt₃ hNM₃
    have hHeads₁ : ∀ j, (if j = tRegs then nt₁ else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hNM₁'.head_eq, hPref₂Len] using Nat.lt_of_lt_of_le (by omega : pref.length + 1 < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hHeads₂ : ∀ j, (if j = tRegs then nt₂ else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hNM₂.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hStepBack := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes nt₂ nt₃ ft .backToTag .goLeft hHeads₂
      (by rw [hNM₃.head_eq]; omega) hUpd₃ hGo (by simp [resetLeftRegs])
    have hStepFix := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes nt₁ nt₂ ft .fixLSB .backToTag hHeads₁
      (by rw [hNM₂.head_eq]; omega) hUpd₂ hStepBack (by simp [resetLeftRegs])
    have hStepWipe := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt₁ ft .wipeBits .fixLSB hHeads
      (by rw [hNM₁'.head_eq, hPref₂Len]; omega) hUpd₁ hStepFix (by simp [resetLeftRegs, hRead])
    exact ⟨ft, hStepWipe, hRes⟩
  | succ p ih =>
    intro hpLe tape hM
    let midPref := pref ++ SimSym.tag b :: (bits.take p).map SimSym.bit
    let midSuf := List.replicate (bits.length - (p + 1)) (SimSym.bit false) ++ SimSym.sep :: suf
    have hMidPrefLen : midPref.length = pref.length + p + 1 := by
      simp [midPref, Nat.min_eq_left (by omega : p ≤ bits.length)]; omega
    have hTakeSucc : bits.take (p + 1) = bits.take p ++ [bits[p]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega : p < bits.length)]
      rfl
    have hRepSucc : List.replicate (bits.length - p) (SimSym.bit false) =
        SimSym.bit false :: List.replicate (bits.length - (p + 1)) (SimSym.bit false) := by
      rw [show bits.length - p = (bits.length - (p + 1)) + 1 by omega, List.replicate_succ]
    have hCurListEq : pref ++ SimSym.tag b ::
        ((bits.take (p + 1)).map SimSym.bit ++
          List.replicate (bits.length - (p + 1)) (SimSym.bit false) ++ SimSym.sep :: suf) =
        midPref ++ SimSym.bit (bits[p]'(by omega)) :: midSuf := by
      rw [hTakeSucc]
      simp only [List.map_append, List.map_cons, List.map_nil, midPref, midSuf,
        List.append_assoc, List.cons_append, List.nil_append]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit (bits[p]'(by omega)) :: midSuf)
        midPref.length := by
      rw [hMidPrefLen, ← hCurListEq]
      simpa [Nat.add_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length + (p + 1) < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit (bits[p]'(by omega)) := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit _) midSuf
    have hMove : moveOneSidedHead (pref.length + (p + 1)) .left = some (pref.length + p) := by
      simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ :=
      hM'.update_set (.bit false) .left (by rw [hMidPrefLen]; simpa [Nat.add_assoc] using hMove)
        (by simp)
    rw [list_set_append_mid] at hNM
    have hNextListEq : midPref ++ SimSym.bit false :: midSuf =
        pref ++ SimSym.tag b ::
          ((bits.take p).map SimSym.bit ++
            List.replicate (bits.length - p) (SimSym.bit false) ++ SimSym.sep :: suf) := by
      simp [midPref, midSuf, hRepSucc, List.append_assoc]
    rw [hNextListEq] at hNM
    obtain ⟨ft, hRest, hRes⟩ := ih (by omega) nt hNM
    refine ⟨ft, ?_, hRes⟩
    exact singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt ft .wipeBits .wipeBits hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [resetLeftRegs, hRead])

private theorem resetLeftRegs_goLeft {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (revPref : List (Bool × List Bool)) (suf : List (Bool × List Bool)),
      (∀ r ∈ revPref, r.2.length = W) →
      1 + (revPref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (revPref.reverse ++ suf) src)
          ((encodeRegsPrefix revPref.reverse).length - 1) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (encodeRegsTape (revPref.reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src) 1 := by
  intro revPref
  induction revPref with
  | nil =>
    intro suf _ hBound tape hM
    have hPrefLen : (encodeRegsPrefix ([] : List (Bool × List Bool)).reverse).length = 1 := rfl
    rw [hPrefLen] at hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using Nat.lt_of_lt_of_le (by omega : 0 < 1 + (0 + suf.length) * (W + 2) + (W + 3)) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hM.read_lt (by simp [encodeRegsTape, encodeRegsPrefix])]
      rfl
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_set .leftMark .right hMove
      (by simp [encodeRegsTape, encodeRegsPrefix])
    have hSetSame : (encodeRegsTape ([] ++ suf) src).set 0 .leftMark = encodeRegsTape ([] ++ suf) src := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        cases i with
        | zero => simp [encodeRegsTape, encodeRegsPrefix]
        | succ i' => simp
    simp only [List.reverse_nil, Nat.sub_self] at hNM
    rw [hSetSame] at hNM
    refine ⟨nt, ?_, by simpa using hNM⟩
    exact singleTape_compStep_exit_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt .goLeft hHeads (by rw [hNM.head_eq]; omega)
      hUpd (by simp [resetLeftRegs, hRead])
  | cons cur rest ih =>
    intro suf hRevLen hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := hRevLen (b, bs) (by simp)
    have hRestLen : ∀ r ∈ rest, r.2.length = W := fun r hr => hRevLen r (by simp [hr])
    have hRestPrefixLen : (encodeRegsPrefix rest.reverse).length = 1 + rest.length * (W + 2) := by
      have := encodeRegsPrefix_length W rest.reverse (fun r hr => hRestLen r (by simpa using hr))
      simpa using this
    have hCurPrefixLen : (encodeRegsPrefix ((b, bs) :: rest).reverse).length =
        (encodeRegsPrefix rest.reverse).length + (W + 2) := by
      simp [List.reverse_cons, encodeRegsPrefix_snoc, encodeRegEntry_length, hBsLen]
    have hMulEq : ((b, bs) :: rest).length + suf.length = rest.length + (suf.length + 1) := by
      simp; omega
    have hBound' : 1 + rest.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simpa [hMulEq, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
    let prefSyms := encodeRegsPrefix rest.reverse
    let tailSyms : List SimSym := suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hTapeEq : encodeRegsTape (((b, bs) :: rest).reverse ++ suf) src =
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) ++ SimSym.sep :: tailSyms := by
      simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append,
        encodeRegEntry, List.reverse_cons, List.append_assoc]
    have hPrefSymLen : (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length =
        prefSyms.length + W + 1 := by
      simp [hBsLen]; omega
    have hSepPos : ((encodeRegsPrefix ((b, bs) :: rest).reverse).length - 1) =
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length := by
      rw [hCurPrefixLen]
      simp [prefSyms, hBsLen]
    have hM' : TapeMatches tape
        ((prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) ++ SimSym.sep :: tailSyms)
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length := by
      rw [← hTapeEq, ← hSepPos]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefSymLen, hRestPrefixLen] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) .sep tailSyms
    have hMove : moveOneSidedHead (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length .left =
        some (prefSyms.length + bs.length) := by
      simp [moveOneSidedHead, hBsLen]
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .left hMove
    have hNM' : TapeMatches nt
        (prefSyms ++ SimSym.tag b ::
          ((bs.take bs.length).map SimSym.bit ++
            List.replicate (bs.length - bs.length) (SimSym.bit false) ++
            SimSym.sep :: tailSyms))
        (prefSyms.length + bs.length) := by
      rw [List.take_length, Nat.sub_self, List.replicate_zero]
      simpa [List.append_assoc] using hNM
    have hPost : ∀ tape₂, TapeMatches tape₂
        (prefSyms ++ encodeRegEntry false (natToBits W 1) ++ tailSyms) (prefSyms.length - 1) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape₂ else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (encodeRegsTape (((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src)
            1 := by
      intro tape₂ hM₂
      have hList₂ : prefSyms ++ encodeRegEntry false (natToBits W 1) ++ tailSyms =
          encodeRegsTape (rest.reverse ++ (false, natToBits W 1) :: suf) src := by
        simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry,
          List.append_assoc]
      rw [hList₂] at hM₂
      have hBoundRec : 1 + (rest.length + ((false, natToBits W 1) :: suf).length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      obtain ⟨ft, hRun, hFM⟩ := ih ((false, natToBits W 1) :: suf) hRestLen hBoundRec tape₂ hM₂
      have hFinalEq : (rest.reverse.map (fun _ => (false, natToBits W 1)) ++
          (false, natToBits W 1) :: suf) =
          ((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hFinalEq] at hFM
      exact ⟨ft, hRun, hFM⟩
    obtain ⟨ft, hWipe, hRes⟩ := resetLeftRegs_wipeBits input bound W hW b bs hBsLen prefSyms tailSyms
      (by simp [prefSyms, encodeRegsPrefix])
      (fun ft => TapeMatches ft
        (encodeRegsTape (((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src) 1)
      initTapes inHead (by rw [hRestPrefixLen]; omega) hOtherBounds hPost
      bs.length le_rfl nt hNM'
    refine ⟨ft, ?_, hRes⟩
    exact singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt ft .goLeft .wipeBits hHeads
      (by rw [hNM'.head_eq, hRestPrefixLen, hBsLen]; omega)
      hUpd hWipe (by simp [resetLeftRegs, hRead])

theorem resetLeftRegs_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hCurLen : cur.2.length = W)
    (_hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src)
      (encodeRegsPrefix pref).length) :
    ∃ ft,
      (resetLeftRegs InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft
        (encodeRegsTape (pref.map (fun _ => (false, natToBits W 1)) ++ cur :: suf) src) 1 := by
  have hPrefPos : 1 ≤ (encodeRegsPrefix pref).length := by simp [encodeRegsPrefix]
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = tRegs
    · subst hj
      have hPL := encodeRegsPrefix_length W pref hPrefLen
      have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
      simpa [hMatch.head_eq, hPL] using by omega
    · exact hOtherBounds j hj
  have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .left =
      some ((encodeRegsPrefix pref).length - 1) := by
    simp [moveOneSidedHead, show (encodeRegsPrefix pref).length ≠ 0 by omega]
  obtain ⟨nt, hUpd, hNM⟩ := hMatch.update_keep .left hMove
  have hRevEq : pref.reverse.reverse = pref := List.reverse_reverse pref
  have hNM' : TapeMatches nt (encodeRegsTape (pref.reverse.reverse ++ cur :: suf) src)
      ((encodeRegsPrefix pref.reverse.reverse).length - 1) := by
    simpa [hRevEq] using hNM
  have hBoundGo : 1 + (pref.reverse.length + (cur :: suf).length) * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simp only [List.length_reverse, List.length_cons]
    have hEqLen : pref.length + (suf.length + 1) = pref.length + 1 + suf.length := by omega
    rw [hEqLen]
    exact hBound
  obtain ⟨ft, hGo, hFM⟩ := resetLeftRegs_goLeft input bound W hW src hSrcLen initTapes inHead
    hOtherBounds pref.reverse (cur :: suf) (fun r hr => hPrefLen r (by simpa using hr))
    hBoundGo nt hNM'
  have hFM' : TapeMatches ft
      (encodeRegsTape (pref.map (fun _ => (false, natToBits W 1)) ++ cur :: suf) src) 1 := by
    simpa [hRevEq] using hFM
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
  have hStep := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
    input bound initTapes (initTapes tRegs) nt ft .stepInit .goLeft hHeadsOv
    (by rw [hNM.head_eq, encodeRegsPrefix_length W pref hPrefLen]; omega)
    hUpd hGo (by simp [resetLeftRegs])
  rw [hTapesSelf] at hStep
  exact ⟨ft, hStep, hFM'⟩

/-- Scan Tape 1 from cell `1` for the first `.tag false` working register.
If found, halts with `true` leaving Tape 1's head on that `.tag false` cell;
if all working registers are tagged (reaching `.srcSep`), rewinds Tape 1 to cell `1`
and returns `false`. -/
inductive FindUntaggedState where
  | scanTag
  | skipBits
  deriving DecidableEq

def FindUntaggedState.equivFin : FindUntaggedState ≃ Fin 2 where
  toFun | .scanTag => 0 | .skipBits => 1
  invFun | 0 => .scanTag | _ => .skipBits
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype FindUntaggedState := Fintype.ofEquiv (Fin 2) FindUntaggedState.equivFin.symm

def findFirstUntaggedBody (InputAlphabet : Type*) :
    TMComponent FindUntaggedState InputAlphabet SimSym 5 Bool where
  start := .scanTag
  step s _ scanned :=
    match s with
    | .scanTag =>
      match scanned tRegs with
      | .tag false => singleTapeAction (.inr true) tRegs (.tag false) .stay scanned
      | .tag true => singleTapeAction (.inl .skipBits) tRegs (.tag true) .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .skipBits =>
      match scanned tRegs with
      | .sep => singleTapeAction (.inl .scanTag) tRegs .sep .right scanned
      | sym => singleTapeAction (.inl .skipBits) tRegs sym .right scanned

def findFirstUntagged (InputAlphabet : Type*) :=
  (findFirstUntaggedBody InputAlphabet).branch
    (TMComponent.atom fun _ scanned => singleTapeAction true tRegs (scanned tRegs) .stay scanned)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem findFirstUntaggedBody_skipBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (pref suf : List SimSym) (bs : List Bool) (hBsLen : bs.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + W + 3 ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    {res : Bool} {ft : OneSidedTape SimSym}
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
        (pref.length + W + 2) →
      Relation.ReflTransGen
        (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
          (∀ j, (a.workTapes j).head < bound j) ∧
          (∀ j, (b.workTapes j).head < bound j))
        ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
        ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩) :
    ∀ rem, rem ≤ bs.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
          (pref.length + 1 + (bs.length - rem)) →
        Relation.ReflTransGen
          (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .skipBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
  intro rem
  induction rem with
  | zero =>
    intro _ tape hM
    let prefSyms := pref ++ SimSym.tag true :: bs.map SimSym.bit
    have hPrefLen : prefSyms.length = pref.length + 1 + bs.length := by
      simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ SimSym.sep :: suf) prefSyms.length := by
      simpa [prefSyms, hPrefLen, List.append_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen, hBsLen] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms .sep suf
    have hMove : moveOneSidedHead (pref.length + 1 + bs.length) .right =
        some (pref.length + W + 2) := by
      simp [moveOneSidedHead, hBsLen]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hPrefLen]; exact hMove)
    have hNM' : TapeMatches nt (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
        (pref.length + W + 2) := by
      simpa [prefSyms, List.append_assoc] using hNM
    have hRest := hAfter nt hNM'
    exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .scanTag hHeads
      (by rw [hNM'.head_eq]; omega) hUpd hRest (by simp [findFirstUntaggedBody, hRead])
  | succ r ih =>
    intro hLe tape hM
    let idx := bs.length - (r + 1)
    have hIdxLt : idx < bs.length := by simp [idx]; omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hBsLen] using by simp [idx] at *; omega
      · simpa [hj] using hOtherBounds j hj
    have hNotSep : tape.cells tape.head ≠ .sep := by
      have hM' : TapeMatches tape (pref ++ SimSym.tag true :: (bs.map SimSym.bit ++ SimSym.sep :: suf))
          (pref.length + 1 + idx) := by simpa [List.append_assoc] using hM
      rw [hM'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + 1 + idx)]
      have hSub : pref.length + 1 + idx - pref.length = idx + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      rw [List.getElem_append_left (by simp; exact hIdxLt)]; simp
    have hMove : moveOneSidedHead (pref.length + 1 + idx) .right =
        some (pref.length + 1 + (bs.length - r)) := by
      simp [moveOneSidedHead, idx]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_keep .right hMove
    have hRest := ih (by omega) nt hNM
    exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .skipBits hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [findFirstUntaggedBody])

private theorem findFirstUntaggedBody_scan {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (suf pref : List (Bool × List Bool)),
      (∀ r ∈ pref, r.2.length = W ∧ r.1 = true) →
      (∀ r ∈ suf, r.2.length = W) →
      1 + (pref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix pref).length →
        ∃ (res : Bool) (ft : OneSidedTape SimSym),
          Relation.ReflTransGen
            (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          ft.cells = tape.cells ∧
          (res = false → (∀ r ∈ suf, r.1 = true) ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix (pref ++ suf)).length) ∧
          (res = true → ∃ p₁ cur p₂, suf = p₁ ++ cur :: p₂ ∧
            cur.1 = false ∧ (∀ r ∈ p₁, r.1 = true) ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src)
              (encodeRegsPrefix (pref ++ p₁)).length) := by
  intro suf
  induction suf with
  | nil =>
    intro pref hPref _ hBound tape hM
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hM' : TapeMatches tape (encodeRegsPrefix pref ++ SimSym.srcSep ::
        (SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark]))
        (encodeRegsPrefix pref).length := by
      simpa [encodeRegsTape, encodeSrcEntry] using hM
    have hRead : tape.cells tape.head = .srcSep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) .srcSep _
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
        some (encodeRegsPrefix pref).length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hM'.update_keep .stay hMove
    have hCells : ft.cells = tape.cells := by funext i; exact (hFM.2 i).trans (hM'.2 i).symm
    refine ⟨false, ft, ?_, hCells, ?_, ?_⟩
    · exact singleTape_compStep_exit_override (findFirstUntaggedBody InputAlphabet) tRegs
        input bound initTapes tape ft .scanTag hHeads
        (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [findFirstUntaggedBody, hRead])
    · intro _; refine ⟨by simp, by simpa [encodeRegsTape, encodeSrcEntry] using hFM⟩
    · intro hBad; cases hBad
  | cons cur rs ih =>
    intro pref hPref hSuf hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := (hSuf (b, bs) (by simp))
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hMul : pref.length + ((b, bs) :: rs).length = pref.length + 1 + rs.length := by
      simp; omega
    have hBound' : 1 + pref.length * (W + 2) + (W + 2) + rs.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hBound ⊢
      omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by omega
      · simpa [hj] using hOtherBounds j hj
    let tailSyms : List SimSym := rs.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hSplit : encodeRegsTape (pref ++ (b, bs) :: rs) src =
        encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms) := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hM' : TapeMatches tape
        (encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms))
        (encodeRegsPrefix pref).length := by
      rw [← hSplit]; exact hM
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) (.tag b) _
    cases b with
    | false =>
      have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
          some (encodeRegsPrefix pref).length := rfl
      obtain ⟨ft, hUpd, hFM⟩ := hM'.update_keep .stay hMove
      have hCells : ft.cells = tape.cells := by funext i; exact (hFM.2 i).trans (hM'.2 i).symm
      refine ⟨true, ft, ?_, hCells, ?_, ?_⟩
      · exact singleTape_compStep_exit_override (findFirstUntaggedBody InputAlphabet) tRegs
          input bound initTapes tape ft .scanTag hHeads
          (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [findFirstUntaggedBody, hRead])
      · intro hBad; cases hBad
      · intro _
        refine ⟨[], (false, bs), rs, rfl, rfl, by simp, ?_⟩
        simpa [hSplit] using hFM
    | true =>
      have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .right =
          some ((encodeRegsPrefix pref).length + 1) := by simp [moveOneSidedHead]
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
      have hCellsNt : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
      have hPrefNext : ∀ r ∈ pref ++ [(true, bs)], r.2.length = W ∧ r.1 = true := by
        intro r hr
        rcases List.mem_append.mp hr with hMem | hSingle
        · exact hPref r hMem
        · simp at hSingle; subst hSingle; exact ⟨hBsLen, rfl⟩
      have hSufNext : ∀ r ∈ rs, r.2.length = W := fun r hr => hSuf r (by simp [hr])
      have hBoundNext : 1 + ((pref ++ [(true, bs)]).length + rs.length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have : pref.length + 1 + rs.length = pref.length + (rs.length + 1) := by omega
        rw [this]; exact hBound
      have hHeadNext : ((encodeRegsPrefix pref).length + W + 2) =
          (encodeRegsPrefix (pref ++ [(true, bs)])).length := by
        simp [encodeRegsPrefix_snoc, encodeRegEntry_length, hBsLen]; omega
      let ntNext : OneSidedTape SimSym := ⟨nt.cells, (encodeRegsPrefix pref).length + W + 2⟩
      have hMatchNext : TapeMatches ntNext (encodeRegsTape ((pref ++ [(true, bs)]) ++ rs) src)
          (encodeRegsPrefix (pref ++ [(true, bs)])).length := by
        refine ⟨by simp [ntNext, hHeadNext], fun i => ?_⟩
        have hEqList : encodeRegsTape ((pref ++ [(true, bs)]) ++ rs) src =
            encodeRegsTape (pref ++ (true, bs) :: rs) src := by simp
        rw [hEqList, hSplit]
        simpa [ntNext] using hNM.2 i
      obtain ⟨res, ft, hRec, hCellsFt, hFalse, hTrue⟩ := ih (pref ++ [(true, bs)]) hPrefNext
        hSufNext hBoundNext ntNext hMatchNext
      have hCellsFt' : ft.cells = tape.cells := hCellsFt.trans (by simp [ntNext, hCellsNt])
      have hAfter : ∀ tape₂, TapeMatches tape₂
          (encodeRegsPrefix pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
          ((encodeRegsPrefix pref).length + W + 2) →
          Relation.ReflTransGen
            (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape₂ else initTapes j⟩
            ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
        intro tape₂ hM₂
        have hEqTape : tape₂ = ntNext := by
          have hC : tape₂.cells = ntNext.cells := by
            funext i
            have h1 := hM₂.2 i
            have h2 := hNM.2 i
            simp only [ntNext]
            rw [h1, h2]
            simp [List.append_assoc]
          cases tape₂; simp only [ntNext, OneSidedTape.mk.injEq]; exact ⟨hC, hM₂.head_eq⟩
        rw [hEqTape]; exact hRec
      have hNM_skip : TapeMatches nt
          (encodeRegsPrefix pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
          ((encodeRegsPrefix pref).length + 1 + (bs.length - bs.length)) := by
        simpa [List.append_assoc] using hNM
      have hSkip := findFirstUntaggedBody_skipBits input bound W (encodeRegsPrefix pref) tailSyms
        bs hBsLen initTapes inHead (by rw [hPL]; omega) hOtherBounds hAfter
        bs.length le_rfl nt hNM_skip
      refine ⟨res, ft, ?_, hCellsFt', ?_, ?_⟩
      · exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
          input bound initTapes tape nt ft .scanTag .skipBits hHeads
          (by rw [hNM.head_eq, hPL]; omega) hUpd hSkip (by simp [findFirstUntaggedBody, hRead])
      · intro hResF
        obtain ⟨hAllT, hFM⟩ := hFalse hResF
        refine ⟨fun r hr => ?_, by simpa [List.append_assoc] using hFM⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · rfl
        · exact hAllT r hMem
      · intro hResT
        obtain ⟨p₁, cur, p₂, hEqRs, hCurF, hP1T, hFM⟩ := hTrue hResT
        refine ⟨(true, bs) :: p₁, cur, p₂, by simp [hEqRs], hCurF, fun r hr => ?_, ?_⟩
        · rcases List.mem_cons.mp hr with rfl | hMem
          · rfl
          · exact hP1T r hMem
        · simpa [List.append_assoc] using hFM

theorem findFirstUntagged_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src) 1) :
    (∀ r ∈ work, r.1 = true) ∧
      (∃ ft, (findFirstUntagged InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) 1) ∨
    (∃ pref cur suf, work = pref ++ cur :: suf ∧ cur.1 = false ∧
      (∀ r ∈ pref, r.1 = true) ∧
      ∃ ft, (findFirstUntagged InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) (encodeRegsPrefix pref).length) := by
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  obtain ⟨res, mt, hBody, _, hFalse, hTrue⟩ := findFirstUntaggedBody_scan input bound W src hSrc
    initTapes inHead hOtherBounds work [] (by simp) hWork (by simpa using hBound)
    (initTapes tRegs) (by simpa [encodeRegsPrefix] using hMatch)
  rw [hTapesSelf] at hBody
  cases res with
  | true =>
    obtain ⟨p₁, cur, p₂, hEqW, hCurF, hP1T, hMT⟩ := hTrue rfl
    simp only [List.nil_append] at hEqW hMT
    have hHeadsM : ∀ j, (if j = tRegs then mt else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj
        have hP1Len : p₁.length < work.length := by rw [hEqW]; simp
        have hP1W : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
        have hPL := encodeRegsPrefix_length W p₁ hP1W
        have hB1 : 1 + p₁.length * (W + 2) < 1 + work.length * (W + 2) + (W + 3) := by
          have : p₁.length * (W + 2) ≤ work.length * (W + 2) := Nat.mul_le_mul_right _ hP1Len.le
          omega
        simpa [hMT.head_eq, hPL] using Nat.lt_of_lt_of_le hB1 hBound
      · simpa [hj] using hOtherBounds j hj
    have hMove : moveOneSidedHead (encodeRegsPrefix p₁).length .stay =
        some (encodeRegsPrefix p₁).length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hMT.update_keep .stay hMove
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ sym => (true, sym, .stay)) tRegs input bound
      (fun j => if j = tRegs then mt else initTapes j) inHead hHeadsM
      (by simpa using hUpd) (by
        have hP1Len : p₁.length < work.length := by rw [hEqW]; simp
        have hP1W : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
        have hPL := encodeRegsPrefix_length W p₁ hP1W
        have hB1 : 1 + p₁.length * (W + 2) < 1 + work.length * (W + 2) + (W + 3) := by
          have : p₁.length * (W + 2) ≤ work.length * (W + 2) := Nat.mul_le_mul_right _ hP1Len.le
          omega
        simpa [hFM.head_eq, hPL] using Nat.lt_of_lt_of_le hB1 hBound)
    have hFtEq : (fun j => if j = tRegs then ft
        else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hAtom
    right
    refine ⟨p₁, cur, p₂, hEqW, hCurF, hP1T, ft, ?_, hFM⟩
    exact (findFirstUntaggedBody InputAlphabet).branch_reachesExit _ _ input bound true hBody hAtom
  | false =>
    obtain ⟨hAllT, hMT⟩ := hFalse rfl
    simp only [List.nil_append] at hMT
    have hWLen := encodeRegsPrefix_length W work hWork
    have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
      encodeRegsTape_length W work src hWork hSrc
    have hRewBounds : ∀ j, j ≠ tRegs →
        ((fun j => if j = tRegs then mt else initTapes j) j).head < bound j := by
      intro j hj; simpa [hj] using hOtherBounds j hj
    obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
      (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
      (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
      (fun j => if j = tRegs then mt else initTapes j) inHead hRewBounds
      (encodeRegsPrefix work).length (by rw [hWLen]; omega)
      (by rw [hWorkLen, hWLen]; omega) (by simpa using hMT)
    have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
      funext j; by_cases hj : j = tRegs
      · subst hj; simp
      · rw [hOth j hj]; simp [hj]
    rw [hFinalEq] at hRew
    left
    refine ⟨hAllT, finalTapes tRegs, ?_, hFM⟩
    exact (findFirstUntaggedBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

/-- Starting on `.tag _` of a register in `tRegs`, advance past its bits and tail.
If a `.sep` is followed by another `.tag _` or `.srcSep`, step onto that next `.tag _`
(returning `true`); if `.endMark` is reached (meaning we were on the source register),
rewind `tRegs` to cell `1` and return `false`. -/
inductive AdvanceRegState where
  | stepTag
  | skipBits
  | afterSep
  deriving DecidableEq

def AdvanceRegState.equivFin : AdvanceRegState ≃ Fin 3 where
  toFun | .stepTag => 0 | .skipBits => 1 | .afterSep => 2
  invFun | 0 => .stepTag | 1 => .skipBits | _ => .afterSep
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype AdvanceRegState := Fintype.ofEquiv (Fin 3) AdvanceRegState.equivFin.symm

def advanceToNextRegBody (InputAlphabet : Type*) :
    TMComponent AdvanceRegState InputAlphabet SimSym 5 Bool where
  start := .stepTag
  step s _ scanned :=
    match s with
    | .stepTag => singleTapeAction (.inl .skipBits) tRegs (scanned tRegs) .right scanned
    | .skipBits =>
      match scanned tRegs with
      | .sep => singleTapeAction (.inl .afterSep) tRegs .sep .right scanned
      | .endMark => singleTapeAction (.inr false) tRegs .endMark .stay scanned
      | sym => singleTapeAction (.inl .skipBits) tRegs sym .right scanned
    | .afterSep =>
      match scanned tRegs with
      | .srcSep => singleTapeAction (.inr true) tRegs .srcSep .right scanned
      | sym => singleTapeAction (.inr true) tRegs sym .stay scanned

def advanceToNextReg (InputAlphabet : Type*) :=
  (advanceToNextRegBody InputAlphabet).branch
    (TMComponent.atom fun _ scanned => singleTapeAction true tRegs (scanned tRegs) .stay scanned)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem advanceToNextRegBody_skipBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool) (bits : List Bool) (tailSym : SimSym)
    (hTailNotEndOrSep : tailSym = .sep ∨ tailSym = .endMark)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + bits.length + (if tailSym = .sep then 3 else 2) ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    {res : Bool} {ft : OneSidedTape SimSym}
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
        (pref.length + bits.length + 1) →
      (tailSym = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead, fun j => if j = tRegs then ⟨tape.cells, pref.length + bits.length + 2⟩ else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩) ∧
      (tailSym = .endMark → res = false ∧ ft = tape)) :
    ∀ rem, rem ≤ bits.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
          (pref.length + 1 + (bits.length - rem)) →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .skipBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
  intro rem
  induction rem with
  | zero =>
    intro _ tape hM
    let prefSyms := pref ++ SimSym.tag b :: bits.map SimSym.bit
    have hPrefLen : prefSyms.length = pref.length + bits.length + 1 := by simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ tailSym :: suf) prefSyms.length := by
      rw [hPrefLen]
      simpa [prefSyms, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen] using by cases hTailNotEndOrSep <;> simp_all <;> omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = tailSym := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms tailSym suf
    obtain ⟨hAfterSep, hAfterEnd⟩ := hAfter tape (by rw [← hPrefLen]; simpa [prefSyms, List.append_assoc] using hM')
    rcases hTailNotEndOrSep with rfl | rfl
    · have hMove : moveOneSidedHead prefSyms.length .right =
          some (pref.length + bits.length + 2) := by
        simp [moveOneSidedHead, hPrefLen]
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
      have hCellsNt : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
      have hNtEq : nt = ⟨tape.cells, pref.length + bits.length + 2⟩ := by
        cases nt; simp only [OneSidedTape.mk.injEq]; exact ⟨hCellsNt, hNM.head_eq⟩
      rw [hNtEq] at hUpd hNM
      exact singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
        input bound initTapes tape ⟨tape.cells, pref.length + bits.length + 2⟩ ft
        .skipBits .afterSep hHeads (by simp at hBound ⊢; omega) hUpd (hAfterSep rfl)
        (by simp [advanceToNextRegBody, hRead])
    · obtain ⟨rfl, hFtEq⟩ := hAfterEnd rfl
      have hMove : moveOneSidedHead prefSyms.length .stay = some prefSyms.length := rfl
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .stay hMove
      have hNtEq : nt = tape := by
        have hC : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
        have hH : nt.head = tape.head := hNM.head_eq.trans hM'.head_eq.symm
        cases nt; cases tape; simp only [OneSidedTape.mk.injEq]; exact ⟨hC, hH⟩
      rw [hNtEq] at hUpd
      rw [hFtEq]
      exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
        input bound initTapes tape tape .skipBits hHeads
        (by rw [hM'.head_eq, hPrefLen]; simp at hBound; omega)
        hUpd (by simp [advanceToNextRegBody, hRead])
  | succ r ih =>
    intro hLe tape hM
    let idx := bits.length - (r + 1)
    have hIdxLt : idx < bits.length := by simp [idx]; omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by
          rcases hTailNotEndOrSep with rfl | rfl <;> simp at hBound ⊢ <;> omega
      · simpa [hj] using hOtherBounds j hj
    have hReadBit : tape.cells tape.head = .bit (bits[idx]'hIdxLt) := by
      have hM' : TapeMatches tape (pref ++ SimSym.tag b :: (bits.map SimSym.bit ++ tailSym :: suf))
          (pref.length + 1 + idx) := by simpa [List.append_assoc] using hM
      rw [hM'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + 1 + idx)]
      have hSub : pref.length + 1 + idx - pref.length = idx + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      rw [List.getElem_append_left (by simp; exact hIdxLt)]; simp
    have hMove : moveOneSidedHead (pref.length + 1 + idx) .right =
        some (pref.length + 1 + (bits.length - r)) := by simp [moveOneSidedHead, idx]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_keep .right hMove
    exact singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .skipBits hHeads
      (by rw [hNM.head_eq]; rcases hTailNotEndOrSep with rfl | rfl <;> simp at hBound ⊢ <;> omega)
      hUpd (ih (by omega) nt hNM)
      (by simp [advanceToNextRegBody, hReadBit])

theorem advanceToNextReg_work_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hCurLen : cur.2.length = W)
    (hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src)
      (encodeRegsPrefix pref).length) :
    let nextPos := if suf = [] then (encodeRegsPrefix (pref ++ [cur])).length + 1
                   else (encodeRegsPrefix (pref ++ [cur])).length
    ∃ ft,
      (advanceToNextReg InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape (pref ++ cur :: suf) src) nextPos := by
  intro nextPos
  rcases cur with ⟨b, bs⟩
  have hBsLen : bs.length = W := hCurLen
  have hPL := encodeRegsPrefix_length W pref hPrefLen
  have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
  let prefSyms := encodeRegsPrefix pref
  let tailSyms : List SimSym := suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
  have hTapeEq : encodeRegsTape (pref ++ (b, bs) :: suf) src =
      prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms := by
    simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
  have hM' : TapeMatches (initTapes tRegs)
      (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
      prefSyms.length := by
    rw [← hTapeEq]; exact hMatch
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [hM'.head_eq, prefSyms, hPL] using by omega
    · exact hOtherBounds j hj
  have hMove₁ : moveOneSidedHead prefSyms.length .right = some (prefSyms.length + 1) := by
    simp [moveOneSidedHead]
  obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_keep .right hMove₁
  have hCells₁ : nt₁.cells = (initTapes tRegs).cells := by
    funext i; exact (hNM₁.2 i).trans (hM'.2 i).symm
  let sepNextPos := prefSyms.length + bs.length + 2
  have hSepNextEq : sepNextPos = (encodeRegsPrefix (pref ++ [(b, bs)])).length := by
    simp [sepNextPos, prefSyms, encodeRegsPrefix_snoc, encodeRegEntry_length]
    omega
  have hSufSymHead : ∃ nextSym tail₂,
      tailSyms = nextSym :: tail₂ ∧
      (suf = [] → nextSym = .srcSep) ∧
      (suf ≠ [] → ∃ b' bs' rs, suf = (b', bs') :: rs ∧ nextSym = .tag b') := by
    cases suf with
    | nil =>
      refine ⟨.srcSep, SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark], ?_,
        fun _ => rfl, fun h => (h rfl).elim⟩
      simp [tailSyms, encodeSrcEntry]
    | cons r rs =>
      rcases r with ⟨b', bs'⟩
      refine ⟨.tag b', bs'.map SimSym.bit ++ [SimSym.sep] ++
          rs.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src, ?_,
        (by intro h; cases h), fun _ => ⟨b', bs', rs, rfl, rfl⟩⟩
      simp [tailSyms, encodeRegEntry, List.append_assoc]
  rcases hSufSymHead with ⟨nextSym, tail₂, hTail₂, hWhenNil, hWhenCons⟩
  let midTape : OneSidedTape SimSym := ⟨nt₁.cells, sepNextPos⟩
  let ftPos : ℕ := nextPos
  let ftTape : OneSidedTape SimSym := ⟨nt₁.cells, ftPos⟩
  have hNextPosEq : ftPos = if suf = [] then sepNextPos + 1 else sepNextPos := by
    simp [ftPos, nextPos, hSepNextEq]
  have hAfterBody : ∀ tape, TapeMatches tape
      (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
      (prefSyms.length + bs.length + 1) →
      (SimSym.sep = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead,
            fun j => if j = tRegs then ⟨tape.cells, sepNextPos⟩ else initTapes j⟩
          ⟨.inr true, inHead, fun j => if j = tRegs then ftTape else initTapes j⟩) ∧
      (SimSym.sep = .endMark → true = false ∧ ftTape = tape) := by
    intro tape hMTape
    constructor
    · intro _
      have hTapeCells : tape.cells = nt₁.cells := by
        funext i
        have h1 := hMTape.2 i
        have h2 := hNM₁.2 i
        rw [h1, h2]
      have hMidEq : (⟨tape.cells, sepNextPos⟩ : OneSidedTape SimSym) = midTape := by
        simp [midTape, hTapeCells]
      rw [hMidEq]
      have hMAfter : TapeMatches midTape
          ((prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]) ++ nextSym :: tail₂)
          sepNextPos := by
        refine ⟨rfl, fun i => ?_⟩
        rw [hCells₁]
        have hOrig := hM'.2 i
        simp only [hTail₂, List.append_assoc] at hOrig
        simpa [midTape, List.append_assoc] using hOrig
      have hPrefAfterLen : (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]).length =
          sepNextPos := by
        simp [sepNextPos]; omega
      have hHeadsMid : ∀ j, (if j = tRegs then midTape else initTapes j).head < bound j := by
        intro j; by_cases hj : j = tRegs
        · subst hj; simpa [midTape, sepNextPos, prefSyms, hPL, hBsLen] using by omega
        · simpa [hj] using hOtherBounds j hj
      have hReadNext : midTape.cells midTape.head = nextSym := by
        rw [hMAfter.read_lt (by rw [← hPrefAfterLen]; simp)]
        convert list_get_append_mid (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep])
          nextSym tail₂
        · simp [sepNextPos]; omega
      cases suf with
      | nil =>
        have hNS : nextSym = .srcSep := hWhenNil rfl
        have hMoveA : moveOneSidedHead sepNextPos .right = some ftPos := by
          simp [moveOneSidedHead, hNextPosEq]
        obtain ⟨ntA, hUpdA, hNMA⟩ := hMAfter.update_keep .right hMoveA
        have hNtAEq : ntA = ftTape := by
          have hC : ntA.cells = nt₁.cells := by
            funext i
            have h1 := hNMA.2 i
            have h2 := hMAfter.2 i
            exact h1.trans h2.symm
          cases ntA; simp only [ftTape, OneSidedTape.mk.injEq]; exact ⟨hC, hNMA.head_eq⟩
        rw [hNtAEq] at hUpdA
        exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
          input bound initTapes midTape ftTape .afterSep hHeadsMid
          (by simp [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen]; omega)
          hUpdA (by simp [advanceToNextRegBody, hReadNext, hNS])
      | cons r rs =>
        obtain ⟨b', bs', rs', hEqSuf, hNS⟩ := hWhenCons (by simp)
        have hMoveA : moveOneSidedHead sepNextPos .stay = some ftPos := by
          simp [moveOneSidedHead, hNextPosEq]
        obtain ⟨ntA, hUpdA, hNMA⟩ := hMAfter.update_keep .stay hMoveA
        have hNtAEq : ntA = ftTape := by
          have hC : ntA.cells = nt₁.cells := by
            funext i
            have h1 := hNMA.2 i
            have h2 := hMAfter.2 i
            exact h1.trans h2.symm
          cases ntA; simp only [ftTape, OneSidedTape.mk.injEq]; exact ⟨hC, hNMA.head_eq⟩
        rw [hNtAEq] at hUpdA
        exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
          input bound initTapes midTape ftTape .afterSep hHeadsMid
          (by simp [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen]; omega)
          hUpdA (by simp [advanceToNextRegBody, hReadNext, hNS])
    · intro hBad; cases hBad
  have hSkip := advanceToNextRegBody_skipBits input bound prefSyms tailSyms b bs .sep (Or.inl rfl)
    initTapes inHead (by simp [prefSyms, hPL, hBsLen]; omega) hOtherBounds hAfterBody
    bs.length le_rfl nt₁ (by simpa [Nat.sub_self] using hNM₁)
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBody : (advanceToNextRegBody InputAlphabet).ReachesExit input bound initTapes inHead true
      (fun j => if j = tRegs then ftTape else initTapes j) inHead := by
    have hRun := singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes (initTapes tRegs) nt₁ ftTape .stepTag .skipBits hHeadsOv
      (by rw [hNM₁.head_eq, hPL]; omega) hUpd₁ hSkip (by simp [advanceToNextRegBody])
    rw [hTapesSelf] at hRun
    exact hRun
  have hFtMatch : TapeMatches ftTape (encodeRegsTape (pref ++ (b, bs) :: suf) src) ftPos := by
    refine ⟨rfl, fun i => ?_⟩
    rw [hCells₁, hTapeEq]
    exact hM'.2 i
  have hHeadsFt : ∀ j, (if j = tRegs then ftTape else initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen] using by
        split <;> omega
    · simpa [hj] using hOtherBounds j hj
  have hMoveStay : moveOneSidedHead ftPos .stay = some ftPos := rfl
  obtain ⟨ftFinal, hUpdF, hFMF⟩ := hFtMatch.update_keep .stay hMoveStay
  have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
    (fun _ sym => (true, sym, .stay)) tRegs input bound
    (fun j => if j = tRegs then ftTape else initTapes j) inHead hHeadsFt
    (by simpa using hUpdF) (by
      simpa [hFMF.head_eq, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen] using by split <;> omega)
  have hFtEq : (fun j => if j = tRegs then ftFinal
      else if j = tRegs then ftTape else initTapes j) =
      (fun j => if j = tRegs then ftFinal else initTapes j) := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  rw [hFtEq] at hAtom
  refine ⟨ftFinal, ?_, hFMF⟩
  exact (advanceToNextRegBody InputAlphabet).branch_reachesExit _ _ input bound true hBody hAtom

theorem advanceToNextReg_src_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src)
      ((encodeRegsPrefix work).length + 1)) :
    ∃ ft,
      (advanceToNextReg InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape work src) 1 := by
  have hWL := encodeRegsPrefix_length W work hWork
  let prefSyms := encodeRegsPrefix work ++ [SimSym.srcSep]
  have hPrefLen : prefSyms.length = (encodeRegsPrefix work).length + 1 := by simp [prefSyms]
  have hTapeEq : encodeRegsTape work src =
      prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [] := by
    simp [prefSyms, encodeRegsTape, encodeSrcEntry, List.append_assoc]
  have hM' : TapeMatches (initTapes tRegs)
      (prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [])
      prefSyms.length := by
    rw [← hTapeEq, hPrefLen]; exact hMatch
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [hM'.head_eq, hPrefLen, hWL] using by omega
    · exact hOtherBounds j hj
  have hMove₁ : moveOneSidedHead prefSyms.length .right = some (prefSyms.length + 1) := by
    simp [moveOneSidedHead]
  obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_keep .right hMove₁
  have hCells₁ : nt₁.cells = (initTapes tRegs).cells := by
    funext i; exact (hNM₁.2 i).trans (hM'.2 i).symm
  let mtTape : OneSidedTape SimSym := ⟨nt₁.cells, prefSyms.length + src.length + 1⟩
  have hAfterBody : ∀ tape, TapeMatches tape
      (prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [])
      (prefSyms.length + src.length + 1) →
      (SimSym.endMark = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead,
            fun j => if j = tRegs then ⟨tape.cells, prefSyms.length + src.length + 2⟩ else initTapes j⟩
          ⟨.inr false, inHead, fun j => if j = tRegs then mtTape else initTapes j⟩) ∧
      (SimSym.endMark = .endMark → false = false ∧ mtTape = tape) := by
    intro tape hMTape
    constructor
    · intro hBad; cases hBad
    · intro _
      refine ⟨rfl, ?_⟩
      have hC : mtTape.cells = tape.cells := by
        funext i
        have h1 := hMTape.2 i
        have h2 := hNM₁.2 i
        simp only [mtTape]
        rw [h2, h1]
      cases tape; simp only [mtTape, OneSidedTape.mk.injEq]; exact ⟨hC, hMTape.head_eq.symm⟩
  have hSkip := advanceToNextRegBody_skipBits input bound prefSyms [] true src .endMark (Or.inr rfl)
    initTapes inHead (by simp [hPrefLen, hWL, hSrc]; omega) hOtherBounds hAfterBody
    src.length le_rfl nt₁ (by simpa [Nat.sub_self] using hNM₁)
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBody : (advanceToNextRegBody InputAlphabet).ReachesExit input bound initTapes inHead false
      (fun j => if j = tRegs then mtTape else initTapes j) inHead := by
    have hRun := singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes (initTapes tRegs) nt₁ mtTape .stepTag .skipBits hHeadsOv
      (by rw [hNM₁.head_eq, hPrefLen, hWL]; omega) hUpd₁ hSkip (by simp [advanceToNextRegBody])
    rw [hTapesSelf] at hRun
    exact hRun
  have hMtMatch : TapeMatches mtTape (encodeRegsTape work src) (prefSyms.length + src.length + 1) := by
    refine ⟨rfl, fun i => ?_⟩
    rw [hCells₁, hTapeEq]
    exact hM'.2 i
  have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
    encodeRegsTape_length W work src hWork hSrc
  have hRewBounds : ∀ j, j ≠ tRegs →
      ((fun j => if j = tRegs then mtTape else initTapes j) j).head < bound j := by
    intro j hj; simpa [hj] using hOtherBounds j hj
  obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
    (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
    (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
    (fun j => if j = tRegs then mtTape else initTapes j) inHead hRewBounds
    (prefSyms.length + src.length + 1) (by omega)
    (by rw [hWorkLen, hPrefLen, hWL, hSrc]; omega) hMtMatch
  have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
    funext j; by_cases hj : j = tRegs
    · subst hj; simp
    · rw [hOth j hj]; simp [hj]
  rw [hFinalEq] at hRew
  refine ⟨finalTapes tRegs, ?_, hFM⟩
  exact (advanceToNextRegBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
    (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

/-- Find the first untagged register on Tape 1 (from cell `1`), set its tag to `true`,
and reset all working registers to its left to untagged `firstCode = 1`.
Returns `true` if an untagged register existed (leaving Tape 1 at cell `1`), or `false`
if all working registers were already tagged. -/
def findFirstUntaggedAndTag (InputAlphabet : Type*) :=
  (findFirstUntagged InputAlphabet).branch
    (((TMComponent.atom fun _ scanned =>
        singleTapeAction () tRegs (.tag true) .stay scanned).seq
      (resetLeftRegs InputAlphabet)).mapExit fun _ => true)
    (TMComponent.atom fun _ scanned => singleTapeAction false tRegs (scanned tRegs) .stay scanned)

theorem findFirstUntaggedAndTag_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hPrefT : ∀ r ∈ pref, r.1 = true)
    (hCurLen : cur.2.length = W) (hCurF : cur.1 = false)
    (hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src) 1) :
    ∃ ft,
      (findFirstUntaggedAndTag InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape
        (pref.map (fun _ => (false, natToBits W 1)) ++ (true, cur.2) :: suf) src) 1 := by
  have hAllWorkLen : ∀ r ∈ pref ++ cur :: suf, r.2.length = W := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact hPrefLen r h1
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hCurLen
      · exact hSufLen r h3
  have hBoundWork : 1 + (pref ++ cur :: suf).length * (W + 2) + (W + 3) ≤ bound tRegs := by
    simp only [List.length_append, List.length_cons]
    have : pref.length + (suf.length + 1) = pref.length + 1 + suf.length := by omega
    rw [this]; exact hBound
  have hFind := findFirstUntagged_reachesExit input bound W (pref ++ cur :: suf) src
    hAllWorkLen hSrcLen hBoundWork initTapes inHead hOtherBounds hMatch
  rcases hFind with ⟨hAllT, _⟩ | ⟨p₁, cur₁, p₂, hEq, hCur1F, hP1T, mt, hFindRun, hMT⟩
  · have hF := hAllT cur (by simp)
    rw [hCurF] at hF
    cases hF
  · have hP1LenEq : p₁.length = pref.length := by
      by_contra hNe
      rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
      · have hMem : (pref ++ cur :: suf)[p₁.length]'(by simp; omega) = cur₁ := by
          simp only [hEq, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        rw [List.getElem_append_left hLt] at hMem
        have hT : cur₁.1 = true := by rw [← hMem]; exact hPrefT _ (List.getElem_mem _)
        rw [hCur1F] at hT; cases hT
      · have hMem : (p₁ ++ cur₁ :: p₂)[pref.length]'(by rw [← hEq]; simp) = cur := by
          simp only [← hEq, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        rw [List.getElem_append_left hGt] at hMem
        have hT : cur.1 = true := by rw [← hMem]; exact hP1T _ (List.getElem_mem _)
        rw [hCurF] at hT; cases hT
    have hP1Eq : p₁ = pref := by
      have := congrArg (List.take pref.length) hEq
      symm
      simpa [List.take_left', hP1LenEq] using this
    subst p₁
    have hPL := encodeRegsPrefix_length W pref hPrefLen
    have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
    have hHeadsMT : ∀ j, (if j = tRegs then mt else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hMT.head_eq, hPL] using by omega
      · simpa [hj] using hOtherBounds j hj
    let tailSyms : List SimSym :=
      suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hSplit : encodeRegsTape (pref ++ cur :: suf) src =
        encodeRegsPrefix pref ++ SimSym.tag cur.1 :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms) := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hMT' : TapeMatches mt
        (encodeRegsPrefix pref ++ SimSym.tag cur.1 :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms))
        (encodeRegsPrefix pref).length := by
      rw [← hSplit]; exact hMT
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
        some (encodeRegsPrefix pref).length := rfl
    obtain ⟨nt, hUpd, hNM⟩ := hMT'.update_set (.tag true) .stay hMove (by simp)
    rw [list_set_append_mid] at hNM
    have hNextSplit : encodeRegsPrefix pref ++
        SimSym.tag true :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms) =
        encodeRegsTape (pref ++ (true, cur.2) :: suf) src := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    rw [hNextSplit] at hNM
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ _ => ((), .tag true, .stay)) tRegs input bound
      (fun j => if j = tRegs then mt else initTapes j) inHead hHeadsMT
      (by simpa using hUpd) (by simpa [hNM.head_eq, hPL] using by omega)
    have hNtEq : (fun j => if j = tRegs then nt else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then nt else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hNtEq] at hAtom
    obtain ⟨ft, hReset, hFM⟩ := resetLeftRegs_reachesExit input bound W hW pref (true, cur.2) suf src
      hPrefLen hCurLen hSufLen hSrcLen hBound (fun j => if j = tRegs then nt else initTapes j)
      inHead (fun j hj => by simp [hj, hOtherBounds j hj]) (by simpa using hNM)
    have hFtEq : (fun j => if j = tRegs then ft else if j = tRegs then nt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hReset
    refine ⟨ft, ?_, hFM⟩
    have hSeq := TMComponent.seq_reachesExit _ _ input bound hAtom hReset
    have hMap := TMComponent.mapExit_reachesExit _ (fun _ => true) input bound hSeq
    exact (findFirstUntagged InputAlphabet).branch_reachesExit _ _ input bound true hFindRun hMap

/-- D3 backtracking on Tape 1: find the least working register strictly below
the maximum code (`2^W - 1`, i.e., containing at least one `.bit false`),
increment it, clear its tag, reset all working registers to its left, and rewind
Tape 1 to cell `1`. If all working registers are at `2^W - 1`, rewind Tape 1 to
cell `1` and return `false`. -/
inductive IncRegState where
  | scanTag
  | tryInc
  | backZero
  deriving DecidableEq

def IncRegState.equivFin : IncRegState ≃ Fin 3 where
  toFun | .scanTag => 0 | .tryInc => 1 | .backZero => 2
  invFun | 0 => .scanTag | 1 => .tryInc | _ => .backZero
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype IncRegState := Fintype.ofEquiv (Fin 3) IncRegState.equivFin.symm

def incFirstBody (InputAlphabet : Type*) :
    TMComponent IncRegState InputAlphabet SimSym 5 Bool where
  start := .scanTag
  step s _ scanned :=
    match s with
    | .scanTag =>
      match scanned tRegs with
      | .tag b => singleTapeAction (.inl .tryInc) tRegs (.tag b) .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .tryInc =>
      match scanned tRegs with
      | .bit true => singleTapeAction (.inl .tryInc) tRegs (.bit true) .right scanned
      | .bit false => singleTapeAction (.inl .backZero) tRegs (.bit true) .left scanned
      | .sep => singleTapeAction (.inl .scanTag) tRegs .sep .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .backZero =>
      match scanned tRegs with
      | .tag _ => singleTapeAction (.inr true) tRegs (.tag false) .stay scanned
      | _ => singleTapeAction (.inl .backZero) tRegs (.bit false) .left scanned

def incFirstRegBelowMax (InputAlphabet : Type*) :=
  (incFirstBody InputAlphabet).branch
    ((resetLeftRegs InputAlphabet).mapExit fun _ => true)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem incFirstBody_backZero {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ pos (sufBits : List Bool),
      pref.length + pos + sufBits.length + 2 ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            (List.replicate pos (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
            SimSym.sep :: suf)
          (pref.length + pos) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .backZero, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (pref ++ SimSym.tag false ::
              (List.replicate pos (SimSym.bit false) ++ sufBits.map SimSym.bit) ++
              SimSym.sep :: suf)
            pref.length := by
  intro pos
  induction pos with
  | zero =>
    intro sufBits hBound tape hM
    let tailSyms := sufBits.map SimSym.bit ++ SimSym.sep :: suf
    have hMEq : pref ++ SimSym.tag b ::
        (List.replicate 0 (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
        SimSym.sep :: suf = pref ++ SimSym.tag b :: tailSyms := by
      simp [tailSyms, List.append_assoc]
    have hM' : TapeMatches tape (pref ++ SimSym.tag b :: tailSyms) pref.length := by
      rw [← hMEq]; simpa using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid pref (.tag b) tailSyms
    have hMove : moveOneSidedHead pref.length .stay = some pref.length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hM'.update_set (.tag false) .stay hMove (by simp)
    rw [list_set_append_mid] at hFM
    have hOutEq : pref ++ SimSym.tag false :: tailSyms =
        pref ++ SimSym.tag false ::
          (List.replicate 0 (SimSym.bit false) ++ sufBits.map SimSym.bit) ++
          SimSym.sep :: suf := by
      simp [tailSyms, List.append_assoc]
    rw [hOutEq] at hFM
    refine ⟨ft, ?_, hFM⟩
    exact singleTape_compStep_exit_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape ft .backZero hHeads (by rw [hFM.head_eq]; omega)
      hUpd (by simp [incFirstBody, hRead])
  | succ p ih =>
    intro sufBits hBound tape hM
    let midPref := pref ++ SimSym.tag b :: List.replicate p (SimSym.bit true)
    let midSuf := sufBits.map SimSym.bit ++ SimSym.sep :: suf
    have hMidPrefLen : midPref.length = pref.length + (p + 1) := by simp [midPref]
    have hCurEq : pref ++ SimSym.tag b ::
        (List.replicate (p + 1) (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
        SimSym.sep :: suf = midPref ++ SimSym.bit true :: midSuf := by
      simp [midPref, midSuf, List.replicate_succ', List.append_assoc]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit true :: midSuf) midPref.length := by
      rw [hMidPrefLen, ← hCurEq]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit true := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit true) midSuf
    have hMove : moveOneSidedHead (pref.length + (p + 1)) .left = some (pref.length + p) := by
      simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ :=
      hM'.update_set (.bit false) .left (by rw [hMidPrefLen]; exact hMove) (by simp)
    rw [list_set_append_mid] at hNM
    have hNextEq : midPref ++ SimSym.bit false :: midSuf =
        pref ++ SimSym.tag b ::
          (List.replicate p (SimSym.bit true) ++ (false :: sufBits).map SimSym.bit) ++
          SimSym.sep :: suf := by
      simp [midPref, midSuf, List.append_assoc]
    rw [hNextEq] at hNM
    obtain ⟨ft, hRest, hFM⟩ := ih (false :: sufBits) (by simp; omega) nt hNM
    have hRepOut : List.replicate (p + 1) (SimSym.bit false) ++ sufBits.map SimSym.bit =
        List.replicate p (SimSym.bit false) ++ (false :: sufBits).map SimSym.bit := by
      simp [List.replicate_succ', List.append_assoc]
    rw [← hRepOut] at hFM
    refine ⟨ft, ?_, hFM⟩
    exact singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .backZero .backZero hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [incFirstBody, hRead])

private theorem incFirstBody_tryInc {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (sufBits : List Bool) (nOnes : ℕ),
      pref.length + nOnes + sufBits.length + 3 ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            (List.replicate nOnes (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
            SimSym.sep :: suf)
          (pref.length + 1 + nOnes) →
        (∃ ft,
          (false ∈ sufBits ∧
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (pref ++ SimSym.tag false ::
                (incBits (List.replicate nOnes true ++ sufBits)).map SimSym.bit ++
                SimSym.sep :: suf)
              pref.length) ∨
          (false ∉ sufBits ∧
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (pref ++ SimSym.tag b ::
                (List.replicate nOnes (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
                SimSym.sep :: suf)
              (pref.length + nOnes + sufBits.length + 2))) := by
  intro sufBits
  induction sufBits with
  | nil =>
    intro nOnes hBound tape hM
    let prefSyms := pref ++ SimSym.tag b :: List.replicate nOnes (SimSym.bit true)
    have hPrefLen : prefSyms.length = pref.length + 1 + nOnes := by simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ SimSym.sep :: suf) prefSyms.length := by
      simpa [prefSyms, hPrefLen, List.append_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms .sep suf
    have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .right =
        some (pref.length + nOnes + ([] : List Bool).length + 2) := by
      simp [moveOneSidedHead]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hPrefLen]; exact hMove)
    have hNM' : TapeMatches nt
        (pref ++ SimSym.tag b :: (List.replicate nOnes (SimSym.bit true) ++ ([] : List Bool).map SimSym.bit) ++
          SimSym.sep :: suf)
        (pref.length + nOnes + ([] : List Bool).length + 2) := by
      simpa [prefSyms, List.append_assoc] using hNM
    refine ⟨nt, Or.inr ⟨by simp, ?_, hNM'⟩⟩
    refine Relation.ReflTransGen.single ⟨?_, hHeads, fun j => ?_⟩
    · have hNext : ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
          (fun j => (if j = tRegs then tape else initTapes j).cells
            (if j = tRegs then tape else initTapes j).head)).nextState = .inl .scanTag := by
        simp [incFirstBody, singleTapeAction, hRead]
      have hInMove : moveHead (n + 2) inHead
          ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
            (fun j => (if j = tRegs then tape else initTapes j).cells
              (if j = tRegs then tape else initTapes j).head)).inputMove = some inHead := by
        simp [incFirstBody, singleTapeAction, hRead, moveHead]
      have hWork : ∀ j,
          (if j = tRegs then tape else initTapes j).updateAndMove
            (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
              (fun j => (if j = tRegs then tape else initTapes j).cells
                (if j = tRegs then tape else initTapes j).head)).write j)
            (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
              (fun j => (if j = tRegs then tape else initTapes j).cells
                (if j = tRegs then tape else initTapes j).head)).workMove j) =
            some (if j = tRegs then nt else initTapes j) := by
        intro j
        have hStepEq : (incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
            (fun y => (if y = tRegs then tape else initTapes y).cells
              (if y = tRegs then tape else initTapes y).head) =
            singleTapeAction (.inl .scanTag) tRegs .sep .right
              (fun y => (if y = tRegs then tape else initTapes y).cells
                (if y = tRegs then tape else initTapes y).head) := by
          simp [incFirstBody, hRead]
        rw [hStepEq]
        have hApp := singleTapeAction_apply (Sum.inl IncRegState.scanTag : IncRegState ⊕ Bool)
          tRegs .sep .right (fun y => if y = tRegs then tape else initTapes y)
          (by simpa [hRead] using hUpd) j
        by_cases hj : j = tRegs
        · subst hj; simpa using hApp
        · simpa [hj] using hApp
      exact ⟨.tryInc, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
    · by_cases hj : j = tRegs
      · subst hj; simpa [hNM'.head_eq] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
  | cons x xs ih =>
    intro nOnes hBound tape hM
    let midPref := pref ++ SimSym.tag b :: List.replicate nOnes (SimSym.bit true)
    let midSuf := xs.map SimSym.bit ++ SimSym.sep :: suf
    have hMidLen : midPref.length = pref.length + 1 + nOnes := by simp [midPref]; omega
    have hCurEq : pref ++ SimSym.tag b ::
        (List.replicate nOnes (SimSym.bit true) ++ (x :: xs).map SimSym.bit) ++
        SimSym.sep :: suf = midPref ++ SimSym.bit x :: midSuf := by
      simp [midPref, midSuf, List.append_assoc]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit x :: midSuf) midPref.length := by
      rw [hMidLen, ← hCurEq]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit x := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit x) midSuf
    cases x with
    | false =>
      have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .left =
          some (pref.length + nOnes) := by simp [moveOneSidedHead]
      obtain ⟨nt, hUpd, hNM⟩ :=
        hM'.update_set (.bit true) .left (by rw [hMidLen]; exact hMove) (by simp)
      rw [list_set_append_mid] at hNM
      have hNextEq : midPref ++ SimSym.bit true :: midSuf =
          pref ++ SimSym.tag b ::
            (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
            SimSym.sep :: suf := by
        simp [midPref, midSuf, List.append_assoc]
      rw [hNextEq] at hNM
      obtain ⟨ft, hBack, hFM⟩ := incFirstBody_backZero input bound pref suf b initTapes inHead
        hOtherBounds nOnes (true :: xs) (by simp at hBound ⊢; omega) nt hNM
      have hIncRep : ∀ m (r : List Bool),
          incBits (List.replicate m true ++ false :: r) =
            List.replicate m false ++ true :: r := by
        intro m r
        induction m with
        | zero => simp [incBits]
        | succ m ihm => simp [List.replicate_succ, incBits, ihm]
      have hIncEq : (incBits (List.replicate nOnes true ++ false :: xs)).map SimSym.bit =
          List.replicate nOnes (SimSym.bit false) ++ (true :: xs).map SimSym.bit := by
        rw [hIncRep]
        simp [List.map_replicate]
      rw [← hIncEq] at hFM
      have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
        input bound initTapes tape nt ft .tryInc .backZero hHeads
        (by rw [hNM.head_eq]; simp at hBound; omega) hUpd hBack (by simp [incFirstBody, hRead])
      exact ⟨ft, Or.inl ⟨by simp, hStep, hFM⟩⟩
    | true =>
      have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .right =
          some (pref.length + 1 + (nOnes + 1)) := by simp [moveOneSidedHead]; omega
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hMidLen]; exact hMove)
      have hNextEq : midPref ++ SimSym.bit true :: midSuf =
          pref ++ SimSym.tag b ::
            (List.replicate (nOnes + 1) (SimSym.bit true) ++ xs.map SimSym.bit) ++
            SimSym.sep :: suf := by
        simp [midPref, midSuf, List.replicate_succ', List.append_assoc]
      rw [hNextEq] at hNM
      obtain ⟨ft, hBranch⟩ := ih (nOnes + 1) (by simp at hBound ⊢; omega) nt hNM
      rcases hBranch with ⟨hMemXs, hWin, hFM⟩ | ⟨hNoXs, hCont, hFM⟩
      · have hIncEq : incBits (List.replicate nOnes true ++ true :: xs) =
            incBits (List.replicate (nOnes + 1) true ++ xs) := by
          simp [List.replicate_succ', List.append_assoc]
        rw [← hIncEq] at hFM
        have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
          input bound initTapes tape nt ft .tryInc .tryInc hHeads
          (by rw [hNM.head_eq]; simp at hBound ⊢; omega) hUpd hWin (by simp [incFirstBody, hRead])
        exact ⟨ft, Or.inl ⟨by simp [hMemXs], hStep, hFM⟩⟩
      · have hOutEq : pref ++ SimSym.tag b ::
            (List.replicate (nOnes + 1) (SimSym.bit true) ++ xs.map SimSym.bit) ++
            SimSym.sep :: suf =
            pref ++ SimSym.tag b ::
              (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
              SimSym.sep :: suf := by
          simp [List.replicate_succ', List.append_assoc]
        rw [hOutEq] at hFM
        have hFM' : TapeMatches ft
            (pref ++ SimSym.tag b ::
              (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
              SimSym.sep :: suf)
            (pref.length + nOnes + (true :: xs).length + 2) := by
          simpa [Nat.add_assoc, Nat.add_comm 1] using hFM
        have hStep : Relation.ReflTransGen
            (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
          refine Relation.ReflTransGen.head ⟨?_, hHeads, fun j => ?_⟩ hCont
          · have hNext : ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head)).nextState = .inl .tryInc := by
              simp [incFirstBody, singleTapeAction, hRead]
            have hInMove : moveHead (n + 2) inHead
                ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).inputMove = some inHead := by
              simp [incFirstBody, singleTapeAction, hRead, moveHead]
            have hWork : ∀ j,
                (if j = tRegs then tape else initTapes j).updateAndMove
                  (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head)).write j)
                  (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head)).workMove j) =
                  some (if j = tRegs then nt else initTapes j) := by
              intro j
              have hStepEq : (incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head) =
                  singleTapeAction (.inl .tryInc) tRegs (.bit true) .right
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head) := by
                simp [incFirstBody, hRead]
              rw [hStepEq]
              have hApp := singleTapeAction_apply (Sum.inl IncRegState.tryInc : IncRegState ⊕ Bool)
                tRegs (.bit true) .right (fun y => if y = tRegs then tape else initTapes y)
                (by simpa [hRead] using hUpd) j
              by_cases hj : j = tRegs
              · subst hj; simpa using hApp
              · simpa [hj] using hApp
            exact ⟨.tryInc, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
          · by_cases hj : j = tRegs
            · subst hj; simpa [hNM.head_eq] using by simp at hBound; omega
            · simpa [hj] using hOtherBounds j hj
        exact ⟨ft, Or.inr ⟨by simp [hNoXs], hStep, hFM'⟩⟩

private theorem incFirstBody_scan {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (suf pref : List (Bool × List Bool)),
      (∀ r ∈ pref, r.2.length = W ∧ false ∉ r.2) →
      (∀ r ∈ suf, r.2.length = W) →
      1 + (pref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix pref).length →
        (∃ p₁ cur p₂, suf = p₁ ++ cur :: p₂ ∧
          false ∈ cur.2 ∧ (∀ r ∈ p₁, false ∉ r.2) ∧
          ∃ ft,
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (encodeRegsTape (pref ++ p₁ ++ (false, incBits cur.2) :: p₂) src)
              (encodeRegsPrefix (pref ++ p₁)).length) ∨
        ((∀ r ∈ suf, false ∉ r.2) ∧
          ∃ ft,
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr false, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src)
              (encodeRegsPrefix (pref ++ suf)).length) := by
  intro suf
  induction suf with
  | nil =>
    intro pref hPref _ hBound tape hM
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hM' : TapeMatches tape (encodeRegsPrefix pref ++ SimSym.srcSep ::
        (SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark]))
        (encodeRegsPrefix pref).length := by
      simpa [encodeRegsTape, encodeSrcEntry] using hM
    have hRead : tape.cells tape.head = .srcSep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) .srcSep _
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
        some (encodeRegsPrefix pref).length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hM'.update_keep .stay hMove
    right
    refine ⟨by simp, ft, ?_, by simpa [encodeRegsTape, encodeSrcEntry] using hFM⟩
    exact singleTape_compStep_exit_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape ft .scanTag hHeads
      (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [incFirstBody, hRead])
  | cons cur rs ih =>
    intro pref hPref hSuf hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := hSuf (b, bs) (by simp)
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hBound' : 1 + pref.length * (W + 2) + (W + 2) + rs.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hBound ⊢
      omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by omega
      · simpa [hj] using hOtherBounds j hj
    let tailSyms : List SimSym := rs.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hSplit : encodeRegsTape (pref ++ (b, bs) :: rs) src =
        encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms) := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hM' : TapeMatches tape
        (encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms))
        (encodeRegsPrefix pref).length := by
      rw [← hSplit]; exact hM
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) (.tag b) _
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .right =
        some ((encodeRegsPrefix pref).length + 1) := by simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
    have hNM' : TapeMatches nt
        (encodeRegsPrefix pref ++ SimSym.tag b ::
          (List.replicate 0 (SimSym.bit true) ++ bs.map SimSym.bit) ++ SimSym.sep :: tailSyms)
        ((encodeRegsPrefix pref).length + 1 + 0) := by
      simpa [List.append_assoc] using hNM
    obtain ⟨mt, hBranch⟩ := incFirstBody_tryInc input bound (encodeRegsPrefix pref) tailSyms b
      initTapes inHead hOtherBounds bs 0 (by rw [hPL, hBsLen]; omega) nt hNM'
    rcases hBranch with ⟨hMemBs, hWin, hFM⟩ | ⟨hNoBs, hCont, hFM⟩
    · have hOutEq : encodeRegsPrefix pref ++ SimSym.tag false ::
          (incBits (List.replicate 0 true ++ bs)).map SimSym.bit ++ SimSym.sep :: tailSyms =
          encodeRegsTape (pref ++ [] ++ (false, incBits bs) :: rs) src := by
        simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
      rw [hOutEq] at hFM
      have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
        input bound initTapes tape nt mt .scanTag .tryInc hHeads
        (by rw [hNM.head_eq, hPL]; omega) hUpd hWin (by simp [incFirstBody, hRead])
      left
      exact ⟨[], (b, bs), rs, rfl, hMemBs, by simp, mt, hStep, by simpa using hFM⟩
    · have hMtEq : encodeRegsPrefix pref ++ SimSym.tag b ::
          (List.replicate 0 (SimSym.bit true) ++ bs.map SimSym.bit) ++ SimSym.sep :: tailSyms =
          encodeRegsTape ((pref ++ [(b, bs)]) ++ rs) src := by
        simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
      rw [hMtEq] at hFM
      have hHeadNext : (encodeRegsPrefix pref).length + 0 + bs.length + 2 =
          (encodeRegsPrefix (pref ++ [(b, bs)])).length := by
        simp [encodeRegsPrefix_snoc, encodeRegEntry_length]
        omega
      rw [hHeadNext] at hFM
      have hPrefNext : ∀ r ∈ pref ++ [(b, bs)], r.2.length = W ∧ false ∉ r.2 := by
        intro r hr
        rcases List.mem_append.mp hr with hMem | hSingle
        · exact hPref r hMem
        · simp at hSingle; subst hSingle; exact ⟨hBsLen, hNoBs⟩
      have hBoundNext : 1 + ((pref ++ [(b, bs)]).length + rs.length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have : pref.length + 1 + rs.length = pref.length + (rs.length + 1) := by omega
        rw [this]; exact hBound
      have hSufNext : ∀ r ∈ rs, r.2.length = W := fun r hr => hSuf r (by simp [hr])
      have hStepHead : Relation.ReflTransGen
          (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inl .scanTag, inHead, fun j => if j = tRegs then mt else initTapes j⟩ := by
        refine Relation.ReflTransGen.head ⟨?_, hHeads, fun j => ?_⟩ hCont
        · have hNext : ((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
              (fun y => (if y = tRegs then tape else initTapes y).cells
                (if y = tRegs then tape else initTapes y).head)).nextState = .inl .tryInc := by
            simp [incFirstBody, singleTapeAction, hRead]
          have hInMove : moveHead (n + 2) inHead
              ((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head)).inputMove = some inHead := by
            simp [incFirstBody, singleTapeAction, hRead, moveHead]
          have hWork : ∀ j,
              (if j = tRegs then tape else initTapes j).updateAndMove
                (((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).write j)
                (((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).workMove j) =
                some (if j = tRegs then nt else initTapes j) := by
            intro j
            have hStepEq : (incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head) =
                singleTapeAction (.inl .tryInc) tRegs (.tag b) .right
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head) := by
              simp [incFirstBody, hRead]
            rw [hStepEq]
            have hApp := singleTapeAction_apply (Sum.inl IncRegState.tryInc : IncRegState ⊕ Bool)
              tRegs (.tag b) .right (fun y => if y = tRegs then tape else initTapes y)
              (by simpa [hRead] using hUpd) j
            by_cases hj : j = tRegs
            · subst hj; simpa using hApp
            · simpa [hj] using hApp
          exact ⟨.scanTag, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
        · by_cases hj : j = tRegs
          · subst hj; simpa [hNM.head_eq, hPL] using by omega
          · simpa [hj] using hOtherBounds j hj
      rcases ih (pref ++ [(b, bs)]) hPrefNext hSufNext hBoundNext mt hFM with
        ⟨p₁, cur, p₂, hEqRs, hMemCur, hNoP1, ft, hRec, hF⟩ |
        ⟨hNoRs, ft, hRec, hF⟩
      · left
        refine ⟨(b, bs) :: p₁, cur, p₂, by simp [hEqRs], hMemCur, fun r hr => ?_, ft,
          hStepHead.trans hRec, by simpa [List.append_assoc] using hF⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · exact hNoBs
        · exact hNoP1 r hMem
      · right
        refine ⟨fun r hr => ?_, ft, hStepHead.trans hRec, by simpa [List.append_assoc] using hF⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · exact hNoBs
        · exact hNoRs r hMem

theorem incFirstRegBelowMax_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src) 1) :
    (∃ pref cur suf, work = pref ++ cur :: suf ∧ false ∈ cur.2 ∧
      (∀ r ∈ pref, false ∉ r.2) ∧
      ∃ ft, (incFirstRegBelowMax InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape
          (pref.map (fun _ => (false, natToBits W 1)) ++ (false, incBits cur.2) :: suf) src) 1) ∨
    ((∀ r ∈ work, false ∉ r.2) ∧
      ∃ ft, (incFirstRegBelowMax InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) 1) := by
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  rcases incFirstBody_scan input bound W src hSrc initTapes inHead hOtherBounds work []
      (by simp) hWork (by simpa using hBound) (initTapes tRegs)
      (by simpa [encodeRegsPrefix] using hMatch) with
    ⟨p₁, cur, p₂, hEqW, hCurF, hNoP1, mt, hBody, hMT⟩ |
    ⟨hNoW, mt, hBody, hMT⟩
  · simp only [List.nil_append] at hEqW hMT
    rw [hTapesSelf] at hBody
    have hP1Len : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
    have hCurLen : cur.2.length = W := hWork cur (by rw [hEqW]; simp)
    have hP2Len : ∀ r ∈ p₂, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
    have hBoundReset : 1 + (p₁.length + 1 + p₂.length) * (W + 2) + (W + 3) ≤ bound tRegs := by
      have hLenEq : p₁.length + 1 + p₂.length = work.length := by
        rw [hEqW]; simp; omega
      rw [hLenEq]; exact hBound
    obtain ⟨ft, hReset, hFM⟩ := resetLeftRegs_reachesExit input bound W hW p₁
      (false, incBits cur.2) p₂ src hP1Len (by simp [incBits_length, hCurLen]) hP2Len hSrc
      hBoundReset (fun j => if j = tRegs then mt else initTapes j) inHead
      (fun j hj => by simp [hj, hOtherBounds j hj]) hMT
    have hFtEq : (fun j => if j = tRegs then ft else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hReset
    left
    refine ⟨p₁, cur, p₂, hEqW, hCurF, hNoP1, ft, ?_, hFM⟩
    exact (incFirstBody InputAlphabet).branch_reachesExit _ _ input bound true hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => true) input bound hReset)
  · simp only [List.nil_append] at hMT
    rw [hTapesSelf] at hBody
    have hWL := encodeRegsPrefix_length W work hWork
    have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
      encodeRegsTape_length W work src hWork hSrc
    have hRewBounds : ∀ j, j ≠ tRegs →
        ((fun j => if j = tRegs then mt else initTapes j) j).head < bound j := by
      intro j hj; simpa [hj] using hOtherBounds j hj
    obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
      (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
      (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
      (fun j => if j = tRegs then mt else initTapes j) inHead hRewBounds
      (encodeRegsPrefix work).length (by rw [hWL]; omega)
      (by rw [hWorkLen, hWL]; omega) hMT
    have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
      funext j; by_cases hj : j = tRegs
      · subst hj; simp
      · rw [hOth j hj]; simp [hj]
    rw [hFinalEq] at hRew
    right
    refine ⟨hNoW, finalTapes tRegs, ?_, hFM⟩
    exact (incFirstBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

theorem false_mem_natToBits_iff_lt {W v : ℕ} (hv : v < 2 ^ W) :
    false ∈ natToBits W v ↔ v < 2 ^ W - 1 := by
  constructor
  · intro hMem
    by_contra hGe
    have hvEq : v = 2 ^ W - 1 := by omega
    subst hvEq
    have hRep : natToBits W (2 ^ W - 1) = List.replicate W true := by
      calc
        natToBits W (2 ^ W - 1)
          = natToBits (List.replicate W true).length (bitsToNat (List.replicate W true)) := by
            simp [bitsToNat_replicate_true]
        _ = List.replicate W true := natToBits_bitsToNat _
    rw [hRep] at hMem
    simp at hMem
  · intro hLt
    by_contra hNo
    have hAllT : ∀ b ∈ natToBits W v, b = true := by
      intro b hb; cases b with
      | false => exact (hNo hb).elim
      | true => rfl
    have hRep : natToBits W v = List.replicate W true := by
      apply List.eq_replicate_iff.mpr
      exact ⟨natToBits_length W v, hAllT⟩
    have hVal : v = 2 ^ W - 1 := by
      calc
        v = bitsToNat (natToBits W v) := (bitsToNat_natToBits_of_lt hv).symm
        _ = bitsToNat (List.replicate W true) := by rw [hRep]
        _ = 2 ^ W - 1 := bitsToNat_replicate_true W
    omega

theorem incBits_natToBits {W v : ℕ} (hLt : v < 2 ^ W - 1) :
    incBits (natToBits W v) = natToBits W (v + 1) := by
  have hv : v < 2 ^ W := by omega
  have hFalse : false ∈ natToBits W v := (false_mem_natToBits_iff_lt hv).mpr hLt
  calc
    incBits (natToBits W v)
      = natToBits (incBits (natToBits W v)).length (bitsToNat (incBits (natToBits W v))) :=
        (natToBits_bitsToNat _).symm
    _ = natToBits W (v + 1) := by
      rw [incBits_length, natToBits_length, bitsToNat_incBits hFalse, bitsToNat_natToBits_of_lt hv]

/-- Append one initial working register `(false, natToBits W 1)` onto `tRegs`
using `tArgA` (`1^W`) as a template, then rewind `tArgA` to cell `1`. -/
inductive WriteOneRegState where
  | wTag
  | wOne
  | wZeros
  deriving DecidableEq

def WriteOneRegState.equivFin : WriteOneRegState ≃ Fin 3 where
  toFun | .wTag => 0 | .wOne => 1 | .wZeros => 2
  invFun | 0 => .wTag | 1 => .wOne | _ => .wZeros
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype WriteOneRegState := Fintype.ofEquiv (Fin 3) WriteOneRegState.equivFin.symm

def writeOneRegBody (InputAlphabet : Type*) :
    TMComponent WriteOneRegState InputAlphabet SimSym 5 Unit where
  start := .wTag
  step s _ scanned :=
    match s with
    | .wTag =>
      twoTapeAction (.inl .wOne) tRegs tArgA (.tag false) (scanned tArgA) .right .right scanned
    | .wOne =>
      twoTapeAction (.inl .wZeros) tRegs tArgA (.bit true) (scanned tArgA) .right .stay scanned
    | .wZeros =>
      match scanned tArgA with
      | .bit _ =>
        twoTapeAction (.inl .wZeros) tRegs tArgA (.bit false) (scanned tArgA) .right .right scanned
      | s =>
        twoTapeAction (.inr ()) tRegs tArgA .sep s .right .left scanned

def writeOneInitReg (InputAlphabet : Type*) :=
  (writeOneRegBody InputAlphabet).seq (rewindTape InputAlphabet tArgA)

def initLoopFn : SimSym → (Bool × SimSym × TapeMove)
  | .bit b => (true, .bit b, .right)
  | s => (false, s, .stay)

def initLoopCheck (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom fun _ scanned =>
    let res := initLoopFn (scanned tArgB)
    singleTapeAction res.1 tArgB res.2.1 res.2.2 scanned

/-- Using `1^W` templates on both `tArgA` and `tArgB` (with `1 ≤ W`), write `W + 1`
initial working registers `(false, firstCode)` followed by `[.srcSep, .tag true]` onto
`tRegs`, and clear both `tArgA` and `tArgB` back to `[.leftMark]`. -/
def initWorkRegsFromTemplate (InputAlphabet : Type*) :=
  (writeOneInitReg InputAlphabet).seq
    ((((initLoopCheck InputAlphabet).branch
        ((writeOneInitReg InputAlphabet).mapExit fun _ => Sum.inl ())
        (TMComponent.atom fun _ scanned =>
          singleTapeAction (.inr ()) tRegs .srcSep .right scanned)).loop).seq
      ((TMComponent.atom fun _ scanned =>
          singleTapeAction () tRegs (.tag true) .right scanned).seq
        ((rewindTape InputAlphabet tArgB).seq
          ((clearTape InputAlphabet tArgA).seq (clearTape InputAlphabet tArgB)))))

private theorem writeOneRegBody_wZeros {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (prefSyms : List SimSym)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : prefSyms.length + W + 3 ≤ bound tRegs)
    (hBoundA : W + 2 ≤ bound tArgA)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ tArgA → (initTapes j).head < bound j) :
    ∀ rem, rem ≤ W - 1 →
      let zDone := (W - 1) - rem
      ∀ tapeReg tapeA,
        TapeMatches tapeReg
          (prefSyms ++ [SimSym.tag false, SimSym.bit true] ++
            List.replicate zDone (SimSym.bit false))
          (prefSyms.length + 2 + zDone) →
        TapeMatches tapeA
          (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark])
          (2 + zDone) →
        ∃ ftReg ftA,
          Relation.ReflTransGen
            (fun a b => (writeOneRegBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .wZeros, inHead,
              fun j => if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j⟩
            ⟨.inr (), inHead,
              fun j => if j = tRegs then ftReg else if j = tArgA then ftA else initTapes j⟩ ∧
          TapeMatches ftReg (prefSyms ++ encodeRegEntry false (natToBits W 1))
            (prefSyms.length + (W + 2)) ∧
          TapeMatches ftA
            (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) W := by
  intro rem
  induction rem with
  | zero =>
    intro _ zDone tapeReg tapeA hMReg hMA
    have hzEq : zDone = W - 1 := by simp [zDone]
    have hNe : tRegs ≠ tArgA := by decide
    let curReg := prefSyms ++ [SimSym.tag false, SimSym.bit true] ++
      List.replicate zDone (SimSym.bit false)
    have hCurLen : curReg.length = prefSyms.length + 2 + zDone := by simp [curReg]; omega
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head < bound j := by
      intro j; by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg.head_eq] using by omega
      · by_cases h2 : j = tArgA
        · subst h2; simpa [h1, hMA.head_eq] using by omega
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hReadA : tapeA.cells tapeA.head = .endMark := by
      rw [hMA.read_lt (by simp; omega)]
      have hPosA : 2 + zDone = W + 1 := by omega
      simp [hPosA, List.getElem_append_right]
    have hMoveR : moveOneSidedHead (prefSyms.length + 2 + zDone) .right =
        some (prefSyms.length + (W + 2)) := by
      simp [moveOneSidedHead, hzEq]; omega
    have hMoveA : moveOneSidedHead (2 + zDone) .left = some W := by
      simp [moveOneSidedHead, hzEq]; omega
    obtain ⟨ftR, hUpdR, hFMR⟩ :=
      hMReg.update_append_move (by simp; omega) .sep .right hMoveR
    obtain ⟨ftA, hUpdA, hFMA⟩ := hMA.update_keep .left hMoveA
    have hOutRegEq : curReg ++ [SimSym.sep] = prefSyms ++ encodeRegEntry false (natToBits W 1) := by
      simp [curReg, encodeRegEntry, natToBits_one hW, hzEq, List.map_replicate, List.append_assoc]
    rw [hOutRegEq] at hFMR
    have hStepEq : (writeOneRegBody InputAlphabet).step .wZeros (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).cells
          (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head) =
        twoTapeAction (.inr ()) tRegs tArgA .sep .endMark .right .left
          (fun j => (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).cells
            (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head) := by
      simp only [writeOneRegBody, ↓reduceIte, hNe.symm, hReadA]
    refine ⟨ftR, ftA, ?_, hFMR, hFMA⟩
    exact twoTape_compStep_exit_override (writeOneRegBody InputAlphabet) tRegs tArgA hNe
      input bound initTapes tapeReg tapeA ftR ftA .wZeros hHeads
      (by rw [hFMR.head_eq]; omega) (by rw [hFMA.head_eq]; omega)
      hUpdR (by simpa [hReadA] using hUpdA) hStepEq
  | succ r ih =>
    intro hLe zDone tapeReg tapeA hMReg hMA
    have hzLt : zDone < W - 1 := by simp [zDone]; omega
    have hNe : tRegs ≠ tArgA := by decide
    let curReg := prefSyms ++ [SimSym.tag false, SimSym.bit true] ++
      List.replicate zDone (SimSym.bit false)
    have hHeads : ∀ j,
        (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head < bound j := by
      intro j; by_cases h1 : j = tRegs
      · subst h1; simpa [hMReg.head_eq] using by omega
      · by_cases h2 : j = tArgA
        · subst h2; simpa [h1, hMA.head_eq] using by omega
        · simpa [h1, h2] using hOtherBounds j h1 h2
    have hReadA : tapeA.cells tapeA.head = .bit true := by
      rw [hMA.read_lt (by simp; omega)]
      have hPosA : 2 + zDone = (1 + zDone) + 1 := by omega
      simp only [hPosA, List.cons_append, List.getElem_cons_succ]
      simp [List.getElem_append_left (by simp; omega : 1 + zDone < (List.replicate W (SimSym.bit true)).length)]
    have hMoveR : moveOneSidedHead (prefSyms.length + 2 + zDone) .right =
        some (prefSyms.length + 2 + (zDone + 1)) := by
      simp [moveOneSidedHead]; omega
    have hMoveA : moveOneSidedHead (2 + zDone) .right = some (2 + (zDone + 1)) := by
      simp [moveOneSidedHead]; omega
    obtain ⟨ntR, hUpdR, hNMR⟩ :=
      hMReg.update_append_move (by simp; omega) (.bit false) .right hMoveR
    obtain ⟨ntA, hUpdA, hNMA⟩ := hMA.update_keep .right hMoveA
    have hNextRegEq : curReg ++ [SimSym.bit false] =
        prefSyms ++ [SimSym.tag false, SimSym.bit true] ++
          List.replicate (zDone + 1) (SimSym.bit false) := by
      simp [curReg, List.replicate_succ', List.append_assoc]
    rw [hNextRegEq] at hNMR
    have hZNext : (W - 1) - r = zDone + 1 := by simp [zDone]; omega
    rw [← hZNext] at hNMR hNMA
    obtain ⟨ftR, ftA, hRest, hFMR, hFMA⟩ := ih (by omega) ntR ntA hNMR hNMA
    have hStepEq : (writeOneRegBody InputAlphabet).step .wZeros (readInput input inHead)
        (fun j => (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).cells
          (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head) =
        twoTapeAction (.inl .wZeros) tRegs tArgA (.bit false) (.bit true) .right .right
          (fun j => (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).cells
            (if j = tRegs then tapeReg else if j = tArgA then tapeA else initTapes j).head) := by
      simp only [writeOneRegBody, ↓reduceIte, hNe.symm, hReadA]
    refine ⟨ftR, ftA, ?_, hFMR, hFMA⟩
    exact twoTape_compStep_head_override (writeOneRegBody InputAlphabet) tRegs tArgA hNe
      input bound initTapes tapeReg tapeA ntR ntA ftR ftA .wZeros .wZeros hHeads
      (by rw [hNMR.head_eq, hZNext]; omega) (by rw [hNMA.head_eq, hZNext]; omega)
      hUpdR (by simpa [hReadA] using hUpdA) hRest hStepEq

theorem writeOneInitReg_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (prefSyms : List SimSym)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : prefSyms.length + W + 3 ≤ bound tRegs)
    (hBoundA : W + 2 ≤ bound tArgA)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ tArgA → (initTapes j).head < bound j)
    (hMatchReg : TapeMatches (initTapes tRegs) prefSyms prefSyms.length)
    (hMatchA : TapeMatches (initTapes tArgA)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1) :
    ∃ ftR ftA,
      (writeOneInitReg InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRegs then ftR else if j = tArgA then ftA else initTapes j) inHead ∧
      TapeMatches ftR (prefSyms ++ encodeRegEntry false (natToBits W 1))
        (prefSyms.length + (W + 2)) ∧
      TapeMatches ftA
        (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1 := by
  have hNe : tRegs ≠ tArgA := by decide
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases h1 : j = tRegs
    · subst h1; simpa [hMatchReg.head_eq] using by omega
    · by_cases h2 : j = tArgA
      · subst h2; simpa [h1, hMatchA.head_eq] using by omega
      · exact hOtherBounds j h1 h2
  have hMoveR₁ : moveOneSidedHead prefSyms.length .right = some (prefSyms.length + 1) := by
    simp [moveOneSidedHead]
  have hMoveA₁ : moveOneSidedHead 1 .right = some 2 := rfl
  obtain ⟨ntR₁, hUpdR₁, hNMR₁⟩ := hMatchReg.update_append_move rfl (.tag false) .right hMoveR₁
  obtain ⟨ntA₁, hUpdA₁, hNMA₁⟩ := hMatchA.update_keep .right hMoveA₁
  have hMoveR₂ : moveOneSidedHead (prefSyms.length + 1) .right = some (prefSyms.length + 2) := by
    simp [moveOneSidedHead]
  have hMoveA₂ : moveOneSidedHead 2 .stay = some 2 := rfl
  obtain ⟨ntR₂, hUpdR₂, hNMR₂⟩ := hNMR₁.update_append_move (by simp) (.bit true) .right hMoveR₂
  obtain ⟨ntA₂, hUpdA₂, hNMA₂⟩ := hNMA₁.update_keep .stay hMoveA₂
  have hEqA₂ : ntA₂ = ntA₁ := by
    have hC : ntA₂.cells = ntA₁.cells := by funext i; exact (hNMA₂.2 i).trans (hNMA₁.2 i).symm
    have hH : ntA₂.head = ntA₁.head := hNMA₂.head_eq.trans hNMA₁.head_eq.symm
    cases ntA₂; cases ntA₁; simp only [OneSidedTape.mk.injEq]; exact ⟨hC, hH⟩
  rw [hEqA₂] at hUpdA₂
  have hNMR₂' : TapeMatches ntR₂
      (prefSyms ++ [SimSym.tag false, SimSym.bit true] ++ List.replicate ((W - 1) - (W - 1)) (SimSym.bit false))
      (prefSyms.length + 2 + ((W - 1) - (W - 1))) := by
    simpa [List.append_assoc] using hNMR₂
  obtain ⟨mtR, mtA, hZeros, hMMR, hMMA⟩ := writeOneRegBody_wZeros input bound W hW prefSyms
    initTapes inHead hBoundReg hBoundA hOtherBounds (W - 1) le_rfl ntR₂ ntA₁
    hNMR₂' (by simpa using hNMA₁)
  have hHeads₁ : ∀ j, (if j = tRegs then ntR₁ else if j = tArgA then ntA₁ else initTapes j).head < bound j := by
    intro j; by_cases h1 : j = tRegs
    · subst h1; simpa [hNMR₁.head_eq] using by omega
    · by_cases h2 : j = tArgA
      · subst h2; simpa [h1, hNMA₁.head_eq] using by omega
      · simpa [h1, h2] using hOtherBounds j h1 h2
  have hStepOne := twoTape_compStep_head_override (writeOneRegBody InputAlphabet) tRegs tArgA hNe
    input bound initTapes ntR₁ ntA₁ ntR₂ ntA₁ mtR mtA .wOne .wZeros hHeads₁
    (by rw [hNMR₂.head_eq]; omega) (by rw [hNMA₁.head_eq]; omega)
    hUpdR₂ hUpdA₂ hZeros (by simp [writeOneRegBody, hNe.symm])
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs
      else if j = tArgA then initTapes tArgA else initTapes j) = initTapes := by
    funext j; by_cases h1 : j = tRegs
    · subst h1; simp
    · by_cases h2 : j = tArgA
      · subst h2; simp [hNe.symm]
      · simp [h1, h2]
  have hHeads₀ : ∀ j, (if j = tRegs then initTapes tRegs
      else if j = tArgA then initTapes tArgA else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBody : (writeOneRegBody InputAlphabet).ReachesExit input bound initTapes inHead ()
      (fun j => if j = tRegs then mtR else if j = tArgA then mtA else initTapes j) inHead := by
    have hRun := twoTape_compStep_head_override (writeOneRegBody InputAlphabet) tRegs tArgA hNe
      input bound initTapes (initTapes tRegs) (initTapes tArgA) ntR₁ ntA₁ mtR mtA
      .wTag .wOne hHeads₀ (by rw [hNMR₁.head_eq]; omega) (by rw [hNMA₁.head_eq]; omega)
      hUpdR₁ hUpdA₁ hStepOne (by simp [writeOneRegBody, hNe.symm])
    rw [hTapesSelf] at hRun
    exact hRun
  let cA := SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]
  have hNoLeftA : ∀ i, 1 ≤ i → i < cA.length → cA[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [cA, List.length_cons, List.length_append, List.length_replicate, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp [cA]; omega)]
      simp only [cA, List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < W
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = W := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  have hRewBounds : ∀ j, j ≠ tArgA →
      ((fun j => if j = tRegs then mtR else if j = tArgA then mtA else initTapes j) j).head <
        bound j := by
    intro j hj; by_cases h1 : j = tRegs
    · subst h1; simpa [hMMR.head_eq] using by omega
    · simpa [h1, hj] using hOtherBounds j h1 hj
  obtain ⟨finalTapes, hRew, hFMA, hOth⟩ := rewindTape_reachesExit tArgA input bound cA
    (by simp [cA]) rfl hNoLeftA (by simp [cA]; exact hBoundA) _ inHead hRewBounds W hW
    (by simp [cA]; omega) (by simpa [cA, hNe.symm] using hMMA)
  have hFinalEq : finalTapes = fun j => if j = tRegs then mtR
      else if j = tArgA then finalTapes tArgA else initTapes j := by
    funext j; by_cases h2 : j = tArgA
    · simp [h2, hNe.symm]
    · rw [hOth j h2]
      by_cases h1 : j = tRegs <;> simp [h1, h2]
  rw [hFinalEq] at hRew
  exact ⟨mtR, finalTapes tArgA, (writeOneRegBody InputAlphabet).seq_reachesExit
    (rewindTape InputAlphabet tArgA) input bound hBody hRew, hMMR, hFMA⟩

theorem initWorkRegsFromTemplate_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundReg : 1 + (W + 1) * (W + 2) + 3 ≤ bound tRegs)
    (hBoundA : W + 2 ≤ bound tArgA)
    (hBoundB : W + 2 ≤ bound tArgB)
    (hOtherBounds : ∀ j, j ≠ tRegs → j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchReg : TapeMatches (initTapes tRegs) [SimSym.leftMark] 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1) :
    ∃ ftR ftA ftB,
      (initWorkRegsFromTemplate InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRegs then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR
        (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1)) ++
          [SimSym.srcSep, SimSym.tag true])
        (1 + (W + 1) * (W + 2) + 2) ∧
      TapeMatches ftA [SimSym.leftMark] 1 ∧
      TapeMatches ftB [SimSym.leftMark] 1 := by
  have hNeRA : tRegs ≠ tArgA := by decide
  have hNeRB : tRegs ≠ tArgB := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  have hFirstBound : ([SimSym.leftMark] : List SimSym).length + W + 3 ≤ bound tRegs := by
    have : (1 + (W + 1) * (W + 2) + 3) = (1 + (W + 2) + W * (W + 2) + 3) := by
      rw [Nat.succ_mul]; omega
    simp; omega
  obtain ⟨r₁, a₁, hFirst, hMR₁, hMA₁⟩ := writeOneInitReg_reachesExit input bound W hW
    [SimSym.leftMark] initTapes inHead hFirstBound hBoundA
    (fun j h1 h2 => by
      by_cases h3 : j = tArgB
      · subst h3; simpa [hMatchB.head_eq] using by omega
      · exact hOtherBounds j h1 h2 h3)
    hMatchReg hMatchA
  have hRep1 : [SimSym.leftMark] ++ encodeRegEntry false (natToBits W 1) =
      encodeRegsPrefix (List.replicate 1 (false, natToBits W 1)) := by
    simp [encodeRegsPrefix, List.replicate_one]
  rw [hRep1] at hMR₁
  have hMR₁' : TapeMatches r₁ (encodeRegsPrefix (List.replicate 1 (false, natToBits W 1)))
      (1 + 1 * (W + 2)) := by
    simpa using hMR₁
  let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRegs → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    TapeMatches (tapes tArgA)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1 ∧
    ∃ done, done ≤ W ∧
      TapeMatches (tapes tRegs)
        (encodeRegsPrefix (List.replicate (1 + done) (false, natToBits W 1)))
        (1 + (1 + done) * (W + 2)) ∧
      TapeMatches (tapes tArgB)
        (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark])
        (1 + done)
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun _ tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRegs → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    TapeMatches (tapes tArgA)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]) 1 ∧
    TapeMatches (tapes tRegs)
      (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1)) ++ [SimSym.srcSep])
      (1 + (W + 1) * (W + 2) + 1) ∧
    TapeMatches (tapes tArgB)
      (SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark])
      (1 + W)
  let loopBody := (initLoopCheck InputAlphabet).branch
    ((writeOneInitReg InputAlphabet).mapExit fun _ => Sum.inl ())
    (TMComponent.atom fun _ scanned => singleTapeAction (.inr ()) tRegs .srcSep .right scanned)
  have hLoopStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        loopBody.ReachesExit input bound tapes ih (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧ (W + 1 - (tapes' tArgB).head) < (W + 1 - (tapes tArgB).head)) ∨
      (∃ e : Unit, ∃ tapes' ih',
        loopBody.ReachesExit input bound tapes ih (.inr e) tapes' ih' ∧
        Post e tapes' ih') := by
    intro tapes ih ⟨hIhEq, hOth, hMA, done, hDoneLe, hMR, hMB⟩
    subst ih
    have hHeads : ∀ j, (tapes j).head < bound j := by
      intro j; by_cases h1 : j = tRegs
      · subst h1; rw [hMR.head_eq]
        have : (1 + done) * (W + 2) ≤ (W + 1) * (W + 2) := Nat.mul_le_mul_right _ (by omega)
        omega
      · by_cases h2 : j = tArgA
        · subst h2; simpa [hMA.head_eq] using by omega
        · by_cases h3 : j = tArgB
          · subst h3; simpa [hMB.head_eq] using by omega
          · rw [hOth j h1 h2 h3]; exact hOtherBounds j h1 h2 h3
    by_cases hDoneLt : done < W
    · have hReadB : (tapes tArgB).cells (tapes tArgB).head = .bit true := by
        rw [hMB.read_lt (by simp; omega)]
        have hLtRep : done < (List.replicate W (SimSym.bit true)).length := by simp [hDoneLt]
        simp only [Nat.add_comm 1 done, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left hLtRep]
        simp
      have hMoveB : moveOneSidedHead (1 + done) .right = some (1 + (done + 1)) := by
        simp [moveOneSidedHead]; omega
      obtain ⟨ntB, hUpdB, hNMB⟩ := hMB.update_keep .right hMoveB
      have hCheck' := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
        (fun _ => initLoopFn) tArgB input bound tapes inHead hHeads
        (by simpa [initLoopFn, hReadB] using hUpdB) (by rw [hNMB.head_eq]; omega)
      have hCheck : (initLoopCheck InputAlphabet).ReachesExit input bound tapes inHead true
          (fun j => if j = tArgB then ntB else tapes j) inHead := by
        simpa [initLoopCheck, initLoopFn, hReadB] using hCheck'
      have hPL : (encodeRegsPrefix (List.replicate (1 + done) (false, natToBits W 1))).length =
          1 + (1 + done) * (W + 2) := by
        have := encodeRegsPrefix_length W (List.replicate (1 + done) (false, natToBits W 1))
          (fun r hr => by
            rcases List.mem_replicate.mp hr with ⟨_, rfl⟩
            simp [natToBits_length])
        simpa using this
      have hNextBoundReg : (encodeRegsPrefix (List.replicate (1 + done) (false, natToBits W 1))).length +
          W + 3 ≤ bound tRegs := by
        rw [hPL]
        have : (1 + done + 1) * (W + 2) ≤ (W + 1) * (W + 2) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      obtain ⟨ntR, ntA, hWrite, hNMR, hNMA⟩ := writeOneInitReg_reachesExit input bound W hW
        (encodeRegsPrefix (List.replicate (1 + done) (false, natToBits W 1)))
        (fun j => if j = tArgB then ntB else tapes j) inHead hNextBoundReg hBoundA
        (fun j h1 h2 => by
          by_cases h3 : j = tArgB
          · subst h3; simpa [hNMB.head_eq] using by omega
          · simpa [h1, h2, h3] using hHeads j)
        (by simp [hNeRB, hPL]; exact hMR) (by simp; exact hMA)
      have hMapWrite := TMComponent.mapExit_reachesExit _ (fun _ => (Sum.inl () : Unit ⊕ Unit))
        input bound hWrite
      have hBranch := (initLoopCheck InputAlphabet).branch_reachesExit
        ((writeOneInitReg InputAlphabet).mapExit fun _ => Sum.inl ())
        (TMComponent.atom fun _ scanned => singleTapeAction (.inr ()) tRegs .srcSep .right scanned)
        input bound true hCheck hMapWrite
      left
      refine ⟨_, inHead, hBranch, ?_, ?_⟩
      · refine ⟨rfl, fun j h1 h2 h3 => by simp [h1, h2, h3, hOth j h1 h2 h3],
          by simp; exact hNMA, done + 1, by omega, ?_, by simp [hNeRB.symm, hNeAB.symm]; exact hNMB⟩
        have hListNext : encodeRegsPrefix (List.replicate (1 + done) (false, natToBits W 1)) ++
            encodeRegEntry false (natToBits W 1) =
            encodeRegsPrefix (List.replicate (1 + (done + 1)) (false, natToBits W 1)) := by
          rw [show 1 + (done + 1) = (1 + done) + 1 by omega, List.replicate_succ',
            encodeRegsPrefix_snoc]
        have hMulNext : (1 + (done + 1)) * (W + 2) = (1 + done) * (W + 2) + (W + 2) := by
          rw [show 1 + (done + 1) = (1 + done) + 1 by omega, Nat.add_mul, Nat.one_mul]
        have hHeadNext : (1 + (1 + done) * (W + 2)) + (W + 2) = 1 + (1 + (done + 1)) * (W + 2) := by
          rw [hMulNext]; omega
        rw [hListNext, hPL, hHeadNext] at hNMR
        simpa [hNeRA, hNeRB] using hNMR
      · simp [hNMB.head_eq, hMB.head_eq, hNeRB.symm, hNeAB.symm]; omega
    · have hDoneW : done = W := by omega
      rw [hDoneW] at hMB hMR
      have hReadB : (tapes tArgB).cells (tapes tArgB).head = .endMark := by
        rw [hMB.read_lt (by simp; omega)]
        simp [Nat.add_comm 1 W, List.cons_append]
      have hMoveB : moveOneSidedHead (1 + W) .stay = some (1 + W) := rfl
      obtain ⟨ntB, hUpdB, hNMB⟩ := hMB.update_keep .stay hMoveB
      have hCheck' := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
        (fun _ => initLoopFn) tArgB input bound tapes inHead hHeads
        (by simpa [initLoopFn, hReadB] using hUpdB) (by rw [hNMB.head_eq]; omega)
      have hCheck : (initLoopCheck InputAlphabet).ReachesExit input bound tapes inHead false
          (fun j => if j = tArgB then ntB else tapes j) inHead := by
        simpa [initLoopCheck, initLoopFn, hReadB] using hCheck'
      have hPL : (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1))).length =
          1 + (W + 1) * (W + 2) := by
        have := encodeRegsPrefix_length W (List.replicate (W + 1) (false, natToBits W 1))
          (fun r hr => by rcases List.mem_replicate.mp hr with ⟨_, rfl⟩; simp [natToBits_length])
        simpa using this
      have hMoveR : moveOneSidedHead (1 + (W + 1) * (W + 2)) .right =
          some (1 + (W + 1) * (W + 2) + 1) := by simp [moveOneSidedHead]
      have hMR' : TapeMatches ((fun j => if j = tArgB then ntB else tapes j) tRegs)
          (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1)))
          (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1))).length := by
        simpa [hNeRB, hPL, Nat.add_comm 1 W] using hMR
      obtain ⟨ftR, hUpdR, hFMR⟩ := hMR'.update_append_move rfl .srcSep .right
        (by rw [hPL]; exact hMoveR)
      have hAtomSrc := TMComponent.atom_reachesExit
        (fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          singleTapeAction (Sum.inr () : Unit ⊕ Unit) tRegs .srcSep .right scanned)
        input bound (fun j => if j = tArgB then ntB else tapes j) inHead
        (fun j => by
          by_cases hj : j = tArgB
          · subst hj; simpa [hNMB.head_eq] using by omega
          · simpa [hj] using hHeads j)
        inHead (by simp [singleTapeAction, moveHead])
        (fun j => if j = tRegs then ftR else if j = tArgB then ntB else tapes j)
        (fun j => singleTapeAction_apply (Sum.inr () : Unit ⊕ Unit) tRegs .srcSep .right _
          (by simpa using hUpdR) j)
        (fun j => by
          by_cases h1 : j = tRegs
          · subst h1; simpa [hFMR.head_eq, hPL] using by omega
          · by_cases h2 : j = tArgB
            · subst h2; simpa [h1, hNMB.head_eq] using by omega
            · simpa [h1, h2] using hHeads j)
      have hBranch := (initLoopCheck InputAlphabet).branch_reachesExit
        ((writeOneInitReg InputAlphabet).mapExit fun _ => Sum.inl ())
        (TMComponent.atom fun _ scanned => singleTapeAction (.inr ()) tRegs .srcSep .right scanned)
        input bound false hCheck hAtomSrc
      right
      refine ⟨(), _, inHead, hBranch, rfl,
        fun j h1 h2 h3 => by simp [h1, h3, hOth j h1 h2 h3],
        by simp [hNeRA.symm, hNeAB]; exact hMA,
        by simpa [hNeRB, hPL] using hFMR,
        by simp [hNeRB.symm]; exact hNMB⟩
  have hInitInv : Inv (fun j => if j = tRegs then r₁ else if j = tArgA then a₁ else initTapes j)
      inHead := by
    refine ⟨rfl, fun j h1 h2 _ => by simp [h1, h2], by simp [hNeRA.symm]; exact hMA₁,
      0, by omega, by simpa [hNeRA] using hMR₁', by simp [hNeRB.symm, hNeAB.symm]; exact hMatchB⟩
  obtain ⟨_, midTapes, inMid, hLoopRun, hPost⟩ := TMComponent.loop_reachesExit loopBody
    input bound Inv (fun tapes => W + 1 - (tapes tArgB).head) Post hLoopStep _ inHead hInitInv
  rcases hPost with ⟨hIhMid, hMidOth, hMidMA, hMidMR, hMidMB⟩
  subst inMid
  have hMidHeads : ∀ j, (midTapes j).head < bound j := by
    intro j; by_cases h1 : j = tRegs
    · subst h1; simpa [hMidMR.head_eq] using by omega
    · by_cases h2 : j = tArgA
      · subst h2; simpa [hMidMA.head_eq] using by omega
      · by_cases h3 : j = tArgB
        · subst h3; simpa [hMidMB.head_eq] using by omega
        · rw [hMidOth j h1 h2 h3]; exact hOtherBounds j h1 h2 h3
  have hMidLen : (encodeRegsPrefix (List.replicate (W + 1) (false, natToBits W 1)) ++
      [SimSym.srcSep]).length = 1 + (W + 1) * (W + 2) + 1 := by
    have := encodeRegsPrefix_length W (List.replicate (W + 1) (false, natToBits W 1))
      (fun r hr => by rcases List.mem_replicate.mp hr with ⟨_, rfl⟩; simp [natToBits_length])
    simpa using this
  have hMoveTag : moveOneSidedHead (1 + (W + 1) * (W + 2) + 1) .right =
      some (1 + (W + 1) * (W + 2) + 2) := by simp [moveOneSidedHead]
  obtain ⟨r₂, hUpdTag, hMR₂⟩ := hMidMR.update_append_move (by rw [hMidLen]) (.tag true) .right hMoveTag
  have hAtomTag := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
    (fun _ _ => ((), .tag true, .right)) tRegs input bound midTapes inHead hMidHeads
    (by simpa using hUpdTag) (by rw [hMR₂.head_eq]; omega)
  let cB := SimSym.leftMark :: List.replicate W (SimSym.bit true) ++ [SimSym.endMark]
  have hNoLeftB : ∀ i, 1 ≤ i → i < cB.length → cB[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [cB, List.length_cons, List.length_append, List.length_replicate, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp [cB]; omega)]
      simp only [cB, List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < W
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = W := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  obtain ⟨rewBTapes, hRewB, hFMB₁, hRewBOth⟩ := rewindTape_reachesExit tArgB input bound cB
    (by simp [cB]) rfl hNoLeftB (by simp [cB]; exact hBoundB)
    (fun j => if j = tRegs then r₂ else midTapes j) inHead
    (fun j hj => by
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMR₂.head_eq] using by omega
      · simpa [h1] using hMidHeads j)
    (1 + W) (by omega) (by simp [cB]; omega) (by simpa [cB, hNeRB.symm] using hMidMB)
  have hTapesAfterRew : rewBTapes =
      fun j => if j = tRegs then r₂ else if j = tArgB then rewBTapes tArgB else midTapes j := by
    funext j; by_cases h2 : j = tArgB
    · subst h2; simp [hNeRB.symm]
    · rw [hRewBOth j h2]
      by_cases h1 : j = tRegs <;> simp [h1, h2]
  rw [hTapesAfterRew] at hRewB
  obtain ⟨a₂, hClrA, hMA₂⟩ := clearTape_reachesExit tArgA input bound
    (List.replicate W (.bit true)) (by simp; exact hBoundA)
    (fun s hs => by rcases List.mem_replicate.mp hs with ⟨_, rfl⟩; simp)
    (fun j => if j = tRegs then r₂ else if j = tArgB then rewBTapes tArgB else midTapes j)
    inHead (fun j hj => by
      by_cases h1 : j = tRegs
      · subst h1; simpa [hMR₂.head_eq] using by omega
      · by_cases h2 : j = tArgB
        · subst h2; simpa [h1, hFMB₁.head_eq] using by omega
        · simpa [h1, h2] using hMidHeads j)
    (by simp [hNeRA.symm, hNeAB]; exact hMidMA)
  obtain ⟨b₂, hClrB, hMB₂⟩ := clearTape_reachesExit tArgB input bound
    (List.replicate W (.bit true)) (by simp; exact hBoundB)
    (fun s hs => by rcases List.mem_replicate.mp hs with ⟨_, rfl⟩; simp)
    (fun j => if j = tArgA then a₂ else if j = tRegs then r₂
              else if j = tArgB then rewBTapes tArgB else midTapes j)
    inHead (fun j hj => by
      by_cases h2 : j = tArgA
      · subst h2; simpa [hMA₂.head_eq] using by omega
      · by_cases h1 : j = tRegs
        · subst h1; simpa [h2, hMR₂.head_eq] using by omega
        · simpa [h2, h1, hj] using hMidHeads j)
    (by simp [hNeAB.symm, hNeRB.symm]; exact hFMB₁)
  have hFinalTapesEq : (fun j => if j = tArgB then b₂
      else if j = tArgA then a₂
      else if j = tRegs then r₂
      else if j = tArgB then rewBTapes tArgB else midTapes j) =
      (fun j => if j = tRegs then r₂ else if j = tArgA then a₂
                else if j = tArgB then b₂ else initTapes j) := by
    funext j
    by_cases h1 : j = tRegs
    · subst h1; simp [hNeRA, hNeRB]
    · by_cases h2 : j = tArgA
      · subst h2; simp [hNeAB, h1]
      · by_cases h3 : j = tArgB
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3, hMidOth j h1 h2 h3]
  rw [hFinalTapesEq] at hClrB
  have hSeqClr := (clearTape InputAlphabet tArgA).seq_reachesExit (clearTape InputAlphabet tArgB)
    input bound hClrA hClrB
  have hSeqRewB := (rewindTape InputAlphabet tArgB).seq_reachesExit _ input bound hRewB hSeqClr
  have hSeqTag := TMComponent.seq_reachesExit _ _ input bound hAtomTag hSeqRewB
  have hSeqLoop := TMComponent.seq_reachesExit _ _ input bound hLoopRun hSeqTag
  refine ⟨r₂, a₂, b₂, TMComponent.seq_reachesExit _ _ input bound hFirst hSeqLoop, ?_, hMA₂, hMB₂⟩
  simpa [List.append_assoc] using hMR₂

end SavitchLemma


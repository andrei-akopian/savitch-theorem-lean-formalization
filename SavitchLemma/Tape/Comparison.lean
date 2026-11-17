module

public import SavitchLemma.Tape.BinaryArithmetic

@[expose] public section

/-!
# Tape comparison

Implements bit-tape comparison and fixed-width bit reading.
-/

namespace SavitchLemma

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

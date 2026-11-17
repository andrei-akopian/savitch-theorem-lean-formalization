module

public import SavitchLemma.Simulator.InitRegisters

@[expose] public section

/-!
# Complete simulator initialization

Writes the encoded initial machine configuration and assembles the full D0 component.
-/

namespace SavitchLemma

/-- Write `encodeConfigBits Q Γ (M.initialConfig S hS)` and `[.endMark]` onto `tRegs`,
then rewind `tRegs` to cell `1`. -/
noncomputable def writeInitialSrcBits {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  let startQBits := natToBits (qBits Q) (Fintype.equivFin Q M.startState).val
  let blankSymBits := natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val
  let oneTapeInit :=
    (writeRulerListRegs InputAlphabet [false]).seq (writeRulerListRegs InputAlphabet blankSymBits)
  (writeFixedBits InputAlphabet tRegs startQBits).seq
    ((writeFixedBits InputAlphabet tRegs [false, false]).seq
      ((writeRulerListRegs InputAlphabet [false]).seq
        ((repeatUnit k oneTapeInit).seq
          ((writeFixedBits InputAlphabet tRegs [true, false]).seq
            ((writeEndMarkStayAtom InputAlphabet tRegs).seq (rewindTape InputAlphabet tRegs))))))

/-- Full D0 initialization component: prepares `1^W` templates on `tArgA`/`tArgB`,
builds all `W + 1` working registers initialized to `(false, 1)`, writes the encoded
initial configuration into the `source` register, and leaves `tRegs` at head `1`. -/
noncomputable def initSavitchTapes {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (writeWidthOnes Q Γ k InputAlphabet).seq
    ((initWorkRegsFromTemplate InputAlphabet).seq (writeInitialSrcBits M))

theorem encodeConfigBits_initialConfig {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (S : ℕ) (hS : 0 < S) :
    encodeConfigBits Q Γ (M.initialConfig (n := n) S hS) =
      natToBits (qBits Q) (Fintype.equivFin Q M.startState).val ++
      ([false, false] ++ (List.replicate S [false]).flatten) ++
      ((List.replicate k ((List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten)).flatten) ++
      [true, false] := by
  unfold encodeConfigBits MultitapeNTM.initialConfig
  dsimp only
  have hIn : natToBits (S + 2) 0 = [false, false] ++ (List.replicate S [false]).flatten := by
    have hRepF : (List.replicate S [false]).flatten = List.replicate S false := by
      induction S with
      | zero => rfl
      | succ s _ => simp [List.replicate_succ]
    rw [natToBits_zero, hRepF, Nat.add_comm S 2, List.replicate_add]
    rfl
  have hTape : encodeTapeBits Γ
      (⟨fun _ => M.blank, ⟨0, hS⟩⟩ : BoundedTape Γ S) =
      (List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten := by
    unfold encodeTapeBits
    dsimp only
    have hRepF : (List.replicate S [false]).flatten = List.replicate S false := by
      induction S with
      | zero => rfl
      | succ s _ => simp [List.replicate_succ]
    rw [natToBits_zero, ← hRepF, list_flatMap_finRange_const]
  have hTapes : (List.finRange k).flatMap
      (fun _ : Fin k => encodeTapeBits Γ (⟨fun _ => M.blank, ⟨0, hS⟩⟩ : BoundedTape Γ S)) =
      (List.replicate k ((List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten)).flatten := by
    rw [list_flatMap_finRange_const]
    simp [hTape]
  rw [hIn, hTapes]

theorem writeInitialSrcBits_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (work : List (Bool × List Bool))
    (hWork : ∀ r ∈ work, r.2.length = configBitWidth Q Γ k S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : 1 + work.length * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tRegs → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs)
      (encodeRegsPrefix work ++ [.srcSep, .tag true])
      (1 + work.length * (configBitWidth Q Γ k S + 2) + 2)) :
    ∃ ftR ftReg,
      (writeInitialSrcBits M).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg
        (encodeRegsTape work (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)))) 1 := by
  have hNeRR : tRuler ≠ tRegs := by decide
  let W := configBitWidth Q Γ k S
  let srcPref := encodeRegsPrefix work ++ [SimSym.srcSep, SimSym.tag true]
  have hPL : (encodeRegsPrefix work).length = 1 + work.length * (W + 2) :=
    encodeRegsPrefix_length W work hWork
  have hSrcPrefLen : srcPref.length = 1 + work.length * (W + 2) + 2 := by
    simp [srcPref, hPL]
  have hWVal : W = qBits Q + (S + 2) + k * (S + S * gammaBits Γ) + 2 := rfl
  have hBoundReg' :
      1 + work.length * (W + 2) + (qBits Q + (S + 2) + k * (S + S * gammaBits Γ) + 5) ≤
        bound tRegs := by
    simpa [W, configBitWidth, tapeBitWidth] using hBoundReg
  let startQBits := natToBits (qBits Q) (Fintype.equivFin Q M.startState).val
  let blankSymBits := natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val
  have hQBLen : startQBits.length = qBits Q := natToBits_length _ _
  have hBBLen : blankSymBits.length = gammaBits Γ := natToBits_length _ _
  have hMReg' : TapeMatches (initTapes tRegs) srcPref srcPref.length := by
    rw [hSrcPrefLen]; exact hMatchReg
  obtain ⟨rg₁, hStep1, hMG₁⟩ := writeFixedBits_reachesExit tRegs startQBits input bound srcPref
    (by rw [hSrcPrefLen, hQBLen]; omega)
    initTapes inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hMatchR.head_eq] using by omega
      · exact hOtherBounds j h1 hj)
    hMReg'
  let t₁ := fun j => if j = tRegs then rg₁ else initTapes j
  let p₁ := srcPref ++ startQBits.map SimSym.bit
  have hP1Len : p₁.length = 1 + work.length * (W + 2) + 2 + qBits Q := by
    simp [p₁, hSrcPrefLen, hQBLen]
  obtain ⟨rg₂, hStep2, hMG₂⟩ := writeFixedBits_reachesExit tRegs [false, false] input bound p₁
    (by rw [hP1Len]; simp; omega)
    t₁ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₁, hNeRR, hMatchR.head_eq] using by omega
      · simpa [t₁, hj] using hOtherBounds j h1 hj)
    (by rw [hP1Len]; simpa [t₁, p₁, hSrcPrefLen, hQBLen, Nat.add_assoc] using hMG₁)
  let t₂ := fun j => if j = tRegs then rg₂ else t₁ j
  let p₂ := p₁ ++ ([false, false] : List Bool).map SimSym.bit
  have hP2Len : p₂.length = 1 + work.length * (W + 2) + 2 + qBits Q + 2 := by
    simp [p₂, hP1Len]
  obtain ⟨ru₃, rg₃, hStep3, hMR₃, hMG₃⟩ := writeRulerListRegs_reachesExit [false] input bound S p₂
    hBoundR (by rw [hP2Len]; simp; omega)
    t₂ inHead (fun j hj1 hj2 => by
      simp [t₂, t₁, hj2, hOtherBounds j hj1 hj2])
    (by simpa [t₂, t₁, hNeRR] using hMatchR)
    (by rw [hP2Len]; simpa [t₂, p₂, hP1Len] using hMG₂)
  let t₃ := fun j => if j = tRuler then ru₃ else if j = tRegs then rg₃ else t₂ j
  let p₃ := p₂ ++ ((List.replicate S ([false] : List Bool)).flatten).map SimSym.bit
  have hRepF1 : ((List.replicate S ([false] : List Bool)).flatten).length = S := by
    induction S with
    | zero => simp
    | succ s _ => simp [List.replicate_succ]
  have hP3Len : p₃.length = 1 + work.length * (W + 2) + 2 + qBits Q + (S + 2) := by
    simp [p₃, hP2Len]
    omega
  let oneTapeInit :=
    (writeRulerListRegs InputAlphabet [false]).seq (writeRulerListRegs InputAlphabet blankSymBits)
  let oneTapeBits : List Bool :=
    (List.replicate S [false]).flatten ++ (List.replicate S blankSymBits).flatten
  have hOneLen : oneTapeBits.length = S + S * gammaBits Γ := by
    have hRepB : ((List.replicate S blankSymBits).flatten).length = S * gammaBits Γ := by
      induction S with
      | zero => simp
      | succ s _ => simp [List.replicate_succ, hBBLen, Nat.succ_mul, Nat.add_comm]
    simp only [oneTapeBits, List.length_append, hRepF1, hRepB]
  let LoopInv : ℕ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun idx tapes ih =>
    idx ≤ k ∧
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
    TapeMatches (tapes tRegs)
      (p₃ ++ ((List.replicate idx oneTapeBits).flatten).map SimSym.bit)
      (p₃.length + idx * oneTapeBits.length)
  have hLoopStep : ∀ i, i < k → ∀ tapes ih, LoopInv i tapes ih →
      ∃ tapes' ih',
        oneTapeInit.ReachesExit input bound tapes ih () tapes' ih' ∧ LoopInv (i + 1) tapes' ih' := by
    intro i hiK tapes ih ⟨_, hIh, hOth, htR, htReg⟩
    subst ih
    have hFlatOneLen : ((List.replicate i oneTapeBits).flatten).length = i * oneTapeBits.length := by
      induction i with
      | zero => simp
      | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
    let curP := p₃ ++ ((List.replicate i oneTapeBits).flatten).map SimSym.bit
    have hCurPLen : curP.length = p₃.length + i * oneTapeBits.length := by
      simp [curP]
    have hMulLe : (i + 1) * (S + S * gammaBits Γ) ≤ k * (S + S * gammaBits Γ) :=
      Nat.mul_le_mul_right _ hiK
    have hBoundA : curP.length + S * ([false] : List Bool).length < bound tRegs := by
      rw [hCurPLen, hP3Len, hOneLen]
      simp only [List.length_singleton, Nat.mul_one]
      have hSub : i * (S + S * gammaBits Γ) + S ≤ k * (S + S * gammaBits Γ) := by
        rw [Nat.succ_mul] at hMulLe
        omega
      omega
    obtain ⟨ruA, rgA, hRunA, hMR_A, hMG_A⟩ := writeRulerListRegs_reachesExit [false] input bound S
      curP hBoundR hBoundA tapes inHead (fun j h1 h2 => by
        rw [hOth j h1 h2]; exact hOtherBounds j h1 h2)
      htR (by rw [hCurPLen]; exact htReg)
    let mTapes := fun j => if j = tRuler then ruA else if j = tRegs then rgA else tapes j
    let curP2 := curP ++ ((List.replicate S ([false] : List Bool)).flatten).map SimSym.bit
    have hCurP2Len : curP2.length = curP.length + S := by
      simp [curP2]
    have hBoundB : curP2.length + S * blankSymBits.length < bound tRegs := by
      rw [hCurP2Len, hCurPLen, hP3Len, hOneLen, hBBLen]
      have hSub : i * (S + S * gammaBits Γ) + (S + S * gammaBits Γ) ≤ k * (S + S * gammaBits Γ) := by
        rw [← Nat.succ_mul]; exact hMulLe
      omega
    obtain ⟨ruB, rgB, hRunB, hMR_B, hMG_B⟩ := writeRulerListRegs_reachesExit blankSymBits input bound S
      curP2 hBoundR hBoundB mTapes inHead (fun j h1 h2 => by
        simp [mTapes, h1, h2, hOth j h1 h2, hOtherBounds j h1 h2])
      (by simpa [mTapes] using hMR_A)
      (by
        rw [hCurP2Len]
        simpa [mTapes, hNeRR.symm, curP2] using hMG_A)
    let fTapes := fun j => if j = tRuler then ruB else if j = tRegs then rgB else mTapes j
    refine ⟨fTapes, inHead,
      (writeRulerListRegs InputAlphabet [false]).seq_reachesExit
        (writeRulerListRegs InputAlphabet blankSymBits) input bound hRunA hRunB,
      hiK, rfl, fun j h1 h2 => by simp [fTapes, mTapes, h1, h2, hOth j h1 h2],
      by simpa [fTapes] using hMR_B, ?_⟩
    have hLenFinal : p₃.length + (i + 1) * oneTapeBits.length = curP2.length + S * blankSymBits.length := by
      rw [hCurP2Len, hCurPLen, Nat.succ_mul, hOneLen, hBBLen]; omega
    have hTapeFinal :
        curP2 ++ ((List.replicate S blankSymBits).flatten).map SimSym.bit =
          p₃ ++ ((List.replicate (i + 1) oneTapeBits).flatten).map SimSym.bit := by
      simp only [curP2, curP, oneTapeBits, List.replicate_succ', List.flatten_concat,
        List.map_append, List.append_assoc]
    rw [hLenFinal, ← hTapeFinal]
    simpa [fTapes, mTapes, hNeRR.symm] using hMG_B
  have hInitLoop : LoopInv 0 t₃ inHead := by
    refine ⟨Nat.zero_le k, rfl, fun j h1 h2 => by simp [t₃, t₂, t₁, h1, h2],
      by simpa [t₃] using hMR₃, ?_⟩
    have hEqPos : 1 + work.length * (W + 2) + 2 + qBits Q + 2 + S = p₃.length := by
      rw [hP3Len]; omega
    rw [← hEqPos]
    simpa [t₃, hNeRR.symm, p₃, hP2Len, hRepF1] using hMG₃
  obtain ⟨t₄, ih₄, hLoopRun, _, hIh4, hOth4, hMR4, hMG4⟩ :=
    repeatUnit_reachesExit k oneTapeInit input bound LoopInv hLoopStep t₃ inHead hInitLoop
      (fun j => by
        by_cases h1 : j = tRuler
        · subst h1; simpa [t₃, hMR₃.head_eq] using by omega
        · by_cases h2 : j = tRegs
          · subst h2
            simp only [t₃, h1, ↓reduceIte]
            rw [hMG₃.head_eq, hP2Len]
            simp; omega
          · simp [t₃, t₂, t₁, h1, h2, hOtherBounds j h1 h2])
  subst ih₄
  let p₄ := p₃ ++ ((List.replicate k oneTapeBits).flatten).map SimSym.bit
  have hFlatKLen : ((List.replicate k oneTapeBits).flatten).length = k * oneTapeBits.length := by
    induction k with
    | zero => simp
    | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
  have hP4Len : p₄.length = 1 + work.length * (W + 2) + 2 + qBits Q + (S + 2) + k * oneTapeBits.length := by
    simp [p₄, hP3Len]
  obtain ⟨rg₅, hStep5, hMG₅⟩ := writeFixedBits_reachesExit tRegs [true, false] input bound p₄
    (by rw [hP4Len, hOneLen]; simp; omega)
    t₄ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hMR4.head_eq] using by omega
      · rw [hOth4 j h1 hj]; exact hOtherBounds j h1 hj)
    (by rw [hP4Len]; simpa [p₄, hP3Len] using hMG4)
  let t₅ := fun j => if j = tRegs then rg₅ else t₄ j
  let p₅ := p₄ ++ ([true, false] : List Bool).map SimSym.bit
  have hP5Len : p₅.length = 1 + work.length * (W + 2) + (W + 2) := by
    simp [p₅, hP4Len, hOneLen, hWVal]; omega
  have hP4Add2 : p₄.length + 2 = 1 + work.length * (W + 2) + (W + 2) := by
    rw [hP4Len, hOneLen, hWVal]; omega
  obtain ⟨rg₆, hStep6, hMG₆⟩ := writeEndMarkStayAtom_reachesExit tRegs input bound p₅
    (by rw [hP5Len]; omega) t₅ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₅, hNeRR, hMR4.head_eq] using by omega
      · simp [t₅, hj, hOth4 j h1 hj, hOtherBounds j h1 hj])
    (by rw [hP5Len, ← hP4Add2]; simpa [t₅, p₅, hP4Len] using hMG₅)
  let t₆ := fun j => if j = tRegs then rg₆ else t₅ j
  let cfgBits := encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega))
  have hFullTape : p₅ ++ [.endMark] = encodeRegsTape work cfgBits := by
    have hCfgMap : List.map SimSym.bit cfgBits =
        List.map SimSym.bit startQBits ++ List.map SimSym.bit [false, false] ++
        List.map SimSym.bit (List.replicate S [false]).flatten ++
        List.map SimSym.bit (List.replicate k oneTapeBits).flatten ++
        List.map SimSym.bit [true, false] := by
      simp only [cfgBits, encodeConfigBits_initialConfig M S (by omega), startQBits,
        blankSymBits, oneTapeBits, List.map_append, List.append_assoc]
    simp only [p₅, p₄, p₃, p₂, p₁, srcPref, encodeRegsTape, encodeSrcEntry, hCfgMap,
      List.append_assoc, List.cons_append, List.nil_append]
  have hMG₆' : TapeMatches (t₆ tRegs) (encodeRegsTape work cfgBits)
      (1 + work.length * (W + 2) + (W + 2)) := by
    simpa [t₆, hFullTape, hP5Len] using hMG₆
  have hCfgLen : cfgBits.length = W := encodeConfigBits_length Q Γ _
  have hFullLen : (encodeRegsTape work cfgBits).length = 1 + work.length * (W + 2) + (W + 3) :=
    encodeRegsTape_length W work cfgBits hWork hCfgLen
  obtain ⟨rewTapes, hStep7, hMG₇, hRewOth⟩ := rewindTape_reachesExit tRegs input bound
    (encodeRegsTape work cfgBits) (by rw [hFullLen]; omega)
    (encodeRegsTape_head_leftMark work cfgBits)
    (encodeRegsTape_no_other_leftMark work cfgBits)
    (by rw [hFullLen]; exact hBoundReg) t₆ inHead
    (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₆, t₅, hNeRR, hMR4.head_eq] using by omega
      · simp [t₆, t₅, hj, hOth4 j h1 hj, hOtherBounds j h1 hj])
    (1 + work.length * (W + 2) + (W + 2)) (by omega) (by rw [hFullLen]; omega) hMG₆'
  have hSeq67 := (writeEndMarkStayAtom InputAlphabet tRegs).seq_reachesExit (rewindTape InputAlphabet tRegs)
    input bound hStep6 hStep7
  have hSeq5 := (writeFixedBits InputAlphabet tRegs [true, false]).seq_reachesExit _ input bound hStep5 hSeq67
  have hSeq4 := (repeatUnit k oneTapeInit).seq_reachesExit _ input bound hLoopRun hSeq5
  have hSeq3 := (writeRulerListRegs InputAlphabet [false]).seq_reachesExit _ input bound hStep3 hSeq4
  have hSeq2 := (writeFixedBits InputAlphabet tRegs [false, false]).seq_reachesExit _ input bound hStep2 hSeq3
  have hSeq1 := (writeFixedBits InputAlphabet tRegs startQBits).seq_reachesExit _ input bound hStep1 hSeq2
  have hFinalEq : rewTapes = fun j => if j = tRuler then t₄ tRuler
      else if j = tRegs then rewTapes tRegs else initTapes j := by
    funext j
    by_cases h2 : j = tRegs
    · subst h2; simp [hNeRR.symm]
    · rw [hRewOth j h2]
      by_cases h1 : j = tRuler
      · subst h1; simp [t₆, t₅, h2]
      · simp [t₆, t₅, h1, h2, hOth4 j h1 h2]
  rw [hFinalEq] at hSeq1
  exact ⟨t₄ tRuler, rewTapes tRegs, hSeq1, hMR4, hMG₇⟩

theorem initSavitchTapes_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundS : (initTapes tScratch).head < bound tScratch)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs) [.leftMark] 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1) :
    ∃ ftR ftReg ftA ftB,
      (initSavitchTapes M).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg
                  else if j = tArgA then ftA else if j = tArgB then ftB
                  else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg
        (zdRegsContents (configBitWidth Q Γ k S)
          (zdInitial (configBitWidth Q Γ k S + 1) (2 ^ configBitWidth Q Γ k S - 1)
            (configBitWidth_gt_one_pow Q Γ k S)
            (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega))))) 1 ∧
      TapeMatches ftA [.leftMark] 1 ∧
      TapeMatches ftB [.leftMark] 1 := by
  have hNeRR : tRuler ≠ tRegs := by decide
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeRS : tRuler ≠ tScratch := by decide
  have hNeRegA : tRegs ≠ tArgA := by decide
  have hNeRegB : tRegs ≠ tArgB := by decide
  have hNeRegS : tRegs ≠ tScratch := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  have hNeAS : tArgA ≠ tScratch := by decide
  have hNeBS : tArgB ≠ tScratch := by decide
  let W := configBitWidth Q Γ k S
  obtain ⟨r₁, a₁, b₁, hWOnes, hMR₁, hMA₁, hMB₁⟩ := writeWidthOnes_reachesExit Q Γ k input bound S
    hBoundR hBoundA hBoundB initTapes inHead (fun j hj1 hj2 hj3 => by
      by_cases hReg : j = tRegs
      · subst hReg; simpa [hMatchReg.head_eq] using by omega
      · have hjS : j = tScratch := by
          match j with
          | ⟨0, _⟩ => exact (hj1 rfl).elim
          | ⟨1, _⟩ => exact (hReg rfl).elim
          | ⟨2, _⟩ => exact (hj2 rfl).elim
          | ⟨3, _⟩ => exact (hj3 rfl).elim
          | ⟨4, _⟩ => rfl
        subst hjS; exact hBoundS)
    hMatchR hMatchA hMatchB
  let t₁ := fun j => if j = tRuler then r₁ else if j = tArgA then a₁
      else if j = tArgB then b₁ else initTapes j
  have hWGe1 : 1 ≤ W := by
    have := configBitWidth_ge_two Q Γ k S; omega
  obtain ⟨reg₂, a₂, b₂, hInitWork, hMReg₂, hMA₂, hMB₂⟩ := initWorkRegsFromTemplate_reachesExit
    input bound W hWGe1 t₁ inHead (by unfold W; omega) hBoundA hBoundB
    (fun j h1 h2 h3 => by
      by_cases hR : j = tRuler
      · subst hR; simpa [t₁, hMR₁.head_eq] using by omega
      · have hjS : j = tScratch := by
          match j with
          | ⟨0, _⟩ => exact (hR rfl).elim
          | ⟨1, _⟩ => exact (h1 rfl).elim
          | ⟨2, _⟩ => exact (h2 rfl).elim
          | ⟨3, _⟩ => exact (h3 rfl).elim
          | ⟨4, _⟩ => rfl
        subst hjS; simpa [t₁, hNeRS.symm, hNeAS.symm, hNeBS.symm] using hBoundS)
    (by simpa [t₁, hNeRR.symm, hNeRegA, hNeRegB] using hMatchReg)
    (by simpa [t₁, hNeRA.symm] using hMA₁)
    (by simpa [t₁, hNeRB.symm, hNeAB.symm] using hMB₁)
  let t₂ := fun j => if j = tRegs then reg₂ else if j = tArgA then a₂
      else if j = tArgB then b₂ else t₁ j
  let workInit := List.replicate (W + 1) (false, natToBits W 1)
  have hWorkInitLen : ∀ r ∈ workInit, r.2.length = W := by
    intro r hr; rcases List.mem_replicate.mp hr with ⟨_, rfl⟩; simp [natToBits_length]
  have hPLInit : (encodeRegsPrefix workInit).length = 1 + (W + 1) * (W + 2) := by
    simpa [workInit] using encodeRegsPrefix_length W workInit hWorkInitLen
  have hMReg₂' : TapeMatches (t₂ tRegs) (encodeRegsPrefix workInit ++ [.srcSep, .tag true])
      (1 + workInit.length * (W + 2) + 2) := by
    simpa [t₂, workInit, List.length_replicate, hPLInit] using hMReg₂
  obtain ⟨r₃, reg₃, hInitSrc, hMR₃, hMReg₃⟩ := writeInitialSrcBits_reachesExit M input bound S hS
    workInit hWorkInitLen hBoundR (by simpa [workInit] using hBoundReg) t₂ inHead
    (fun j h1 h2 => by
      by_cases hA : j = tArgA
      · subst hA; simpa [t₂, hNeRegA.symm, hMA₂.head_eq] using by omega
      · by_cases hB : j = tArgB
        · subst hB; simpa [t₂, hNeRegB.symm, hNeAB.symm, hMB₂.head_eq] using by omega
        · have hjS : j = tScratch := by
            match j with
            | ⟨0, _⟩ => exact (h1 rfl).elim
            | ⟨1, _⟩ => exact (h2 rfl).elim
            | ⟨2, _⟩ => exact (hA rfl).elim
            | ⟨3, _⟩ => exact (hB rfl).elim
            | ⟨4, _⟩ => rfl
          subst hjS
          simpa [t₂, t₁, hNeRegS.symm, hNeAS.symm, hNeBS.symm, hNeRS.symm] using hBoundS)
    (by simpa [t₂, t₁, hNeRR, hNeRA, hNeRB] using hMR₁)
    hMReg₂'
  have hSeq23 := (initWorkRegsFromTemplate InputAlphabet).seq_reachesExit
    (writeInitialSrcBits M) input bound hInitWork hInitSrc
  have hSeq123 := (writeWidthOnes Q Γ k InputAlphabet).seq_reachesExit _ input bound hWOnes hSeq23
  have hZDInitEq : encodeZDRegs W
      (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) = workInit := by
    apply List.ext_getElem
    · simp [encodeZDRegs, workInit]
    · intro i hi1 hi2
      simp only [encodeZDRegs, List.getElem_ofFn, zdInitial, firstCode, workInit,
        List.getElem_replicate]
      have hNe : i ≠ W + 1 := by simp [workInit] at hi2; omega
      simp [hNe]
  have hZDSrcEq : encodeZDSrc W
      (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) =
      encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)) := by
    simp only [encodeZDSrc, zdInitial, Fin.val_last, ↓reduceIte, bitEncodeConfig]
    have hId := natToBits_bitsToNat (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)))
    rwa [encodeConfigBits_length] at hId
  have hFullZD : encodeRegsTape workInit (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega))) =
      zdRegsContents W (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) := by
    unfold zdRegsContents
    rw [hZDInitEq, hZDSrcEq]
  rw [hFullZD] at hMReg₃
  have hFinalEq : (fun j => if j = tRuler then r₃ else if j = tRegs then reg₃ else t₂ j) =
      fun j => if j = tRuler then r₃ else if j = tRegs then reg₃
        else if j = tArgA then a₂ else if j = tArgB then b₂ else initTapes j := by
    funext j
    match j with
    | ⟨0, _⟩ => simp [tRuler]
    | ⟨1, _⟩ => simp [tRuler, tRegs]
    | ⟨2, _⟩ => simp [tRuler, tRegs, tArgA, t₂, t₁]
    | ⟨3, _⟩ => simp [tRuler, tRegs, tArgA, tArgB, t₂, t₁]
    | ⟨4, _⟩ => simp [tRuler, tRegs, tArgA, tArgB, t₂, t₁]
  rw [hFinalEq] at hSeq123
  exact ⟨r₃, reg₃, a₂, b₂, hSeq123, hMR₃, hMReg₃, hMA₂, hMB₂⟩

end SavitchLemma

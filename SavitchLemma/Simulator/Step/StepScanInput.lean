module

public import SavitchLemma.Simulator.Step.StepChecker

@[expose] public section

/-!
# Serialized configuration cell scanner

Implements the control-state decoder, physical input-head positioning and
reading, and per-tape cell scanner (`scanTapeCells`) for `StepScanner`.
-/

namespace SavitchLemma

instance {InputAlphabet : Type*} [Fintype InputAlphabet] :
    Fintype (InputSymbol InputAlphabet) :=
  Fintype.ofEquiv (Unit ⊕ InputAlphabet ⊕ Unit)
    { toFun := fun
        | .inl () => .leftEnd
        | .inr (.inl a) => .symbol a
        | .inr (.inr ()) => .rightEnd
      invFun := fun
        | .leftEnd => .inl ()
        | .symbol a => .inr (.inl a)
        | .rightEnd => .inr (.inr ())
      left_inv := fun x => by rcases x with ⟨⟩ | a | ⟨⟩ <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-! ## 1. Control-state decoder -/

/-- Decode a pair of `qBits Q`-bit vectors into `Option (Q × Q)`. -/
noncomputable def decodeControlPair (Q : Type*) [Fintype Q] :
    Option ((Fin (qBits Q) → Bool) × (Fin (qBits Q) → Bool)) → Option (Q × Q)
  | none => none
  | some (fA, fB) =>
    match decodeBitsOpt (qBits Q) Q fA, decodeBitsOpt (qBits Q) Q fB with
    | some qA, some qB => some (qA, qB)
    | _, _ => none

/-- Read `qBits Q` bits from `tArgA` and `tArgB` and decode both control states. -/
noncomputable def readControlStates (Q InputAlphabet : Type*) [Fintype Q] :=
  (readFixedBits InputAlphabet (qBits Q) tArgA tArgB).mapExit (decodeControlPair Q)

theorem readControlStates_reachesExit {Q InputAlphabet : Type*} {n : ℕ} [Fintype Q]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (qA qB : Q) (prefA sufA prefB sufB : List SimSym)
    (hBoundA : prefA.length + qBits Q < bound tArgA)
    (hBoundB : prefB.length + qBits Q < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchA : TapeMatches (initTapes tArgA)
      (prefA ++ (natToBits (qBits Q) (Fintype.equivFin Q qA).val).map SimSym.bit ++ sufA)
      prefA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (prefB ++ (natToBits (qBits Q) (Fintype.equivFin Q qB).val).map SimSym.bit ++ sufB)
      prefB.length) :
    ∃ ftA ftB,
      (readControlStates Q InputAlphabet).ReachesExit input bound initTapes inHead
        (some (qA, qB))
        (fun j => if j = tArgA then ftA else if j = tArgB then ftB else initTapes j)
        inHead ∧
      TapeMatches ftA
        (prefA ++ (natToBits (qBits Q) (Fintype.equivFin Q qA).val).map SimSym.bit ++ sufA)
        (prefA.length + qBits Q) ∧
      TapeMatches ftB
        (prefB ++ (natToBits (qBits Q) (Fintype.equivFin Q qB).val).map SimSym.bit ++ sufB)
        (prefB.length + qBits Q) := by
  let sA := natToBits (qBits Q) (Fintype.equivFin Q qA).val
  let sB := natToBits (qBits Q) (Fintype.equivFin Q qB).val
  have hNeAB : tArgA ≠ tArgB := by decide
  obtain ⟨ftA, ftB, hRead, hFA, hFB, _, _⟩ :=
    readFixedBits_reachesExit (qBits Q) tArgA tArgB hNeAB input bound prefA sufA prefB sufB
      sA sB (natToBits_length _ _) (natToBits_length _ _) hBoundA hBoundB initTapes inHead
      hOtherBounds hMatchA hMatchB
  have hPow : Fintype.card Q + 1 ≤ 2 ^ qBits Q :=
    Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card Q + 1)
  let fA : Fin (qBits Q) → Bool := fun i => sA[i.val]'(by rw [natToBits_length]; exact i.isLt)
  let fB : Fin (qBits Q) → Bool := fun i => sB[i.val]'(by rw [natToBits_length]; exact i.isLt)
  have hListA : List.ofFn fA = sA := List.ext_getElem
    (by simp [sA, natToBits_length]) (fun i h1 _ => by simp [fA])
  have hListB : List.ofFn fB = sB := List.ext_getElem
    (by simp [sB, natToBits_length]) (fun i h1 _ => by simp [fB])
  have hDecA : decodeBitsOpt (qBits Q) Q fA = some qA :=
    (decodeBitsOpt_eq_some_iff hPow fA qA).mpr hListA.symm
  have hDecB : decodeBitsOpt (qBits Q) Q fB = some qB :=
    (decodeBitsOpt_eq_some_iff hPow fB qB).mpr hListB.symm
  have hMapped := TMComponent.mapExit_reachesExit
    (readFixedBits InputAlphabet (qBits Q) tArgA tArgB) (decodeControlPair Q) input bound hRead
  have hSliceA : (fun i : Fin (qBits Q) => sA[i.val]'(by rw [natToBits_length]; exact i.isLt)) = fA := rfl
  have hSliceB : (fun i : Fin (qBits Q) => sB[i.val]'(by rw [natToBits_length]; exact i.isLt)) = fB := rfl
  refine ⟨ftA, ftB, ?_, hFA, hFB⟩
  simpa [readControlStates, decodeControlPair, sA, sB, hSliceA, hSliceB, hDecA, hDecB] using hMapped

/-! ## 2. Physical input-head positioning and reading -/

/-- One iteration of positioning the physical input head using `tScratch`:
decrement `tScratch`, and if nonzero move the input head right; if zero,
return the scanned input symbol. -/
def seekInputHeadStep (InputAlphabet : Type*) :
    TMComponent (DecState ⊕ (Bool × Unit)) InputAlphabet SimSym 5
      (Unit ⊕ InputSymbol InputAlphabet) :=
  bindComponent (decScratch InputAlphabet tScratch) fun b =>
    if b then
      TMComponent.atom fun _ scanned =>
        TMAction.mk (Sum.inl ()) .right scanned (fun _ => .stay)
    else
      TMComponent.atom fun inSym scanned =>
        TMAction.mk (Sum.inr inSym) .stay scanned (fun _ => .stay)

/-- Advance the physical input head by the number stored on `tScratch`, then
return the scanned `InputSymbol`. -/
def seekInputHeadAndRead (InputAlphabet : Type*) :=
  loopWithState () (fun _ => seekInputHeadStep InputAlphabet)

theorem seekInputHeadAndRead_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) (target : Fin (n + 2))
    (hBoundS : (S + 2) + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym)
    (hOtherBounds : ∀ j, j ≠ tScratch → (initTapes j).head < bound j)
    (hMatchS : TapeMatches (initTapes tScratch)
      (.leftMark :: (natToBits (S + 2) target.val).map SimSym.bit ++ [.endMark]) 1) :
    ∃ finalTapes,
      (seekInputHeadAndRead InputAlphabet).ReachesExit input bound initTapes ⟨0, by omega⟩
        (readInput input target) finalTapes target ∧
      TapeMatches (finalTapes tScratch)
        (.leftMark :: (List.replicate (S + 2) false).map SimSym.bit ++ [.endMark]) 1 ∧
      (∀ j, j ≠ tScratch → finalTapes j = initTapes j) := by
  let Inv : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      ∃ bits : List Bool,
        bits.length = S + 2 ∧
        curInHead.val + bitsToNat bits = target.val ∧
        TapeMatches (tapes tScratch) (.leftMark :: bits.map SimSym.bit ++ [.endMark]) 1 ∧
        (∀ j, j ≠ tScratch → tapes j = initTapes j)
  let measure : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ _ curInHead => target.val - curInHead.val
  let Post : InputSymbol InputAlphabet → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun sym tapes curInHead =>
      sym = readInput input target ∧
      curInHead = target ∧
      TapeMatches (tapes tScratch)
        (.leftMark :: (List.replicate (S + 2) false).map SimSym.bit ++ [.endMark]) 1 ∧
      (∀ j, j ≠ tScratch → tapes j = initTapes j)
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (seekInputHeadStep InputAlphabet).ReachesExit input bound tapes curInHead
          (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (seekInputHeadStep InputAlphabet).ReachesExit input bound tapes curInHead
          (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟩ tapes curInHead ⟨bits, hLen, hSum, hMS, hOthers⟩
    have hBoundsCur : ∀ j, j ≠ tScratch → (tapes j).head < bound j := by
      intro j hj
      rw [hOthers j hj]
      exact hOtherBounds j hj
    obtain ⟨res, ftS, bits', hLen', hDec, hMS', hHasTrue, hDecVal, hEqBits⟩ :=
      decScratch_reachesExit tScratch input bound bits (by rw [hLen]; exact hBoundS)
        tapes curInHead hBoundsCur hMS
    let midTapes := fun j => if j = tScratch then ftS else tapes j
    have hMidBounds : ∀ j, (midTapes j).head < bound j := by
      intro j
      by_cases hj : j = tScratch
      · subst hj; simpa [midTapes, hMS'.head_eq] using (by omega : 1 < bound tScratch)
      · simp only [midTapes, hj, ↓reduceIte]
        exact hBoundsCur j hj
    cases res with
    | true =>
      left
      have hPosBits : 0 < bitsToNat bits := (true_mem_iff_bitsToNat_pos bits).mp (hHasTrue.mp rfl)
      have hDecEq := hDecVal rfl
      have hNextLt : curInHead.val + 1 < n + 2 := by
        have := target.isLt
        omega
      let nextInHead : Fin (n + 2) := ⟨curInHead.val + 1, hNextLt⟩
      have hAtom :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            TMAction.mk (Sum.inl () : Unit ⊕ InputSymbol InputAlphabet)
              TapeMove.right scanned (fun _ => TapeMove.stay)).ReachesExit
            input bound midTapes curInHead (.inl ()) midTapes nextInHead := by
        apply TMComponent.atom_reachesExit _ input bound midTapes curInHead hMidBounds nextInHead
        · simp [moveHead, hNextLt, nextInHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (midTapes j)
        · exact hMidBounds
      have hBind := bindComponent_reachesExit (decScratch InputAlphabet tScratch)
        (fun b => if b then
          TMComponent.atom fun _ scanned =>
            TMAction.mk (Sum.inl ()) .right scanned (fun _ => .stay)
          else
          TMComponent.atom fun inSym scanned =>
            TMAction.mk (Sum.inr inSym) .stay scanned (fun _ => .stay))
        input bound hDec (by simpa using hAtom)
      refine ⟨(), midTapes, nextInHead, hBind, ⟨bits', hLen'.trans hLen, ?_, ?_, ?_⟩, ?_⟩
      · simp only [nextInHead]; omega
      · simpa [midTapes] using hMS'
      · intro j hj
        simp only [midTapes, hj, ↓reduceIte]
        exact hOthers j hj
      · simp only [measure, nextInHead]; omega
    | false =>
      right
      have hZero : bitsToNat bits = 0 :=
        (true_not_mem_iff_bitsToNat_zero bits).mp (fun h => by
          have hFalse := hHasTrue.mpr h
          cases hFalse)
      have hCurEq : curInHead = target := Fin.ext (by omega)
      subst curInHead
      have hBitsEq : bits' = bits := hEqBits rfl
      have hAllFalse : bits' = List.replicate (S + 2) false := by
        have hId := natToBits_bitsToNat bits
        rw [hZero, natToBits_zero, hLen] at hId
        rw [hBitsEq]
        exact hId.symm
      have hAtom :
          (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            TMAction.mk (Sum.inr inSym : Unit ⊕ InputSymbol InputAlphabet)
              TapeMove.stay scanned (fun _ => TapeMove.stay)).ReachesExit
            input bound midTapes target (.inr (readInput input target)) midTapes target := by
        apply TMComponent.atom_reachesExit _ input bound midTapes target hMidBounds target
        · simp [moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (midTapes j)
        · exact hMidBounds
      have hBind := bindComponent_reachesExit (decScratch InputAlphabet tScratch)
        (fun b => if b then
          TMComponent.atom fun _ scanned =>
            TMAction.mk (Sum.inl ()) .right scanned (fun _ => .stay)
          else
          TMComponent.atom fun inSym scanned =>
            TMAction.mk (Sum.inr inSym) .stay scanned (fun _ => .stay))
        input bound hDec (by simpa using hAtom)
      refine ⟨readInput input target, midTapes, target, hBind, rfl, rfl, ?_, ?_⟩
      · simpa [midTapes, hAllFalse] using hMS'
      · intro j hj
        simp only [midTapes, hj, ↓reduceIte]
        exact hOthers j hj
  have hInitInv : Inv () initTapes ⟨0, by omega⟩ := by
    refine ⟨natToBits (S + 2) target.val, natToBits_length _ _, ?_, hMatchS, fun _ _ => rfl⟩
    have h2S : 2 ≤ 2 ^ S := by
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide : 0 < 2) hS
    have hTargetLt : target.val < 2 ^ (S + 2) := by
      have h1 : target.val < n + 2 := target.isLt
      have h2 : n + 2 ≤ 2 ^ (S + 1) := by
        rw [pow_succ']
        omega
      have h3 : 2 ^ (S + 1) ≤ 2 ^ (S + 2) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      omega
    simp [bitsToNat_natToBits_of_lt hTargetLt]
  obtain ⟨sym, finalTapes, finalInHead, hRun, hSym, hHead, hMS, hOthers⟩ :=
    loopWithState_reachesExit () (fun _ => seekInputHeadStep InputAlphabet) input bound
      Inv measure Post hStep initTapes ⟨0, by omega⟩ hInitInv
  subst sym
  subst finalInHead
  exact ⟨finalTapes, hRun, hMS, hOthers⟩

/-- Read the `(S + 2)`-bit input head block from `tArgA` and `tArgB`, move the
physical input head to `before.inputHead` to read `inSym`, then rewind the
input head to `0` and clear `tScratch`. -/
def readInputHeadAndCheck (InputAlphabet : Type*) :=
  bindComponent (readHeadBlock InputAlphabet ⟨0, by decide⟩) fun relInput =>
    bindComponent (seekInputHeadAndRead InputAlphabet) fun inSym =>
      ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch)).mapExit
        (fun _ => (inSym, relInput))

theorem readInputHeadAndCheck_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) (hA hB : Fin (n + 2))
    (pA sA pB sB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + (S + 2) < bound tArgA)
    (hBoundB : pB.length + (S + 2) < bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym)
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA)
      (pA ++ (natToBits (S + 2) hA.val).map SimSym.bit ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ (natToBits (S + 2) hB.val).map SimSym.bit ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ finalTapes,
      (readInputHeadAndCheck InputAlphabet).ReachesExit input bound initTapes ⟨0, by omega⟩
        (readInput input hA,
          BitRelState.init.runList (natToBits (S + 2) hA.val) (natToBits (S + 2) hB.val))
        finalTapes ⟨0, by omega⟩ ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA)
        (pA ++ (natToBits (S + 2) hA.val).map SimSym.bit ++ sA) (pA.length + (S + 2)) ∧
      TapeMatches (finalTapes tArgB)
        (pB ++ (natToBits (S + 2) hB.val).map SimSym.bit ++ sB) (pB.length + (S + 2)) ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 ∧
      finalTapes tRegs = initTapes tRegs := by
  let ua := natToBits (S + 2) hA.val
  let ub := natToBits (S + 2) hB.val
  obtain ⟨t1, hRead, hR1, hA1, hB1, hS1, hReg1⟩ :=
    readHeadBlock_reachesExit ⟨0, by decide⟩ (Or.inl rfl) input bound S
      pA (ua.map SimSym.bit) sA pB (ub.map SimSym.bit) sB ua ub
      (by simp [ua, natToBits_length, Nat.add_comm])
      (by simp [ub, natToBits_length, Nat.add_comm])
      rfl rfl hBoundR (by simpa [ua, natToBits_length] using hBoundA)
      (by simpa [ub, natToBits_length] using hBoundB)
      (by simpa [ua, natToBits_length] using hBoundS)
      initTapes ⟨0, by omega⟩ hOther hMatchR hMatchA hMatchB hMatchS
  have hBounds1 : ∀ j, j ≠ tScratch → (t1 j).head < bound j := by
    intro j hj
    match j with
    | ⟨0, _⟩ =>
      change (t1 tRuler).head < bound tRuler
      rw [hR1.head_eq]
      omega
    | ⟨1, _⟩ =>
      change (t1 tRegs).head < bound tRegs
      rw [hReg1]
      exact hOther
    | ⟨2, _⟩ =>
      change (t1 tArgA).head < bound tArgA
      rw [hA1.head_eq]
      simpa [ua, natToBits_length] using hBoundA
    | ⟨3, _⟩ =>
      change (t1 tArgB).head < bound tArgB
      rw [hB1.head_eq]
      simpa [ub, natToBits_length] using hBoundB
    | ⟨4, _⟩ => exact False.elim (hj rfl)
  obtain ⟨t2, hSeek, hS2, hOthers2⟩ :=
    seekInputHeadAndRead_reachesExit input bound S hS hInput hA hBoundS t1 hBounds1 hS1
  have hBounds2 : ∀ j, (t2 j).head < bound j := by
    intro j
    by_cases hj : j = tScratch
    · subst hj
      rw [hS2.head_eq]
      omega
    · rw [hOthers2 j hj]; exact hBounds1 j hj
  have hRewindIn := rewindInput_reachesExit input bound t2 hBounds2 hA
  have hBounds2Other : ∀ j, j ≠ tScratch → (t2 j).head < bound j := fun j hj => hBounds2 j
  let prefSyms := (List.replicate (S + 2) false).map SimSym.bit
  have hNoEnd : ∀ s ∈ prefSyms, s ≠ SimSym.endMark := by
    intro s hs
    simp only [prefSyms, List.mem_map, List.mem_replicate] at hs
    rcases hs with ⟨_, _, rfl⟩
    simp
  obtain ⟨ftS, hClear, hS3⟩ :=
    clearTape_reachesExit tScratch input bound prefSyms
      (by simp [prefSyms, hBoundS]) hNoEnd t2 ⟨0, by omega⟩ hBounds2Other hS2
  have hSeq := TMComponent.seq_reachesExit (rewindInput InputAlphabet 5)
    (clearTape InputAlphabet tScratch) input bound hRewindIn hClear
  have hMapped := TMComponent.mapExit_reachesExit
    ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch))
    (fun _ => (readInput input hA, BitRelState.init.runList ua ub)) input bound hSeq
  have hBind2 := bindComponent_reachesExit (seekInputHeadAndRead InputAlphabet)
    (fun inSym => ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch)).mapExit
      (fun _ => (inSym, BitRelState.init.runList ua ub)))
    input bound hSeek (by simpa using hMapped)
  have hBind1 := bindComponent_reachesExit (readHeadBlock InputAlphabet ⟨0, by decide⟩)
    (fun relInput => bindComponent (seekInputHeadAndRead InputAlphabet) fun inSym =>
      ((rewindInput InputAlphabet 5).seq (clearTape InputAlphabet tScratch)).mapExit
        (fun _ => (inSym, relInput)))
    input bound hRead hBind2
  refine ⟨_, hBind1, ?_, ?_, ?_, ?_, ?_⟩
  · have hNe : tRuler ≠ tScratch := by decide
    simpa [hNe, hOthers2 tRuler hNe] using hR1
  · have hNe : tArgA ≠ tScratch := by decide
    simpa [hNe, hOthers2 tArgA hNe, ua, natToBits_length] using hA1
  · have hNe : tArgB ≠ tScratch := by decide
    simpa [hNe, hOthers2 tArgB hNe, ub, natToBits_length] using hB1
  · simpa using hS3
  · have hNe : tRegs ≠ tScratch := by decide
    simp only [hNe, ↓reduceIte]
    rw [hOthers2 tRegs hNe, hReg1]


end SavitchLemma

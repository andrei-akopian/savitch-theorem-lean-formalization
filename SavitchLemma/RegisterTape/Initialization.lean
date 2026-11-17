module

public import SavitchLemma.RegisterTape.Increment

@[expose] public section

/-!
# Register initialization

Builds the initial register array from unary templates on the argument tapes.
-/

namespace SavitchLemma

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

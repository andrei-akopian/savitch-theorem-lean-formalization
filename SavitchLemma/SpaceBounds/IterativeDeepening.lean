module

public import SavitchLemma.SpaceBounds.IterativeDeepeningPrimitives
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Iterative deepening loop and non-measurable Theorem 1

Defines `idBody`, `idLoop`, and `savitchDTM_nonmeasurable`, and proves
`savitchDTM_nonmeasurable_correct`.
-/

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

namespace SavitchLemma

/-! ### Iterative-deepening loop and compiled DTM -/

noncomputable def idBody {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  let extendAndCont := (extendRuler InputAlphabet).mapExit fun _ => (.inl () : Unit ⊕ Bool)
  let simFalse := (rewindInputHead InputAlphabet).seq
    ((clearTape InputAlphabet tRegs).seq extendAndCont)
  let simBranch := (savitchSimulator M).branch
    (TMComponent.atom fun _ scanned => mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay))
    simFalse
  (checkInputLenComp InputAlphabet).branch simBranch extendAndCont

noncomputable def idLoop {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
    mkWorkAction (decide (scanned tRuler = .blank)) scanned (fun _ => .stay)).branch
    ((idInit InputAlphabet).mapExit fun _ => (.inl () : Unit ⊕ Bool))
    (idBody M)

noncomputable def savitchID {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (idLoop M).loop

noncomputable def savitchDTM_nonmeasurable {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (savitchID M).toDTM .blank

private theorem configBitWidth_mono (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ)
    {S₁ S₂ : ℕ} (h : S₁ ≤ S₂) :
    configBitWidth Q Γ k S₁ ≤ configBitWidth Q Γ k S₂ := by
  rw [configBitWidth_eq_linear, configBitWidth_eq_linear]
  gcongr

theorem idBody_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (hBoundR : S + 3 ≤ bound tRuler)
    (hBoundRegs : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hClean : CleanTapesFor S tapes inHead) :
    (¬ (n ≤ 2 ^ S ∧ M.AcceptsWithinCapacity input S (by omega)) →
      ∃ tapes' inHead',
        (idBody M).ReachesExit input bound tapes inHead (.inl ()) tapes' inHead' ∧
        CleanTapesFor (S + 1) tapes' inHead') ∧
    (n ≤ 2 ^ S → M.AcceptsWithinCapacity input S (by omega) →
      ∃ tapes' inHead',
        (idBody M).ReachesExit input bound tapes inHead (.inr true) tapes' inHead') := by
  rcases hClean with ⟨hIn0, hMR, hMRegs, hMA, hMB, hMS⟩
  have hInEq : inHead = ⟨0, by omega⟩ := Fin.ext hIn0
  rw [hInEq]
  have hBOthRS : ∀ j, j ≠ tRuler → j ≠ tScratch → (tapes j).head < bound j := fun j hjR hjS => by
    match j with
    | ⟨0, _⟩ => exact False.elim (hjR rfl)
    | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; rw [hMRegs.head_eq]; omega
    | ⟨2, _⟩ => change (tapes tArgA).head < bound tArgA; rw [hMA.head_eq]; omega
    | ⟨3, _⟩ => change (tapes tArgB).head < bound tArgB; rw [hMB.head_eq]; omega
    | ⟨4, _⟩ => exact False.elim (hjS rfl)
  obtain ⟨ftR1, ftS1, hLenChk, hMR1, hMS1⟩ := checkInputLenComp_reachesExit input bound S hS
    (by omega) (by omega) tapes ⟨0, by omega⟩ rfl hBOthRS hMR hMS
  let t1 := fun j => if j = tRuler then ftR1 else if j = tScratch then ftS1 else tapes j
  have hT1Bounds : ∀ j, (t1 j).head < bound j := fun j => by
    match j with
    | ⟨0, _⟩ => change (t1 tRuler).head < bound tRuler; simp [t1, hMR1.head_eq]; omega
    | ⟨1, _⟩ =>
      change (t1 tRegs).head < bound tRegs
      dsimp [t1]; simp only [show tRegs ≠ tRuler by decide, show tRegs ≠ tScratch by decide, ↓reduceIte, hMRegs.head_eq]; omega
    | ⟨2, _⟩ =>
      change (t1 tArgA).head < bound tArgA
      dsimp [t1]; simp only [show tArgA ≠ tRuler by decide, show tArgA ≠ tScratch by decide, ↓reduceIte, hMA.head_eq]; omega
    | ⟨3, _⟩ =>
      change (t1 tArgB).head < bound tArgB
      dsimp [t1]; simp only [show tArgB ≠ tRuler by decide, show tArgB ≠ tScratch by decide, ↓reduceIte, hMB.head_eq]; omega
    | ⟨4, _⟩ =>
      change (t1 tScratch).head < bound tScratch
      simp only [t1, show tScratch ≠ tRuler by decide, ↓reduceIte, hMS1.head_eq]; omega
  constructor
  · intro hNotAcc
    by_cases hn : n ≤ 2 ^ S
    · have hDec : decide (n ≤ 2 ^ S) = true := decide_eq_true hn
      rw [hDec] at hLenChk
      obtain ⟨res, t2, in2, hSim, hIff, hClean2⟩ :=
        savitchSimulator_reachesExit_clean M input bound S hS hn (by omega) hBoundRegs
          hBoundA hBoundB hBoundS t1 ⟨0, by omega⟩
          (by simpa [t1, tRuler] using hMR1)
          (by simpa [t1, tRuler, tRegs, tScratch] using hMRegs)
          (by simpa [t1, tRuler, tRegs, tArgA, tScratch] using hMA)
          (by simpa [t1, tRuler, tRegs, tArgA, tArgB, tScratch] using hMB)
          (by simpa [t1, tRuler, tScratch] using hMS1)
      have hResF : res = false := by
        cases res with
        | false => rfl
        | true => exact False.elim (hNotAcc ⟨hn, hIff.mp rfl⟩)
      subst hResF
      obtain ⟨hMR2, ⟨prefixSyms, hNoEnd, hLenP, hMRegs2⟩, hMA2, hMB2, hMS2⟩ := hClean2 rfl
      have hT2Bounds : ∀ j, (t2 j).head < bound j := fun j => by
        match j with
        | ⟨0, _⟩ => change (t2 tRuler).head < bound tRuler; rw [hMR2.head_eq]; omega
        | ⟨1, _⟩ => change (t2 tRegs).head < bound tRegs; rw [hMRegs2.head_eq]; omega
        | ⟨2, _⟩ => change (t2 tArgA).head < bound tArgA; rw [hMA2.head_eq]; omega
        | ⟨3, _⟩ => change (t2 tArgB).head < bound tArgB; rw [hMB2.head_eq]; omega
        | ⟨4, _⟩ => change (t2 tScratch).head < bound tScratch; rw [hMS2.head_eq]; omega
      have hRew := rewindInputHead_reachesExit input bound t2 hT2Bounds in2
      obtain ⟨ftRegs3, hClrRegs, hMRegs3⟩ := clearTape_reachesExit tRegs input bound prefixSyms
        (by omega) hNoEnd t2 ⟨0, by omega⟩ (fun j hj => hT2Bounds j) hMRegs2
      let t3 := fun j => if j = tRegs then ftRegs3 else t2 j
      obtain ⟨ftR4, hExt, hMR4⟩ := extendRuler_reachesExit input bound S hBoundR t3 ⟨0, by omega⟩
        (fun j hj => by
          by_cases hjR : j = tRegs
          · subst hjR; simp [t3, hMRegs3.head_eq]; omega
          · simp [t3, hjR, hT2Bounds j])
        (by simpa [t3, show tRuler ≠ tRegs by decide] using hMR2)
      let t4 := fun j => if j = tRuler then ftR4 else t3 j
      have hExtExit := TMComponent.mapExit_reachesExit _ (fun _ => (.inl () : Unit ⊕ Bool))
        input bound hExt
      have hSimFalse := TMComponent.seq_reachesExit _ _ input bound hRew
        (TMComponent.seq_reachesExit _ _ input bound hClrRegs hExtExit)
      have hSimBranch := TMComponent.branch_reachesExit (savitchSimulator M)
        (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
          mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay))
        ((rewindInputHead InputAlphabet).seq
          ((clearTape InputAlphabet tRegs).seq
            ((extendRuler InputAlphabet).mapExit (fun _ => (.inl () : Unit ⊕ Bool)))))
        input bound false hSim hSimFalse
      refine ⟨t4, ⟨0, by omega⟩,
        TMComponent.branch_reachesExit _ _ _ input bound true hLenChk hSimBranch,
        rfl, hMR4, ?_, ?_, ?_, ?_⟩
      · simpa [t4, t3, show tRegs ≠ tRuler by decide] using hMRegs3
      · simpa [t4, t3, show tArgA ≠ tRuler by decide, show tArgA ≠ tRegs by decide] using hMA2
      · simpa [t4, t3, show tArgB ≠ tRuler by decide, show tArgB ≠ tRegs by decide] using hMB2
      · simpa [t4, t3, show tScratch ≠ tRuler by decide, show tScratch ≠ tRegs by decide] using hMS2
    · have hDec : decide (n ≤ 2 ^ S) = false := decide_eq_false hn
      rw [hDec] at hLenChk
      obtain ⟨ftR2, hExt, hMR2⟩ := extendRuler_reachesExit input bound S hBoundR t1 ⟨0, by omega⟩
        (fun j hj => hT1Bounds j) (by simpa [t1] using hMR1)
      let t2 := fun j => if j = tRuler then ftR2 else t1 j
      have hExtExit := TMComponent.mapExit_reachesExit _ (fun _ => (.inl () : Unit ⊕ Bool))
        input bound hExt
      refine ⟨t2, ⟨0, by omega⟩,
        TMComponent.branch_reachesExit _ _ _ input bound false hLenChk hExtExit,
        rfl, hMR2, ?_, ?_, ?_, ?_⟩
      · simpa [t2, t1, show tRegs ≠ tRuler by decide, show tRegs ≠ tScratch by decide] using hMRegs
      · simpa [t2, t1, show tArgA ≠ tRuler by decide, show tArgA ≠ tScratch by decide] using hMA
      · simpa [t2, t1, show tArgB ≠ tRuler by decide, show tArgB ≠ tScratch by decide] using hMB
      · simpa [t2, t1, show tScratch ≠ tRuler by decide] using hMS1
  · intro hn hAcc
    have hDec : decide (n ≤ 2 ^ S) = true := decide_eq_true hn
    rw [hDec] at hLenChk
    obtain ⟨res, t2, in2, hSim, hIff, _⟩ :=
      savitchSimulator_reachesExit_clean M input bound S hS hn (by omega) hBoundRegs
        hBoundA hBoundB hBoundS t1 ⟨0, by omega⟩
        (by simpa [t1, tRuler] using hMR1)
        (by simpa [t1, tRuler, tRegs, tScratch] using hMRegs)
        (by simpa [t1, tRuler, tRegs, tArgA, tScratch] using hMA)
        (by simpa [t1, tRuler, tRegs, tArgA, tArgB, tScratch] using hMB)
        (by simpa [t1, tRuler, tScratch] using hMS1)
    have hResT : res = true := hIff.mpr hAcc
    subst hResT
    have hT2Bounds : ∀ j, (t2 j).head < bound j := by
      intro j
      rcases Relation.ReflTransGen.cases_tail hSim with hEq | ⟨_, _, hStep⟩
      · have hTpEq := congrArg OneSidedTMConfig.workTapes hEq
        dsimp only at hTpEq
        rw [hTpEq]
        exact hT1Bounds j
      · exact hStep.2.2 j
    have hAtom : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
        mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay)).ReachesExit
        input bound t2 in2 (.inr true) t2 in2 :=
      TMComponent.atom_reachesExit _ input bound t2 in2 hT2Bounds in2 (by simp [mkWorkAction, moveHead]) t2
        (fun j => OneSidedTape.updateAndMove_stay_self _) hT2Bounds
    exact ⟨t2, in2, TMComponent.branch_reachesExit _ _ _ input bound true hLenChk
      (TMComponent.branch_reachesExit _ _ _ input bound true hSim hAtom)⟩

theorem idLoop_blank_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (hBR : 3 ≤ bound tRuler) (hBOth : ∀ t, t ≠ tRuler → 2 ≤ bound t) :
    ∃ tapes',
      (idLoop M).ReachesExit input bound (fun _ => ⟨fun _ => .blank, 0⟩) (⟨0, by omega⟩ : Fin (n + 2))
        (.inl ()) tapes' (⟨0, by omega⟩ : Fin (n + 2)) ∧
      CleanTapesFor 1 tapes' (⟨0, by omega⟩ : Fin (n + 2)) := by
  let t0 : Fin 5 → OneSidedTape SimSym := fun _ => ⟨fun _ => .blank, 0⟩
  have hB0 : ∀ j, (t0 j).head < bound j := fun j => by
    by_cases hj : j = tRuler
    · subst hj; simp [t0]; omega
    · simp [t0]; have := hBOth j hj; omega
  have hChk : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
      mkWorkAction (decide (scanned tRuler = .blank)) scanned (fun _ => .stay)).ReachesExit
      input bound t0 ⟨0, by omega⟩ true t0 ⟨0, by omega⟩ := by
    have hAt := TMComponent.atom_reachesExit
      (fun _ (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (scanned tRuler = .blank)) scanned (fun _ => .stay))
      input bound t0 ⟨0, by omega⟩ hB0 ⟨0, by omega⟩ (by simp [mkWorkAction, moveHead]) t0
      (fun j => OneSidedTape.updateAndMove_stay_self _) hB0
    simpa [t0, mkWorkAction] using hAt
  obtain ⟨t1, hInit, hClean⟩ := idInit_reachesExit input bound hBR hBOth
  exact ⟨t1, TMComponent.branch_reachesExit _ _ _ input bound true hChk
    (TMComponent.mapExit_reachesExit _ _ input bound hInit), hClean⟩

theorem idLoop_clean_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (hBoundR : S + 3 ≤ bound tRuler)
    (hBoundRegs : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hClean : CleanTapesFor S tapes inHead) :
    (¬ (n ≤ 2 ^ S ∧ M.AcceptsWithinCapacity input S (by omega)) →
      ∃ tapes' inHead',
        (idLoop M).ReachesExit input bound tapes inHead (.inl ()) tapes' inHead' ∧
        CleanTapesFor (S + 1) tapes' inHead') ∧
    (n ≤ 2 ^ S → M.AcceptsWithinCapacity input S (by omega) →
      ∃ tapes' inHead',
        (idLoop M).ReachesExit input bound tapes inHead (.inr true) tapes' inHead') := by
  have hB0 : ∀ j, (tapes j).head < bound j := fun j => by
    rcases hClean with ⟨_, hMR, hMRegs, hMA, hMB, hMS⟩
    match j with
    | ⟨0, _⟩ => change (tapes tRuler).head < bound tRuler; rw [hMR.head_eq]; omega
    | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; rw [hMRegs.head_eq]; omega
    | ⟨2, _⟩ => change (tapes tArgA).head < bound tArgA; rw [hMA.head_eq]; omega
    | ⟨3, _⟩ => change (tapes tArgB).head < bound tArgB; rw [hMB.head_eq]; omega
    | ⟨4, _⟩ => change (tapes tScratch).head < bound tScratch; rw [hMS.head_eq]; omega
  have hReadBit : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
    have hMR := hClean.2.1
    rw [hMR.read_lt (by simp)]
    have hS0 : 0 < S := by omega
    rw [List.getElem_append_left (by simp; omega)]
    simp
  have hChk : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
      mkWorkAction (decide (scanned tRuler = .blank)) scanned (fun _ => .stay)).ReachesExit
      input bound tapes inHead false tapes inHead := by
    simpa [hReadBit, mkWorkAction] using TMComponent.atom_reachesExit
      (fun _ (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (scanned tRuler = .blank)) scanned (fun _ => .stay))
      input bound tapes inHead hB0 inHead (by simp [mkWorkAction, moveHead]) tapes
      (fun j => OneSidedTape.updateAndMove_stay_self _) hB0
  obtain ⟨hNeg, hPos⟩ := idBody_reachesExit M input bound S hS hBoundR hBoundRegs hBoundA hBoundB hBoundS
    tapes inHead hClean
  constructor
  · intro hNotAcc
    obtain ⟨t', ih', hRun, hClean'⟩ := hNeg hNotAcc
    exact ⟨t', ih', TMComponent.branch_reachesExit _ _ _ input bound false hChk hRun, hClean'⟩
  · intro hn hAcc
    obtain ⟨t', ih', hRun⟩ := hPos hn hAcc
    exact ⟨t', ih', TMComponent.branch_reachesExit _ _ _ input bound false hChk hRun⟩

private theorem ruler_bit_filter_card {tape : OneSidedTape SimSym} {S M : ℕ}
    (hMatch : TapeMatches tape (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hSM : S ≤ M) :
    ((Finset.range M).filter (fun i => tape.cells (i + 1) = .bit true)).card = S := by
  have hEq : (Finset.range M).filter (fun i => tape.cells (i + 1) = .bit true) =
      Finset.range S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hBit⟩
      rw [hMatch.2 (i + 1)] at hBit
      by_contra hGe
      have hiGe : S ≤ i := by omega
      by_cases hiEq : i = S
      · subst hiEq
        simp only [List.cons_append, List.getElem?_cons_succ] at hBit
        rw [List.getElem?_append_right (by simp)] at hBit
        simp at hBit
      · have hNone : (.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark])[i + 1]? = none :=
          List.getElem?_eq_none (by simp; omega)
        rw [hNone] at hBit
        simp at hBit
    · intro hiS
      refine ⟨by omega, ?_⟩
      rw [hMatch.2 (i + 1)]
      rw [List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega),
        List.getElem?_eq_getElem (by simp; omega)]
      simp
  rw [hEq, Finset.card_range]

/-- **Theorem 1** (general, non-measurable case) via iterative deepening. -/
theorem savitchDTM_nonmeasurable_correct {Q InputAlphabet Γ : Type} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ)
    (hL : ∀ n, 1 ≤ L n ∧ n ≤ 2 ^ L n)
    (hM : M.AcceptsLanguageWithinSpace A L) :
    ∃ C : ℕ,
      (savitchDTM_nonmeasurable M).AcceptsLanguageWithinSpace A
        (fun n => 1 + (configBitWidth Q Γ k (L n) + 1) * (configBitWidth Q Γ k (L n) + 2) +
          (configBitWidth Q Γ k (L n) + 3) + (L n + 4)) ∧
      ∀ n, 1 + (configBitWidth Q Γ k (L n) + 1) * (configBitWidth Q Γ k (L n) + 2) +
          (configBitWidth Q Γ k (L n) + 3) + (L n + 4) ≤ C * (L n + 1) ^ 2 := by
  let S_bound : ℕ → ℕ := fun n =>
    1 + (configBitWidth Q Γ k (L n) + 1) * (configBitWidth Q Γ k (L n) + 2) +
      (configBitWidth Q Γ k (L n) + 3) + (L n + 4)
  refine ⟨1 + ((qBits Q + 4) + (1 + k * (1 + gammaBits Γ)) + 2) ^ 2 + 10, ⟨?_, ?_⟩, ?_⟩
  · intro n input hA
    have hSn : 1 ≤ L n := (hL n).1
    have hn : n ≤ 2 ^ L n := (hL n).2
    have hAcc : M.AcceptsWithinCapacity input (L n) (by omega) :=
      (M.acceptsOneSidedWithin_iff_acceptsWithinCapacity input (L n) (by omega)).1
        (hM.1 n input hA)
    let bound : Fin 5 → ℕ := fun _ => S_bound n
    have hB_ge : ∀ S, 1 ≤ S → S ≤ L n →
        S + 3 ≤ bound tRuler ∧
        1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
          (configBitWidth Q Γ k S + 3) ≤ bound tRegs ∧
        configBitWidth Q Γ k S + 2 ≤ bound tArgA ∧
        configBitWidth Q Γ k S + 2 ≤ bound tArgB ∧
        S + 4 ≤ bound tScratch := by
      intro S hS1 hSL
      have hW : configBitWidth Q Γ k S ≤ configBitWidth Q Γ k (L n) :=
        configBitWidth_mono Q Γ k hSL
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [bound, S_bound]
      · omega
      · have : (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) ≤
            (configBitWidth Q Γ k (L n) + 1) * (configBitWidth Q Γ k (L n) + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      · omega
      · omega
      · omega
    let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tp ih =>
      (tp = (fun _ => ⟨fun _ => .blank, 0⟩) ∧ ih = ⟨0, by omega⟩) ∨
      (∃ S, 1 ≤ S ∧ S ≤ L n ∧ CleanTapesFor S tp ih)
    let meas : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ := fun tp _ =>
      if (tp tRuler).cells 0 = .blank then L n + 1
      else L n - ((Finset.range (L n)).filter (fun i => (tp tRuler).cells (i + 1) = .bit true)).card
    have hLoop := TMComponent.loop_reachesExit (idLoop M) input bound
      Inv meas (fun e _ _ => e = true)
      (fun tp ih hInv => by
        rcases hInv with ⟨rfl, rfl⟩ | ⟨S, hS1, hSL, hClean⟩
        · obtain ⟨tp', hRun, hClean'⟩ := idLoop_blank_reachesExit M input bound
            (by dsimp [bound, S_bound]; omega) (fun _ _ => by dsimp [bound, S_bound]; omega)
          refine Or.inl ⟨tp', ⟨0, by omega⟩, hRun, Or.inr ⟨1, by omega, hSn, hClean'⟩, ?_⟩
          have hLeft0 : (tp' tRuler).cells 0 = .leftMark := by
            rw [hClean'.2.1.2 0]; rfl
          simp only [meas, ↓reduceIte, hLeft0, show SimSym.leftMark ≠ .blank by decide]
          rw [ruler_bit_filter_card hClean'.2.1 hSn]
          omega
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hB_ge S hS1 hSL
          have hStep := idLoop_clean_reachesExit M input bound S hS1 h1 h2 h3 h4 h5 tp ih hClean
          by_cases hCond : n ≤ 2 ^ S ∧ M.AcceptsWithinCapacity input S (by omega)
          · obtain ⟨tp', ih', hRun⟩ := hStep.2 hCond.1 hCond.2
            exact Or.inr ⟨true, tp', ih', hRun, rfl⟩
          · have hSLt : S < L n := by
              by_contra hGe
              have hEq : S = L n := by omega
              subst hEq
              exact hCond ⟨hn, hAcc⟩
            obtain ⟨tp', ih', hRun, hClean'⟩ := hStep.1 hCond
            refine Or.inl ⟨tp', ih', hRun, Or.inr ⟨S + 1, by omega, by omega, hClean'⟩, ?_⟩
            have hLeft0 : (tp tRuler).cells 0 = .leftMark := by rw [hClean.2.1.2 0]; rfl
            have hLeft0' : (tp' tRuler).cells 0 = .leftMark := by rw [hClean'.2.1.2 0]; rfl
            simp only [meas, hLeft0, hLeft0', show SimSym.leftMark ≠ .blank by decide, ↓reduceIte]
            rw [ruler_bit_filter_card hClean.2.1 hSL,
              ruler_bit_filter_card hClean'.2.1 (by omega)]
            omega)
      (fun _ => ⟨fun _ => .blank, 0⟩) ⟨0, by omega⟩ (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨e, tpEnd, ihEnd, hRun, rfl⟩ := hLoop
    exact TMComponent.toDTM_acceptsWithin (savitchID M) .blank input bound (S_bound n)
      (fun _ => le_rfl) hRun
  · intro n input hAcc
    by_contra hNotA
    have hNotAcc : ¬ M.AcceptsOneSided input := fun h => hNotA (hM.2 n input h)
    have hInvStep : ∀ tp ih,
        ((tp = (fun _ => ⟨fun _ => .blank, 0⟩) ∧ ih = ⟨0, by omega⟩) ∨
          (∃ S, 1 ≤ S ∧ CleanTapesFor S tp ih)) →
        ∃ bound tp' ih',
          (idLoop M).ReachesExit input bound tp ih (.inl ()) tp' ih' ∧
          ((tp' = (fun _ => ⟨fun _ => .blank, 0⟩) ∧ ih' = ⟨0, by omega⟩) ∨
            (∃ S, 1 ≤ S ∧ CleanTapesFor S tp' ih')) := by
      rintro tp ih (⟨rfl, rfl⟩ | ⟨S, hS1, hClean⟩)
      · refine ⟨fun _ => 4, ?_⟩
        obtain ⟨tp', hRun, hClean'⟩ := idLoop_blank_reachesExit M input (fun _ => 4)
          (by omega) (fun _ _ => by omega)
        exact ⟨tp', ⟨0, by omega⟩, hRun, Or.inr ⟨1, by omega, hClean'⟩⟩
      · have hNotCap : ¬ M.AcceptsWithinCapacity input S (by omega) := by
          intro hCap
          exact hNotAcc (M.acceptsOneSided_of_acceptsOneSidedWithin input S
            ((M.acceptsOneSidedWithin_iff_acceptsWithinCapacity input S (by omega)).2 hCap))
        let B := 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
          (configBitWidth Q Γ k S + 3) + (S + 4)
        obtain ⟨tp', ih', hRun, hClean'⟩ := (idLoop_clean_reachesExit M input (fun _ => B) S hS1
          (by dsimp [B]; omega) (by dsimp [B]; omega)
          (by dsimp [B]; omega) (by dsimp [B]; omega) (by dsimp [B]; omega)
          tp ih hClean).1 (fun ⟨_, h⟩ => hNotCap h)
        exact ⟨fun _ => B, tp', ih', hRun, Or.inr ⟨S + 1, by omega, hClean'⟩⟩
    exact TMComponent.loop_toDTM_never_accepts (idLoop M) .blank input
      (fun tp ih => (tp = (fun _ => ⟨fun _ => .blank, 0⟩) ∧ ih = ⟨0, by omega⟩) ∨
        (∃ S, 1 ≤ S ∧ CleanTapesFor S tp ih))
      (Or.inl ⟨rfl, rfl⟩) hInvStep
      hAcc
  · intro n
    set m := (qBits Q + 4) + (1 + k * (1 + gammaBits Γ)) + 2 with hm
    have hW : configBitWidth Q Γ k (L n) + 2 ≤ m * (L n + 1) := by
      rw [configBitWidth_eq_linear, hm]
      have hExp : (qBits Q + 4 + (1 + k * (1 + gammaBits Γ)) + 2) * (L n + 1) =
          (qBits Q + 4 + 2) * L n + L n * (1 + k * (1 + gammaBits Γ)) +
            (qBits Q + 4 + (1 + k * (1 + gammaBits Γ)) + 2) := by ring
      rw [hExp]; omega
    have h1 : L n + 1 ≤ (L n + 1) ^ 2 := by nlinarith
    have h2 : 1 ≤ (L n + 1) ^ 2 := by nlinarith
    have h3 : (configBitWidth Q Γ k (L n) + 2) ^ 2 ≤ m ^ 2 * (L n + 1) ^ 2 := by
      calc (configBitWidth Q Γ k (L n) + 2) ^ 2
          ≤ (m * (L n + 1)) ^ 2 := Nat.pow_le_pow_left hW 2
        _ = m ^ 2 * (L n + 1) ^ 2 := by ring
    nlinarith

end SavitchLemma

module

public import SavitchLemma.Simulator.AcceptChecker

@[expose] public section

/-!
# Configuration-validity checker on `tArgB`

Checks that a `configBitWidth Q Γ k S`-bit list on `tArgB` has:
1. every work-tape head field strictly below `S`, and
2. the two-bit valid-ID suffix `[true, false]`.

Combined with `checkStep`, this ensures any accepted candidate `x_j` is a
valid `encodeConfigBits Q Γ c_j` with `M.step input S c_i c_j`.
-/

namespace SavitchLemma

/-! ## 1. Skipping fixed and ruler-scaled bit blocks on `tArgB` -/

/-- Advance tape `t` by `m` cells without modifying any tape contents. -/
def skipFixedBits1 (InputAlphabet : Type*) {k : ℕ} (m : ℕ) (t : Fin k) :
    TMComponent (Fin (m + 1)) InputAlphabet SimSym k Unit where
  start := ⟨0, Nat.zero_lt_succ m⟩
  step idx _ scanned :=
    if h : idx.val < m then
      if hNext : idx.val + 1 = m then
        singleTapeAction (.inr ()) t (scanned t) .right scanned
      else
        singleTapeAction (.inl ⟨idx.val + 1, by omega⟩) t (scanned t) .right scanned
    else
      singleTapeAction (.inr ()) t (scanned t) .stay scanned

theorem skipFixedBits1_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (m : ℕ) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (contents : List SimSym) (pos : ℕ)
    (_hPos : pos + m ≤ contents.length) (hBound : pos + m < bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ ft,
      (skipFixedBits1 InputAlphabet m t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft contents (pos + m) := by
  have hRem : ∀ rem idx (hSum : idx + rem = m),
      ∀ tape, TapeMatches tape contents (pos + idx) →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (skipFixedBits1 InputAlphabet m t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl ⟨idx, by omega⟩, inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr (), inHead, fun j => if j = t then ft else initTapes j⟩ ∧
        TapeMatches ft contents (pos + m) := by
    intro rem
    induction rem with
    | zero =>
      intro idx hSum tape hMT
      have hIdxEq : idx = m := by omega
      have hMT' : TapeMatches tape contents (pos + m) := by simpa [hIdxEq] using hMT
      obtain ⟨ft, hUpd, hFM⟩ := hMT'.update_keep .stay rfl
      refine ⟨ft, ?_, hFM⟩
      have hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · simp only [hj, ↓reduceIte]; rw [hMT'.head_eq]; exact hBound
        · simp [hj, hOtherBounds j hj]
      exact singleTape_compStep_exit_override (skipFixedBits1 InputAlphabet m t) t input bound
        initTapes tape ft ⟨idx, by omega⟩ hHeads (by rw [hFM.head_eq]; exact hBound) hUpd
        (by simp [skipFixedBits1, hIdxEq])
    | succ rem' ih =>
      intro idx hSum tape hMT
      have hIdxLt : idx < m := by omega
      have hMove : moveOneSidedHead (pos + idx) .right = some (pos + idx + 1) := by
        simp [moveOneSidedHead]
      obtain ⟨nt, hUpd, hNM⟩ := hMT.update_keep .right hMove
      have hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · simp only [hj, ↓reduceIte]; rw [hMT.head_eq]; omega
        · simp [hj, hOtherBounds j hj]
      by_cases hNext : idx + 1 = m
      · refine ⟨nt, ?_, by simpa [hNext, Nat.add_assoc] using hNM⟩
        exact singleTape_compStep_exit_override (skipFixedBits1 InputAlphabet m t) t input bound
          initTapes tape nt ⟨idx, by omega⟩ hHeads (by rw [hNM.head_eq]; omega) hUpd
          (by simp [skipFixedBits1, hIdxLt, hNext])
      · obtain ⟨ft, hRest, hFM⟩ := ih (idx + 1) (by omega) nt
          (by simpa [Nat.add_assoc] using hNM)
        refine ⟨ft, ?_, hFM⟩
        exact singleTape_compStep_head_override (skipFixedBits1 InputAlphabet m t) t input bound
          initTapes tape nt ft ⟨idx, by omega⟩ ⟨idx + 1, by omega⟩ hHeads
          (by rw [hNM.head_eq]; omega) hUpd hRest
          (by simp [skipFixedBits1, hIdxLt, hNext])
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j; by_cases hj : j = t <;> simp [hj]
  obtain ⟨ft, hRun, hFM⟩ := hRem m 0 (Nat.zero_add m) (initTapes t) (by simpa using hMatch)
  rw [hTapesSelf] at hRun
  exact ⟨ft, hRun, hFM⟩

/-- Advance `tArgB` by `S * scale` cells using `tRuler` and rewind `tRuler`. -/
def skipRulerScaledB (InputAlphabet : Type*) (scale : ℕ) :=
  (loopWithState () fun _ =>
    TMComponent.branch
      (TMComponent.atom fun _ scanned =>
        mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
      ((skipFixedBits1 InputAlphabet scale tArgB).seq
        ((stepRightAtom InputAlphabet tRuler).mapExit fun _ => Sum.inl ()))
      (TMComponent.atom fun _ scanned =>
        mkWorkAction (Sum.inr ()) scanned (fun _ => .stay))).seq
    (rewindTape InputAlphabet tRuler)

theorem skipRulerScaledB_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (scale : ℕ) (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (contentsB : List SimSym) (posB : ℕ)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hPosB : posB + S * scale ≤ contentsB.length)
    (hBoundB : posB + S * scale < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB) contentsB posB) :
    ∃ ftR ftB,
      (skipRulerScaledB InputAlphabet scale).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB contentsB (posB + S * scale) := by
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  have hRLen : rulerList.length = S + 2 := by simp [rulerList]
  let body := fun (_ : Unit) =>
    TMComponent.branch
      (TMComponent.atom fun _ scanned =>
        mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
      ((skipFixedBits1 InputAlphabet scale tArgB).seq
        ((stepRightAtom InputAlphabet tRuler).mapExit fun _ => Sum.inl ()))
      (TMComponent.atom fun _ scanned =>
        mkWorkAction (Sum.inr ()) scanned (fun _ => .stay))
  let Inv : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      ∃ i : ℕ, i ≤ S ∧
        curInHead = inHead ∧
        TapeMatches (tapes tRuler) rulerList (1 + i) ∧
        TapeMatches (tapes tArgB) contentsB (posB + i * scale) ∧
        (∀ j, j ≠ tRuler → j ≠ tArgB → tapes j = initTapes j)
  let measure : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (1 + S) - (tapes tRuler).head
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes curInHead =>
      curInHead = inHead ∧
      TapeMatches (tapes tRuler) rulerList (1 + S) ∧
      TapeMatches (tapes tArgB) contentsB (posB + S * scale) ∧
      (∀ j, j ≠ tRuler → j ≠ tArgB → tapes j = initTapes j)
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟩ tapes curInHead ⟨i, hiLe, hCurIn, hMR, hMB, hOthers⟩
    cases hCurIn
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hMR.head_eq]; omega
      · by_cases hjB : j = tArgB
        · subst hjB; rw [hMB.head_eq]
          have : i * scale ≤ S * scale := Nat.mul_le_mul_right _ hiLe
          omega
        · rw [hOthers j hjR hjB]; exact hOtherBounds j hjR hjB
    by_cases hiLt : i < S
    · left
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ]
        simp
      have hDecR : decide ((tapes tRuler).cells (tapes tRuler).head = .bit true) = true := by
        rw [hReadR]; decide
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead true tapes inHead := by
        have hTmp :
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
              input bound tapes inHead
              (decide ((tapes tRuler).cells (tapes tRuler).head = .bit true)) tapes inHead := by
          apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
          · simp [mkWorkAction, moveHead]
          · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
          · exact hBounds
        rwa [hDecR] at hTmp
      have hScaleLe : (i + 1) * scale ≤ S * scale := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hScaleLe
      obtain ⟨ftB1, hSkip, hFB1⟩ := skipFixedBits1_reachesExit scale tArgB input bound
        contentsB (posB + i * scale) (by omega) (by omega) tapes inHead
        (fun j _ => hBounds j) hMB
      let t1 := fun j => if j = tArgB then ftB1 else tapes j
      have hT1OtherR : ∀ j, j ≠ tRuler → (t1 j).head < bound j := by
        intro j hjR
        by_cases hjB : j = tArgB
        · subst hjB; simpa [t1, hFB1.head_eq] using (by omega : posB + i * scale + scale < bound tArgB)
        · simpa [t1, hjB] using hBounds j
      have hMR1 : TapeMatches (t1 tRuler) rulerList (1 + i) := by
        have hNe : tRuler ≠ tArgB := by decide
        simpa [t1, hNe] using hMR
      obtain ⟨ftR1, hStepR, hFR1⟩ := stepRightAtom_reachesExit tRuler input bound rulerList
        (1 + i) (by omega) t1 inHead hT1OtherR hMR1
      let t2 := fun j => if j = tRuler then ftR1 else t1 j
      have hMapStep := TMComponent.mapExit_reachesExit (stepRightAtom InputAlphabet tRuler)
        (fun _ => (Sum.inl () : Unit ⊕ Unit)) input bound hStepR
      have hSeq := TMComponent.seq_reachesExit (skipFixedBits1 InputAlphabet scale tArgB)
        ((stepRightAtom InputAlphabet tRuler).mapExit fun _ => (Sum.inl () : Unit ⊕ Unit))
        input bound hSkip hMapStep
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
        ((skipFixedBits1 InputAlphabet scale tArgB).seq
          ((stepRightAtom InputAlphabet tRuler).mapExit fun _ => (Sum.inl () : Unit ⊕ Unit)))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound true hAtomBranch (by simpa using hSeq)
      refine ⟨(), t2, inHead, hBranch, ⟨i + 1, by omega, rfl, ?_, ?_, ?_⟩, ?_⟩
      · simpa [t2, Nat.add_assoc] using hFR1
      · have hNe : tArgB ≠ tRuler := by decide
        have hPosEq : posB + (i + 1) * scale = posB + i * scale + scale := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        simpa [t2, t1, hNe, hPosEq] using hFB1
      · intro j hjR hjB
        simp only [t2, t1, hjR, hjB, ↓reduceIte]
        exact hOthers j hjR hjB
      · change 1 + S - ftR1.head < 1 + S - (tapes tRuler).head
        rw [hFR1.head_eq, hMR.head_eq]
        omega
    · right
      have hiS : i = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_right (by simp [hiS])]
        simp [hiS]
      have hDecR : decide ((tapes tRuler).cells (tapes tRuler).head = .bit true) = false := by
        rw [hReadR]; decide
      have hAtomBranch :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead false tapes inHead := by
        have hTmp :
            (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
              mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)).ReachesExit
              input bound tapes inHead
              (decide ((tapes tRuler).cells (tapes tRuler).head = .bit true)) tapes inHead := by
          apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
          · simp [mkWorkAction, moveHead]
          · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
          · exact hBounds
        rwa [hDecR] at hTmp
      have hAtomExit :
          (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay)).ReachesExit
            input bound tapes inHead (.inr ()) tapes inHead := by
        apply TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead
        · simp [mkWorkAction, moveHead]
        · intro j; exact OneSidedTape.updateAndMove_stay_self (tapes j)
        · exact hBounds
      have hBranch := TMComponent.branch_reachesExit
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
        ((skipFixedBits1 InputAlphabet scale tArgB).seq
          ((stepRightAtom InputAlphabet tRuler).mapExit fun _ => (Sum.inl () : Unit ⊕ Unit)))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound false hAtomBranch (by simpa using hAtomExit)
      exact ⟨(), tapes, inHead, hBranch, rfl, by simpa [hiS] using hMR,
        by simpa [hiS] using hMB, hOthers⟩
  obtain ⟨⟨⟩, tLoop, finalInHead, hLoop, hHead, hRL, hBL, hOthersL⟩ :=
    loopWithState_reachesExit () body input bound Inv measure Post hStep initTapes inHead
      ⟨0, Nat.zero_le S, rfl, hMatchR, by simpa using hMatchB, fun _ _ _ => rfl⟩
  subst finalInHead
  have hRulerNoLeft : ∀ i, 1 ≤ i → i < rulerList.length →
      rulerList[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [rulerList, List.length_append, List.length_cons, List.length_replicate,
        List.length_nil] at hiLt
      by_cases hiS : i < S
      · simp only [rulerList]
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_cons_succ,
          List.getElem?_eq_getElem (by simp [hiS])]
        simp
      · have hiEq : i = S := by omega
        subst hiEq
        simp only [rulerList]
        rw [List.getElem?_append_right (by simp)]
        simp
  have hTLoopOtherR : ∀ j, j ≠ tRuler → (tLoop j).head < bound j := by
    intro j hjR
    by_cases hjB : j = tArgB
    · subst hjB; rw [hBL.head_eq]; exact hBoundB
    · rw [hOthersL j hjR hjB]; exact hOtherBounds j hjR hjB
  obtain ⟨tEnd, hRew, hRFin, hOthersFin⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
      rulerList (by simp [rulerList]) (by simp [rulerList]) hRulerNoLeft
      (by rw [hRLen]; exact hBoundR) tLoop inHead hTLoopOtherR (1 + S) (by omega)
      (by rw [hRLen]; omega) hRL
  have hSeqFull := TMComponent.seq_reachesExit (loopWithState () body)
    (rewindTape InputAlphabet tRuler) input bound hLoop hRew
  have hEndEq : tEnd = fun j => if j = tRuler then tEnd tRuler
      else if j = tArgB then tLoop tArgB else initTapes j := by
    funext j
    by_cases hjR : j = tRuler
    · subst hjR; rfl
    · rw [hOthersFin j hjR]
      by_cases hjB : j = tArgB
      · subst hjB; simp [hjR]
      · simp [hjR, hjB, hOthersL j hjR hjB]
  rw [hEndEq] at hSeqFull
  exact ⟨tEnd tRuler, tLoop tArgB, hSeqFull, hRFin, hBL⟩

end SavitchLemma

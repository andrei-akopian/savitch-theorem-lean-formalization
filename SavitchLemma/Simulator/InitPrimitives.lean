module

public import SavitchLemma.Simulator.Core

@[expose] public section

/-!
# Simulator initialization primitives

Builds unary-width templates and the first-stage D0 tape operations.
-/

namespace SavitchLemma

/-! ## D0: Initializing the Savitch register array from `tRuler = 1^S` -/

/-- Write `m` copies of `.bit true` simultaneously onto `tArgA` and `tArgB`. -/
def writeConstOnes (InputAlphabet : Type*) (m : ℕ) :
    TMComponent (Fin (m + 1)) InputAlphabet SimSym 5 Unit where
  start := ⟨0, Nat.zero_lt_succ m⟩
  step idx _ scanned :=
    if h : idx.val < m then
      mkWorkAction (.inl ⟨idx.val + 1, by omega⟩)
        (fun j => if j = tArgA ∨ j = tArgB then .bit true else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB then .right else .stay)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem writeConstOnes_reachesExit {InputAlphabet : Type*} {n : ℕ} (m : ℕ)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (prefA prefB : List SimSym)
    (hBoundA : prefA.length + m < bound tArgA)
    (hBoundB : prefB.length + m < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchA : TapeMatches (initTapes tArgA) prefA prefA.length)
    (hMatchB : TapeMatches (initTapes tArgB) prefB prefB.length) :
    ∃ ftA ftB,
      (writeConstOnes InputAlphabet m).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tArgA then ftA else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftA (prefA ++ List.replicate m (.bit true)) (prefA.length + m) ∧
      TapeMatches ftB (prefB ++ List.replicate m (.bit true)) (prefB.length + m) := by
  have hNeAB : tArgA ≠ tArgB := by decide
  have hStep : ∀ rem, ∀ done (hSum : done + rem = m) pA pB tA tB,
      TapeMatches tA pA pA.length →
      TapeMatches tB pB pB.length →
      pA.length + rem < bound tArgA →
      pB.length + rem < bound tArgB →
      ∃ ftA ftB,
        Relation.ReflTransGen
          (fun a b => (writeConstOnes InputAlphabet m).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl ⟨done, by omega⟩, inHead,
            fun j => if j = tArgA then tA else if j = tArgB then tB else initTapes j⟩
          ⟨.inr (), inHead,
            fun j => if j = tArgA then ftA else if j = tArgB then ftB else initTapes j⟩ ∧
        TapeMatches ftA (pA ++ List.replicate rem (.bit true)) (pA.length + rem) ∧
        TapeMatches ftB (pB ++ List.replicate rem (.bit true)) (pB.length + rem) := by
    intro rem
    induction rem with
    | zero =>
      intro done hSum pA pB tA tB htA htB hBA hBB
      have hDone : done = m := by omega
      have hHeads : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [htA.head_eq] using hBA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, htB.head_eq] using hBB
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ftA, hUpdA, hMA⟩ := htA.update_keep .stay rfl
      obtain ⟨ftB, hUpdB, hMB⟩ := htB.update_keep .stay rfl
      have hUpd : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).updateAndMove
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).write j)
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).workMove j) =
            some (if j = tArgA then ftA else if j = tArgB then ftB else initTapes j) := by
        intro j
        have hNotLt : ¬ done < m := by omega
        simp only [writeConstOnes, mkWorkAction, hNotLt, ↓reduceDIte]
        by_cases h1 : j = tArgA
        · subst h1; simpa using hUpdA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1] using hUpdB
          · simp only [h1, h2, ↓reduceIte]
            exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j,
          (if j = tArgA then ftA else if j = tArgB then ftB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [hMA.head_eq] using hBA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, hMB.head_eq] using hBB
          · simp [h1, h2, hOtherBounds j h1 h2]
      refine ⟨ftA, ftB, compStep_exit_override (writeConstOnes InputAlphabet m) input bound
        _ _ inHead () ⟨done, by omega⟩ hHeads hNextH
        (by
          have hNotLt : ¬ done < m := by omega
          simp [writeConstOnes, mkWorkAction, moveHead, hNotLt])
        hUpd
        (by
          have hNotLt : ¬ done < m := by omega
          simp [writeConstOnes, mkWorkAction, hNotLt]),
        by simpa using hMA, by simpa using hMB⟩
    | succ r ih =>
      intro done hSum pA pB tA tB htA htB hBA hBB
      have hLt : done < m := by omega
      have hHeads : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [htA.head_eq] using by omega
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, htB.head_eq] using by omega
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ntA, hUpdA, hMA⟩ := htA.update_append (.bit true)
      obtain ⟨ntB, hUpdB, hMB⟩ := htB.update_append (.bit true)
      have hUpd : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).updateAndMove
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).write j)
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).workMove j) =
            some (if j = tArgA then ntA else if j = tArgB then ntB else initTapes j) := by
        intro j
        simp only [writeConstOnes, mkWorkAction, hLt, ↓reduceDIte]
        by_cases h1 : j = tArgA
        · subst h1; simpa using hUpdA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1] using hUpdB
          · simp only [h1, h2, ↓reduceIte]
            exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j,
          (if j = tArgA then ntA else if j = tArgB then ntB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [hMA.head_eq] using by omega
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, hMB.head_eq] using by omega
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ftA, ftB, hRest, hFA, hFB⟩ := ih (done + 1) (by omega) (pA ++ [.bit true])
        (pB ++ [.bit true]) ntA ntB (by simpa using hMA) (by simpa using hMB)
        (by simp; omega) (by simp; omega)
      refine ⟨ftA, ftB, compStep_head_override (writeConstOnes InputAlphabet m) input bound
        _ _ _ inHead inHead () ⟨done, by omega⟩ ⟨done + 1, by omega⟩ hHeads hNextH
        (by simp [writeConstOnes, mkWorkAction, moveHead, hLt]) hUpd
        (by simp [writeConstOnes, mkWorkAction, hLt]) hRest, ?_, ?_⟩
      · have : pA.length + (r + 1) = (pA ++ [SimSym.bit true]).length + r := by simp; omega
        rw [this]
        simpa [List.replicate_succ, List.append_assoc] using hFA
      · have : pB.length + (r + 1) = (pB ++ [SimSym.bit true]).length + r := by simp; omega
        rw [this]
        simpa [List.replicate_succ, List.append_assoc] using hFB
  have hTapesSelf : (fun j => if j = tArgA then initTapes tArgA
      else if j = tArgB then initTapes tArgB else initTapes j) = initTapes := by
    funext j; by_cases h1 : j = tArgA <;> by_cases h2 : j = tArgB <;> simp [h1, h2, hNeAB.symm]
  have hRes := hStep m 0 (Nat.zero_add m) prefA prefB
    (initTapes tArgA) (initTapes tArgB) hMatchA hMatchB hBoundA hBoundB
  rw [hTapesSelf] at hRes
  exact hRes

/-- One-step atom advancing a single tape `t` one cell to the right without changing its cell. -/
def stepRightAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) scanned (fun j => if j = t then .right else .stay)

theorem stepRightAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (contents : List SimSym) (pos : ℕ) (hBound : pos + 1 < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ ft,
      (stepRightAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft contents (pos + 1) := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using by omega
    · exact hOtherBounds j hj
  have hMove : moveOneSidedHead pos .right = some (pos + 1) := by simp [moveOneSidedHead]
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_keep .right hMove
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [stepRightAtom, mkWorkAction] using hUpdT
    · simp only [stepRightAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (stepRightAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH rfl hUpd rfl, hFT⟩

/-- Check `tRuler`: if `.bit true`, exit `true` (staying put); else write `.endMark`
on `tArgA` and `tArgB` (`.stay`) and exit `false`. -/
def rulerCheckOrEndAB (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5) (Exit := Bool)
    (fun _ scanned =>
      match scanned tRuler with
      | .bit true => mkWorkAction true scanned (fun _ => .stay)
      | _ => mkWorkAction false
          (fun j => if j = tArgA ∨ j = tArgB then .endMark else scanned j) (fun _ => .stay))

/-- Loop body for `writeRulerScaledOnes`: on each `.bit true` of `tRuler`, append `scale`
ones to `tArgA` and `tArgB` and advance `tRuler`; on `.endMark`, write `.endMark` on
`tArgA` and `tArgB` and exit. -/
def writeRulerScaledOnesBody (InputAlphabet : Type*) (scale : ℕ) :=
  (rulerCheckOrEndAB InputAlphabet).branch
    (((writeConstOnes InputAlphabet scale).seq (stepRightAtom InputAlphabet tRuler)).mapExit
      (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit)))
    (TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5)
      (Exit := Unit ⊕ Unit)
      (fun _ scanned => mkWorkAction (.inr ()) scanned (fun _ => .stay)))

def writeRulerScaledOnes (InputAlphabet : Type*) (scale : ℕ) :=
  (writeRulerScaledOnesBody InputAlphabet scale).loop

theorem writeRulerScaledOnes_reachesExit {InputAlphabet : Type*} {n : ℕ} (scale : ℕ)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pA pB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + S * scale < bound tArgA)
    (hBoundB : pB.length + S * scale < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) pA pA.length)
    (hMatchB : TapeMatches (initTapes tArgB) pB pB.length) :
    ∃ ftR ftA ftB,
      (writeRulerScaledOnes InputAlphabet scale).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) (1 + S) ∧
      TapeMatches ftA (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
        (pA.length + S * scale) ∧
      TapeMatches ftB (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
        (pB.length + S * scale) := by
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    ∃ done rem curA curB,
      done + rem = S ∧
      curA = pA ++ List.replicate (done * scale) (.bit true) ∧
      curB = pB ++ List.replicate (done * scale) (.bit true) ∧
      TapeMatches (tapes tRuler) rC (1 + done) ∧
      TapeMatches (tapes tArgA) curA curA.length ∧
      TapeMatches (tapes tArgB) curB curB.length
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (writeRulerScaledOnesBody InputAlphabet scale).ReachesExit input bound tapes ih
          (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧
        (S + 1 - (tapes' tRuler).head) < (S + 1 - (tapes tRuler).head)) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (writeRulerScaledOnesBody InputAlphabet scale).ReachesExit input bound tapes ih
          (.inr e) tapes' ih' ∧
        ih' = inHead ∧
        (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes' j = initTapes j) ∧
        TapeMatches (tapes' tRuler) rC (1 + S) ∧
        TapeMatches (tapes' tArgA) (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
          (pA.length + S * scale) ∧
        TapeMatches (tapes' tArgB) (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
          (pB.length + S * scale)) := by
    intro tapes ih ⟨hIh, hOth, done, rem, curA, curB, hSum, hCurA, hCurB, htR, htA, htB⟩
    subst ih
    have hCurALen : curA.length = pA.length + done * scale := by simp [hCurA]
    have hCurBLen : curB.length = pB.length + done * scale := by simp [hCurB]
    have hMulLe : done * scale + rem * scale = S * scale := by
      rw [← Nat.add_mul, hSum]
    have hHeads : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRuler
      · subst h1; simpa [htR.head_eq] using by omega
      · by_cases h2 : j = tArgA
        · subst h2; simpa [htA.head_eq, hCurALen] using by omega
        · by_cases h3 : j = tArgB
          · subst h3; simpa [htB.head_eq, hCurBLen] using by omega
          · rw [hOth j h1 h2 h3]; exact hOtherBounds j h1 h2 h3
    cases rem with
    | zero =>
      have hDone : done = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = S + 1 := by omega
        simp [rC, hIdx]
      obtain ⟨ntA, hUpdA, hMA⟩ := htA.update_append_move rfl .endMark .stay rfl
      obtain ⟨ntB, hUpdB, hMB⟩ := htB.update_append_move rfl .endMark .stay rfl
      let nextT := fun j => if j = tArgA then ntA else if j = tArgB then ntB else tapes j
      have hChk : (rulerCheckOrEndAB InputAlphabet).ReachesExit input bound tapes inHead
          false nextT inHead := by
        refine compStep_exit_override (rulerCheckOrEndAB InputAlphabet) input bound tapes nextT
          inHead false () hHeads
          (fun j => by
            by_cases h2 : j = tArgA
            · subst h2; simpa [nextT, hMA.head_eq, hCurALen, hDone] using hBoundA
            · by_cases h3 : j = tArgB
              · subst h3; simpa [nextT, h2, hMB.head_eq, hCurBLen, hDone] using hBoundB
              · simpa [nextT, h2, h3] using hHeads j)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction,
              nextT]
            by_cases h2 : j = tArgA
            · subst h2; simpa using hUpdA
            · by_cases h3 : j = tArgB
              · subst h3; simpa [h2] using hUpdB
              · simp only [h2, h3, ↓reduceIte]
                exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hNextH : ∀ j, (nextT j).head < bound j := by
        intro j
        by_cases h2 : j = tArgA
        · subst h2; simpa [nextT, hMA.head_eq, hCurALen, hDone] using hBoundA
        · by_cases h3 : j = tArgB
          · subst h3; simpa [nextT, h2, hMB.head_eq, hCurBLen, hDone] using hBoundB
          · simpa [nextT, h2, h3] using hHeads j
      have hExit := TMComponent.atom_reachesExit
        (fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound nextT inHead hNextH inHead (by simp [mkWorkAction, moveHead]) nextT
        (fun j => by
          simp only [mkWorkAction]
          exact OneSidedTape.updateAndMove_stay_self _)
        hNextH
      refine Or.inr ⟨(), nextT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound false hChk (by simpa [mkWorkAction] using hExit),
        rfl, fun j hj1 hj2 hj3 => by simp [nextT, hj2, hj3, hOth j hj1 hj2 hj3],
        ?_, ?_, ?_⟩
      · simpa [nextT, hNeRA, hNeRB, hDone] using htR
      · simpa [nextT, hCurA, hDone, List.append_assoc] using hMA
      · simpa [nextT, hCurB, hNeAB.symm, hDone, List.append_assoc] using hMB
    | succ r =>
      have hDoneLt : done < S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : (1 + done) = done + 1 := Nat.add_comm 1 done
        simp only [rC, hIdx, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left (by simp; exact hDoneLt)]
        simp
      have hChk : (rulerCheckOrEndAB InputAlphabet).ReachesExit input bound tapes inHead
          true tapes inHead := by
        refine compStep_exit_override (rulerCheckOrEndAB InputAlphabet) input bound tapes tapes
          inHead true () hHeads hHeads
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hScaleBoundA : curA.length + scale < bound tArgA := by
        have : 1 * scale ≤ (r + 1) * scale := Nat.mul_le_mul_right scale (by omega)
        omega
      have hScaleBoundB : curB.length + scale < bound tArgB := by
        have : 1 * scale ≤ (r + 1) * scale := Nat.mul_le_mul_right scale (by omega)
        omega
      obtain ⟨ftA, ftB, hWriteOnes, hFA, hFB⟩ := writeConstOnes_reachesExit scale input bound
        curA curB hScaleBoundA hScaleBoundB tapes inHead
        (fun j h1 h2 => hHeads j) htA htB
      let midT := fun j => if j = tArgA then ftA else if j = tArgB then ftB else tapes j
      have hMidR : TapeMatches (midT tRuler) rC (1 + done) := by
        simpa [midT, hNeRA, hNeRB] using htR
      obtain ⟨ftR, hStepR, hFR⟩ := stepRightAtom_reachesExit tRuler input bound rC (1 + done)
        (by omega) midT inHead (fun j hj => by
          by_cases h2 : j = tArgA
          · subst h2; simpa [midT, hFA.head_eq, hCurALen] using by omega
          · by_cases h3 : j = tArgB
            · subst h3; simpa [midT, h2, hFB.head_eq, hCurBLen] using by omega
            · simpa [midT, h2, h3] using hHeads j)
        hMidR
      have hSeq := TMComponent.mapExit_reachesExit _ (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit))
        input bound ((writeConstOnes InputAlphabet scale).seq_reachesExit
          (stepRightAtom InputAlphabet tRuler) input bound hWriteOnes hStepR)
      let finalT := fun j => if j = tRuler then ftR else midT j
      refine Or.inl ⟨finalT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound true hChk hSeq, ?_, ?_⟩
      · refine ⟨rfl, fun j hj1 hj2 hj3 => by simp [finalT, midT, hj1, hj2, hj3, hOth j hj1 hj2 hj3],
          done + 1, r, curA ++ List.replicate scale (.bit true), curB ++ List.replicate scale (.bit true),
          by omega, ?_, ?_, ?_,
          by simpa [finalT, midT, hNeRA.symm] using hFA,
          by simpa [finalT, midT, hNeRB.symm, hNeAB.symm] using hFB⟩
        · rw [hCurA, List.append_assoc, ← List.replicate_add]
          congr 2
          rw [Nat.succ_mul]
        · rw [hCurB, List.append_assoc, ← List.replicate_add]
          congr 2
          rw [Nat.succ_mul]
        · have : 1 + done + 1 = 1 + (done + 1) := by omega
          rw [← this]
          simpa [finalT] using hFR
      · simp [finalT, hFR.head_eq, htR.head_eq]
        omega
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun _ tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) rC (1 + S) ∧
    TapeMatches (tapes tArgA) (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
      (pA.length + S * scale) ∧
    TapeMatches (tapes tArgB) (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
      (pB.length + S * scale)
  have hInitInv : Inv initTapes inHead :=
    ⟨rfl, fun _ _ _ _ => rfl, 0, S, pA, pB, Nat.zero_add S, by simp, by simp, hMatchR, hMatchA, hMatchB⟩
  obtain ⟨e, finalTapes, finalInHead, hLoop, hIh, hOth, hFR, hFA, hFB⟩ :=
    TMComponent.loop_reachesExit (writeRulerScaledOnesBody InputAlphabet scale) input bound
      Inv (fun tapes _ => S + 1 - (tapes tRuler).head) Post hStep initTapes inHead hInitInv
  have hEqTapes : finalTapes = fun j => if j = tRuler then finalTapes tRuler
      else if j = tArgA then finalTapes tArgA
      else if j = tArgB then finalTapes tArgB else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1; rfl
    · by_cases h2 : j = tArgA
      · subst h2; simp [h1]
      · by_cases h3 : j = tArgB
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3, hOth j h1 h2 h3]
  rw [hEqTapes, hIh] at hLoop
  exact ⟨finalTapes tRuler, finalTapes tArgA, finalTapes tArgB, hLoop, hFR, hFA, hFB⟩

/-- Build `1^W` templates on `tArgA` and `tArgB` from `tRuler = 1^S`, restoring
`tRuler`, `tArgA`, and `tArgB` to head `1`. -/
def writeWidthOnes (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ)
    (InputAlphabet : Type*) :=
  (writeConstOnes InputAlphabet (qBits Q + 4)).seq
    ((writeRulerScaledOnes InputAlphabet (1 + k * (1 + gammaBits Γ))).seq
      ((rewindTape InputAlphabet tRuler).seq
        ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB))))

theorem configBitWidth_eq_linear (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    configBitWidth Q Γ k S = (qBits Q + 4) + S * (1 + k * (1 + gammaBits Γ)) := by
  unfold configBitWidth tapeBitWidth
  have h1 : k * (S + S * gammaBits Γ) = S * (k * (1 + gammaBits Γ)) := by
    calc
      k * (S + S * gammaBits Γ) = k * S + k * (S * gammaBits Γ) := Nat.mul_add _ _ _
      _ = S * k + S * (k * gammaBits Γ) := by rw [Nat.mul_comm k S, Nat.mul_left_comm k S]
      _ = S * (k + k * gammaBits Γ) := (Nat.mul_add _ _ _).symm
      _ = S * (k * (1 + gammaBits Γ)) := by rw [Nat.mul_add k 1 (gammaBits Γ), Nat.mul_one]
  have h2 : S + S * (k * (1 + gammaBits Γ)) = S * (1 + k * (1 + gammaBits Γ)) := by
    rw [Nat.mul_add S 1, Nat.mul_one]
  omega

theorem writeWidthOnes_reachesExit (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ)
    {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1) :
    ∃ ftR ftA ftB,
      (writeWidthOnes Q Γ k InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftA
        (.leftMark :: List.replicate (configBitWidth Q Γ k S) (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB
        (.leftMark :: List.replicate (configBitWidth Q Γ k S) (.bit true) ++ [.endMark]) 1 := by
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  let W := configBitWidth Q Γ k S
  have hW : W = (qBits Q + 4) + S * (1 + k * (1 + gammaBits Γ)) :=
    configBitWidth_eq_linear Q Γ k S
  obtain ⟨a₁, b₁, hConst, hMA₁, hMB₁⟩ := writeConstOnes_reachesExit (qBits Q + 4) input bound
    [.leftMark] [.leftMark] (by simp; omega) (by simp; omega) initTapes inHead
    (fun j h1 h2 => by
      by_cases hR : j = tRuler
      · subst hR; simpa [hMatchR.head_eq] using by omega
      · exact hOtherBounds j hR h1 h2)
    hMatchA hMatchB
  let t₁ := fun j => if j = tArgA then a₁ else if j = tArgB then b₁ else initTapes j
  have hT1R : TapeMatches (t₁ tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
    simpa [t₁, hNeRA, hNeRB] using hMatchR
  obtain ⟨r₂, a₂, b₂, hScaled, hMR₂, hMA₂, hMB₂⟩ := writeRulerScaledOnes_reachesExit
    (1 + k * (1 + gammaBits Γ)) input bound S
    ([.leftMark] ++ List.replicate (qBits Q + 4) (.bit true))
    ([.leftMark] ++ List.replicate (qBits Q + 4) (.bit true))
    hBoundR (by simp; omega) (by simp; omega) t₁ inHead
    (fun j hj1 hj2 hj3 => by simp [t₁, hj2, hj3, hOtherBounds j hj1 hj2 hj3])
    hT1R
    (by
      have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length =
          1 + (qBits Q + 4) := by simp; omega
      rw [hPos]
      simpa [t₁] using hMA₁)
    (by
      have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length =
          1 + (qBits Q + 4) := by simp; omega
      rw [hPos]
      simpa [t₁, hNeAB.symm] using hMB₁)
  let cR := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  let cW := SimSym.leftMark :: List.replicate W (.bit true) ++ [SimSym.endMark]
  have hNoLeftS : ∀ (M : ℕ) i, 1 ≤ i →
      i < (SimSym.leftMark :: List.replicate M (.bit true) ++ [SimSym.endMark]).length →
      (SimSym.leftMark :: List.replicate M (.bit true) ++ [SimSym.endMark])[i]? ≠
        some SimSym.leftMark := by
    intro M i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < M
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = M := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  have hW_A : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true) ++
      List.replicate (S * (1 + k * (1 + gammaBits Γ))) (SimSym.bit true) ++ [SimSym.endMark]) = cW := by
    rw [List.append_assoc [SimSym.leftMark], ← List.replicate_add]
    simp [cW, hW]
  have hMA₂' : TapeMatches a₂ cW (1 + W) := by
    have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length +
        S * (1 + k * (1 + gammaBits Γ)) = 1 + W := by
      simp [hW]; omega
    rw [hW_A, hPos] at hMA₂
    exact hMA₂
  have hMB₂' : TapeMatches b₂ cW (1 + W) := by
    have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length +
        S * (1 + k * (1 + gammaBits Γ)) = 1 + W := by
      simp [hW]; omega
    rw [hW_A, hPos] at hMB₂
    exact hMB₂
  let t₂ := fun j => if j = tRuler then r₂ else if j = tArgA then a₂
      else if j = tArgB then b₂ else t₁ j
  obtain ⟨rewR, hRewR, hFR, hRewROth⟩ := rewindTape_reachesExit tRuler input bound cR
    (by simp [cR]) rfl (hNoLeftS S) (by simp [cR]; exact hBoundR) t₂ inHead
    (fun j hj => by
      by_cases h2 : j = tArgA
      · subst h2; simpa [t₂, hj, hMA₂'.head_eq] using by omega
      · by_cases h3 : j = tArgB
        · subst h3; simpa [t₂, hj, h2, hMB₂'.head_eq] using by omega
        · simp [t₂, t₁, hj, h2, h3, hOtherBounds j hj h2 h3])
    (1 + S) (by omega) (by simp [cR]; omega) (by simpa [t₂, cR] using hMR₂)
  obtain ⟨rewA, hRewA, hFA, hRewAOth⟩ := rewindTape_reachesExit tArgA input bound cW
    (by simp [cW]) rfl (hNoLeftS W) (by simp [cW]; exact hBoundA) rewR inHead
    (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hFR.head_eq] using by omega
      · by_cases h3 : j = tArgB
        · subst h3; rw [hRewROth tArgB hNeRB.symm]
          simpa [t₂, hNeRA.symm, hNeRB.symm, hNeAB.symm, hMB₂'.head_eq] using by omega
        · rw [hRewROth j h1]; simp [t₂, t₁, h1, hj, h3, hOtherBounds j h1 hj h3])
    (1 + W) (by omega) (by simp [cW]; omega)
    (by rw [hRewROth tArgA hNeRA.symm]; simpa [t₂, hNeRA.symm] using hMA₂')
  obtain ⟨rewB, hRewB, hFB, hRewBOth⟩ := rewindTape_reachesExit tArgB input bound cW
    (by simp [cW]) rfl (hNoLeftS W) (by simp [cW]; exact hBoundB) rewA inHead
    (fun j hj => by
      by_cases h2 : j = tArgA
      · subst h2; simpa [hFA.head_eq] using by omega
      · by_cases h1 : j = tRuler
        · subst h1; rw [hRewAOth tRuler hNeRA]; simpa [hFR.head_eq] using by omega
        · rw [hRewAOth j h2, hRewROth j h1]
          simp [t₂, t₁, h1, h2, hj, hOtherBounds j h1 h2 hj])
    (1 + W) (by omega) (by simp [cW]; omega)
    (by
      rw [hRewAOth tArgB hNeAB.symm, hRewROth tArgB hNeRB.symm]
      simpa [t₂, hNeRA, hNeRB.symm, hNeAB.symm] using hMB₂')
  have hSeqAB := (rewindTape InputAlphabet tArgA).seq_reachesExit (rewindTape InputAlphabet tArgB)
    input bound hRewA hRewB
  have hSeqRAB := (rewindTape InputAlphabet tRuler).seq_reachesExit _ input bound hRewR hSeqAB
  have hSeqScaled := (writeRulerScaledOnes InputAlphabet (1 + k * (1 + gammaBits Γ))).seq_reachesExit
    _ input bound hScaled hSeqRAB
  have hSeqFull := (writeConstOnes InputAlphabet (qBits Q + 4)).seq_reachesExit
    _ input bound hConst hSeqScaled
  have hFinalEq : rewB = fun j => if j = tRuler then rewR tRuler
      else if j = tArgA then rewA tArgA
      else if j = tArgB then rewB tArgB else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1
      rw [hRewBOth tRuler hNeRB, hRewAOth tRuler hNeRA]
      simp
    · by_cases h2 : j = tArgA
      · subst h2
        rw [hRewBOth tArgA hNeAB]
        simp [h1]
      · by_cases h3 : j = tArgB
        · subst h3; simp [h1, h2]
        · rw [hRewBOth j h3, hRewAOth j h2, hRewROth j h1]
          simp [t₂, t₁, h1, h2, h3]
  rw [hFinalEq] at hSeqFull
  exact ⟨rewR tRuler, rewA tArgA, rewB tArgB, hSeqFull, hFR, hFA, hFB⟩

end SavitchLemma

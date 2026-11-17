module

public import SavitchLemma.Simulator.Loops

@[expose] public section

/-!
# Simulator transition checker

Implements the component that checks a serialized configuration transition.
-/

namespace SavitchLemma

/-! ## Step checker (`checkStep`): comparing `tArgA` and `tArgB` against `bitProblem` -/

def simBitVal : SimSym → Bool
  | .bit b => b
  | _ => false

/-- Copy `2 + S` (when `startIdx = 0`) or `S` (when `startIdx = 2`) bit pairs from
`tArgA`/`tArgB`, writing `tArgA`'s bits + `.endMark` onto `tScratch`, advancing
`tRuler`/`tArgA`/`tArgB`, and computing `BitRelState`. -/
def copyHeadBitsRel (InputAlphabet : Type*) (startIdx : Fin 3) :
    TMComponent (Fin 3 × BitRelState) InputAlphabet SimSym 5 BitRelState where
  start := (startIdx, BitRelState.init)
  step st _ scanned :=
    let bA := simBitVal (scanned tArgA)
    let bB := simBitVal (scanned tArgB)
    let st' := st.2.step bA bB
    match st.1.val with
    | 0 =>
      mkWorkAction (.inl (⟨1, by decide⟩, st'))
        (fun j => if j = tScratch then .bit bA else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
    | 1 =>
      mkWorkAction (.inl (⟨2, by decide⟩, st'))
        (fun j => if j = tScratch then .bit bA else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
    | _ =>
      match scanned tRuler with
      | .bit true =>
        mkWorkAction (.inl (⟨2, by decide⟩, st'))
          (fun j => if j = tScratch then .bit bA else scanned j)
          (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
      | _ =>
        mkWorkAction (.inr st.2)
          (fun j => if j = tScratch then .endMark else scanned j)
          (fun _ => .stay)

/-- Read `2 + S` (or `S`) head bits into `tScratch` + `BitRelState`, and rewind
`tRuler` and `tScratch` to cell `1`. -/
def readHeadBlock (InputAlphabet : Type*) (startIdx : Fin 3) :=
  bindComponent (copyHeadBitsRel InputAlphabet startIdx) fun rel =>
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch)).mapExit
      (fun _ => rel)

theorem copyHeadBitsRel_reachesExit {InputAlphabet : Type*} {n : ℕ} (startIdx : Fin 3)
    (hIdx : startIdx.val = 0 ∨ startIdx.val = 2)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pA uA sA pB uB sB : List SimSym) (ua ub : List Bool)
    (hUA : ua.length = (if startIdx.val = 0 then 2 else 0) + S)
    (hUB : ub.length = (if startIdx.val = 0 then 2 else 0) + S)
    (hUA_syms : uA = ua.map SimSym.bit) (hUB_syms : uB = ub.map SimSym.bit)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + ua.length < bound tArgA)
    (hBoundB : pB.length + ub.length < bound tArgB)
    (hBoundS : ua.length + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) (pA ++ uA ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB) (pB ++ uB ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ ftR ftA ftB ftS,
      (copyHeadBitsRel InputAlphabet startIdx).ReachesExit input bound initTapes inHead
        (BitRelState.init.runList ua ub)
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS
                  else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) (1 + S) ∧
      TapeMatches ftA (pA ++ uA ++ sA) (pA.length + ua.length) ∧
      TapeMatches ftB (pB ++ uB ++ sB) (pB.length + ub.length) ∧
      TapeMatches ftS (.leftMark :: uA ++ [.endMark]) (1 + ua.length) := by
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
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hScanRuler : ∀ rem done pA' pB' pS' uA' uB' st tR tA tB tS,
      done + rem = S →
      uA'.length = rem → uB'.length = rem →
      pA'.length + rem < bound tArgA →
      pB'.length + rem < bound tArgB →
      pS'.length + rem + 1 < bound tScratch →
      TapeMatches tR rC (1 + done) →
      TapeMatches tA (pA' ++ uA'.map SimSym.bit ++ sA) pA'.length →
      TapeMatches tB (pB' ++ uB'.map SimSym.bit ++ sB) pB'.length →
      TapeMatches tS pS' pS'.length →
      ∃ ftR ftA ftB ftS,
        Relation.ReflTransGen
          (fun a b => (copyHeadBitsRel InputAlphabet startIdx).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl (⟨2, by decide⟩, st), inHead,
            fun j => if j = tRuler then tR else if j = tArgA then tA
                      else if j = tArgB then tB else if j = tScratch then tS
                      else initTapes j⟩
          ⟨.inr (st.runList uA' uB'), inHead,
            fun j => if j = tRuler then ftR else if j = tArgA then ftA
                      else if j = tArgB then ftB else if j = tScratch then ftS
                      else initTapes j⟩ ∧
        TapeMatches ftR rC (1 + S) ∧
        TapeMatches ftA (pA' ++ uA'.map SimSym.bit ++ sA) (pA'.length + rem) ∧
        TapeMatches ftB (pB' ++ uB'.map SimSym.bit ++ sB) (pB'.length + rem) ∧
        TapeMatches ftS (pS' ++ uA'.map SimSym.bit ++ [.endMark]) (pS'.length + rem) := by
    intro rem
    induction rem with
    | zero =>
      intro done pA' pB' pS' uA' uB' st tR tA tB tS hSum hLA hLB hBA hBB hBS htR htA htB htS
      have hDone : done = S := by omega
      have hUA0 : uA' = [] := List.eq_nil_of_length_eq_zero hLA
      have hUB0 : uB' = [] := List.eq_nil_of_length_eq_zero hLB
      subst hUA0 hUB0
      have hReadR : tR.cells tR.head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdxD : 1 + done = S + 1 := by omega
        simp [rC, hIdxD]
      have hHeads : ∀ j,
          (if j = tRuler then tR else if j = tArgA then tA
            else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
            bound j := by
        intro j
        match j with
        | ⟨0, _⟩ => simpa [tRuler, htR.head_eq] using by omega
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using hBA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using hBB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
      obtain ⟨ftS, hUpdS, hFS⟩ := htS.update_append_move rfl .endMark .stay rfl
      let nextT := fun j => if j = tRuler then tR else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then ftS else initTapes j
      have hNextH : ∀ j, (nextT j).head < bound j := by
        intro j
        match j with
        | ⟨0, _⟩ => simpa [nextT, tRuler, htR.head_eq] using by omega
        | ⟨1, _⟩ => simpa [nextT, tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ => simpa [nextT, tRuler, tArgA, htA.head_eq] using hBA
        | ⟨3, _⟩ => simpa [nextT, tArgA, tArgB, htB.head_eq] using hBB
        | ⟨4, _⟩ => simpa [nextT, tRuler, tArgA, tArgB, tScratch, hFS.head_eq] using by omega
      have hStep1 := compStep_exit_override (copyHeadBitsRel InputAlphabet startIdx) input bound
        (fun j => if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j)
        nextT inHead (st.runList [] []) (⟨2, by decide⟩, st) hHeads hNextH
        (by simp [copyHeadBitsRel, mkWorkAction, moveHead, hReadR])
        (fun j => by
          simp only [copyHeadBitsRel, mkWorkAction, hReadR, nextT]
          match j with
          | ⟨0, _⟩ => simpa [tRuler, tScratch] using OneSidedTape.updateAndMove_stay_self tR
          | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
              OneSidedTape.updateAndMove_stay_self (initTapes 1)
          | ⟨2, _⟩ => simpa [tRuler, tArgA, tScratch] using OneSidedTape.updateAndMove_stay_self tA
          | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using OneSidedTape.updateAndMove_stay_self tB
          | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
        (by simp [copyHeadBitsRel, mkWorkAction, hReadR, BitRelState.runList])
      refine ⟨tR, tA, tB, ftS, by simpa [BitRelState.runList] using hStep1,
        by simpa [hDone] using htR, by simpa using htA, by simpa using htB, by simpa using hFS⟩
    | succ r ih =>
      intro done pA' pB' pS' uA' uB' st tR tA tB tS hSum hLA hLB hBA hBB hBS htR htA htB htS
      cases uA' with
      | nil => simp at hLA
      | cons a usA =>
        cases uB' with
        | nil => simp at hLB
        | cons b usB =>
          simp only [List.length_cons, Nat.succ.injEq] at hLA hLB
          have hDoneLt : done < S := by omega
          have hReadR : tR.cells tR.head = .bit true := by
            rw [htR.read_lt (by rw [hRC_len]; omega)]
            have hIdxD : 1 + done = done + 1 := Nat.add_comm 1 done
            simp only [rC, hIdxD, List.cons_append, List.getElem_cons_succ]
            rw [List.getElem_append_left (by simp; exact hDoneLt)]
            simp
          have hReadA : tA.cells tA.head = .bit a := by
            rw [htA.read_lt (by simp; omega)]
            simp [List.getElem_append_left (by simp : pA'.length < (pA' ++ SimSym.bit a :: (usA.map SimSym.bit ++ sA)).length)]
          have hReadB : tB.cells tB.head = .bit b := by
            rw [htB.read_lt (by simp; omega)]
            simp
          have hHeads : ∀ j,
              (if j = tRuler then tR else if j = tArgA then tA
                else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ => simpa [tRuler, htR.head_eq] using by omega
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using by omega
            | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using by omega
            | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
          obtain ⟨ntR, hUpdR, hNR⟩ := htR.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (.bit a)
          have hNextH : ∀ j,
              (if j = tRuler then ntR else if j = tArgA then ntA
                else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ => simpa [tRuler, hNR.head_eq] using by omega
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ => simpa [tRuler, tArgA, hNA.head_eq] using by omega
            | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, hNB.head_eq] using by omega
            | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using by omega
          have hNA' : TapeMatches ntA ((pA' ++ [.bit a]) ++ usA.map SimSym.bit ++ sA) (pA' ++ [.bit a]).length := by
            simpa [List.append_assoc] using hNA
          have hNB' : TapeMatches ntB ((pB' ++ [.bit b]) ++ usB.map SimSym.bit ++ sB) (pB' ++ [.bit b]).length := by
            simpa [List.append_assoc] using hNB
          obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ :=
            ih (done + 1) (pA' ++ [.bit a]) (pB' ++ [.bit b]) (pS' ++ [.bit a]) usA usB
              (st.step a b) ntR ntA ntB ntS (by omega) hLA hLB
              (by simp; omega) (by simp; omega) (by simp; omega) hNR hNA' hNB' (by simpa using hNS)
          have hStepEq :
              (copyHeadBitsRel InputAlphabet startIdx).step (⟨2, by decide⟩, st) (readInput input inHead)
                (fun j => (if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j).cells
                  (if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head) =
              mkWorkAction (.inl (⟨2, by decide⟩, st.step a b))
                (fun j => if j = tScratch then .bit a else
                  (if j = tRuler then tR else if j = tArgA then tA
                    else if j = tArgB then tB else if j = tScratch then tS else initTapes j).cells
                  (if j = tRuler then tR else if j = tArgA then tA
                    else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head)
                (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay) := by
            simp [copyHeadBitsRel, hReadR, hReadA, hReadB, simBitVal]
          refine ⟨ftR, ftA, ftB, ftS,
            compStep_head_override (copyHeadBitsRel InputAlphabet startIdx) input bound
              _ _ _ inHead inHead (st.runList (a :: usA) (b :: usB))
              (⟨2, by decide⟩, st) (⟨2, by decide⟩, st.step a b) hHeads hNextH
              (by rw [hStepEq]; simp [mkWorkAction, moveHead])
              (fun j => by
                rw [hStepEq]
                simp only [mkWorkAction]
                match j with
                | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdR
                | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
                    OneSidedTape.updateAndMove_stay_self (initTapes 1)
                | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
                | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
                | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
              (by rw [hStepEq]; rfl)
              (by simpa [BitRelState.runList] using hRest),
            hFR,
            by simpa [List.append_assoc, Nat.add_assoc] using hFA,
            by simpa [List.append_assoc, Nat.add_assoc] using hFB,
            by simpa [List.append_assoc, Nat.add_assoc] using hFS⟩
  have hStepOne : ∀ (kIdx : ℕ) (hk : kIdx = 0 ∨ kIdx = 1),
      ∀ a b uA' uB' pA' pB' pS' tA tB tS st,
        pA'.length + 1 + uA'.length < bound tArgA →
        pB'.length + 1 + uB'.length < bound tArgB →
        pS'.length + 1 + uA'.length + 1 < bound tScratch →
        TapeMatches tA (pA' ++ (.bit a :: uA'.map SimSym.bit) ++ sA) pA'.length →
        TapeMatches tB (pB' ++ (.bit b :: uB'.map SimSym.bit) ++ sB) pB'.length →
        TapeMatches tS pS' pS'.length →
        (initTapes tRuler).head < bound tRuler →
        ∃ ntA ntB ntS,
          Relation.ReflTransGen
            (fun x y => (copyHeadBitsRel InputAlphabet startIdx).CompStep input x y ∧
              (∀ j, (x.workTapes j).head < bound j) ∧
              (∀ j, (y.workTapes j).head < bound j))
            ⟨.inl (⟨kIdx, by omega⟩, st), inHead,
              fun j => if j = tRuler then initTapes tRuler else if j = tArgA then tA
                        else if j = tArgB then tB else if j = tScratch then tS else initTapes j⟩
            ⟨.inl (⟨kIdx + 1, by omega⟩, st.step a b), inHead,
              fun j => if j = tRuler then initTapes tRuler else if j = tArgA then ntA
                        else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j⟩ ∧
          TapeMatches ntA ((pA' ++ [.bit a]) ++ uA'.map SimSym.bit ++ sA) (pA' ++ [.bit a]).length ∧
          TapeMatches ntB ((pB' ++ [.bit b]) ++ uB'.map SimSym.bit ++ sB) (pB' ++ [.bit b]).length ∧
          TapeMatches ntS (pS' ++ [.bit a]) (pS' ++ [.bit a]).length := by
    intro kIdx hk a b uA' uB' pA' pB' pS' tA tB tS st hBA hBB hBS htA htB htS hTRB
    have hReadA : tA.cells tA.head = .bit a := by
      rw [htA.read_lt (by simp; omega)]
      simp [List.getElem_append_left]
    have hReadB : tB.cells tB.head = .bit b := by
      rw [htB.read_lt (by simp; omega)]
      simp [List.getElem_append_left]
    have hHeads : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using by omega
      | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using by omega
      | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
    obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right (by simp [moveOneSidedHead])
    obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right (by simp [moveOneSidedHead])
    obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (.bit a)
    have hNextH : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then ntA
          else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ => simpa [tRuler, tArgA, hNA.head_eq] using by omega
      | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, hNB.head_eq] using by omega
      | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using by omega
    have hNextFin : (⟨kIdx + 1, by omega⟩ : Fin 3) =
        if kIdx = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩ := by
      rcases hk with rfl | rfl <;> rfl
    refine ⟨ntA, ntB, ntS, Relation.ReflTransGen.single ⟨?_, hHeads, hNextH⟩,
      by simpa [List.append_assoc] using hNA,
      by simpa [List.append_assoc] using hNB,
      by simpa using hNS⟩
    refine ⟨(⟨kIdx, by omega⟩, st), rfl, ?_, inHead, ?_, rfl, ?_⟩
    · rcases hk with rfl | rfl <;>
        simp [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
    · rcases hk with rfl | rfl <;>
        simp [copyHeadBitsRel, mkWorkAction, moveHead]
    · intro j
      rcases hk with rfl | rfl
      · simp only [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
        match j with
        | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes tRuler)
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes 1)
        | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS
      · simp only [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
        match j with
        | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes tRuler)
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes 1)
        | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS
  have hTapesSelf :
      (fun j => if j = tRuler then initTapes tRuler else if j = tArgA then initTapes tArgA
        else if j = tArgB then initTapes tArgB else if j = tScratch then initTapes tScratch
        else initTapes j) = initTapes := by
    funext j; match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
  rcases hIdx with h0 | h2
  · have hStartFin : startIdx = ⟨0, by decide⟩ := Fin.ext h0
    subst startIdx
    simp only [↓reduceIte] at hUA hUB
    rcases ua with _ | ⟨a₀, _ | ⟨a₁, usA⟩⟩ <;> try (simp at hUA; omega)
    rcases ub with _ | ⟨b₀, _ | ⟨b₁, usB⟩⟩ <;> try (simp at hUB; omega)
    simp only [List.length_cons, Nat.succ.injEq] at hUA hUB
    have hTRB : (initTapes tRuler).head < bound tRuler := by simpa [hMatchR.head_eq] using by omega
    obtain ⟨a₂, b₂, s₂, hS0, hMA2, hMB2, hMS2⟩ := hStepOne 0 (Or.inl rfl) a₀ b₀ (a₁ :: usA) (b₁ :: usB)
      pA pB [.leftMark] (initTapes tArgA) (initTapes tArgB) (initTapes tScratch) BitRelState.init
      (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega) (by simp at hBoundS ⊢; omega)
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS hTRB
    obtain ⟨a₃, b₃, s₃, hS1, hMA3, hMB3, hMS3⟩ := hStepOne 1 (Or.inr rfl) a₁ b₁ usA usB
      (pA ++ [.bit a₀]) (pB ++ [.bit b₀]) [.leftMark, .bit a₀] a₂ b₂ s₂ (BitRelState.init.step a₀ b₀)
      (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega) (by simp at hBoundS ⊢; omega)
      hMA2 hMB2 hMS2 hTRB
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0
      (pA ++ [.bit a₀, .bit a₁]) (pB ++ [.bit b₀, .bit b₁]) [.leftMark, .bit a₀, .bit a₁]
      usA usB ((BitRelState.init.step a₀ b₀).step a₁ b₁) (initTapes tRuler) a₃ b₃ s₃
      (Nat.zero_add S) hUA hUB (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega)
      (by simp at hBoundS ⊢; omega) hMatchR (by simpa [List.append_assoc] using hMA3)
      (by simpa [List.append_assoc] using hMB3) hMS3
    have hRun : (copyHeadBitsRel InputAlphabet ⟨0, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList (a₀ :: a₁ :: usA) (b₀ :: b₁ :: usB))
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      change Relation.ReflTransGen _ ⟨.inl (⟨0, by decide⟩, BitRelState.init), inHead, initTapes⟩ _
      rw [← hTapesSelf]
      simpa [BitRelState.runList] using hS0.trans (hS1.trans hRest)
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · simpa [hUA_syms, List.append_assoc, Nat.add_assoc] using hFA
    · simpa [hUB_syms, List.append_assoc, Nat.add_assoc] using hFB
    · simpa [hUA_syms, List.append_assoc, Nat.add_assoc] using hFS
  · have hStartFin : startIdx = ⟨2, by decide⟩ := Fin.ext h2
    subst startIdx
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.zero_add] at hUA hUB
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0 pA pB [.leftMark]
      ua ub BitRelState.init (initTapes tRuler) (initTapes tArgA) (initTapes tArgB) (initTapes tScratch)
      (Nat.zero_add S) hUA hUB hBoundA hBoundB (by simp at hBoundS ⊢; omega) hMatchR
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS
    have hRun : (copyHeadBitsRel InputAlphabet ⟨2, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList ua ub)
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      change Relation.ReflTransGen _ ⟨.inl (⟨2, by decide⟩, BitRelState.init), inHead, initTapes⟩ _
      rw [← hTapesSelf]
      exact hRest
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · simpa [hUA_syms] using hFA
    · simpa [hUB_syms] using hFB
    · simpa [hUA_syms] using hFS

end SavitchLemma

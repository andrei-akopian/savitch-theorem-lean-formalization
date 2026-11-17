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

/-- On either of the two initialization states, consume one bit pair and advance
the index. -/
theorem copyHeadBitsRel_step_initial {InputAlphabet : Type*} (startIdx idx : Fin 3)
    (st : BitRelState) (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym)
    (a b : Bool) (hIdx : idx.val = 0 ∨ idx.val = 1)
    (hA : scanned tArgA = .bit a) (hB : scanned tArgB = .bit b) :
    (copyHeadBitsRel InputAlphabet startIdx).step (idx, st) inSym scanned =
      mkWorkAction (.inl (⟨idx.val + 1, by omega⟩, st.step a b))
        (fun j => if j = tScratch then .bit a else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay) := by
  rcases hIdx with h0 | h1
  · have hEq : idx = ⟨0, by decide⟩ := Fin.ext h0
    subst idx
    simp [copyHeadBitsRel, mkWorkAction, hA, hB, simBitVal]
  · have hEq : idx = ⟨1, by decide⟩ := Fin.ext h1
    subst idx
    simp [copyHeadBitsRel, mkWorkAction, hA, hB, simBitVal]

/-- On the ruler scan state, consume one bit pair while the ruler is on a true bit. -/
theorem copyHeadBitsRel_step_scan {InputAlphabet : Type*} (startIdx : Fin 3) (st : BitRelState)
    (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) (a b : Bool)
    (hA : scanned tArgA = .bit a) (hB : scanned tArgB = .bit b)
    (hR : scanned tRuler = .bit true) :
    (copyHeadBitsRel InputAlphabet startIdx).step (⟨2, by decide⟩, st) inSym scanned =
      mkWorkAction (.inl (⟨2, by decide⟩, st.step a b))
        (fun j => if j = tScratch then .bit a else scanned j)
        (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay) := by
  simp [copyHeadBitsRel, mkWorkAction, hA, hB, hR, simBitVal]

/-- When the ruler reaches its end marker, terminate and append the scratch end marker. -/
theorem copyHeadBitsRel_step_finish {InputAlphabet : Type*} (startIdx : Fin 3) (st : BitRelState)
    (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym)
    (hR : scanned tRuler ≠ .bit true) :
    (copyHeadBitsRel InputAlphabet startIdx).step (⟨2, by decide⟩, st) inSym scanned =
      mkWorkAction (.inr st) (fun j => if j = tScratch then .endMark else scanned j)
        (fun _ => .stay) := by
  cases hScan : scanned tRuler with
  | bit b =>
    cases b with
    | false => simp [copyHeadBitsRel, mkWorkAction, hScan]
    | true => exact False.elim (hR hScan)
  | blank => simp [copyHeadBitsRel, mkWorkAction, hScan]
  | leftMark => simp [copyHeadBitsRel, mkWorkAction, hScan]
  | tag b => simp [copyHeadBitsRel, mkWorkAction, hScan]
  | sep => simp [copyHeadBitsRel, mkWorkAction, hScan]
  | srcSep => simp [copyHeadBitsRel, mkWorkAction, hScan]
  | endMark => simp [copyHeadBitsRel, mkWorkAction, hScan]

/-- Read `2 + S` (or `S`) head bits into `tScratch` + `BitRelState`, and rewind
`tRuler` and `tScratch` to cell `1`. -/
def readHeadBlock (InputAlphabet : Type*) (startIdx : Fin 3) :=
  bindComponent (copyHeadBitsRel InputAlphabet startIdx) fun rel =>
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch)).mapExit
      (fun _ => rel)

/-- After the input-head bit block has been read, check whether its relation
summary witnesses the proposed input-head movement. The component leaves all
work tapes and the physical input head unchanged. -/
def checkInputHeadMove {InputAlphabet : Type*} (rel : BitRelState) (mv : TapeMove) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom fun inSym scanned =>
    mkWorkAction (relMatchesInputMove inSym rel mv) scanned (fun _ => .stay)

/-- The finite-state input-head movement check executes in one stationary step. -/
theorem checkInputHeadMove_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (rel : BitRelState) (mv : TapeMove) (input : Fin n → InputAlphabet)
    (bound : Fin 5 → ℕ) (tapes : Fin 5 → OneSidedTape SimSym)
    (inHead : Fin (n + 2)) (hHeads : ∀ j, (tapes j).head < bound j) :
    (checkInputHeadMove rel mv).ReachesExit input bound tapes inHead
      (relMatchesInputMove (readInput input inHead) rel mv) tapes inHead := by
  apply TMComponent.atom_reachesExit
    (f := fun inSym scanned =>
      mkWorkAction (relMatchesInputMove inSym rel mv) scanned (fun _ => .stay))
    input bound tapes inHead hHeads inHead
  · simp [mkWorkAction, moveHead]
  · intro j
    exact OneSidedTape.updateAndMove_stay_self (tapes j)
  · exact hHeads

/-- Read an encoded input-head pair, then return whether it matches the given
machine movement. -/
def readHeadBlockCheckInputMove (InputAlphabet : Type*) (startIdx : Fin 3)
    (mv : TapeMove) :=
  bindComponent (readHeadBlock InputAlphabet startIdx) fun rel =>
    checkInputHeadMove rel mv

/-- Correctness of the reader followed by the input-head movement check. The
returned Boolean is true exactly when the encoded destination is the result of
the proposed bounded input-head move. -/
theorem readHeadBlockCheckInputMove_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (startIdx : Fin 3) (mv : TapeMove) (input : Fin n → InputAlphabet)
    (bound : Fin 5 → ℕ) (inHead : Fin (n + 2)) (h₂val : ℕ)
    (ua ub : List Bool) (hLen : ua.length = ub.length)
    (hU : bitsToNat ua = inHead.val) (hV : bitsToNat ub = h₂val)
    {tapes₀ tapes₁ : Fin 5 → OneSidedTape SimSym}
    (hRead : (readHeadBlock InputAlphabet startIdx).ReachesExit input bound
      tapes₀ inHead (BitRelState.init.runList ua ub) tapes₁ inHead)
    (hHeads : ∀ j, (tapes₁ j).head < bound j) :
    (readHeadBlockCheckInputMove InputAlphabet startIdx mv).ReachesExit input bound
      tapes₀ inHead
      (relMatchesInputMove (readInput input inHead)
        (BitRelState.init.runList ua ub) mv) tapes₁ inHead ∧
    (relMatchesInputMove (readInput input inHead)
      (BitRelState.init.runList ua ub) mv = true ↔
      ∃ h₂ : Fin (n + 2), moveHead (n + 2) inHead mv = some h₂ ∧ h₂.val = h₂val) := by
  have hCheck := checkInputHeadMove_reachesExit
    (BitRelState.init.runList ua ub) mv input bound tapes₁ inHead hHeads
  have hRun := bindComponent_reachesExit
    (readHeadBlock InputAlphabet startIdx)
    (fun rel => checkInputHeadMove rel mv) input bound hRead hCheck
  refine ⟨?_, ?_⟩
  · simpa [readHeadBlockCheckInputMove] using hRun
  · exact relMatchesInputMove_iff input inHead h₂val ua ub hLen hU hV mv

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
  have hScanRuler :
      ∀ (rem done : ℕ) (pA' pB' pS' : List SimSym) (uA' uB' : List Bool)
        (st : BitRelState) (tR tA tB tS : OneSidedTape SimSym),
      done + rem = S →
      uA'.length = rem → uB'.length = rem →
      pA'.length + rem < bound tArgA →
      pB'.length + rem < bound tArgB →
      pS'.length + rem < bound tScratch →
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
        | ⟨0, _⟩ =>
            simpa [tRuler, htR.head_eq] using (show 1 + done < bound tRuler by omega)
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ =>
            simpa [tRuler, tArgA, htA.head_eq] using (show pA'.length < bound tArgA by omega)
        | ⟨3, _⟩ =>
            simpa [tRuler, tArgA, tArgB, htB.head_eq] using
              (show pB'.length < bound tArgB by omega)
        | ⟨4, _⟩ =>
            simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using
              (show pS'.length < bound tScratch by omega)
      obtain ⟨ftS, hUpdS, hFS⟩ := htS.update_append_move rfl .endMark .stay rfl
      let nextT := fun j => if j = tRuler then tR else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then ftS else initTapes j
      have hNextH : ∀ j, (nextT j).head < bound j := by
        intro j
        match j with
        | ⟨0, _⟩ =>
            simpa [nextT, tRuler, htR.head_eq] using (show 1 + done < bound tRuler by omega)
        | ⟨1, _⟩ => simpa [nextT, tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ =>
            simpa [nextT, tRuler, tArgA, htA.head_eq] using
              (show pA'.length < bound tArgA by omega)
        | ⟨3, _⟩ =>
            simpa [nextT, tRuler, tArgA, tArgB, htB.head_eq] using
              (show pB'.length < bound tArgB by omega)
        | ⟨4, _⟩ =>
            simpa [nextT, tRuler, tArgA, tArgB, tScratch, hFS.head_eq] using
              (show pS'.length < bound tScratch by omega)
      let startTapes := fun j =>
        if j = tRuler then tR else if j = tArgA then tA
        else if j = tArgB then tB else if j = tScratch then tS else initTapes j
      let scannedStart := fun j => (startTapes j).cells (startTapes j).head
      have hRulerEnd : scannedStart tRuler ≠ SimSym.bit true := by
        simp [scannedStart, startTapes, tRuler, tArgA, tArgB, tScratch, hReadR]
      have hFinish := copyHeadBitsRel_step_finish startIdx st
        (readInput input inHead) scannedStart hRulerEnd
      have hStep1 := compStep_exit_override (copyHeadBitsRel InputAlphabet startIdx) input bound
        startTapes nextT inHead (st.runList [] []) (⟨2, by decide⟩, st) hHeads hNextH
        (by rw [hFinish]; simp [mkWorkAction, moveHead])
        (fun j => by
          rw [hFinish]
          simp only [mkWorkAction, startTapes, scannedStart, nextT,
            tRuler, tArgA, tArgB, tScratch]
          match j with
          | ⟨0, _⟩ => simpa [tRuler, tScratch] using OneSidedTape.updateAndMove_stay_self tR
          | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
              OneSidedTape.updateAndMove_stay_self (initTapes 1)
          | ⟨2, _⟩ => simpa [tRuler, tArgA, tScratch] using OneSidedTape.updateAndMove_stay_self tA
          | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using OneSidedTape.updateAndMove_stay_self tB
          | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
        (by rw [hFinish]; simp [mkWorkAction, BitRelState.runList])
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
            have hIndex : pA'.length < (pA' ++ List.map SimSym.bit (a :: usA) ++ sA).length := by
              simp
            rw [htA.read_lt hIndex]
            simp
          have hReadB : tB.cells tB.head = .bit b := by
            have hIndex : pB'.length < (pB' ++ List.map SimSym.bit (b :: usB) ++ sB).length := by
              simp
            rw [htB.read_lt hIndex]
            simp
          have hHeads : ∀ j,
              (if j = tRuler then tR else if j = tArgA then tA
                else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ =>
                simpa [tRuler, htR.head_eq] using (show 1 + done < bound tRuler by omega)
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ =>
                simpa [tRuler, tArgA, htA.head_eq] using
                  (show pA'.length < bound tArgA by omega)
            | ⟨3, _⟩ =>
                simpa [tRuler, tArgA, tArgB, htB.head_eq] using
                  (show pB'.length < bound tArgB by omega)
            | ⟨4, _⟩ =>
                simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using
                  (show pS'.length < bound tScratch by omega)
          obtain ⟨ntR, hUpdR, hNR⟩ := htR.update_keep .right
            (nextPos := 1 + (done + 1)) (by simp [moveOneSidedHead, Nat.add_assoc])
          obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right
            (nextPos := pA'.length + 1) (by simp [moveOneSidedHead])
          obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right
            (nextPos := pB'.length + 1) (by simp [moveOneSidedHead])
          obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (.bit a)
          have hNextH : ∀ j,
              (if j = tRuler then ntR else if j = tArgA then ntA
                else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ =>
                simpa [tRuler, hNR.head_eq] using
                  (show 1 + (done + 1) < bound tRuler by omega)
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ =>
                simpa [tRuler, tArgA, hNA.head_eq] using
                  (show pA'.length + 1 < bound tArgA by omega)
            | ⟨3, _⟩ =>
                simpa [tRuler, tArgA, tArgB, hNB.head_eq] using
                  (show pB'.length + 1 < bound tArgB by omega)
            | ⟨4, _⟩ =>
                simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using
                  (show pS'.length + 1 < bound tScratch by omega)
          have hNA' : TapeMatches ntA
              ((pA' ++ [SimSym.bit a]) ++ usA.map SimSym.bit ++ sA)
              (pA' ++ [SimSym.bit a]).length := by
            simpa [List.append_assoc] using hNA
          have hNB' : TapeMatches ntB
              ((pB' ++ [SimSym.bit b]) ++ usB.map SimSym.bit ++ sB)
              (pB' ++ [SimSym.bit b]).length := by
            simpa [List.append_assoc] using hNB
          obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ :=
            ih (done + 1) (pA' ++ [.bit a]) (pB' ++ [.bit b]) (pS' ++ [.bit a]) usA usB
              (st.step a b) ntR ntA ntB ntS (by omega) hLA hLB
              (by simp; omega) (by simp; omega) (by simp; omega) hNR hNA' hNB' (by simpa using hNS)
          let tapesAt := fun j =>
            if j = tRuler then tR else if j = tArgA then tA
            else if j = tArgB then tB else if j = tScratch then tS else initTapes j
          let scannedAt := fun j => (tapesAt j).cells (tapesAt j).head
          have hScanA : scannedAt tArgA = SimSym.bit a := by
            simpa [scannedAt, tapesAt, tRuler, tArgA, tArgB, tScratch] using hReadA
          have hScanB : scannedAt tArgB = SimSym.bit b := by
            simpa [scannedAt, tapesAt, tRuler, tArgA, tArgB, tScratch] using hReadB
          have hScanR : scannedAt tRuler = SimSym.bit true := by
            simpa [scannedAt, tapesAt, tRuler, tArgA, tArgB, tScratch] using hReadR
          have hStepEq :
              (copyHeadBitsRel InputAlphabet startIdx).step (⟨2, by decide⟩, st)
                (readInput input inHead) scannedAt =
              mkWorkAction (.inl (⟨2, by decide⟩, st.step a b))
                (fun j => if j = tScratch then .bit a else scannedAt j)
                (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay) :=
            copyHeadBitsRel_step_scan startIdx st (readInput input inHead) scannedAt a b
              hScanA hScanB hScanR
          refine ⟨ftR, ftA, ftB, ftS,
            compStep_head_override (copyHeadBitsRel InputAlphabet startIdx) input bound
              tapesAt _ _ inHead inHead (st.runList (a :: usA) (b :: usB))
              (⟨2, by decide⟩, st) (⟨2, by decide⟩, st.step a b) hHeads hNextH
              (by rw [hStepEq]; simp [mkWorkAction, moveHead])
              (fun j => by
                rw [hStepEq]
                simp only [mkWorkAction, tapesAt, scannedAt,
                  tRuler, tArgA, tArgB, tScratch]
                match j with
                | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdR
                | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
                    OneSidedTape.updateAndMove_stay_self (initTapes 1)
                | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
                | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
                | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
              (by rw [hStepEq]; rfl)
              (by simpa [BitRelState.runList] using hRest),
            hFR, ?_, ?_, ?_⟩
          · have hIndex : pA'.length + 1 + r = pA'.length + (r + 1) := by omega
            rw [← hIndex]
            simpa [List.append_assoc, List.length_append] using hFA
          · have hIndex : pB'.length + 1 + r = pB'.length + (r + 1) := by omega
            rw [← hIndex]
            simpa [List.append_assoc, List.length_append] using hFB
          · have hIndex : pS'.length + 1 + r = pS'.length + (r + 1) := by omega
            rw [← hIndex]
            simpa [List.append_assoc, List.length_append] using hFS
  have hStepOne : ∀ (kIdx : ℕ) (hk : kIdx = 0 ∨ kIdx = 1),
      ∀ (a b : Bool) (uA' uB' : List Bool) (pA' pB' pS' : List SimSym)
        (tA tB tS : OneSidedTape SimSym) (st : BitRelState),
        pA'.length + 1 + uA'.length < bound tArgA →
        pB'.length + 1 + uB'.length < bound tArgB →
        pS'.length + 1 + uA'.length < bound tScratch →
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
          TapeMatches ntA ((pA' ++ [SimSym.bit a]) ++ uA'.map SimSym.bit ++ sA)
            (pA' ++ [SimSym.bit a]).length ∧
          TapeMatches ntB ((pB' ++ [SimSym.bit b]) ++ uB'.map SimSym.bit ++ sB)
            (pB' ++ [SimSym.bit b]).length ∧
          TapeMatches ntS (pS' ++ [SimSym.bit a]) (pS' ++ [SimSym.bit a]).length := by
    intro kIdx hk a b uA' uB' pA' pB' pS' tA tB tS st hBA hBB hBS htA htB htS hTRB
    have hReadA : tA.cells tA.head = SimSym.bit a := by
      have hIndex : pA'.length <
          (pA' ++ List.map SimSym.bit (a :: uA') ++ sA).length := by simp
      rw [htA.read_lt hIndex]
      simp
    have hReadB : tB.cells tB.head = SimSym.bit b := by
      have hIndex : pB'.length <
          (pB' ++ List.map SimSym.bit (b :: uB') ++ sB).length := by simp
      rw [htB.read_lt hIndex]
      simp
    have hHeads : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ =>
          simpa [tRuler, tArgA, htA.head_eq] using (show pA'.length < bound tArgA by omega)
      | ⟨3, _⟩ =>
          simpa [tRuler, tArgA, tArgB, htB.head_eq] using (show pB'.length < bound tArgB by omega)
      | ⟨4, _⟩ =>
          simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using
            (show pS'.length < bound tScratch by omega)
    obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right
      (nextPos := pA'.length + 1) (by simp [moveOneSidedHead])
    obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right
      (nextPos := pB'.length + 1) (by simp [moveOneSidedHead])
    obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (SimSym.bit a)
    have hNextH : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then ntA
          else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ =>
          simpa [tRuler, tArgA, hNA.head_eq] using
            (show pA'.length + 1 < bound tArgA by omega)
      | ⟨3, _⟩ =>
          simpa [tRuler, tArgA, tArgB, hNB.head_eq] using
            (show pB'.length + 1 < bound tArgB by omega)
      | ⟨4, _⟩ =>
          simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using
            (show pS'.length + 1 < bound tScratch by omega)
    have hNextFin : (⟨kIdx + 1, by omega⟩ : Fin 3) =
        if kIdx = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩ := by
      rcases hk with rfl | rfl <;> rfl
    let sourceTapes := fun j =>
      if j = tRuler then initTapes tRuler else if j = tArgA then tA
      else if j = tArgB then tB else if j = tScratch then tS else initTapes j
    let sourceCfg : OneSidedTMConfig ((Fin 3 × BitRelState) ⊕ BitRelState) SimSym 5 n :=
      ⟨.inl (⟨kIdx, by omega⟩, st), inHead, sourceTapes⟩
    have hScanA : sourceCfg.scannedWork tArgA = SimSym.bit a := by
      simpa [sourceCfg, OneSidedTMConfig.scannedWork, sourceTapes,
        tRuler, tArgA, tArgB, tScratch] using hReadA
    have hScanB : sourceCfg.scannedWork tArgB = SimSym.bit b := by
      simpa [sourceCfg, OneSidedTMConfig.scannedWork, sourceTapes,
        tRuler, tArgA, tArgB, tScratch] using hReadB
    have hIdx : (⟨kIdx, by omega⟩ : Fin 3).val = 0 ∨
        (⟨kIdx, by omega⟩ : Fin 3).val = 1 := by simpa using hk
    have hAction := copyHeadBitsRel_step_initial startIdx ⟨kIdx, by omega⟩ st
      (readInput input inHead) sourceCfg.scannedWork a b hIdx hScanA hScanB
    refine ⟨ntA, ntB, ntS, Relation.ReflTransGen.single ⟨?_, hHeads, hNextH⟩,
      by simpa [List.append_assoc] using hNA,
      by simpa [List.append_assoc] using hNB,
      by simpa [List.append_assoc] using hNS⟩
    refine ⟨(⟨kIdx, by omega⟩, st), rfl, ?_, inHead, ?_, rfl, ?_⟩
    · simpa [mkWorkAction] using (congrArg TMAction.nextState hAction).symm
    · rw [hAction]
      simp [mkWorkAction, moveHead]
    · intro j
      rw [hAction]
      simp only [mkWorkAction, sourceCfg, OneSidedTMConfig.scannedWork, sourceTapes,
        tRuler, tArgA, tArgB, tScratch]
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
    simp only [List.length_cons] at hUA hUB
    have hUsALen : usA.length = S := by omega
    have hUsBLen : usB.length = S := by omega
    have hBoundAFull : pA.length + (S + 2) < bound tArgA := by
      have hA := hBoundA
      simp only [List.length_cons] at hA
      omega
    have hBoundBFull : pB.length + (S + 2) < bound tArgB := by
      have hB := hBoundB
      simp only [List.length_cons] at hB
      omega
    have hBoundScratch : S + 4 ≤ bound tScratch := by
      have hS := hBoundS
      simp only [List.length_cons] at hS
      omega
    have hBoundScratchStrict : S + 3 < bound tScratch := by omega
    have hTailALen : (a₁ :: usA).length = S + 1 := by simp [hUsALen]
    have hBoundAFirst : pA.length + 1 + (a₁ :: usA).length < bound tArgA := by
      simp only [List.length_cons]
      omega
    have hBoundBFirst : pB.length + 1 + (b₁ :: usB).length < bound tArgB := by
      simp only [List.length_cons]
      omega
    have hBoundASecond : (pA ++ [SimSym.bit a₀]).length + 1 + usA.length <
        bound tArgA := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hBoundBSecond : (pB ++ [SimSym.bit b₀]).length + 1 + usB.length <
        bound tArgB := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hBoundScratchFirst : ([SimSym.leftMark] : List SimSym).length + 1 +
        (a₁ :: usA).length < bound tScratch := by
      rw [hTailALen]
      simp only [List.length_cons, List.length_nil]
      omega
    have hBoundScratchSecond :
        ([SimSym.leftMark, SimSym.bit a₀] : List SimSym).length + 1 + usA.length <
          bound tScratch := by
      rw [hUsALen]
      simp only [List.length_cons, List.length_nil]
      omega
    have hTRB : (initTapes tRuler).head < bound tRuler := by
      simpa [hMatchR.head_eq] using (show 1 < bound tRuler by omega)
    obtain ⟨a₂, b₂, s₂, hS0, hMA2, hMB2, hMS2⟩ := hStepOne 0 (Or.inl rfl) a₀ b₀ (a₁ :: usA) (b₁ :: usB)
      pA pB [.leftMark] (initTapes tArgA) (initTapes tArgB) (initTapes tScratch) BitRelState.init
        hBoundAFirst hBoundBFirst hBoundScratchFirst
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS hTRB
    obtain ⟨a₃, b₃, s₃, hS1, hMA3, hMB3, hMS3⟩ := hStepOne 1 (Or.inr rfl) a₁ b₁ usA usB
      (pA ++ [.bit a₀]) (pB ++ [.bit b₀]) [.leftMark, .bit a₀] a₂ b₂ s₂ (BitRelState.init.step a₀ b₀)
        hBoundASecond hBoundBSecond hBoundScratchSecond
        hMA2 hMB2 hMS2 hTRB
    have hUaLen : (a₀ :: a₁ :: usA).length = 2 + S := by
      simp [hUsALen]
      omega
    have hUbLen : (b₀ :: b₁ :: usB).length = 2 + S := by
      simp [hUsBLen]
      omega
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0
       (pA ++ [.bit a₀, .bit a₁]) (pB ++ [.bit b₀, .bit b₁]) [.leftMark, .bit a₀, .bit a₁]
       usA usB ((BitRelState.init.step a₀ b₀).step a₁ b₁) (initTapes tRuler) a₃ b₃ s₃
        (Nat.zero_add S) hUsALen hUsBLen
         (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
         (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
         (by simp only [List.length_cons, List.length_nil]; omega) hMatchR
        (by simpa [List.append_assoc] using hMA3)
        (by simpa [List.append_assoc] using hMB3) hMS3
    have hRun : (copyHeadBitsRel InputAlphabet ⟨0, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList (a₀ :: a₁ :: usA) (b₀ :: b₁ :: usB))
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      have hStart : (copyHeadBitsRel InputAlphabet ⟨0, by decide⟩).start =
          (⟨0, by decide⟩, BitRelState.init) := rfl
      dsimp only [TMComponent.ReachesExit]
      simpa only [hStart, hTapesSelf, BitRelState.runList, List.zip_cons_cons,
        List.foldl_cons] using hS0.trans (hS1.trans hRest)
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · have hContent : pA ++ uA ++ sA =
        pA ++ [SimSym.bit a₀, SimSym.bit a₁] ++ List.map SimSym.bit usA ++ sA := by
        simp [hUA_syms, List.map_cons]
      have hIndex : pA.length + (a₀ :: a₁ :: usA).length = pA.length + (2 + S) := by
        rw [hUaLen]
      rw [hIndex, hContent]
      have hTapeIndex : (pA ++ [SimSym.bit a₀, SimSym.bit a₁]).length + S =
          pA.length + (2 + S) := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [← hTapeIndex]
      exact hFA
    · have hContent : pB ++ uB ++ sB =
        pB ++ [SimSym.bit b₀, SimSym.bit b₁] ++ List.map SimSym.bit usB ++ sB := by
        simp [hUB_syms, List.map_cons, List.append_assoc]
      have hIndex : pB.length + (b₀ :: b₁ :: usB).length = pB.length + (2 + S) := by
        rw [hUbLen]
      rw [hIndex, hContent]
      have hTapeIndex : (pB ++ [SimSym.bit b₀, SimSym.bit b₁]).length + S =
          pB.length + (2 + S) := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [← hTapeIndex]
      exact hFB
    · have hContent : SimSym.leftMark :: uA ++ [SimSym.endMark] =
        SimSym.leftMark :: [SimSym.bit a₀, SimSym.bit a₁] ++
          List.map SimSym.bit usA ++ [SimSym.endMark] := by
        simp [hUA_syms, List.map_cons]
      have hIndex : 1 + (a₀ :: a₁ :: usA).length = 1 + (2 + S) := by rw [hUaLen]
      rw [hIndex, hContent]
      have hTapeIndex : ([SimSym.leftMark, SimSym.bit a₀, SimSym.bit a₁]).length + S =
          1 + (2 + S) := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [← hTapeIndex]
      exact hFS
  · have hStartFin : startIdx = ⟨2, by decide⟩ := Fin.ext h2
    subst startIdx
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.zero_add] at hUA hUB
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0 pA pB [.leftMark]
      ua ub BitRelState.init (initTapes tRuler) (initTapes tArgA) (initTapes tArgB) (initTapes tScratch)
       (Nat.zero_add S) hUA hUB
       (by simpa [hUA] using hBoundA) (by simpa [hUB] using hBoundB)
       (by simp at hBoundS ⊢; omega) hMatchR
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS
    have hRun : (copyHeadBitsRel InputAlphabet ⟨2, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList ua ub)
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      have hStart : (copyHeadBitsRel InputAlphabet ⟨2, by decide⟩).start =
          (⟨2, by decide⟩, BitRelState.init) := rfl
      dsimp only [TMComponent.ReachesExit]
      simpa only [hStart, hTapesSelf] using hRest
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · simpa [hUA_syms, hUA] using hFA
    · simpa [hUB_syms, hUB] using hFB
    · simpa [hUA_syms, hUA] using hFS

/-- A serialized bit block and its end marker contain no further left marker. -/
private theorem bitListContent_no_leftMark (bits : List Bool) (i : ℕ)
    (hPos : 1 ≤ i)
    (hLt : i < (SimSym.leftMark :: (bits.map SimSym.bit ++ [SimSym.endMark])).length) :
    (SimSym.leftMark :: (bits.map SimSym.bit ++ [SimSym.endMark]))[i]? ≠
      some SimSym.leftMark := by
  cases i with
  | zero => omega
  | succ i =>
    have hTailLt : i < (bits.map SimSym.bit ++ [SimSym.endMark]).length := by
      simp only [List.length_cons] at hLt
      omega
    simp only [List.getElem?_cons_succ]
    by_cases hBit : i < (bits.map SimSym.bit).length
    · rw [List.getElem?_append_left hBit, List.getElem?_eq_getElem hBit]
      simp
    · have hEq : i = (bits.map SimSym.bit).length := by
        have hLt' : i < (bits.map SimSym.bit).length + 1 := by
          simpa only [List.length_append, List.length_singleton] using hTailLt
        omega
      subst i
      rw [List.getElem?_append_right (by simp)]
      simp

/-- Copy a configuration bit block into scratch, then restore the ruler and
scratch heads to their left markers. -/
theorem readHeadBlock_reachesExit {InputAlphabet : Type*} {n : ℕ} (startIdx : Fin 3)
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
      (SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) (pA ++ uA ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB) (pB ++ uB ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [SimSym.leftMark] 1) :
    ∃ finalTapes,
      (readHeadBlock InputAlphabet startIdx).ReachesExit input bound initTapes inHead
        (BitRelState.init.runList ua ub) finalTapes inHead ∧
      TapeMatches (finalTapes tRuler)
        (SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]) 1 ∧
      TapeMatches (finalTapes tArgA) (pA ++ uA ++ sA) (pA.length + ua.length) ∧
      TapeMatches (finalTapes tArgB) (pB ++ uB ++ sB) (pB.length + ub.length) ∧
      TapeMatches (finalTapes tScratch) (SimSym.leftMark :: uA ++ [SimSym.endMark]) 1 := by
  rcases copyHeadBitsRel_reachesExit startIdx hIdx input bound S pA uA sA pB uB sB ua ub
      hUA hUB hUA_syms hUB_syms hBoundR hBoundA hBoundB hBoundS initTapes inHead hOther
      hMatchR hMatchA hMatchB hMatchS with
    ⟨ftR, ftA, ftB, ftS, hCopyRun, hCR, hCA, hCB, hCS⟩
  let copiedTapes := fun j =>
    if j = tRuler then ftR else if j = tArgA then ftA
    else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j
  let rulerBits := List.replicate S true
  let rulerContents := SimSym.leftMark :: (rulerBits.map SimSym.bit ++ [SimSym.endMark])
  let scratchContents := SimSym.leftMark :: (ua.map SimSym.bit ++ [SimSym.endMark])
  have hCopiedR : TapeMatches (copiedTapes tRuler) rulerContents (1 + S) := by
    simpa [copiedTapes, rulerContents, rulerBits, tRuler, tArgA, tArgB, tScratch,
      List.map_replicate, List.cons_append] using hCR
  have hCopiedA : TapeMatches (copiedTapes tArgA) (pA ++ uA ++ sA)
      (pA.length + ua.length) := by
    simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCA
  have hCopiedB : TapeMatches (copiedTapes tArgB) (pB ++ uB ++ sB)
      (pB.length + ub.length) := by
    simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCB
  have hCopiedS : TapeMatches (copiedTapes tScratch) scratchContents (1 + ua.length) := by
    simpa [copiedTapes, scratchContents, tRuler, tArgA, tArgB, tScratch,
      hUA_syms, List.append_assoc] using hCS
  have hRulerBound : rulerContents.length ≤ bound tRuler := by
    simpa [rulerContents, rulerBits, List.map_replicate, List.length_append] using hBoundR
  have hScratchBound : scratchContents.length ≤ bound tScratch := by
    simpa [scratchContents, List.length_append] using hBoundS
  have hCopyHeads : ∀ j, j ≠ tRuler → (copiedTapes j).head < bound j := by
    intro j hNeR
    match j with
    | ⟨0, _⟩ => exact False.elim (hNeR rfl)
    | ⟨1, _⟩ =>
        change (initTapes tRegs).head < bound tRegs
        exact hOther
    | ⟨2, _⟩ =>
        change ftA.head < bound tArgA
        have hHeadA : ftA.head = pA.length + ua.length := by
          simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCopiedA.head_eq
        rw [hHeadA]
        exact hBoundA
    | ⟨3, _⟩ =>
        change ftB.head < bound tArgB
        have hHeadB : ftB.head = pB.length + ub.length := by
          simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCopiedB.head_eq
        rw [hHeadB]
        exact hBoundB
    | ⟨4, _⟩ =>
        change ftS.head < bound tScratch
        have hHeadS : ftS.head = 1 + ua.length := by
          simpa [copiedTapes, scratchContents, tRuler, tArgA, tArgB, tScratch] using
            hCopiedS.head_eq
        rw [hHeadS]
        omega
  have hRulerNoLeft : ∀ i, 1 ≤ i → i < rulerContents.length →
      rulerContents[i]? ≠ some SimSym.leftMark := by
    intro i hi hiLt
    exact bitListContent_no_leftMark rulerBits i hi (by
      simpa [rulerContents, rulerBits] using hiLt)
  have hRewindR := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
    rulerContents (by simp [rulerContents, rulerBits]) (by simp [rulerContents, rulerBits])
    hRulerNoLeft hRulerBound copiedTapes inHead (fun j hNe => hCopyHeads j hNe)
    (1 + S) (by omega)
    (by simp [rulerContents, rulerBits]; omega) hCopiedR
  rcases hRewindR with ⟨afterR, hRunR, hMatchR1, hOthersR⟩
  have hScratchMatchR : TapeMatches (afterR tScratch) scratchContents (1 + ua.length) := by
    have hNe : tScratch ≠ tRuler := by decide
    rw [hOthersR tScratch hNe]
    simpa [copiedTapes, scratchContents, tRuler, tArgA, tArgB, tScratch,
      hUA_syms, List.append_assoc] using hCS
  have hOtherBoundsR : ∀ j, j ≠ tScratch → (afterR j).head < bound j := by
    intro j hNeS
    by_cases hR : j = tRuler
    · subst j
      rw [hMatchR1.head_eq]
      omega
    · rw [hOthersR j hR]
      exact hCopyHeads j hR
  have hScratchNoLeft : ∀ i, 1 ≤ i → i < scratchContents.length →
      scratchContents[i]? ≠ some SimSym.leftMark :=
    bitListContent_no_leftMark ua
  have hRewindS := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tScratch input bound
    scratchContents (by simp [scratchContents]) (by simp [scratchContents]) hScratchNoLeft
    hScratchBound afterR inHead hOtherBoundsR (1 + ua.length) (by omega)
    (by simp [scratchContents]; omega) hScratchMatchR
  rcases hRewindS with ⟨finalTapes, hRunS, hMatchS1, hOthersS⟩
  have hRewindBoth :=
    (rewindTape InputAlphabet tRuler).seq_reachesExit (rewindTape InputAlphabet tScratch)
      input bound hRunR hRunS
  have hMapped := TMComponent.mapExit_reachesExit
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch))
    (fun _ => BitRelState.init.runList ua ub) input bound hRewindBoth
  have hBoundRun := bindComponent_reachesExit (copyHeadBitsRel InputAlphabet startIdx)
    (fun rel => ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch)).mapExit
      (fun _ => rel)) input bound hCopyRun hMapped
  have hRun : (readHeadBlock InputAlphabet startIdx).ReachesExit input bound initTapes inHead
      (BitRelState.init.runList ua ub) finalTapes inHead := by
    simpa [readHeadBlock] using hBoundRun
  refine ⟨finalTapes, hRun, ?_, ?_, ?_, ?_⟩
  · have hNe : tRuler ≠ tScratch := by decide
    rw [hOthersS tRuler hNe]
    simpa [rulerContents, rulerBits, List.map_replicate, List.cons_append] using hMatchR1
  · have hNeS : tArgA ≠ tScratch := by decide
    have hNeR : tArgA ≠ tRuler := by decide
    rw [hOthersS tArgA hNeS, hOthersR tArgA hNeR]
    simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCA
  · have hNeS : tArgB ≠ tScratch := by decide
    have hNeR : tArgB ≠ tRuler := by decide
    rw [hOthersS tArgB hNeS, hOthersR tArgB hNeR]
    simpa [copiedTapes, tRuler, tArgA, tArgB, tScratch] using hCB
  · simpa [scratchContents, hUA_syms, List.append_assoc] using hMatchS1

end SavitchLemma

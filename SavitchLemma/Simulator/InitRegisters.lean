module

public import SavitchLemma.Simulator.InitPrimitives

@[expose] public section

/-!
# Simulator register initialization

Provides fixed-bit writing and repeated register-template construction.
-/

namespace SavitchLemma

/-- Append a fixed `List Bool` onto tape `t`, moving right after each bit. -/
def writeFixedBits (InputAlphabet : Type*) (t : Fin 5) (bits : List Bool) :
    TMComponent (Fin (bits.length + 1)) InputAlphabet SimSym 5 Unit where
  start := ⟨0, Nat.zero_lt_succ bits.length⟩
  step idx _ scanned :=
    if h : idx.val < bits.length then
      mkWorkAction (.inl ⟨idx.val + 1, by omega⟩)
        (fun j => if j = t then .bit bits[idx.val] else scanned j)
        (fun j => if j = t then .right else .stay)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem writeFixedBits_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5) (bits : List Bool)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref : List SimSym) (hBound : pref.length + bits.length < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) pref pref.length) :
    ∃ ft,
      (writeFixedBits InputAlphabet t bits).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ bits.map SimSym.bit) (pref.length + bits.length) := by
  have hStep : ∀ suf, ∀ (done : ℕ) (hSum : done + suf.length = bits.length)
      (hDrop : bits.drop done = suf) (p : List SimSym) (tp : OneSidedTape SimSym),
      TapeMatches tp p p.length →
      p.length + suf.length < bound t →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (writeFixedBits InputAlphabet t bits).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl ⟨done, by omega⟩, inHead, fun j => if j = t then tp else initTapes j⟩
          ⟨.inr (), inHead, fun j => if j = t then ft else initTapes j⟩ ∧
        TapeMatches ft (p ++ suf.map SimSym.bit) (p.length + suf.length) := by
    intro suf
    induction suf with
    | nil =>
      intro done hSum _ p tp htp hB
      have hDone : done = bits.length := by simp at hSum; omega
      have hHeads : ∀ j, (if j = t then tp else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [htp.head_eq] using hB
        · simp [hj, hOtherBounds j hj]
      obtain ⟨ft, hUpdT, hFT⟩ := htp.update_keep .stay rfl
      have hNotLt : ¬ done < bits.length := by omega
      have hUpd : ∀ j,
          (if j = t then tp else initTapes j).updateAndMove
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).write j)
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).workMove j) =
            some (if j = t then ft else initTapes j) := by
        intro j
        simp only [writeFixedBits, mkWorkAction, hNotLt, ↓reduceDIte]
        by_cases hj : j = t
        · subst hj; simpa using hUpdT
        · simp only [hj, ↓reduceIte]; exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [hFT.head_eq] using hB
        · simp [hj, hOtherBounds j hj]
      refine ⟨ft, compStep_exit_override (writeFixedBits InputAlphabet t bits) input bound
        _ _ inHead () ⟨done, by omega⟩ hHeads hNextH
        (by simp [writeFixedBits, mkWorkAction, moveHead, hNotLt]) hUpd
        (by simp [writeFixedBits, mkWorkAction, hNotLt]), by simpa using hFT⟩
    | cons b bs ih =>
      intro done hSum hDrop p tp htp hB
      have hLt : done < bits.length := by simp at hSum; omega
      have hBitEq : bits[done] = b := by
        have hGet := congrArg (fun l : List Bool => l[0]?) hDrop
        rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hLt] at hGet
        exact Option.some.inj hGet
      have hDrop' : bits.drop (done + 1) = bs := by
        rw [← List.tail_drop, hDrop]
        rfl
      have hHeads : ∀ j, (if j = t then tp else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [htp.head_eq] using by simp at hB ⊢; omega
        · simp [hj, hOtherBounds j hj]
      obtain ⟨nt, hUpdT, hNT⟩ := htp.update_append (.bit b)
      have hUpd : ∀ j,
          (if j = t then tp else initTapes j).updateAndMove
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).write j)
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).workMove j) =
            some (if j = t then nt else initTapes j) := by
        intro j
        simp only [writeFixedBits, mkWorkAction, hLt, ↓reduceDIte, hBitEq]
        by_cases hj : j = t
        · subst hj; simpa using hUpdT
        · simp only [hj, ↓reduceIte]; exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j, (if j = t then nt else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [hNT.head_eq] using by simp at hB ⊢; omega
        · simp [hj, hOtherBounds j hj]
      obtain ⟨ft, hRest, hFT⟩ := ih (done + 1) (by simp at hSum ⊢; omega) hDrop'
        (p ++ [.bit b]) nt (by simpa using hNT) (by simp at hB ⊢; omega)
      refine ⟨ft, compStep_head_override (writeFixedBits InputAlphabet t bits) input bound
        _ _ _ inHead inHead () ⟨done, by omega⟩ ⟨done + 1, by omega⟩ hHeads hNextH
        (by simp [writeFixedBits, mkWorkAction, moveHead, hLt]) hUpd
        (by simp [writeFixedBits, mkWorkAction, hLt]) hRest, ?_⟩
      have hPos : p.length + (b :: bs).length =
          (p ++ [SimSym.bit b]).length + bs.length := by
        simp; omega
      rw [hPos]
      simpa [List.append_assoc] using hFT
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j; by_cases hj : j = t <;> simp [hj]
  have hRes := hStep bits 0 (Nat.zero_add bits.length) rfl pref (initTapes t) hMatch hBound
  rw [hTapesSelf] at hRes
  exact hRes

/-- Repeat a `Unit`-exiting component `m` times sequentially. -/
def repeatUnit {Q InputAlphabet : Type*} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit) :
    TMComponent (Fin (m + 1) × Q) InputAlphabet SimSym 5 Unit where
  start := (⟨0, Nat.zero_lt_succ m⟩, M.start)
  step st inSym scanned :=
    if h : st.1.val < m then
      (M.step st.2 inSym scanned).mapState fun
        | .inl q' => .inl (st.1, q')
        | .inr () => .inl (⟨st.1.val + 1, by omega⟩, M.start)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem repeatUnit_reachesExit {Q InputAlphabet : Type*} {n : ℕ} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (Inv : ℕ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop)
    (hStep : ∀ i, i < m → ∀ tapes ih, Inv i tapes ih →
      ∃ tapes' ih',
        M.ReachesExit input bound tapes ih () tapes' ih' ∧ Inv (i + 1) tapes' ih') :
    ∀ tapes ih, Inv 0 tapes ih →
      (∀ t, (tapes t).head < bound t) →
      ∃ tapes' ih',
        (repeatUnit m M).ReachesExit input bound tapes ih () tapes' ih' ∧
        Inv m tapes' ih' := by
  intro tapes ih hInv0 hH0
  have hLift : ∀ (i : ℕ) (hi : i < m), ∀ a b,
      (∃ q₀, a.state = .inl q₀) →
      Relation.ReflTransGen
        (fun x y => M.CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j)) a b →
      Relation.ReflTransGen
        (fun x y => (repeatUnit m M).CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j))
        ⟨.inl (⟨i, by omega⟩, match a.state with | .inl q => q | .inr () => M.start),
          a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q => .inl (⟨i, by omega⟩, q)
         | .inr () => .inl (⟨i + 1, by omega⟩, M.start),
          b.inputHead, b.workTapes⟩ := by
    intro i hi a b ha hR
    induction hR with
    | refl =>
      rcases ha with ⟨q₀, hq₀⟩
      simp [hq₀]
      exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ihR =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail (by simpa [hState] using ihR) ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (⟨i, by omega⟩, q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig (Fin (m + 1) × Q ⊕ Unit) SimSym 5 n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(⟨i, by omega⟩, q), by simp, ?_, ihC, ?_, hInC, ?_⟩
      · simp only [repeatUnit, hi, ↓reduceDIte, TMAction.mapState, hScanned, hNext]
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hInM
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hTps
  have hLoop : ∀ rem i (hi : i + rem = m) tps ihC,
      Inv i tps ihC → (∀ j, (tps j).head < bound j) →
      ∃ tps' ih',
        Relation.ReflTransGen
          (fun x y => (repeatUnit m M).CompStep input x y ∧
            (∀ j, (x.workTapes j).head < bound j) ∧
            (∀ j, (y.workTapes j).head < bound j))
          ⟨.inl (⟨i, by omega⟩, M.start), ihC, tps⟩
          ⟨.inr (), ih', tps'⟩ ∧
        Inv m tps' ih' := by
    intro rem
    induction rem with
    | zero =>
      intro i hi tps ihC hInvI hHI
      have hEqM : i = m := by omega
      subst i
      refine ⟨tps, ihC, Relation.ReflTransGen.single ⟨?_, hHI, hHI⟩, hInvI⟩
      refine ⟨(⟨m, Nat.lt_succ_self m⟩, M.start), rfl, ?_, ihC, ?_, rfl, ?_⟩
      · simp [repeatUnit, mkWorkAction]
      · simp [repeatUnit, mkWorkAction, moveHead]
      · intro j
        simp only [repeatUnit, Nat.lt_irrefl, ↓reduceDIte, mkWorkAction]
        exact OneSidedTape.updateAndMove_stay_self _
    | succ r ihR =>
      intro i hi tps ihC hInvI hHI
      obtain ⟨tpsMid, ihMid, hRunM, hInvMid⟩ := hStep i (by omega) tps ihC hInvI
      have hLifted := hLift i (by omega) _ _ ⟨M.start, rfl⟩ hRunM
      have hHMid : ∀ j, (tpsMid j).head < bound j := by
        cases hRunM with
        | tail _ hLast => exact hLast.2.2
      obtain ⟨tpsEnd, ihEnd, hRest, hInvEnd⟩ := ihR (i + 1) (by omega) tpsMid ihMid hInvMid hHMid
      exact ⟨tpsEnd, ihEnd, hLifted.trans hRest, hInvEnd⟩
  exact hLoop m 0 (Nat.zero_add m) tapes ih hInv0 hH0

/-- Check whether `tRuler` currently scans `.bit true`, leaving all tapes stationary. -/
def rulerCheckRegs (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5) (Exit := Bool)
    (fun _ scanned =>
      match scanned tRuler with
      | .bit true => mkWorkAction true scanned (fun _ => .stay)
      | _ => mkWorkAction false scanned (fun _ => .stay))

/-- Loop body appending `bits` onto `tRegs` once per `.bit true` on `tRuler`. -/
def writeRulerListRegsBody (InputAlphabet : Type*) (bits : List Bool) :=
  (rulerCheckRegs InputAlphabet).branch
    (((writeFixedBits InputAlphabet tRegs bits).seq (stepRightAtom InputAlphabet tRuler)).mapExit
      (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit)))
    (TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5)
      (Exit := Unit ⊕ Unit)
      (fun _ scanned => mkWorkAction (.inr ()) scanned (fun _ => .stay)))

/-- Append `(List.replicate S bits).flatten` onto `tRegs` and rewind `tRuler` to cell `1`. -/
def writeRulerListRegs (InputAlphabet : Type*) (bits : List Bool) :=
  (writeRulerListRegsBody InputAlphabet bits).loop.seq (rewindTape InputAlphabet tRuler)

theorem list_flatMap_finRange_const {α : Type*} (S : ℕ) (xs : List α) :
    (List.finRange S).flatMap (fun _ => xs) = (List.replicate S xs).flatten := by
  induction S with
  | zero => simp
  | succ S ih =>
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      List.replicate_succ, List.flatten_cons]
    congr 1

theorem writeRulerListRegs_reachesExit {InputAlphabet : Type*} {n : ℕ} (bits : List Bool)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pref : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : pref.length + S * bits.length < bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tRegs → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs) pref pref.length) :
    ∃ ftR ftReg,
      (writeRulerListRegs InputAlphabet bits).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg (pref ++ ((List.replicate S bits).flatten).map SimSym.bit)
        (pref.length + S * bits.length) := by
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hNeRR : tRuler ≠ tRegs := by decide
  let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    ∃ done rem cur,
      done + rem = S ∧
      cur = pref ++ ((List.replicate done bits).flatten).map SimSym.bit ∧
      TapeMatches (tapes tRuler) rC (1 + done) ∧
      TapeMatches (tapes tRegs) cur cur.length
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun _ tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) rC (1 + S) ∧
    TapeMatches (tapes tRegs) (pref ++ ((List.replicate S bits).flatten).map SimSym.bit)
      (pref.length + S * bits.length)
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (writeRulerListRegsBody InputAlphabet bits).ReachesExit input bound tapes ih
          (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧
        (S + 1 - (tapes' tRuler).head) < (S + 1 - (tapes tRuler).head)) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (writeRulerListRegsBody InputAlphabet bits).ReachesExit input bound tapes ih
          (.inr e) tapes' ih' ∧
        Post e tapes' ih') := by
    intro tapes ih ⟨hIh, hOth, done, rem, cur, hSum, hCur, htR, htReg⟩
    subst ih
    have hFlattenLen : ((List.replicate done bits).flatten).length = done * bits.length := by
      induction done with
      | zero => simp
      | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
    have hCurLen : cur.length = pref.length + done * bits.length := by
      simp [hCur]
    have hMulLe : done * bits.length + rem * bits.length = S * bits.length := by
      rw [← Nat.add_mul, hSum]
    have hHeads : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRuler
      · subst h1; simpa [htR.head_eq] using by omega
      · by_cases h2 : j = tRegs
        · subst h2; simpa [htReg.head_eq, hCurLen] using by omega
        · rw [hOth j h1 h2]; exact hOtherBounds j h1 h2
    cases rem with
    | zero =>
      have hDone : done = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = S + 1 := by omega
        simp [rC, hIdx]
      have hChk : (rulerCheckRegs InputAlphabet).ReachesExit input bound tapes inHead
          false tapes inHead := by
        refine compStep_exit_override (rulerCheckRegs InputAlphabet) input bound tapes tapes
          inHead false () hHeads hHeads
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hExit := TMComponent.atom_reachesExit
        (fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound tapes inHead hHeads inHead (by simp [mkWorkAction, moveHead]) tapes
        (fun j => by simp only [mkWorkAction]; exact OneSidedTape.updateAndMove_stay_self _)
        hHeads
      refine Or.inr ⟨(), tapes, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound false hChk (by simpa [mkWorkAction] using hExit),
        rfl, hOth, by simpa [hDone] using htR, ?_⟩
      simpa [hCur, hCurLen, hDone] using htReg
    | succ r =>
      have hDoneLt : done < S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = done + 1 := Nat.add_comm 1 done
        simp only [rC, hIdx, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left (by simp; exact hDoneLt)]
        simp
      have hChk : (rulerCheckRegs InputAlphabet).ReachesExit input bound tapes inHead
          true tapes inHead := by
        refine compStep_exit_override (rulerCheckRegs InputAlphabet) input bound tapes tapes
          inHead true () hHeads hHeads
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hBitsBound : cur.length + bits.length < bound tRegs := by
        have : 1 * bits.length ≤ (r + 1) * bits.length := Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨ftReg', hWrite, hFTReg'⟩ := writeFixedBits_reachesExit tRegs bits input bound cur
        hBitsBound tapes inHead (fun j hj => hHeads j) htReg
      let midT := fun j => if j = tRegs then ftReg' else tapes j
      have hMidR : TapeMatches (midT tRuler) rC (1 + done) := by
        simpa [midT, hNeRR] using htR
      obtain ⟨ftR', hStepR, hFR'⟩ := stepRightAtom_reachesExit tRuler input bound rC (1 + done)
        (by omega) midT inHead (fun j hj => by
          by_cases h2 : j = tRegs
          · subst h2; simpa [midT, hFTReg'.head_eq, hCurLen] using by omega
          · simpa [midT, h2] using hHeads j)
        hMidR
      have hSeq := TMComponent.mapExit_reachesExit _ (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit))
        input bound ((writeFixedBits InputAlphabet tRegs bits).seq_reachesExit
          (stepRightAtom InputAlphabet tRuler) input bound hWrite hStepR)
      let finalT := fun j => if j = tRuler then ftR' else midT j
      refine Or.inl ⟨finalT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound true hChk hSeq, ?_, ?_⟩
      · refine ⟨rfl, fun j hj1 hj2 => by simp [finalT, midT, hj1, hj2, hOth j hj1 hj2],
          done + 1, r, cur ++ bits.map SimSym.bit, by omega, ?_, ?_, ?_⟩
        · rw [hCur, List.append_assoc, List.replicate_succ', List.flatten_concat, List.map_append]
        · have : 1 + done + 1 = 1 + (done + 1) := by omega
          rw [← this]; simpa [finalT] using hFR'
        · simpa [finalT, midT, hNeRR.symm] using hFTReg'
      · simp [finalT, hFR'.head_eq, htR.head_eq]
        omega
  obtain ⟨_, midTapes, midInHead, hLoop, hIh, hOth, hFR, hFReg⟩ :=
    TMComponent.loop_reachesExit (writeRulerListRegsBody InputAlphabet bits) input bound
      Inv (fun tapes _ => S + 1 - (tapes tRuler).head) Post hStep initTapes inHead
      ⟨rfl, fun _ _ _ => rfl, 0, S, pref, Nat.zero_add S, by simp, hMatchR, hMatchReg⟩
  subst midInHead
  have hNoLeft : ∀ i, 1 ≤ i → i < rC.length → rC[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [rC, List.length_cons, List.length_append, List.length_replicate,
        List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp [rC]; omega)]
      simp only [rC, List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < S
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = S := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  obtain ⟨rewTapes, hRew, hFRewR, hRewOth⟩ := rewindTape_reachesExit tRuler input bound rC
    (by simp [rC]) rfl hNoLeft (by simp [rC]; exact hBoundR) midTapes inHead
    (fun j hj => by
      by_cases h2 : j = tRegs
      · subst h2; simpa [hFReg.head_eq] using by omega
      · rw [hOth j hj h2]; exact hOtherBounds j hj h2)
    (1 + S) (by omega) (by simp [rC]; omega) hFR
  have hFinalEq : rewTapes = fun j => if j = tRuler then rewTapes tRuler
      else if j = tRegs then midTapes tRegs else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1; rfl
    · by_cases h2 : j = tRegs
      · subst h2; rw [hRewOth tRegs hNeRR.symm]; simp [h1]
      · rw [hRewOth j h1, hOth j h1 h2]; simp [h1, h2]
  have hSeq := (writeRulerListRegsBody InputAlphabet bits).loop.seq_reachesExit
    (rewindTape InputAlphabet tRuler) input bound hLoop hRew
  rw [hFinalEq] at hSeq
  exact ⟨rewTapes tRuler, midTapes tRegs, hSeq, hFRewR, hFReg⟩

/-- Append `.endMark` onto tape `t` without moving its head. -/
def writeEndMarkStayAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) (fun j => if j = t then .endMark else scanned j) (fun _ => .stay)

theorem writeEndMarkStayAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref : List SimSym) (hBound : pref.length < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) pref pref.length) :
    ∃ ft,
      (writeEndMarkStayAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ [.endMark]) pref.length := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using hBound
    · exact hOtherBounds j hj
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_append_move rfl .endMark .stay rfl
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [writeEndMarkStayAtom, mkWorkAction] using hUpdT
    · simp only [writeEndMarkStayAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (writeEndMarkStayAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH (by simp [writeEndMarkStayAtom, mkWorkAction, moveHead]) hUpd rfl, hFT⟩

end SavitchLemma

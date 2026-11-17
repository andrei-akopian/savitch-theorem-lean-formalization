module

public import SavitchLemma.RegisterTape.Reset

@[expose] public section

/-!
# Finding an untagged register

Scans the encoded register tape for its first untagged working register.
-/

namespace SavitchLemma

/-- Scan Tape 1 from cell `1` for the first `.tag false` working register.
If found, halts with `true` leaving Tape 1's head on that `.tag false` cell;
if all working registers are tagged (reaching `.srcSep`), rewinds Tape 1 to cell `1`
and returns `false`. -/
inductive FindUntaggedState where
  | scanTag
  | skipBits
  deriving DecidableEq

def FindUntaggedState.equivFin : FindUntaggedState ≃ Fin 2 where
  toFun | .scanTag => 0 | .skipBits => 1
  invFun | 0 => .scanTag | _ => .skipBits
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype FindUntaggedState := Fintype.ofEquiv (Fin 2) FindUntaggedState.equivFin.symm

def findFirstUntaggedBody (InputAlphabet : Type*) :
    TMComponent FindUntaggedState InputAlphabet SimSym 5 Bool where
  start := .scanTag
  step s _ scanned :=
    match s with
    | .scanTag =>
      match scanned tRegs with
      | .tag false => singleTapeAction (.inr true) tRegs (.tag false) .stay scanned
      | .tag true => singleTapeAction (.inl .skipBits) tRegs (.tag true) .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .skipBits =>
      match scanned tRegs with
      | .sep => singleTapeAction (.inl .scanTag) tRegs .sep .right scanned
      | sym => singleTapeAction (.inl .skipBits) tRegs sym .right scanned

def findFirstUntagged (InputAlphabet : Type*) :=
  (findFirstUntaggedBody InputAlphabet).branch
    (TMComponent.atom fun _ scanned => singleTapeAction true tRegs (scanned tRegs) .stay scanned)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem findFirstUntaggedBody_skipBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (pref suf : List SimSym) (bs : List Bool) (hBsLen : bs.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + W + 3 ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    {res : Bool} {ft : OneSidedTape SimSym}
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
        (pref.length + W + 2) →
      Relation.ReflTransGen
        (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
          (∀ j, (a.workTapes j).head < bound j) ∧
          (∀ j, (b.workTapes j).head < bound j))
        ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
        ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩) :
    ∀ rem, rem ≤ bs.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
          (pref.length + 1 + (bs.length - rem)) →
        Relation.ReflTransGen
          (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .skipBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
  intro rem
  induction rem with
  | zero =>
    intro _ tape hM
    let prefSyms := pref ++ SimSym.tag true :: bs.map SimSym.bit
    have hPrefLen : prefSyms.length = pref.length + 1 + bs.length := by
      simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ SimSym.sep :: suf) prefSyms.length := by
      simpa [prefSyms, hPrefLen, List.append_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen, hBsLen] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms .sep suf
    have hMove : moveOneSidedHead (pref.length + 1 + bs.length) .right =
        some (pref.length + W + 2) := by
      simp [moveOneSidedHead, hBsLen]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hPrefLen]; exact hMove)
    have hNM' : TapeMatches nt (pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: suf)
        (pref.length + W + 2) := by
      simpa [prefSyms, List.append_assoc] using hNM
    have hRest := hAfter nt hNM'
    exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .scanTag hHeads
      (by rw [hNM'.head_eq]; omega) hUpd hRest (by simp [findFirstUntaggedBody, hRead])
  | succ r ih =>
    intro hLe tape hM
    let idx := bs.length - (r + 1)
    have hIdxLt : idx < bs.length := by simp [idx]; omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hBsLen] using by simp [idx] at *; omega
      · simpa [hj] using hOtherBounds j hj
    have hNotSep : tape.cells tape.head ≠ .sep := by
      have hM' : TapeMatches tape (pref ++ SimSym.tag true :: (bs.map SimSym.bit ++ SimSym.sep :: suf))
          (pref.length + 1 + idx) := by simpa [List.append_assoc] using hM
      rw [hM'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + 1 + idx)]
      have hSub : pref.length + 1 + idx - pref.length = idx + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      rw [List.getElem_append_left (by simp; exact hIdxLt)]; simp
    have hMove : moveOneSidedHead (pref.length + 1 + idx) .right =
        some (pref.length + 1 + (bs.length - r)) := by
      simp [moveOneSidedHead, idx]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_keep .right hMove
    have hRest := ih (by omega) nt hNM
    exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .skipBits hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [findFirstUntaggedBody])

private theorem findFirstUntaggedBody_scan {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (suf pref : List (Bool × List Bool)),
      (∀ r ∈ pref, r.2.length = W ∧ r.1 = true) →
      (∀ r ∈ suf, r.2.length = W) →
      1 + (pref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix pref).length →
        ∃ (res : Bool) (ft : OneSidedTape SimSym),
          Relation.ReflTransGen
            (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          ft.cells = tape.cells ∧
          (res = false → (∀ r ∈ suf, r.1 = true) ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix (pref ++ suf)).length) ∧
          (res = true → ∃ p₁ cur p₂, suf = p₁ ++ cur :: p₂ ∧
            cur.1 = false ∧ (∀ r ∈ p₁, r.1 = true) ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src)
              (encodeRegsPrefix (pref ++ p₁)).length) := by
  intro suf
  induction suf with
  | nil =>
    intro pref hPref _ hBound tape hM
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hM' : TapeMatches tape (encodeRegsPrefix pref ++ SimSym.srcSep ::
        (SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark]))
        (encodeRegsPrefix pref).length := by
      simpa [encodeRegsTape, encodeSrcEntry] using hM
    have hRead : tape.cells tape.head = .srcSep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) .srcSep _
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
        some (encodeRegsPrefix pref).length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hM'.update_keep .stay hMove
    have hCells : ft.cells = tape.cells := by funext i; exact (hFM.2 i).trans (hM'.2 i).symm
    refine ⟨false, ft, ?_, hCells, ?_, ?_⟩
    · exact singleTape_compStep_exit_override (findFirstUntaggedBody InputAlphabet) tRegs
        input bound initTapes tape ft .scanTag hHeads
        (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [findFirstUntaggedBody, hRead])
    · intro _; refine ⟨by simp, by simpa [encodeRegsTape, encodeSrcEntry] using hFM⟩
    · intro hBad; cases hBad
  | cons cur rs ih =>
    intro pref hPref hSuf hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := (hSuf (b, bs) (by simp))
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hMul : pref.length + ((b, bs) :: rs).length = pref.length + 1 + rs.length := by
      simp; omega
    have hBound' : 1 + pref.length * (W + 2) + (W + 2) + rs.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hBound ⊢
      omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq, hPL] using by omega
      · simpa [hj] using hOtherBounds j hj
    let tailSyms : List SimSym := rs.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hSplit : encodeRegsTape (pref ++ (b, bs) :: rs) src =
        encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms) := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hM' : TapeMatches tape
        (encodeRegsPrefix pref ++ SimSym.tag b :: (bs.map SimSym.bit ++ SimSym.sep :: tailSyms))
        (encodeRegsPrefix pref).length := by
      rw [← hSplit]; exact hM
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (encodeRegsPrefix pref) (.tag b) _
    cases b with
    | false =>
      have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
          some (encodeRegsPrefix pref).length := rfl
      obtain ⟨ft, hUpd, hFM⟩ := hM'.update_keep .stay hMove
      have hCells : ft.cells = tape.cells := by funext i; exact (hFM.2 i).trans (hM'.2 i).symm
      refine ⟨true, ft, ?_, hCells, ?_, ?_⟩
      · exact singleTape_compStep_exit_override (findFirstUntaggedBody InputAlphabet) tRegs
          input bound initTapes tape ft .scanTag hHeads
          (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [findFirstUntaggedBody, hRead])
      · intro hBad; cases hBad
      · intro _
        refine ⟨[], (false, bs), rs, rfl, rfl, by simp, ?_⟩
        simpa [hSplit] using hFM
    | true =>
      have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .right =
          some ((encodeRegsPrefix pref).length + 1) := by simp [moveOneSidedHead]
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
      have hCellsNt : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
      have hPrefNext : ∀ r ∈ pref ++ [(true, bs)], r.2.length = W ∧ r.1 = true := by
        intro r hr
        rcases List.mem_append.mp hr with hMem | hSingle
        · exact hPref r hMem
        · simp at hSingle; subst hSingle; exact ⟨hBsLen, rfl⟩
      have hSufNext : ∀ r ∈ rs, r.2.length = W := fun r hr => hSuf r (by simp [hr])
      have hBoundNext : 1 + ((pref ++ [(true, bs)]).length + rs.length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have : pref.length + 1 + rs.length = pref.length + (rs.length + 1) := by omega
        rw [this]; exact hBound
      have hHeadNext : ((encodeRegsPrefix pref).length + W + 2) =
          (encodeRegsPrefix (pref ++ [(true, bs)])).length := by
        simp [encodeRegsPrefix_snoc, encodeRegEntry_length, hBsLen]; omega
      let ntNext : OneSidedTape SimSym := ⟨nt.cells, (encodeRegsPrefix pref).length + W + 2⟩
      have hMatchNext : TapeMatches ntNext (encodeRegsTape ((pref ++ [(true, bs)]) ++ rs) src)
          (encodeRegsPrefix (pref ++ [(true, bs)])).length := by
        refine ⟨by simp [ntNext, hHeadNext], fun i => ?_⟩
        have hEqList : encodeRegsTape ((pref ++ [(true, bs)]) ++ rs) src =
            encodeRegsTape (pref ++ (true, bs) :: rs) src := by simp
        rw [hEqList, hSplit]
        simpa [ntNext] using hNM.2 i
      obtain ⟨res, ft, hRec, hCellsFt, hFalse, hTrue⟩ := ih (pref ++ [(true, bs)]) hPrefNext
        hSufNext hBoundNext ntNext hMatchNext
      have hCellsFt' : ft.cells = tape.cells := hCellsFt.trans (by simp [ntNext, hCellsNt])
      have hAfter : ∀ tape₂, TapeMatches tape₂
          (encodeRegsPrefix pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
          ((encodeRegsPrefix pref).length + W + 2) →
          Relation.ReflTransGen
            (fun a b => (findFirstUntaggedBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape₂ else initTapes j⟩
            ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
        intro tape₂ hM₂
        have hEqTape : tape₂ = ntNext := by
          have hC : tape₂.cells = ntNext.cells := by
            funext i
            have h1 := hM₂.2 i
            have h2 := hNM.2 i
            simp only [ntNext]
            rw [h1, h2]
            simp [List.append_assoc]
          cases tape₂; simp only [ntNext, OneSidedTape.mk.injEq]; exact ⟨hC, hM₂.head_eq⟩
        rw [hEqTape]; exact hRec
      have hNM_skip : TapeMatches nt
          (encodeRegsPrefix pref ++ SimSym.tag true :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
          ((encodeRegsPrefix pref).length + 1 + (bs.length - bs.length)) := by
        simpa [List.append_assoc] using hNM
      have hSkip := findFirstUntaggedBody_skipBits input bound W (encodeRegsPrefix pref) tailSyms
        bs hBsLen initTapes inHead (by rw [hPL]; omega) hOtherBounds hAfter
        bs.length le_rfl nt hNM_skip
      refine ⟨res, ft, ?_, hCellsFt', ?_, ?_⟩
      · exact singleTape_compStep_head_override (findFirstUntaggedBody InputAlphabet) tRegs
          input bound initTapes tape nt ft .scanTag .skipBits hHeads
          (by rw [hNM.head_eq, hPL]; omega) hUpd hSkip (by simp [findFirstUntaggedBody, hRead])
      · intro hResF
        obtain ⟨hAllT, hFM⟩ := hFalse hResF
        refine ⟨fun r hr => ?_, by simpa [List.append_assoc] using hFM⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · rfl
        · exact hAllT r hMem
      · intro hResT
        obtain ⟨p₁, cur, p₂, hEqRs, hCurF, hP1T, hFM⟩ := hTrue hResT
        refine ⟨(true, bs) :: p₁, cur, p₂, by simp [hEqRs], hCurF, fun r hr => ?_, ?_⟩
        · rcases List.mem_cons.mp hr with rfl | hMem
          · rfl
          · exact hP1T r hMem
        · simpa [List.append_assoc] using hFM

theorem findFirstUntagged_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src) 1) :
    (∀ r ∈ work, r.1 = true) ∧
      (∃ ft, (findFirstUntagged InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) 1) ∨
    (∃ pref cur suf, work = pref ++ cur :: suf ∧ cur.1 = false ∧
      (∀ r ∈ pref, r.1 = true) ∧
      ∃ ft, (findFirstUntagged InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) (encodeRegsPrefix pref).length) := by
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  obtain ⟨res, mt, hBody, _, hFalse, hTrue⟩ := findFirstUntaggedBody_scan input bound W src hSrc
    initTapes inHead hOtherBounds work [] (by simp) hWork (by simpa using hBound)
    (initTapes tRegs) (by simpa [encodeRegsPrefix] using hMatch)
  rw [hTapesSelf] at hBody
  cases res with
  | true =>
    obtain ⟨p₁, cur, p₂, hEqW, hCurF, hP1T, hMT⟩ := hTrue rfl
    simp only [List.nil_append] at hEqW hMT
    have hHeadsM : ∀ j, (if j = tRegs then mt else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj
        have hP1Len : p₁.length < work.length := by rw [hEqW]; simp
        have hP1W : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
        have hPL := encodeRegsPrefix_length W p₁ hP1W
        have hB1 : 1 + p₁.length * (W + 2) < 1 + work.length * (W + 2) + (W + 3) := by
          have : p₁.length * (W + 2) ≤ work.length * (W + 2) := Nat.mul_le_mul_right _ hP1Len.le
          omega
        simpa [hMT.head_eq, hPL] using Nat.lt_of_lt_of_le hB1 hBound
      · simpa [hj] using hOtherBounds j hj
    have hMove : moveOneSidedHead (encodeRegsPrefix p₁).length .stay =
        some (encodeRegsPrefix p₁).length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hMT.update_keep .stay hMove
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ sym => (true, sym, .stay)) tRegs input bound
      (fun j => if j = tRegs then mt else initTapes j) inHead hHeadsM
      (by simpa using hUpd) (by
        have hP1Len : p₁.length < work.length := by rw [hEqW]; simp
        have hP1W : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
        have hPL := encodeRegsPrefix_length W p₁ hP1W
        have hB1 : 1 + p₁.length * (W + 2) < 1 + work.length * (W + 2) + (W + 3) := by
          have : p₁.length * (W + 2) ≤ work.length * (W + 2) := Nat.mul_le_mul_right _ hP1Len.le
          omega
        simpa [hFM.head_eq, hPL] using Nat.lt_of_lt_of_le hB1 hBound)
    have hFtEq : (fun j => if j = tRegs then ft
        else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hAtom
    right
    refine ⟨p₁, cur, p₂, hEqW, hCurF, hP1T, ft, ?_, hFM⟩
    exact (findFirstUntaggedBody InputAlphabet).branch_reachesExit _ _ input bound true hBody hAtom
  | false =>
    obtain ⟨hAllT, hMT⟩ := hFalse rfl
    simp only [List.nil_append] at hMT
    have hWLen := encodeRegsPrefix_length W work hWork
    have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
      encodeRegsTape_length W work src hWork hSrc
    have hRewBounds : ∀ j, j ≠ tRegs →
        ((fun j => if j = tRegs then mt else initTapes j) j).head < bound j := by
      intro j hj; simpa [hj] using hOtherBounds j hj
    obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
      (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
      (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
      (fun j => if j = tRegs then mt else initTapes j) inHead hRewBounds
      (encodeRegsPrefix work).length (by rw [hWLen]; omega)
      (by rw [hWorkLen, hWLen]; omega) (by simpa using hMT)
    have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
      funext j; by_cases hj : j = tRegs
      · subst hj; simp
      · rw [hOth j hj]; simp [hj]
    rw [hFinalEq] at hRew
    left
    refine ⟨hAllT, finalTapes tRegs, ?_, hFM⟩
    exact (findFirstUntaggedBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

end SavitchLemma

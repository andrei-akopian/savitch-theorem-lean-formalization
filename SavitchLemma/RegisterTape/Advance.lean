module

public import SavitchLemma.RegisterTape.FindUntagged

@[expose] public section

/-!
# Advancing between registers

Moves from a register tag to the next register or the source register.
-/

namespace SavitchLemma

/-- Starting on `.tag _` of a register in `tRegs`, advance past its bits and tail.
If a `.sep` is followed by another `.tag _` or `.srcSep`, step onto that next `.tag _`
(returning `true`); if `.endMark` is reached (meaning we were on the source register),
rewind `tRegs` to cell `1` and return `false`. -/
inductive AdvanceRegState where
  | stepTag
  | skipBits
  | afterSep
  deriving DecidableEq

def AdvanceRegState.equivFin : AdvanceRegState ≃ Fin 3 where
  toFun | .stepTag => 0 | .skipBits => 1 | .afterSep => 2
  invFun | 0 => .stepTag | 1 => .skipBits | _ => .afterSep
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype AdvanceRegState := Fintype.ofEquiv (Fin 3) AdvanceRegState.equivFin.symm

def advanceToNextRegBody (InputAlphabet : Type*) :
    TMComponent AdvanceRegState InputAlphabet SimSym 5 Bool where
  start := .stepTag
  step s _ scanned :=
    match s with
    | .stepTag => singleTapeAction (.inl .skipBits) tRegs (scanned tRegs) .right scanned
    | .skipBits =>
      match scanned tRegs with
      | .sep => singleTapeAction (.inl .afterSep) tRegs .sep .right scanned
      | .endMark => singleTapeAction (.inr false) tRegs .endMark .stay scanned
      | sym => singleTapeAction (.inl .skipBits) tRegs sym .right scanned
    | .afterSep =>
      match scanned tRegs with
      | .srcSep => singleTapeAction (.inr true) tRegs .srcSep .right scanned
      | sym => singleTapeAction (.inr true) tRegs sym .stay scanned

def advanceToNextReg (InputAlphabet : Type*) :=
  (advanceToNextRegBody InputAlphabet).branch
    (TMComponent.atom fun _ scanned => singleTapeAction true tRegs (scanned tRegs) .stay scanned)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem advanceToNextRegBody_skipBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool) (bits : List Bool) (tailSym : SimSym)
    (hTailNotEndOrSep : tailSym = .sep ∨ tailSym = .endMark)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + bits.length + (if tailSym = .sep then 3 else 2) ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    {res : Bool} {ft : OneSidedTape SimSym}
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
        (pref.length + bits.length + 1) →
      (tailSym = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead, fun j => if j = tRegs then ⟨tape.cells, pref.length + bits.length + 2⟩ else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩) ∧
      (tailSym = .endMark → res = false ∧ ft = tape)) :
    ∀ rem, rem ≤ bits.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b :: bits.map SimSym.bit ++ tailSym :: suf)
          (pref.length + 1 + (bits.length - rem)) →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .skipBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
  intro rem
  induction rem with
  | zero =>
    intro _ tape hM
    let prefSyms := pref ++ SimSym.tag b :: bits.map SimSym.bit
    have hPrefLen : prefSyms.length = pref.length + bits.length + 1 := by simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ tailSym :: suf) prefSyms.length := by
      rw [hPrefLen]
      simpa [prefSyms, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen] using by cases hTailNotEndOrSep <;> simp_all <;> omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = tailSym := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms tailSym suf
    obtain ⟨hAfterSep, hAfterEnd⟩ := hAfter tape (by rw [← hPrefLen]; simpa [prefSyms, List.append_assoc] using hM')
    rcases hTailNotEndOrSep with rfl | rfl
    · have hMove : moveOneSidedHead prefSyms.length .right =
          some (pref.length + bits.length + 2) := by
        simp [moveOneSidedHead, hPrefLen]
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
      have hCellsNt : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
      have hNtEq : nt = ⟨tape.cells, pref.length + bits.length + 2⟩ := by
        cases nt; simp only [OneSidedTape.mk.injEq]; exact ⟨hCellsNt, hNM.head_eq⟩
      rw [hNtEq] at hUpd hNM
      exact singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
        input bound initTapes tape ⟨tape.cells, pref.length + bits.length + 2⟩ ft
        .skipBits .afterSep hHeads (by simp at hBound ⊢; omega) hUpd (hAfterSep rfl)
        (by simp [advanceToNextRegBody, hRead])
    · obtain ⟨rfl, hFtEq⟩ := hAfterEnd rfl
      have hMove : moveOneSidedHead prefSyms.length .stay = some prefSyms.length := rfl
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .stay hMove
      have hNtEq : nt = tape := by
        have hC : nt.cells = tape.cells := by funext i; exact (hNM.2 i).trans (hM'.2 i).symm
        have hH : nt.head = tape.head := hNM.head_eq.trans hM'.head_eq.symm
        cases nt; cases tape; simp only [OneSidedTape.mk.injEq]; exact ⟨hC, hH⟩
      rw [hNtEq] at hUpd
      rw [hFtEq]
      exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
        input bound initTapes tape tape .skipBits hHeads
        (by rw [hM'.head_eq, hPrefLen]; simp at hBound; omega)
        hUpd (by simp [advanceToNextRegBody, hRead])
  | succ r ih =>
    intro hLe tape hM
    let idx := bits.length - (r + 1)
    have hIdxLt : idx < bits.length := by simp [idx]; omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by
          rcases hTailNotEndOrSep with rfl | rfl <;> simp at hBound ⊢ <;> omega
      · simpa [hj] using hOtherBounds j hj
    have hReadBit : tape.cells tape.head = .bit (bits[idx]'hIdxLt) := by
      have hM' : TapeMatches tape (pref ++ SimSym.tag b :: (bits.map SimSym.bit ++ tailSym :: suf))
          (pref.length + 1 + idx) := by simpa [List.append_assoc] using hM
      rw [hM'.read_lt (by simp; omega)]
      simp only [List.getElem_append_right (by omega : pref.length ≤ pref.length + 1 + idx)]
      have hSub : pref.length + 1 + idx - pref.length = idx + 1 := by omega
      simp only [hSub, List.getElem_cons_succ]
      rw [List.getElem_append_left (by simp; exact hIdxLt)]; simp
    have hMove : moveOneSidedHead (pref.length + 1 + idx) .right =
        some (pref.length + 1 + (bits.length - r)) := by simp [moveOneSidedHead, idx]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_keep .right hMove
    exact singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .skipBits .skipBits hHeads
      (by rw [hNM.head_eq]; rcases hTailNotEndOrSep with rfl | rfl <;> simp at hBound ⊢ <;> omega)
      hUpd (ih (by omega) nt hNM)
      (by simp [advanceToNextRegBody, hReadBit])

theorem advanceToNextReg_work_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hCurLen : cur.2.length = W)
    (hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src)
      (encodeRegsPrefix pref).length) :
    let nextPos := if suf = [] then (encodeRegsPrefix (pref ++ [cur])).length + 1
                   else (encodeRegsPrefix (pref ++ [cur])).length
    ∃ ft,
      (advanceToNextReg InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape (pref ++ cur :: suf) src) nextPos := by
  intro nextPos
  rcases cur with ⟨b, bs⟩
  have hBsLen : bs.length = W := hCurLen
  have hPL := encodeRegsPrefix_length W pref hPrefLen
  have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
  let prefSyms := encodeRegsPrefix pref
  let tailSyms : List SimSym := suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
  have hTapeEq : encodeRegsTape (pref ++ (b, bs) :: suf) src =
      prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms := by
    simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
  have hM' : TapeMatches (initTapes tRegs)
      (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
      prefSyms.length := by
    rw [← hTapeEq]; exact hMatch
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [hM'.head_eq, prefSyms, hPL] using by omega
    · exact hOtherBounds j hj
  have hMove₁ : moveOneSidedHead prefSyms.length .right = some (prefSyms.length + 1) := by
    simp [moveOneSidedHead]
  obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_keep .right hMove₁
  have hCells₁ : nt₁.cells = (initTapes tRegs).cells := by
    funext i; exact (hNM₁.2 i).trans (hM'.2 i).symm
  let sepNextPos := prefSyms.length + bs.length + 2
  have hSepNextEq : sepNextPos = (encodeRegsPrefix (pref ++ [(b, bs)])).length := by
    simp [sepNextPos, prefSyms, encodeRegsPrefix_snoc, encodeRegEntry_length]
    omega
  have hSufSymHead : ∃ nextSym tail₂,
      tailSyms = nextSym :: tail₂ ∧
      (suf = [] → nextSym = .srcSep) ∧
      (suf ≠ [] → ∃ b' bs' rs, suf = (b', bs') :: rs ∧ nextSym = .tag b') := by
    cases suf with
    | nil =>
      refine ⟨.srcSep, SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark], ?_,
        fun _ => rfl, fun h => (h rfl).elim⟩
      simp [tailSyms, encodeSrcEntry]
    | cons r rs =>
      rcases r with ⟨b', bs'⟩
      refine ⟨.tag b', bs'.map SimSym.bit ++ [SimSym.sep] ++
          rs.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src, ?_,
        (by intro h; cases h), fun _ => ⟨b', bs', rs, rfl, rfl⟩⟩
      simp [tailSyms, encodeRegEntry, List.append_assoc]
  rcases hSufSymHead with ⟨nextSym, tail₂, hTail₂, hWhenNil, hWhenCons⟩
  let midTape : OneSidedTape SimSym := ⟨nt₁.cells, sepNextPos⟩
  let ftPos : ℕ := nextPos
  let ftTape : OneSidedTape SimSym := ⟨nt₁.cells, ftPos⟩
  have hNextPosEq : ftPos = if suf = [] then sepNextPos + 1 else sepNextPos := by
    simp [ftPos, nextPos, hSepNextEq]
  have hAfterBody : ∀ tape, TapeMatches tape
      (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ SimSym.sep :: tailSyms)
      (prefSyms.length + bs.length + 1) →
      (SimSym.sep = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead,
            fun j => if j = tRegs then ⟨tape.cells, sepNextPos⟩ else initTapes j⟩
          ⟨.inr true, inHead, fun j => if j = tRegs then ftTape else initTapes j⟩) ∧
      (SimSym.sep = .endMark → true = false ∧ ftTape = tape) := by
    intro tape hMTape
    constructor
    · intro _
      have hTapeCells : tape.cells = nt₁.cells := by
        funext i
        have h1 := hMTape.2 i
        have h2 := hNM₁.2 i
        rw [h1, h2]
      have hMidEq : (⟨tape.cells, sepNextPos⟩ : OneSidedTape SimSym) = midTape := by
        simp [midTape, hTapeCells]
      rw [hMidEq]
      have hMAfter : TapeMatches midTape
          ((prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]) ++ nextSym :: tail₂)
          sepNextPos := by
        refine ⟨rfl, fun i => ?_⟩
        rw [hCells₁]
        have hOrig := hM'.2 i
        simp only [hTail₂, List.append_assoc] at hOrig
        simpa [midTape, List.append_assoc] using hOrig
      have hPrefAfterLen : (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]).length =
          sepNextPos := by
        simp [sepNextPos]; omega
      have hHeadsMid : ∀ j, (if j = tRegs then midTape else initTapes j).head < bound j := by
        intro j; by_cases hj : j = tRegs
        · subst hj; simpa [midTape, sepNextPos, prefSyms, hPL, hBsLen] using by omega
        · simpa [hj] using hOtherBounds j hj
      have hReadNext : midTape.cells midTape.head = nextSym := by
        rw [hMAfter.read_lt (by rw [← hPrefAfterLen]; simp)]
        convert list_get_append_mid (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep])
          nextSym tail₂
        · simp [sepNextPos]; omega
      cases suf with
      | nil =>
        have hNS : nextSym = .srcSep := hWhenNil rfl
        have hMoveA : moveOneSidedHead sepNextPos .right = some ftPos := by
          simp [moveOneSidedHead, hNextPosEq]
        obtain ⟨ntA, hUpdA, hNMA⟩ := hMAfter.update_keep .right hMoveA
        have hNtAEq : ntA = ftTape := by
          have hC : ntA.cells = nt₁.cells := by
            funext i
            have h1 := hNMA.2 i
            have h2 := hMAfter.2 i
            exact h1.trans h2.symm
          cases ntA; simp only [ftTape, OneSidedTape.mk.injEq]; exact ⟨hC, hNMA.head_eq⟩
        rw [hNtAEq] at hUpdA
        exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
          input bound initTapes midTape ftTape .afterSep hHeadsMid
          (by simp [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen]; omega)
          hUpdA (by simp [advanceToNextRegBody, hReadNext, hNS])
      | cons r rs =>
        obtain ⟨b', bs', rs', hEqSuf, hNS⟩ := hWhenCons (by simp)
        have hMoveA : moveOneSidedHead sepNextPos .stay = some ftPos := by
          simp [moveOneSidedHead, hNextPosEq]
        obtain ⟨ntA, hUpdA, hNMA⟩ := hMAfter.update_keep .stay hMoveA
        have hNtAEq : ntA = ftTape := by
          have hC : ntA.cells = nt₁.cells := by
            funext i
            have h1 := hNMA.2 i
            have h2 := hMAfter.2 i
            exact h1.trans h2.symm
          cases ntA; simp only [ftTape, OneSidedTape.mk.injEq]; exact ⟨hC, hNMA.head_eq⟩
        rw [hNtAEq] at hUpdA
        exact singleTape_compStep_exit_override (advanceToNextRegBody InputAlphabet) tRegs
          input bound initTapes midTape ftTape .afterSep hHeadsMid
          (by simp [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen]; omega)
          hUpdA (by simp [advanceToNextRegBody, hReadNext, hNS])
    · intro hBad; cases hBad
  have hSkip := advanceToNextRegBody_skipBits input bound prefSyms tailSyms b bs .sep (Or.inl rfl)
    initTapes inHead (by simp [prefSyms, hPL, hBsLen]; omega) hOtherBounds hAfterBody
    bs.length le_rfl nt₁ (by simpa [Nat.sub_self] using hNM₁)
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBody : (advanceToNextRegBody InputAlphabet).ReachesExit input bound initTapes inHead true
      (fun j => if j = tRegs then ftTape else initTapes j) inHead := by
    have hRun := singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes (initTapes tRegs) nt₁ ftTape .stepTag .skipBits hHeadsOv
      (by rw [hNM₁.head_eq, hPL]; omega) hUpd₁ hSkip (by simp [advanceToNextRegBody])
    rw [hTapesSelf] at hRun
    exact hRun
  have hFtMatch : TapeMatches ftTape (encodeRegsTape (pref ++ (b, bs) :: suf) src) ftPos := by
    refine ⟨rfl, fun i => ?_⟩
    rw [hCells₁, hTapeEq]
    exact hM'.2 i
  have hHeadsFt : ∀ j, (if j = tRegs then ftTape else initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [ftTape, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen] using by
        split <;> omega
    · simpa [hj] using hOtherBounds j hj
  have hMoveStay : moveOneSidedHead ftPos .stay = some ftPos := rfl
  obtain ⟨ftFinal, hUpdF, hFMF⟩ := hFtMatch.update_keep .stay hMoveStay
  have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
    (fun _ sym => (true, sym, .stay)) tRegs input bound
    (fun j => if j = tRegs then ftTape else initTapes j) inHead hHeadsFt
    (by simpa using hUpdF) (by
      simpa [hFMF.head_eq, hNextPosEq, sepNextPos, prefSyms, hPL, hBsLen] using by split <;> omega)
  have hFtEq : (fun j => if j = tRegs then ftFinal
      else if j = tRegs then ftTape else initTapes j) =
      (fun j => if j = tRegs then ftFinal else initTapes j) := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  rw [hFtEq] at hAtom
  refine ⟨ftFinal, ?_, hFMF⟩
  exact (advanceToNextRegBody InputAlphabet).branch_reachesExit _ _ input bound true hBody hAtom

theorem advanceToNextReg_src_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src)
      ((encodeRegsPrefix work).length + 1)) :
    ∃ ft,
      (advanceToNextReg InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape work src) 1 := by
  have hWL := encodeRegsPrefix_length W work hWork
  let prefSyms := encodeRegsPrefix work ++ [SimSym.srcSep]
  have hPrefLen : prefSyms.length = (encodeRegsPrefix work).length + 1 := by simp [prefSyms]
  have hTapeEq : encodeRegsTape work src =
      prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [] := by
    simp [prefSyms, encodeRegsTape, encodeSrcEntry, List.append_assoc]
  have hM' : TapeMatches (initTapes tRegs)
      (prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [])
      prefSyms.length := by
    rw [← hTapeEq, hPrefLen]; exact hMatch
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = tRegs
    · subst hj; simpa [hM'.head_eq, hPrefLen, hWL] using by omega
    · exact hOtherBounds j hj
  have hMove₁ : moveOneSidedHead prefSyms.length .right = some (prefSyms.length + 1) := by
    simp [moveOneSidedHead]
  obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_keep .right hMove₁
  have hCells₁ : nt₁.cells = (initTapes tRegs).cells := by
    funext i; exact (hNM₁.2 i).trans (hM'.2 i).symm
  let mtTape : OneSidedTape SimSym := ⟨nt₁.cells, prefSyms.length + src.length + 1⟩
  have hAfterBody : ∀ tape, TapeMatches tape
      (prefSyms ++ SimSym.tag true :: src.map SimSym.bit ++ SimSym.endMark :: [])
      (prefSyms.length + src.length + 1) →
      (SimSym.endMark = .sep →
        Relation.ReflTransGen
          (fun a b => (advanceToNextRegBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .afterSep, inHead,
            fun j => if j = tRegs then ⟨tape.cells, prefSyms.length + src.length + 2⟩ else initTapes j⟩
          ⟨.inr false, inHead, fun j => if j = tRegs then mtTape else initTapes j⟩) ∧
      (SimSym.endMark = .endMark → false = false ∧ mtTape = tape) := by
    intro tape hMTape
    constructor
    · intro hBad; cases hBad
    · intro _
      refine ⟨rfl, ?_⟩
      have hC : mtTape.cells = tape.cells := by
        funext i
        have h1 := hMTape.2 i
        have h2 := hNM₁.2 i
        simp only [mtTape]
        rw [h2, h1]
      cases tape; simp only [mtTape, OneSidedTape.mk.injEq]; exact ⟨hC, hMTape.head_eq.symm⟩
  have hSkip := advanceToNextRegBody_skipBits input bound prefSyms [] true src .endMark (Or.inr rfl)
    initTapes inHead (by simp [hPrefLen, hWL, hSrc]; omega) hOtherBounds hAfterBody
    src.length le_rfl nt₁ (by simpa [Nat.sub_self] using hNM₁)
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBody : (advanceToNextRegBody InputAlphabet).ReachesExit input bound initTapes inHead false
      (fun j => if j = tRegs then mtTape else initTapes j) inHead := by
    have hRun := singleTape_compStep_head_override (advanceToNextRegBody InputAlphabet) tRegs
      input bound initTapes (initTapes tRegs) nt₁ mtTape .stepTag .skipBits hHeadsOv
      (by rw [hNM₁.head_eq, hPrefLen, hWL]; omega) hUpd₁ hSkip (by simp [advanceToNextRegBody])
    rw [hTapesSelf] at hRun
    exact hRun
  have hMtMatch : TapeMatches mtTape (encodeRegsTape work src) (prefSyms.length + src.length + 1) := by
    refine ⟨rfl, fun i => ?_⟩
    rw [hCells₁, hTapeEq]
    exact hM'.2 i
  have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
    encodeRegsTape_length W work src hWork hSrc
  have hRewBounds : ∀ j, j ≠ tRegs →
      ((fun j => if j = tRegs then mtTape else initTapes j) j).head < bound j := by
    intro j hj; simpa [hj] using hOtherBounds j hj
  obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
    (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
    (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
    (fun j => if j = tRegs then mtTape else initTapes j) inHead hRewBounds
    (prefSyms.length + src.length + 1) (by omega)
    (by rw [hWorkLen, hPrefLen, hWL, hSrc]; omega) hMtMatch
  have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
    funext j; by_cases hj : j = tRegs
    · subst hj; simp
    · rw [hOth j hj]; simp [hj]
  rw [hFinalEq] at hRew
  refine ⟨finalTapes tRegs, ?_, hFM⟩
  exact (advanceToNextRegBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
    (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

end SavitchLemma

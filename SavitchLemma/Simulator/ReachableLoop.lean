module

public import SavitchLemma.Simulator.CheckValidAndStep

@[expose] public section

/-!
# Register-scan reachability loop (D2)

Scans all `r + 1` registers on `tRegs` (the `r` working registers followed by the
source register `Fin.last r`), checking whether any tagged register `x_i` equals `x_j`
(on `tArgB`) or can step to `x_j` via `checkValidAndStep M`, and rewinds `tRegs` to `1`.
-/

namespace SavitchLemma

/-- Invariant on `ZDConfig`: every tagged register holds `bitEncodeConfig Q Γ c`
for some `c : TMConfig Q Γ k n S`. -/
def ValidZDTags (Q Γ : Type*) {k : ℕ} (n : ℕ) [Fintype Q] [Fintype Γ] (S : ℕ) {r : ℕ}
    (cfg : ZDConfig r (2 ^ configBitWidth Q Γ k S - 1)) : Prop :=
  cfg.tag (Fin.last r) = true ∧
  ∀ i : Fin (r + 1),
    cfg.tag i = true → ∃ c : TMConfig Q Γ k n S, cfg.x i = (bitEncodeConfig Q Γ c).val

theorem encodeRegsTape_no_leftMark (work : List (Bool × List Bool)) (src : List Bool) :
    ∀ i, 1 ≤ i → i < (encodeRegsTape work src).length →
      (encodeRegsTape work src)[i]? ≠ some SimSym.leftMark := by
  intro i hi1 hiLt hEq
  rw [List.getElem?_eq_getElem hiLt] at hEq
  simp only [Option.some.injEq] at hEq
  have hMem : (encodeRegsTape work src)[i] ∈
      (work.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src) := by
    have hCons : encodeRegsTape work src =
        SimSym.leftMark :: (work.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src) := by
      simp [encodeRegsTape, encodeRegsPrefix]
    cases i with
    | zero => omega
    | succ i' =>
      have hi' : i' < (work.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src).length := by
        simpa [hCons] using hiLt
      simp only [hCons, List.getElem_cons_succ]
      exact List.getElem_mem hi'
  rw [hEq] at hMem
  rcases List.mem_append.mp hMem with hW | hS
  · rcases List.mem_flatMap.mp hW with ⟨r, _, hr⟩
    simp [encodeRegEntry] at hr
  · simp [encodeSrcEntry] at hS

/-- Scan all registers on `tRegs` starting from `1` (`idx = 0`), testing whether
any tagged register `x_i` satisfies `x_i = x_j` or `M.step x_i x_j` against `tArgB`.
Rewinds `tRegs` to `1` and leaves `tArgA` cleared (`[.leftMark]` at `1`). -/
noncomputable def checkReachableLoop {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  loopWithState () fun (_ : Unit) =>
    TMComponent.branch
      (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
        mkWorkAction (decide (scanned tRegs = .tag true)) scanned (fun _ => .stay))
      (bindComponent (copyRegBitsTo InputAlphabet tArgA) fun _ =>
        TMComponent.branch
          (compareBitTapes InputAlphabet tArgA tArgB)
          (((clearTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tRegs)).mapExit
            (fun _ => (.inr true : Unit ⊕ Bool)))
          (TMComponent.branch
            (checkValidAndStep M)
            (((clearTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tRegs)).mapExit
              (fun _ => (.inr true : Unit ⊕ Bool)))
            (bindComponent (clearTape InputAlphabet tArgA) fun _ =>
              bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
                TMComponent.atom fun _ scanned =>
                  mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                    scanned (fun _ => .stay))))
      (bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
        TMComponent.atom fun _ scanned =>
          mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
            scanned (fun _ => .stay))

private theorem bitEncodeConfig_val_natToBits {Q Γ : Type*} {k n S : ℕ}
    [Fintype Q] [Fintype Γ] (c : TMConfig Q Γ k n S) :
    natToBits (configBitWidth Q Γ k S) (bitEncodeConfig Q Γ c).val = encodeConfigBits Q Γ c := by
  have hLen : (encodeConfigBits Q Γ c).length = configBitWidth Q Γ k S :=
    encodeConfigBits_length Q Γ c
  change natToBits (configBitWidth Q Γ k S) (bitsToNat (encodeConfigBits Q Γ c)) =
    encodeConfigBits Q Γ c
  rw [← hLen, natToBits_bitsToNat]

private def regPosOf (r : ℕ) (work : List (Bool × List Bool)) (idx : ℕ) : ℕ :=
  if idx < r then (encodeRegsPrefix (work.take idx)).length
  else (encodeRegsPrefix work).length + 1

private theorem encodeZDRegs_bits {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    ∀ p ∈ encodeZDRegs W cfg, p.2.length = W := by
  intro p hp
  simp only [encodeZDRegs, List.mem_ofFn] at hp
  rcases hp with ⟨j, rfl⟩
  exact natToBits_length W _

private theorem encodeRegsTape_curSplit {r W N : ℕ} (cfg : ZDConfig r N)
    (hSrcTag : cfg.tag (Fin.last r) = true) (idx : ℕ) (hIdxLe : idx ≤ r) :
    let work := encodeZDRegs W cfg
    let src := encodeZDSrc W cfg
    ∃ (bCur : Bool) (bsCur : List Bool) (tailSym : SimSym) (pSyms sSyms : List SimSym),
      (∀ x : Bool, tailSym ≠ .bit x) ∧
      pSyms.length = regPosOf r work idx ∧
      bsCur.length = W ∧
      encodeRegsTape work src = pSyms ++ SimSym.tag bCur :: bsCur.map SimSym.bit ++ tailSym :: sSyms ∧
      (∀ hLt : idx < r,
        bCur = cfg.tag ⟨idx, by omega⟩ ∧
        bsCur = natToBits W (cfg.x ⟨idx, by omega⟩).val ∧
        work = work.take idx ++ (bCur, bsCur) :: work.drop (idx + 1)) ∧
      (idx = r → bCur = cfg.tag (Fin.last r) ∧ bsCur = src) := by
  intro work src
  by_cases hLt : idx < r
  · let pref := work.take idx
    let cur := (cfg.tag ⟨idx, by omega⟩, natToBits W (cfg.x ⟨idx, by omega⟩).val)
    let suf := work.drop (idx + 1)
    have hWorkLen : work.length = r := encodeZDRegs_length W cfg
    have hWorkSplit : work = pref ++ cur :: suf := by
      have hTakeDrop := (List.take_append_drop idx work).symm
      have hDropCons : work.drop idx = cur :: suf := by
        rw [← List.getElem_cons_drop (by rw [hWorkLen]; exact hLt)]
        congr 1
        simp [work, encodeZDRegs, cur]
      rw [hDropCons] at hTakeDrop
      exact hTakeDrop
    refine ⟨cur.1, cur.2, SimSym.sep, encodeRegsPrefix pref,
      suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src,
      by intro x; simp, by simp only [regPosOf, hLt, ↓reduceIte]; rfl, natToBits_length W _,
      ?_, ?_, ?_⟩
    · conv_lhs => rw [hWorkSplit]
      dsimp only [cur]
      rw [encodeRegsTape_split]
      simp [List.append_assoc]
    · intro _; exact ⟨rfl, rfl, hWorkSplit⟩
    · intro hEq; omega
  · have hEqR : idx = r := by omega
    let pSyms := encodeRegsPrefix work ++ [SimSym.srcSep]
    refine ⟨true, src, SimSym.endMark, pSyms, [], by intro x; simp,
      by simp [regPosOf, hLt, pSyms], natToBits_length W _, ?_, ?_, ?_⟩
    · simp [pSyms, encodeRegsTape, encodeSrcEntry, List.append_assoc]
    · intro hLt'; omega
    · intro _; exact ⟨hSrcTag.symm, rfl⟩

private theorem regPosOf_lt_length {r W N : ℕ} (cfg : ZDConfig r N) (idx : ℕ) (_hIdxLe : idx ≤ r) :
    regPosOf r (encodeZDRegs W cfg) idx <
      (encodeRegsTape (encodeZDRegs W cfg) (encodeZDSrc W cfg)).length := by
  let work := encodeZDRegs W cfg
  let src := encodeZDSrc W cfg
  have hWorkLen : work.length = r := encodeZDRegs_length W cfg
  have hWorkBits := encodeZDRegs_bits W cfg
  have hSrcLen : src.length = W := natToBits_length W _
  have hRegsLen : (encodeRegsTape work src).length = 1 + r * (W + 2) + (W + 3) := by
    rw [encodeRegsTape, List.length_append, encodeRegsPrefix_length W work hWorkBits,
      encodeSrcEntry_length, hWorkLen, hSrcLen]
  by_cases hLt : idx < r
  · simp only [regPosOf, hLt, ↓reduceIte]
    rw [encodeRegsPrefix_length W (work.take idx) (fun r hr => hWorkBits r (List.mem_of_mem_take hr)),
      List.length_take, hWorkLen, Nat.min_eq_left hLt.le, hRegsLen]
    have hMul : idx * (W + 2) + (W + 2) ≤ r * (W + 2) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hLt
    omega
  · simp only [regPosOf, hLt, ↓reduceIte]
    rw [encodeRegsPrefix_length W work hWorkBits, hWorkLen, hRegsLen]
    omega

private theorem regPosOf_succ_matches {r W N : ℕ} (cfg : ZDConfig r N)
    (idx : ℕ) (hIdxLt : idx < r) (cur : Bool × List Bool)
    (hCur : cur = (cfg.tag ⟨idx, by omega⟩, natToBits W (cfg.x ⟨idx, by omega⟩).val))
    (hWorkSplit : encodeZDRegs W cfg =
      (encodeZDRegs W cfg).take idx ++ cur :: (encodeZDRegs W cfg).drop (idx + 1))
    (ftRegs : OneSidedTape SimSym)
    (hFRegs : TapeMatches ftRegs (encodeRegsTape (encodeZDRegs W cfg) (encodeZDSrc W cfg))
      (if (encodeZDRegs W cfg).drop (idx + 1) = [] then
        (encodeRegsPrefix ((encodeZDRegs W cfg).take idx ++ [cur])).length + 1
      else (encodeRegsPrefix ((encodeZDRegs W cfg).take idx ++ [cur])).length)) :
    TapeMatches ftRegs (encodeRegsTape (encodeZDRegs W cfg) (encodeZDSrc W cfg))
      (regPosOf r (encodeZDRegs W cfg) (idx + 1)) := by
  let work := encodeZDRegs W cfg
  have hWorkLen : work.length = r := encodeZDRegs_length W cfg
  have hTakeSucc : work.take idx ++ [cur] = work.take (idx + 1) := by
    rw [List.take_succ_eq_append_getElem (by rw [hWorkLen]; exact hIdxLt)]
    congr 2
    simp [work, encodeZDRegs, hCur]
  by_cases hDropNil : work.drop (idx + 1) = []
  · have hEqR : idx + 1 = r := by
      have := congrArg List.length hDropNil
      simp [List.length_drop, hWorkLen] at this
      omega
    have hNotLt : ¬ (idx + 1 < r) := by omega
    have hTakeAll : work.take idx ++ [cur] = work := by
      simpa [work, hDropNil] using hWorkSplit.symm
    change TapeMatches ftRegs (encodeRegsTape work (encodeZDSrc W cfg)) _ at hFRegs
    have hDropNil' : (encodeZDRegs W cfg).drop (idx + 1) = [] := hDropNil
    simp only [hDropNil', ↓reduceIte] at hFRegs
    rw [hTakeAll] at hFRegs
    simpa [regPosOf, hNotLt] using hFRegs
  · have hLt1 : idx + 1 < r := by
      by_contra hGe
      have hLen0 : (work.drop (idx + 1)).length = 0 := by
        simp [List.length_drop, hWorkLen]; omega
      exact hDropNil (List.eq_nil_of_length_eq_zero hLen0)
    change TapeMatches ftRegs (encodeRegsTape work (encodeZDSrc W cfg)) _ at hFRegs
    have hDropNil' : (encodeZDRegs W cfg).drop (idx + 1) ≠ [] := hDropNil
    simp only [hDropNil', ↓reduceIte] at hFRegs
    rw [hTakeSucc] at hFRegs
    simpa [regPosOf, hLt1] using hFRegs

private theorem regPosOf_lt_succ {r W N : ℕ} (cfg : ZDConfig r N) (idx : ℕ) (hIdxLt : idx < r) :
    regPosOf r (encodeZDRegs W cfg) idx < regPosOf r (encodeZDRegs W cfg) (idx + 1) := by
  let work := encodeZDRegs W cfg
  have hWorkLen : work.length = r := encodeZDRegs_length W cfg
  have hWorkBits := encodeZDRegs_bits W cfg
  by_cases hLt1 : idx + 1 < r
  · simp only [regPosOf, hIdxLt, hLt1, ↓reduceIte]
    rw [encodeRegsPrefix_length W (work.take idx) (fun r hr => hWorkBits r (List.mem_of_mem_take hr)),
      encodeRegsPrefix_length W (work.take (idx + 1)) (fun r hr => hWorkBits r (List.mem_of_mem_take hr)),
      List.length_take, List.length_take, hWorkLen,
      Nat.min_eq_left hIdxLt.le, Nat.min_eq_left hLt1.le, Nat.succ_mul]
    omega
  · have hEqR : idx + 1 = r := by omega
    simp only [regPosOf, hIdxLt, hLt1, ↓reduceIte]
    rw [encodeRegsPrefix_length W (work.take idx) (fun r hr => hWorkBits r (List.mem_of_mem_take hr)),
      encodeRegsPrefix_length W work hWorkBits,
      List.length_take, hWorkLen, Nat.min_eq_left hIdxLt.le]
    have hMul : idx * (W + 2) + (W + 2) = r * (W + 2) := by
      have : (idx + 1) * (W + 2) = r * (W + 2) := by rw [hEqR]
      rw [Nat.succ_mul] at this
      exact this
    omega

theorem checkReachableLoop_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (r : ℕ) (hr : 1 ≤ r)
    (cfg : ZDConfig r (2 ^ configBitWidth Q Γ k S - 1))
    (hValid : ValidZDTags Q Γ n S cfg)
    (xJ : Fin ((2 ^ configBitWidth Q Γ k S - 1) + 1))
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundRegs : 1 + r * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (hBoundS : S + 4 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchRegs : TapeMatches (initTapes tRegs)
      (zdRegsContents (configBitWidth Q Γ k S) cfg) 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (.leftMark :: (natToBits (configBitWidth Q Γ k S) xJ.val).map SimSym.bit ++ [.endMark]) 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ (res : Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (checkReachableLoop M).ReachesExit input bound initTapes inHead res finalTapes finalInHead ∧
      (res = true ↔ ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = xJ ∨ (bitProblem M input S).step (cfg.x i) xJ)) ∧
      TapeMatches (finalTapes tRuler)
        (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tRegs)
        (zdRegsContents (configBitWidth Q Γ k S) cfg) 1 ∧
      TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
      TapeMatches (finalTapes tArgB)
        (.leftMark :: (natToBits (configBitWidth Q Γ k S) xJ.val).map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (finalTapes tScratch) [.leftMark] 1 := by
  classical
  let W := configBitWidth Q Γ k S
  let work := encodeZDRegs W cfg
  let src := encodeZDSrc W cfg
  let bsJ := natToBits W xJ.val
  have hBsJLen : bsJ.length = W := natToBits_length W xJ.val
  have hWorkLen : work.length = r := encodeZDRegs_length W cfg
  have hWorkBits : ∀ r' ∈ work, r'.2.length = W := encodeZDRegs_bits W cfg
  have hSrcLen : src.length = W := natToBits_length W _
  have hPowSub : (2 ^ W - 1) + 1 = 2 ^ W := by
    have := Nat.one_le_pow W 2 (by decide); omega
  have hRegsLen : (encodeRegsTape work src).length = 1 + r * (W + 2) + (W + 3) := by
    rw [encodeRegsTape, List.length_append, encodeRegsPrefix_length W work hWorkBits,
      encodeSrcEntry_length, hWorkLen, hSrcLen]
  have hBoundRegs' : 1 + r * (W + 2) + (W + 3) ≤ bound tRegs := hBoundRegs
  have hNoLeft := encodeRegsTape_no_leftMark work src
  let peekAtom : TMComponent Unit InputAlphabet SimSym 5 Bool :=
    TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (scanned tRegs = .tag true)) scanned (fun _ => .stay)
  let eqTrueBranch :=
    ((clearTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tRegs)).mapExit
      (fun _ => (.inr true : Unit ⊕ Bool))
  let stepFalseBranch :=
    bindComponent (clearTape InputAlphabet tArgA) fun _ =>
      bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
        TMComponent.atom fun _ scanned =>
          mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
            scanned (fun _ => .stay)
  let eqFalseBranch :=
    TMComponent.branch (checkValidAndStep M) eqTrueBranch stepFalseBranch
  let trueBranch :=
    bindComponent (copyRegBitsTo InputAlphabet tArgA) fun _ =>
      TMComponent.branch (compareBitTapes InputAlphabet tArgA tArgB) eqTrueBranch eqFalseBranch
  let falseBranch :=
    bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
      TMComponent.atom fun _ scanned =>
        mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
          scanned (fun _ => .stay)
  let body : Unit → _ := fun _ => TMComponent.branch peekAtom trueBranch falseBranch
  let reaches : Fin (r + 1) → Prop := fun i =>
    cfg.tag i = true ∧ (cfg.x i = xJ ∨ (bitProblem M input S).step (cfg.x i) xJ)
  let Inv : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun _ tapes _ =>
      ∃ idx : ℕ, idx ≤ r ∧
        (∀ i : Fin (r + 1), i.val < idx → ¬ reaches i) ∧
        TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
        TapeMatches (tapes tRegs) (encodeRegsTape work src) (regPosOf r work idx) ∧
        TapeMatches (tapes tArgA) [.leftMark] 1 ∧
        TapeMatches (tapes tArgB) (.leftMark :: bsJ.map SimSym.bit ++ [.endMark]) 1 ∧
        TapeMatches (tapes tScratch) [.leftMark] 1
  let measure : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (encodeRegsTape work src).length - (tapes tRegs).head
  let Post : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun res tapes _ =>
      (res = true ↔ ∃ i : Fin (r + 1), reaches i) ∧
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches (tapes tRegs) (encodeRegsTape work src) 1 ∧
      TapeMatches (tapes tArgA) [.leftMark] 1 ∧
      TapeMatches (tapes tArgB) (.leftMark :: bsJ.map SimSym.bit ++ [.endMark]) 1 ∧
      TapeMatches (tapes tScratch) [.leftMark] 1
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    rintro ⟨⟩ tapes curInHead ⟨idx, hIdxLe, hNoPrev, hMR, hMRegs, hMA, hMB, hMS⟩
    have hPosLt : regPosOf r work idx < (encodeRegsTape work src).length :=
      regPosOf_lt_length (W := W) cfg idx hIdxLe
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => change (tapes tRuler).head < bound tRuler; rw [hMR.head_eq]; omega
      | ⟨1, _⟩ => change (tapes tRegs).head < bound tRegs; rw [hMRegs.head_eq]; omega
      | ⟨2, _⟩ => change (tapes tArgA).head < bound tArgA; rw [hMA.head_eq]; omega
      | ⟨3, _⟩ => change (tapes tArgB).head < bound tArgB; rw [hMB.head_eq]; omega
      | ⟨4, _⟩ => change (tapes tScratch).head < bound tScratch; rw [hMS.head_eq]; omega
    obtain ⟨bCur, bsCur, tailSym, pSyms, sSyms, hTailNotBit, hPSymsLen,
      hBsCurLen, hTapeEq, hIfWork, hIfSrc⟩ := encodeRegsTape_curSplit (W := W) cfg hValid.1 idx hIdxLe
    have hReadTag : (tapes tRegs).cells (tapes tRegs).head = SimSym.tag bCur := by
      rw [hMRegs.read_lt (by simpa [src] using hPosLt)]
      dsimp only [work, src, W] at hTapeEq hPSymsLen ⊢
      simp only [hTapeEq, ← hPSymsLen, List.append_assoc]
      rw [List.getElem_append_right (le_refl _)]
      simp
    have hBCurEq : bCur = cfg.tag ⟨idx, by omega⟩ := by
      by_cases hLt : idx < r
      · exact (hIfWork hLt).1
      · have hEq : idx = r := by omega
        have hSrc := hIfSrc hEq
        have hFinEq : (⟨idx, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; exact hEq
        rw [hFinEq, hSrc.1]
    have hBsCurEq : bsCur = natToBits W (cfg.x ⟨idx, by omega⟩).val := by
      by_cases hLt : idx < r
      · exact (hIfWork hLt).2.1
      · have hEq : idx = r := by omega
        have hSrc := hIfSrc hEq
        have hFinEq : (⟨idx, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; exact hEq
        rw [hFinEq, hSrc.2]; rfl
    cases hBCur : bCur
    · -- bCur = false: untagged work register
      have hIdxLtR : idx < r := by
        by_contra hGe
        have hSrcT := (hIfSrc (by omega)).1
        rw [hValid.1] at hSrcT
        rw [hBCur] at hSrcT
        cases hSrcT
      have hTagF : cfg.tag ⟨idx, by omega⟩ = false := by rw [← hBCurEq, hBCur]
      have hNoPrev' : ∀ i : Fin (r + 1), i.val < idx + 1 → ¬ reaches i := by
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hiLt | hiEq
        · exact hNoPrev i hiLt
        · have : i = ⟨idx, by omega⟩ := by ext; exact hiEq
          rw [this]; rintro ⟨hT, _⟩; rw [hTagF] at hT; cases hT
      have hPeekFalse : peekAtom.ReachesExit input bound tapes curInHead false tapes curInHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes curInHead hBounds curInHead
          _ tapes _ hBounds
        · simp [mkWorkAction, hReadTag, hBCur]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hWorkSplit := (hIfWork hIdxLtR).2.2
      have hOtherRegs : ∀ j, j ≠ tRegs → (tapes j).head < bound j := fun j _ => hBounds j
      have hPrefLen : ∀ r' ∈ work.take idx, r'.2.length = W :=
        fun r' hr' => hWorkBits r' (List.mem_of_mem_take hr')
      have hSufLen : ∀ r' ∈ work.drop (idx + 1), r'.2.length = W :=
        fun r' hr' => hWorkBits r' (List.mem_of_mem_drop hr')
      have hTakeLen : (work.take idx).length = idx := by
        rw [List.length_take, hWorkLen, Nat.min_eq_left hIdxLtR.le]
      have hDropLen : (work.drop (idx + 1)).length = r - (idx + 1) := by
        rw [List.length_drop, hWorkLen]
      have hSumLen : (work.take idx).length + 1 + (work.drop (idx + 1)).length = r := by
        rw [hTakeLen, hDropLen]; omega
      obtain ⟨ftRegs, hAdv, hFRegs⟩ :=
        advanceToNextReg_work_reachesExit input bound W (work.take idx) (bCur, bsCur)
          (work.drop (idx + 1)) src hPrefLen hBsCurLen hSufLen hSrcLen
          (by rw [hSumLen]; exact hBoundRegs')
          tapes curInHead hOtherRegs
          (by dsimp only [src]; rw [← hWorkSplit]; simpa [regPosOf, hIdxLtR] using hMRegs)
      have hFRegsPos : TapeMatches ftRegs (encodeRegsTape work src) (regPosOf r work (idx + 1)) :=
        regPosOf_succ_matches (W := W) cfg idx hIdxLtR (bCur, bsCur)
          (Prod.ext (by rw [← hBCurEq]) (by rw [← hBsCurEq])) hWorkSplit ftRegs
          (by dsimp only [work, src, W] at hFRegs; rw [← hWorkSplit] at hFRegs; exact hFRegs)
      let tNext := fun j => if j = tRegs then ftRegs else tapes j
      have hPos1Le : regPosOf r work (idx + 1) ≤ (encodeRegsTape work src).length := by
        dsimp only [work, src, W]
        exact Nat.le_of_lt (regPosOf_lt_length (W := W) cfg (idx + 1) (by omega))
      have hTNextBounds : ∀ j, (tNext j).head < bound j := by
        intro j
        by_cases hj : j = tRegs
        · subst hj
          have hPosNextLt : regPosOf r work (idx + 1) < (encodeRegsTape work src).length := by
            exact regPosOf_lt_length (W := W) cfg (idx + 1) (by omega)
          change ftRegs.head < bound tRegs
          rw [hFRegsPos.head_eq]
          rw [hRegsLen] at hPosNextLt
          exact Nat.lt_of_lt_of_le hPosNextLt hBoundRegs'
        · simp [tNext, hj, hBounds j]
      have hStay : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (if true then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
            scanned (fun _ => .stay)).ReachesExit
          input bound tNext curInHead (.inl ()) tNext curInHead := by
        convert TMComponent.atom_reachesExit _ input bound tNext curInHead hTNextBounds curInHead
          _ tNext _ hTNextBounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tNext j)
      have hFalseB := bindComponent_reachesExit (advanceToNextReg InputAlphabet)
        (fun hasMore => TMComponent.atom fun _ scanned =>
          mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
            scanned (fun _ => .stay))
        input bound hAdv (by simpa using hStay)
      have hBranch := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
        input bound false hPeekFalse hFalseB
      left
      refine ⟨(), tNext, curInHead, hBranch, ⟨idx + 1, by omega, hNoPrev',
        by simpa [tNext, show tRuler ≠ tRegs by decide] using hMR,
        by simpa [tNext] using hFRegsPos,
        by simpa [tNext, show tArgA ≠ tRegs by decide] using hMA,
        by simpa [tNext, show tArgB ≠ tRegs by decide] using hMB,
        by simpa [tNext, show tScratch ≠ tRegs by decide] using hMS⟩, ?_⟩
      change (encodeRegsTape work src).length - (tNext tRegs).head <
        (encodeRegsTape work src).length - (tapes tRegs).head
      have hPosGt := regPosOf_lt_succ (W := W) cfg idx hIdxLtR
      rw [show (tNext tRegs).head = regPosOf r work (idx + 1) by simp [tNext, hFRegsPos.head_eq],
        hMRegs.head_eq]
      dsimp only [work, src, W] at hPosGt hPos1Le hMRegs ⊢
      omega
    · -- bCur = true: tagged register
      have hTagT : cfg.tag ⟨idx, by omega⟩ = true := by rw [← hBCurEq, hBCur]
      obtain ⟨cCur, hcCur⟩ := hValid.2 ⟨idx, by omega⟩ hTagT
      have hBsCurCfg : bsCur = encodeConfigBits Q Γ cCur := by
        rw [hBsCurEq, hcCur, bitEncodeConfig_val_natToBits]
      have hPeekTrue : peekAtom.ReachesExit input bound tapes curInHead true tapes curInHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes curInHead hBounds curInHead
          _ tapes _ hBounds
        · simp [mkWorkAction, hReadTag, hBCur]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hBoundRegCopy : pSyms.length + bsCur.length + 2 ≤ bound tRegs := by
        rw [hPSymsLen, hBsCurLen]
        by_cases hLt : idx < r
        · simp only [regPosOf, hLt, ↓reduceIte]
          rw [encodeRegsPrefix_length W _ (fun r' hr' => hWorkBits r' (List.mem_of_mem_take hr')),
            List.length_take, hWorkLen, Nat.min_eq_left hLt.le]
          have : idx * (W + 2) + (W + 2) ≤ r * (W + 2) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hLt
          dsimp only [W] at this ⊢; omega
        · simp only [regPosOf, hLt, ↓reduceIte]
          rw [encodeRegsPrefix_length W work hWorkBits, hWorkLen]
          dsimp only [W]; omega
      obtain ⟨ftA1, hCopyA, hFA1⟩ :=
        copyRegBitsTo_reachesExit tArgA (by decide) input bound pSyms sSyms bCur bsCur tailSym
          hTailNotBit tapes curInHead hBoundRegCopy (by rw [hBsCurLen]; exact hBoundA)
          (fun j _ _ => hBounds j)
          (by rw [hPSymsLen, ← hTapeEq]; exact hMRegs) hMA
      let t1 := fun j => if j = tRegs then tapes tRegs else if j = tArgA then ftA1 else tapes j
      have hT1Eq : t1 = fun j => if j = tArgA then ftA1 else tapes j := by
        funext j; by_cases hj : j = tRegs <;> simp [t1, hj, show tRegs ≠ tArgA by decide]
      have hT1OtherAB : ∀ j, j ≠ tArgA → j ≠ tArgB → (t1 j).head < bound j := by
        intro j hjA hjB
        by_cases hjRegs : j = tRegs
        · subst hjRegs; simp [t1, hBounds tRegs]
        · simp [t1, hjRegs, hjA, hBounds j]
      have hT1A : TapeMatches (t1 tArgA) (.leftMark :: bsCur.map SimSym.bit ++ [.endMark]) 1 := by
        simpa [t1, show tArgA ≠ tRegs by decide] using hFA1
      have hT1B : TapeMatches (t1 tArgB) (.leftMark :: bsJ.map SimSym.bit ++ [.endMark]) 1 := by
        simpa [t1, show tArgB ≠ tRegs by decide, show tArgB ≠ tArgA by decide] using hMB
      obtain ⟨ftA2, ftB2, hCmp, hFA2, hFB2⟩ :=
        compareBitTapes_reachesExit tArgA tArgB (by decide) input bound bsCur bsJ
          (by rw [hBsCurLen, hBsJLen]) (by rw [hBsCurLen]; exact hBoundA)
          (by rw [hBsJLen]; exact hBoundB) t1 curInHead hT1OtherAB hT1A hT1B
      let t2 := fun j => if j = tArgA then ftA2 else if j = tArgB then ftB2 else t1 j
      have hT2OtherA : ∀ j, j ≠ tArgA → (t2 j).head < bound j := by
        intro j hjA
        by_cases hjB : j = tArgB
        · subst hjB; simp only [t2, hjA, ↓reduceIte]; rw [hFB2.head_eq]; omega
        · by_cases hjRegs : j = tRegs
          · subst hjRegs; simp [t2, t1, hjA, hjB, hBounds tRegs]
          · simp [t2, t1, hjA, hjB, hjRegs, hBounds j]
      by_cases hEqBits : bsCur = bsJ
      · right
        have hDecEq : decide (bsCur = bsJ) = true := by simp [hEqBits]
        have hEqX : cfg.x ⟨idx, by omega⟩ = xJ := by
          have hLt1 : (cfg.x ⟨idx, by omega⟩).val < 2 ^ W := by
            have := (cfg.x ⟨idx, by omega⟩).isLt
            dsimp only [W] at hPowSub ⊢; omega
          have hLt2 : xJ.val < 2 ^ W := by
            have := xJ.isLt
            dsimp only [W] at hPowSub ⊢; omega
          have hNat := congrArg bitsToNat (hBsCurEq.symm.trans hEqBits)
          rw [bitsToNat_natToBits_of_lt hLt1, bitsToNat_natToBits_of_lt hLt2] at hNat
          exact Fin.ext hNat
        obtain ⟨ftA3, hClrA, hFA3⟩ :=
          clearTape_reachesExit tArgA input bound (bsCur.map SimSym.bit)
            (by simp [hBsCurLen]; exact hBoundA)
            (by intro s hs; rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
            t2 curInHead hT2OtherA (by simpa [t2] using hFA2)
        let t3 := fun j => if j = tArgA then ftA3 else t2 j
        have hT3OtherRegs : ∀ j, j ≠ tRegs → (t3 j).head < bound j := by
          intro j hjRegs
          by_cases hjA : j = tArgA
          · subst hjA; simp only [t3, ↓reduceIte]; rw [hFA3.head_eq]; omega
          · simp [t3, hjA, hT2OtherA j hjA]
        have hT3Regs : TapeMatches (t3 tRegs) (encodeRegsTape work src) (regPosOf r work idx) := by
          simpa [t3, t2, t1, show tRegs ≠ tArgA by decide, show tRegs ≠ tArgB by decide] using hMRegs
        obtain ⟨t4, hRewRegs, hFRegs4, hOthers4⟩ :=
          rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRegs input bound
            (encodeRegsTape work src) (by simp [encodeRegsTape, encodeRegsPrefix])
            (by simp [encodeRegsTape, encodeRegsPrefix]) hNoLeft
            (by rw [hRegsLen]; exact hBoundRegs')
            t3 curInHead hT3OtherRegs (regPosOf r work idx)
            (by
              by_cases hLt : idx < r
              · simp only [regPosOf, hLt, ↓reduceIte]
                rw [encodeRegsPrefix_length W _ (fun r' hr' => hWorkBits r' (List.mem_of_mem_take hr'))]
                omega
              · simp only [regPosOf, hLt, ↓reduceIte]
                rw [encodeRegsPrefix_length W work hWorkBits]
                omega)
            hPosLt hT3Regs
        have hSeqCR := TMComponent.seq_reachesExit (clearTape InputAlphabet tArgA)
          (rewindTape InputAlphabet tRegs) input bound hClrA hRewRegs
        have hMapCR := TMComponent.mapExit_reachesExit
          ((clearTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tRegs))
          (fun _ => (.inr true : Unit ⊕ Bool)) input bound hSeqCR
        have hBindCmp := TMComponent.branch_reachesExit
          (compareBitTapes InputAlphabet tArgA tArgB) eqTrueBranch eqFalseBranch
          input bound true (by rw [hDecEq] at hCmp; exact hCmp) hMapCR
        have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgA)
          (fun _ => TMComponent.branch (compareBitTapes InputAlphabet tArgA tArgB)
            eqTrueBranch eqFalseBranch)
          input bound hCopyA hBindCmp
        have hBranch := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
          input bound true hPeekTrue hBindCopy
        refine ⟨true, t4, curInHead, hBranch, ?_, ?_, hFRegs4, ?_, ?_, ?_⟩
        · simp only [true_iff]; exact ⟨⟨idx, by omega⟩, hTagT, Or.inl hEqX⟩
        · rw [hOthers4 tRuler (by decide)]
          simpa [t3, t2, t1, show tRuler ≠ tArgA by decide, show tRuler ≠ tArgB by decide,
            show tRuler ≠ tRegs by decide] using hMR
        · rw [hOthers4 tArgA (by decide)]; simpa [t3] using hFA3
        · rw [hOthers4 tArgB (by decide)]
          simpa [t3, t2, show tArgB ≠ tArgA by decide] using hFB2
        · rw [hOthers4 tScratch (by decide)]
          simpa [t3, t2, t1, show tScratch ≠ tArgA by decide, show tScratch ≠ tArgB by decide,
            show tScratch ≠ tRegs by decide] using hMS
      · have hDecNeq : decide (bsCur = bsJ) = false := by simp [hEqBits]
        have hNeX : cfg.x ⟨idx, by omega⟩ ≠ xJ := by
          intro hEqX; apply hEqBits; rw [hBsCurEq, hEqX]
        have hT2Regs : (t2 tRegs).head < bound tRegs := by
          have h1 : tRegs ≠ tArgA := by decide
          have h2 : tRegs ≠ tArgB := by decide
          simp [t2, t1, h1, h2, hMRegs.head_eq]
          omega
        have hT2R : TapeMatches (t2 tRuler)
            (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
          simpa [t2, t1, show tRuler ≠ tArgA by decide, show tRuler ≠ tArgB by decide,
            show tRuler ≠ tRegs by decide] using hMR
        have hT2A : TapeMatches (t2 tArgA)
            (.leftMark :: (encodeConfigBits Q Γ cCur).map SimSym.bit ++ [.endMark]) 1 := by
          rw [← hBsCurCfg]; simpa [t2] using hFA2
        have hT2B : TapeMatches (t2 tArgB) (.leftMark :: bsJ.map SimSym.bit ++ [.endMark]) 1 := by
          simpa [t2, show tArgB ≠ tArgA by decide] using hFB2
        have hT2S : TapeMatches (t2 tScratch) [.leftMark] 1 := by
          simpa [t2, t1, show tScratch ≠ tArgA by decide, show tScratch ≠ tArgB by decide,
            show tScratch ≠ tRegs by decide] using hMS
        obtain ⟨stepOk, t3, in3, hStepRun, hStepIff, hR3, hA3, hB3, hS3, hReg3⟩ :=
          checkValidAndStep_reachesExit M input bound S hS hInput cCur bsJ hBsJLen
            hBoundR hBoundA hBoundB hBoundS t2 curInHead hT2Regs hT2R hT2A hT2B hT2S
        have hT3OtherA : ∀ j, j ≠ tArgA → (t3 j).head < bound j := by
          intro j hjA
          match j with
          | ⟨0, _⟩ => change (t3 tRuler).head < bound tRuler; rw [hR3.head_eq]; omega
          | ⟨1, _⟩ => exact hReg3.symm ▸ hT2Regs
          | ⟨2, _⟩ => exact False.elim (hjA rfl)
          | ⟨3, _⟩ =>
            change (t3 tArgB).head < bound tArgB
            rw [hB3.head_eq]
            exact Nat.lt_of_lt_of_le (by omega) hBoundB
          | ⟨4, _⟩ => change (t3 tScratch).head < bound tScratch; rw [hS3.head_eq]; omega
        obtain ⟨ftA4, hClrA, hFA4⟩ :=
          clearTape_reachesExit tArgA input bound ((encodeConfigBits Q Γ cCur).map SimSym.bit)
            (by simp [encodeConfigBits_length]; exact hBoundA)
            (by intro s hs; rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
            t3 in3 hT3OtherA hA3
        let t4 := fun j => if j = tArgA then ftA4 else t3 j
        have hT4OtherRegs : ∀ j, j ≠ tRegs → (t4 j).head < bound j := by
          intro j hjRegs
          by_cases hjA : j = tArgA
          · subst hjA; simp only [t4, ↓reduceIte]; rw [hFA4.head_eq]; omega
          · simp [t4, hjA, hT3OtherA j hjA]
        have hT4Regs : TapeMatches (t4 tRegs) (encodeRegsTape work src) (regPosOf r work idx) := by
          rw [show t4 tRegs = t3 tRegs from by simp [t4, show tRegs ≠ tArgA by decide], hReg3]
          simpa [t2, t1, show tRegs ≠ tArgA by decide, show tRegs ≠ tArgB by decide] using hMRegs
        have hStepIffBit : stepOk = true ↔ (bitProblem M input S).step (cfg.x ⟨idx, by omega⟩) xJ := by
          rw [hStepIff, hcCur]
          constructor
          · rintro ⟨after, hBsJ, hM⟩
            refine ⟨cCur, after, rfl, ?_, hM⟩
            have hLt2 : xJ.val < 2 ^ W :=
              Nat.lt_of_lt_of_le xJ.isLt (Nat.le_of_eq (Nat.sub_add_cancel Nat.one_le_two_pow))
            have hNat := congrArg bitsToNat hBsJ
            rw [bitsToNat_natToBits_of_lt hLt2] at hNat
            exact Fin.ext hNat.symm
          · rintro ⟨b', a', hb', ha', hM⟩
            have hbEq : b' = cCur :=
              bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext hb')
            subst hbEq
            refine ⟨a', ?_, hM⟩
            have hVal : (bitEncodeConfig Q Γ a').val.val = xJ.val := congrArg Fin.val ha'
            have hBits := congrArg (natToBits W) hVal
            rw [bitEncodeConfig_val_natToBits] at hBits
            exact hBits.symm
        cases hSOk : stepOk
        · have hNotStep : ¬ (bitProblem M input S).step (cfg.x ⟨idx, by omega⟩) xJ := by
            intro hSt; have := hStepIffBit.mpr hSt; rw [hSOk] at this; cases this
          have hNotReachCur : ¬ reaches ⟨idx, by omega⟩ := by
            rintro ⟨_, hEq | hSt⟩
            · exact hNeX hEq
            · exact hNotStep hSt
          by_cases hIdxLtR : idx < r
          · left
            have hNoPrev' : ∀ i : Fin (r + 1), i.val < idx + 1 → ¬ reaches i := by
              intro i hi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hiLt | hiEq
              · exact hNoPrev i hiLt
              · have : i = ⟨idx, by omega⟩ := by ext; exact hiEq
                rw [this]; exact hNotReachCur
            have hWorkSplit := (hIfWork hIdxLtR).2.2
            have hPrefLen : ∀ r' ∈ work.take idx, r'.2.length = W :=
              fun r' hr' => hWorkBits r' (List.mem_of_mem_take hr')
            have hSufLen : ∀ r' ∈ work.drop (idx + 1), r'.2.length = W :=
              fun r' hr' => hWorkBits r' (List.mem_of_mem_drop hr')
            have hTakeLen : (work.take idx).length = idx := by
              rw [List.length_take, hWorkLen, Nat.min_eq_left hIdxLtR.le]
            have hDropLen : (work.drop (idx + 1)).length = r - (idx + 1) := by
              rw [List.length_drop, hWorkLen]
            obtain ⟨ftRegs, hAdv, hFRegs⟩ :=
              advanceToNextReg_work_reachesExit input bound W (work.take idx) (bCur, bsCur)
                (work.drop (idx + 1)) src hPrefLen hBsCurLen hSufLen hSrcLen
                (by rw [hTakeLen, hDropLen, show idx + 1 + (r - (idx + 1)) = r by omega]
                    dsimp only [W]; exact hBoundRegs')
                t4 in3 hT4OtherRegs
                (by dsimp only [src]; rw [← hWorkSplit]; simpa [regPosOf, hIdxLtR] using hT4Regs)
            have hFRegsPos : TapeMatches ftRegs (encodeRegsTape work src) (regPosOf r work (idx + 1)) :=
              regPosOf_succ_matches (W := W) cfg idx hIdxLtR (bCur, bsCur)
                (Prod.ext (by rw [← hBCurEq]) (by rw [← hBsCurEq])) hWorkSplit ftRegs
                (by dsimp only [work, src, W] at hFRegs; rw [← hWorkSplit] at hFRegs; exact hFRegs)
            let t5 := fun j => if j = tRegs then ftRegs else t4 j
            have hT5Bounds : ∀ j, (t5 j).head < bound j := by
              intro j
              by_cases hj : j = tRegs
              · subst hj
                have hPos1Lt : regPosOf r work (idx + 1) < (encodeRegsTape work src).length := by
                  dsimp only [work, src, W]
                  exact regPosOf_lt_length (W := W) cfg (idx + 1) (by omega)
                change ftRegs.head < bound tRegs
                rw [hFRegsPos.head_eq]
                dsimp only [work, src, W] at hPos1Lt
                rw [hRegsLen] at hPos1Lt
                exact Nat.lt_of_lt_of_le hPos1Lt hBoundRegs'
              · simp [t5, hj, hT4OtherRegs j hj]
            have hStayAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                mkWorkAction (if true then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                  scanned (fun _ => .stay)).ReachesExit
                input bound t5 in3 (.inl ()) t5 in3 := by
              convert TMComponent.atom_reachesExit _ input bound t5 in3 hT5Bounds in3
                _ t5 _ hT5Bounds
              · simp [mkWorkAction]
              · simp [mkWorkAction, moveHead]
              · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t5 j)
            have hBindAdv := bindComponent_reachesExit (advanceToNextReg InputAlphabet)
              (fun hasMore => TMComponent.atom fun _ scanned =>
                mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                  scanned (fun _ => .stay))
              input bound hAdv (by simpa using hStayAtom)
            have hBindClr := bindComponent_reachesExit (clearTape InputAlphabet tArgA)
              (fun _ => bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
                TMComponent.atom fun _ scanned =>
                  mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                    scanned (fun _ => .stay))
              input bound hClrA hBindAdv
            have hBindStep := TMComponent.branch_reachesExit
              (checkValidAndStep M) eqTrueBranch stepFalseBranch
              input bound false (by rw [hSOk] at hStepRun; exact hStepRun) hBindClr
            have hBindCmp := TMComponent.branch_reachesExit
              (compareBitTapes InputAlphabet tArgA tArgB) eqTrueBranch eqFalseBranch
              input bound false (by rw [hDecNeq] at hCmp; exact hCmp) hBindStep
            dsimp only [t1] at hBindCmp
            have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgA)
              (fun _ => TMComponent.branch (compareBitTapes InputAlphabet tArgA tArgB)
                eqTrueBranch eqFalseBranch)
              input bound hCopyA hBindCmp
            have hBranch := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
              input bound true hPeekTrue hBindCopy
            refine ⟨(), t5, in3, hBranch, ⟨idx + 1, by omega, hNoPrev',
              by simpa [t5, t4, show tRuler ≠ tRegs by decide, show tRuler ≠ tArgA by decide] using hR3,
              by simpa [t5] using hFRegsPos,
              by simpa [t5, t4, show tArgA ≠ tRegs by decide] using hFA4,
              by simpa [t5, t4, show tArgB ≠ tRegs by decide, show tArgB ≠ tArgA by decide] using hB3,
              by simpa [t5, t4, show tScratch ≠ tRegs by decide, show tScratch ≠ tArgA by decide] using hS3⟩, ?_⟩
            change (encodeRegsTape work src).length - (t5 tRegs).head <
              (encodeRegsTape work src).length - (tapes tRegs).head
            have hPosGt := regPosOf_lt_succ (W := W) cfg idx hIdxLtR
            have hPos1Le : regPosOf r work (idx + 1) ≤ (encodeRegsTape work src).length := by
              dsimp only [work, src, W]
              exact Nat.le_of_lt (regPosOf_lt_length (W := W) cfg (idx + 1) (by omega))
            rw [show (t5 tRegs).head = regPosOf r work (idx + 1) by simp [t5, hFRegsPos.head_eq],
              hMRegs.head_eq]
            dsimp only [work, src, W] at hPosGt hPos1Le hMRegs ⊢
            omega
          · right
            have hEqR : idx = r := by omega
            have hNoAll : ∀ i : Fin (r + 1), ¬ reaches i := by
              intro i
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hiLt | hiEq
              · exact hNoPrev i (by omega)
              · have : i = ⟨idx, by omega⟩ := by ext; simp [hiEq, hEqR]
                rw [this]; exact hNotReachCur
            obtain ⟨ftRegs, hAdv, hFRegs⟩ :=
              advanceToNextReg_src_reachesExit input bound W work src hWorkBits hSrcLen
                (by rw [hWorkLen]; exact hBoundRegs') t4 in3 hT4OtherRegs
                (by simpa [regPosOf, hIdxLtR] using hT4Regs)
            let t5 := fun j => if j = tRegs then ftRegs else t4 j
            have hT5Bounds : ∀ j, (t5 j).head < bound j := by
              intro j
              by_cases hj : j = tRegs
              · subst hj; simpa [t5, hFRegs.head_eq] using (by omega : 1 < bound tRegs)
              · simp [t5, hj, hT4OtherRegs j hj]
            have hStayAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                mkWorkAction (if false then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                  scanned (fun _ => .stay)).ReachesExit
                input bound t5 in3 (.inr false) t5 in3 := by
              convert TMComponent.atom_reachesExit _ input bound t5 in3 hT5Bounds in3
                _ t5 _ hT5Bounds
              · simp [mkWorkAction]
              · simp [mkWorkAction, moveHead]
              · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t5 j)
            have hBindAdv := bindComponent_reachesExit (advanceToNextReg InputAlphabet)
              (fun hasMore => TMComponent.atom fun _ scanned =>
                mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                  scanned (fun _ => .stay))
              input bound hAdv (by simpa using hStayAtom)
            have hBindClr := bindComponent_reachesExit (clearTape InputAlphabet tArgA)
              (fun _ => bindComponent (advanceToNextReg InputAlphabet) fun hasMore =>
                TMComponent.atom fun _ scanned =>
                  mkWorkAction (if hasMore then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool))
                    scanned (fun _ => .stay))
              input bound hClrA hBindAdv
            have hBindStep := TMComponent.branch_reachesExit
              (checkValidAndStep M) eqTrueBranch stepFalseBranch
              input bound false (by rw [hSOk] at hStepRun; exact hStepRun) hBindClr
            have hBindCmp := TMComponent.branch_reachesExit
              (compareBitTapes InputAlphabet tArgA tArgB) eqTrueBranch eqFalseBranch
              input bound false (by rw [hDecNeq] at hCmp; exact hCmp) hBindStep
            have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgA)
              (fun _ => TMComponent.branch (compareBitTapes InputAlphabet tArgA tArgB)
                eqTrueBranch eqFalseBranch)
              input bound hCopyA hBindCmp
            have hBranch := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
              input bound true hPeekTrue hBindCopy
            refine ⟨false, t5, in3, hBranch, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [Bool.false_eq_true, false_iff, not_exists]
              exact hNoAll
            · simpa [t5, t4, show tRuler ≠ tRegs by decide, show tRuler ≠ tArgA by decide] using hR3
            · simpa [t5] using hFRegs
            · simpa [t5, t4, show tArgA ≠ tRegs by decide] using hFA4
            · simpa [t5, t4, show tArgB ≠ tRegs by decide, show tArgB ≠ tArgA by decide] using hB3
            · simpa [t5, t4, show tScratch ≠ tRegs by decide, show tScratch ≠ tArgA by decide] using hS3
        · right
          have hStepTrue : (bitProblem M input S).step (cfg.x ⟨idx, by omega⟩) xJ :=
            hStepIffBit.mp hSOk
          obtain ⟨ftRegs, hRewRegs, hFRegs4, hOthers4⟩ :=
            rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRegs input bound
              (encodeRegsTape work src) (by simp [encodeRegsTape, encodeRegsPrefix])
              (by simp [encodeRegsTape, encodeRegsPrefix]) hNoLeft
              (by rw [hRegsLen]; exact hBoundRegs')
              t4 in3 hT4OtherRegs (regPosOf r work idx)
              (by
                by_cases hLt : idx < r
                · simp only [regPosOf, hLt, ↓reduceIte]
                  rw [encodeRegsPrefix_length W _ (fun r' hr' => hWorkBits r' (List.mem_of_mem_take hr'))]
                  omega
                · simp only [regPosOf, hLt, ↓reduceIte]
                  rw [encodeRegsPrefix_length W work hWorkBits]
                  omega)
              hPosLt hT4Regs
          have hSeqCR := TMComponent.seq_reachesExit (clearTape InputAlphabet tArgA)
            (rewindTape InputAlphabet tRegs) input bound hClrA hRewRegs
          have hMapCR := TMComponent.mapExit_reachesExit
            ((clearTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tRegs))
            (fun _ => (.inr true : Unit ⊕ Bool)) input bound hSeqCR
          have hBindStep := TMComponent.branch_reachesExit
            (checkValidAndStep M) eqTrueBranch stepFalseBranch
            input bound true (by rw [hSOk] at hStepRun; exact hStepRun) hMapCR
          have hBindCmp := TMComponent.branch_reachesExit
            (compareBitTapes InputAlphabet tArgA tArgB) eqTrueBranch eqFalseBranch
            input bound false (by rw [hDecNeq] at hCmp; exact hCmp) hBindStep
          have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgA)
            (fun _ => TMComponent.branch (compareBitTapes InputAlphabet tArgA tArgB)
              eqTrueBranch eqFalseBranch)
            input bound hCopyA hBindCmp
          have hBranch := TMComponent.branch_reachesExit peekAtom trueBranch falseBranch
            input bound true hPeekTrue hBindCopy
          refine ⟨true, ftRegs, in3, hBranch, ?_, ?_, hFRegs4, ?_, ?_, ?_⟩
          · simp only [true_iff]; exact ⟨⟨idx, by omega⟩, hTagT, Or.inr hStepTrue⟩
          · rw [hOthers4 tRuler (by decide)]
            simpa [t4, show tRuler ≠ tArgA by decide] using hR3
          · rw [hOthers4 tArgA (by decide)]; simpa [t4] using hFA4
          · rw [hOthers4 tArgB (by decide)]
            simpa [t4, show tArgB ≠ tArgA by decide] using hB3
          · rw [hOthers4 tScratch (by decide)]
            simpa [t4, show tScratch ≠ tArgA by decide] using hS3
  have hInitInv : Inv () initTapes inHead := by
    refine ⟨0, Nat.zero_le r, fun i hi => by omega, hMatchR, ?_, hMatchA, hMatchB, hMatchS⟩
    have hr0 : 0 < r := by omega
    simp only [regPosOf, hr0, ↓reduceIte, List.take_zero, encodeRegsPrefix_nil]
    exact hMatchRegs
  obtain ⟨res, finalTapes, finalInHead, hLoop, hResIff, hFR, hFRegs, hFA, hFB, hFS⟩ :=
    loopWithState_reachesExit () body input bound Inv measure Post hStep initTapes inHead hInitInv
  dsimp only [body, peekAtom, trueBranch, falseBranch, eqTrueBranch, eqFalseBranch,
    stepFalseBranch] at hLoop
  exact ⟨res, finalTapes, finalInHead, hLoop, hResIff, hFR, hFRegs, hFA, hFB, hFS⟩

end SavitchLemma

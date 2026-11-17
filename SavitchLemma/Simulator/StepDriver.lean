module

public import SavitchLemma.Simulator.ReachableLoop
public import SavitchLemma.RegisterTape.FindUntagged
public import SavitchLemma.RegisterTape.Tag
public import SavitchLemma.RegisterTape.Increment
public import SavitchLemma.AcceptingZD

@[expose] public section

/-!
# Concrete D1–D3 Step Driver

Composes `findFirstUntagged`, `copyRegBitsTo`, `rewindTape`, `checkReachableLoop`,
`checkAccepting`, `clearTape`, `findFirstUntaggedAndTag`, and `incFirstRegBelowMax`
to implement one iteration of Savitch's `D1`–`D3` machine (`zdAcceptingStep`).
-/

namespace SavitchLemma

/-! ### Helper lemmas connecting `ZDConfig` operations to `encodeZDRegs` -/

private theorem encodeZDRegs_bits' {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    ∀ x ∈ encodeZDRegs W cfg, x.2.length = W := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨j, rfl⟩
  exact natToBits_length W _

theorem two_le_configBitWidth' (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    2 ≤ configBitWidth Q Γ k S := by
  unfold configBitWidth; omega

theorem one_lt_two_pow_sub_one' {W : ℕ} (hW : 2 ≤ W) : 1 < 2 ^ W - 1 := by
  have h4 : 4 ≤ 2 ^ W := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  omega

private theorem bitEncodeConfig_val_natToBits' {Q Γ : Type*} {k n S : ℕ}
    [Fintype Q] [Fintype Γ] (c : TMConfig Q Γ k n S) :
    natToBits (configBitWidth Q Γ k S) (bitEncodeConfig Q Γ c).val = encodeConfigBits Q Γ c := by
  have hLen : (encodeConfigBits Q Γ c).length = configBitWidth Q Γ k S :=
    encodeConfigBits_length Q Γ c
  change natToBits (configBitWidth Q Γ k S) (bitsToNat (encodeConfigBits Q Γ c)) =
    encodeConfigBits Q Γ c
  rw [← hLen, natToBits_bitsToNat]

private theorem firstUntagged_none_iff {r W N : ℕ} (cfg : ZDConfig r N) :
    firstUntagged cfg = none ↔ ∀ r' ∈ encodeZDRegs W cfg, r'.1 = true := by
  unfold firstUntagged encodeZDRegs
  rw [List.find?_eq_none]
  constructor
  · intro h r' hr'
    rcases List.mem_ofFn.mp hr' with ⟨i, rfl⟩
    simpa using h i (List.mem_finRange i)
  · intro h i _
    simpa using h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

private theorem firstUntagged_some_of_split {r W N : ℕ} (cfg : ZDConfig r N)
    (pref : List (Bool × List Bool)) (cur : Bool × List Bool) (suf : List (Bool × List Bool))
    (hSplit : encodeZDRegs W cfg = pref ++ cur :: suf)
    (hCurF : cur.1 = false) (hPrefT : ∀ r' ∈ pref, r'.1 = true) :
    ∃ hLt : pref.length < r,
      firstUntagged cfg = some ⟨pref.length, hLt⟩ ∧
      cur.2 = natToBits W (cfg.x ⟨pref.length, by omega⟩).val := by
  have hLen : (encodeZDRegs W cfg).length = r := encodeZDRegs_length W cfg
  have hPrefLt : pref.length < r := by
    have := congrArg List.length hSplit
    simp [hLen] at this
    omega
  refine ⟨hPrefLt, ?_, ?_⟩
  · unfold firstUntagged
    rw [List.find?_eq_some_iff_getElem]
    have hGet : (encodeZDRegs W cfg)[pref.length]'(by omega) = cur := by
      have := congrArg (fun l => l[pref.length]?) hSplit
      simp only [List.getElem?_eq_getElem (by omega : pref.length < (encodeZDRegs W cfg).length),
        List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hCurEq : cur = (cfg.tag ⟨pref.length, by omega⟩,
        natToBits W (cfg.x ⟨pref.length, by omega⟩).val) := by
      rw [← hGet]; simp [encodeZDRegs]
    refine ⟨?_, pref.length, by simp [hPrefLt], by simp, ?_⟩
    · simp only [Fin.castSucc_mk, Bool.not_eq_true']
      have := congrArg Prod.fst hCurEq
      rw [hCurF] at this
      exact this.symm
    · intro k hk
      have hkLt : k < r := Nat.lt_trans hk hPrefLt
      have hGetK : (encodeZDRegs W cfg)[k]'(by omega) = pref[k]'hk := by
        have := congrArg (fun l => l[k]?) hSplit
        simp only [List.getElem?_eq_getElem (by omega : k < (encodeZDRegs W cfg).length),
          List.getElem?_append_left hk,
          List.getElem?_eq_getElem hk] at this
        exact Option.some.inj this
      have hMemK : (encodeZDRegs W cfg)[k]'(by omega) ∈ pref := by
        rw [hGetK]; exact List.getElem_mem _
      have hT := hPrefT _ hMemK
      simp only [encodeZDRegs, List.getElem_ofFn, Fin.castSucc_mk] at hT
      simp [hT]
  · have hGet : (encodeZDRegs W cfg)[pref.length]'(by omega) = cur := by
      have := congrArg (fun l => l[pref.length]?) hSplit
      simp only [List.getElem?_eq_getElem (by omega : pref.length < (encodeZDRegs W cfg).length),
        List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at this
      exact Option.some.inj this
    rw [← hGet]
    simp [encodeZDRegs]

private theorem firstBelowMax_none_iff {r W : ℕ} (cfg : ZDConfig r (2 ^ W - 1)) :
    firstBelowMax cfg = none ↔ ∀ r' ∈ encodeZDRegs W cfg, false ∉ r'.2 := by
  unfold firstBelowMax encodeZDRegs
  rw [List.find?_eq_none]
  constructor
  · intro h r' hr'
    rcases List.mem_ofFn.mp hr' with ⟨i, rfl⟩
    have hGe : ¬ (cfg.x i.castSucc).val < 2 ^ W - 1 := by simpa using h i (List.mem_finRange i)
    have hLt : (cfg.x i.castSucc).val < 2 ^ W :=
      Nat.lt_of_lt_of_le (cfg.x i.castSucc).isLt (Nat.le_of_eq (Nat.sub_add_cancel Nat.one_le_two_pow))
    intro hMem
    exact hGe ((false_mem_natToBits_iff_lt hLt).mp hMem)
  · intro h i _
    have hNo := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have hLt : (cfg.x i.castSucc).val < 2 ^ W :=
      Nat.lt_of_lt_of_le (cfg.x i.castSucc).isLt (Nat.le_of_eq (Nat.sub_add_cancel Nat.one_le_two_pow))
    simp only [decide_eq_true_eq]
    intro hLtN
    exact hNo ((false_mem_natToBits_iff_lt hLt).mpr hLtN)

private theorem firstBelowMax_some_of_split {r W : ℕ} (cfg : ZDConfig r (2 ^ W - 1))
    (pref : List (Bool × List Bool)) (cur : Bool × List Bool) (suf : List (Bool × List Bool))
    (hSplit : encodeZDRegs W cfg = pref ++ cur :: suf)
    (hCurF : false ∈ cur.2) (hPrefNo : ∀ r' ∈ pref, false ∉ r'.2) :
    ∃ hLt : pref.length < r,
      firstBelowMax cfg = some ⟨pref.length, hLt⟩ ∧
      cur.2 = natToBits W (cfg.x ⟨pref.length, by omega⟩).val ∧
      (cfg.x ⟨pref.length, by omega⟩).val < 2 ^ W - 1 := by
  have hLen : (encodeZDRegs W cfg).length = r := encodeZDRegs_length W cfg
  have hPrefLt : pref.length < r := by
    have := congrArg List.length hSplit
    simp [hLen] at this
    omega
  have hGet : (encodeZDRegs W cfg)[pref.length]'(by omega) = cur := by
    have := congrArg (fun l => l[pref.length]?) hSplit
    simp only [List.getElem?_eq_getElem (by omega : pref.length < (encodeZDRegs W cfg).length),
      List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at this
    exact Option.some.inj this
  have hCurEq : cur.2 = natToBits W (cfg.x ⟨pref.length, by omega⟩).val := by
    rw [← hGet]; simp [encodeZDRegs]
  have hLtPow : (cfg.x ⟨pref.length, by omega⟩).val < 2 ^ W :=
    Nat.lt_of_lt_of_le (cfg.x ⟨pref.length, by omega⟩).isLt
      (Nat.le_of_eq (Nat.sub_add_cancel Nat.one_le_two_pow))
  have hLtN : (cfg.x ⟨pref.length, by omega⟩).val < 2 ^ W - 1 :=
    (false_mem_natToBits_iff_lt hLtPow).mp (hCurEq ▸ hCurF)
  refine ⟨hPrefLt, ?_, hCurEq, hLtN⟩
  unfold firstBelowMax
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp [hLtN], pref.length, by simp [hPrefLt], by simp, ?_⟩
  · intro k hk
    have hkLt : k < r := Nat.lt_trans hk hPrefLt
    have hGetK : (encodeZDRegs W cfg)[k]'(by omega) = pref[k]'hk := by
      have := congrArg (fun l => l[k]?) hSplit
      simp only [List.getElem?_eq_getElem (by omega : k < (encodeZDRegs W cfg).length),
        List.getElem?_append_left hk,
        List.getElem?_eq_getElem hk] at this
      exact Option.some.inj this
    have hMemK : (encodeZDRegs W cfg)[k]'(by omega) ∈ pref := by
      rw [hGetK]; exact List.getElem_mem _
    have hNoK := hPrefNo _ hMemK
    simp only [encodeZDRegs, List.getElem_ofFn, Fin.castSucc_mk] at hNoK
    have hLtPowK : (cfg.x ⟨k, by omega⟩).val < 2 ^ W :=
      Nat.lt_of_lt_of_le (cfg.x ⟨k, by omega⟩).isLt
        (Nat.le_of_eq (Nat.sub_add_cancel Nat.one_le_two_pow))
    simp only [List.getElem_finRange, Bool.not_eq_true', decide_eq_false_iff_not]
    intro hLtNK
    exact hNoK ((false_mem_natToBits_iff_lt hLtPowK).mpr (by simpa using hLtNK))

private theorem encodeZDRegs_updateAndReset {r W N : ℕ} (hN : 1 < N)
    (cfg : ZDConfig r N) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (hSplit : encodeZDRegs W cfg = pref ++ cur :: suf)
    (hLt : pref.length < r) (newTag : Bool) (newVal : Fin (N + 1))
    (hNewVal : natToBits W newVal.val = if newTag then cur.2 else incBits cur.2) :
    encodeZDRegs W (updateAndReset hN cfg ⟨pref.length, hLt⟩ newVal newTag) =
      pref.map (fun _ => (false, natToBits W 1)) ++
        (newTag, if newTag then cur.2 else incBits cur.2) :: suf := by
  have hLen : (encodeZDRegs W cfg).length = r := encodeZDRegs_length W cfg
  have hSufLen : suf.length = r - (pref.length + 1) := by
    have := congrArg List.length hSplit
    simp [hLen] at this
    omega
  apply List.ext_getElem
  · simp [encodeZDRegs_length, hSufLen]; omega
  · intro i hi1 hi2
    rw [encodeZDRegs_length] at hi1
    simp only [encodeZDRegs, List.getElem_ofFn]
    by_cases hLtP : i < pref.length
    · have hNe : i ≠ pref.length := by omega
      rw [List.getElem_append_left (by simp [hLtP])]
      simp [updateAndReset, hNe, hLtP, firstCode]
    · by_cases hEqP : i = pref.length
      · subst hEqP
        rw [List.getElem_append_right (by simp)]
        simp only [updateAndReset, List.length_map, Nat.sub_self, List.getElem_cons_zero,
          Fin.val_castSucc, ↓reduceIte, hNewVal]
      · have hGtP : pref.length < i := by omega
        have hNotLt : ¬ i < pref.length := by omega
        have hSufGet : suf[i - pref.length - 1]'(by omega) =
            (encodeZDRegs W cfg)[i]'(by omega) := by
          have := congrArg (fun l => l[i]?) hSplit
          rw [List.getElem?_eq_getElem (by omega : i < (encodeZDRegs W cfg).length),
            List.getElem?_append_right (by omega : pref.length ≤ i)] at this
          have hIdx : i - pref.length = (i - pref.length - 1) + 1 := by omega
          rw [hIdx, List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega)] at this
          exact (Option.some.inj this).symm
        simp only [updateAndReset, Fin.val_castSucc,
          show i ≠ pref.length from hEqP, show ¬ i < pref.length from hNotLt, ↓reduceIte]
        rw [List.getElem_append_right (by simp; omega)]
        have hSub : i - (pref.map (fun _ => (false, natToBits W 1))).length =
            (i - pref.length - 1) + 1 := by simp; omega
        simp only [hSub, List.getElem_cons_succ]
        rw [hSufGet]
        simp [encodeZDRegs]

/-! ### Concrete D1–D3 step component -/

/-- Concrete single step of Savitch's `D1`–`D3` machine on the 5 simulation tapes.
Exits with `.inl ()` to continue looping, `.inr true` to accept, or `.inr false` to reject. -/
noncomputable def zdConcreteStep {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  let backtrackBranch :=
    (incFirstRegBelowMax InputAlphabet).mapExit fun hasNext =>
      if hasNext then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool)
  let accTrueBranch :=
    TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay)
  let accFalseBranch :=
    bindComponent (clearTape InputAlphabet tArgB) fun _ =>
      (findFirstUntaggedAndTag InputAlphabet).mapExit fun _ => (.inl () : Unit ⊕ Bool)
  let reachTrueBranch := (checkAccepting M).branch accTrueBranch accFalseBranch
  let reachFalseBranch := bindComponent (clearTape InputAlphabet tArgB) fun _ => backtrackBranch
  let foundUntaggedBranch :=
    bindComponent (copyRegBitsTo InputAlphabet tArgB) fun _ =>
      bindComponent (rewindTape InputAlphabet tRegs) fun _ =>
        (checkReachableLoop M).branch reachTrueBranch reachFalseBranch
  (findFirstUntagged InputAlphabet).branch
    foundUntaggedBranch
    backtrackBranch

theorem zdConcreteStep_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (r : ℕ) (hr : 1 ≤ r)
    (cfg : ZDConfig r (2 ^ configBitWidth Q Γ k S - 1))
    (hValid : ValidZDTags Q Γ n S cfg)
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
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    let W := configBitWidth Q Γ k S
    let hN : 1 < 2 ^ W - 1 := one_lt_two_pow_sub_one' (two_le_configBitWidth' Q Γ k S)
    ∃ (res : Unit ⊕ Bool) (finalTapes : Fin 5 → OneSidedTape SimSym) (finalInHead : Fin (n + 2)),
      (zdConcreteStep M).ReachesExit input bound initTapes inHead res finalTapes finalInHead ∧
      match zdAcceptingStep (bitProblem M input S) hN (bitIsAccepting M n S) cfg with
      | .accept => res = .inr true
      | .reject => res = .inr false
      | .running next =>
        res = .inl () ∧
        ValidZDTags Q Γ n S next ∧
        TapeMatches (finalTapes tRuler)
          (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
        TapeMatches (finalTapes tRegs) (zdRegsContents W next) 1 ∧
        TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
        TapeMatches (finalTapes tArgB) [.leftMark] 1 ∧
        TapeMatches (finalTapes tScratch) [.leftMark] 1 := by
  classical
  let W := configBitWidth Q Γ k S
  have hW : 1 ≤ W := Nat.le_trans (by decide) (two_le_configBitWidth' Q Γ k S)
  have hN : 1 < 2 ^ W - 1 := one_lt_two_pow_sub_one' (two_le_configBitWidth' Q Γ k S)
  let work := encodeZDRegs W cfg
  let src := encodeZDSrc W cfg
  have hWorkLen : work.length = r := encodeZDRegs_length W cfg
  have hWorkBits : ∀ r' ∈ work, r'.2.length = W := encodeZDRegs_bits' W cfg
  have hSrcLen : src.length = W := encodeZDSrc_length W cfg
  have hBounds0 : ∀ j, j ≠ tRegs → (initTapes j).head < bound j := by
    intro j hj
    match j with
    | ⟨0, _⟩ => change (initTapes tRuler).head < bound tRuler; rw [hMatchR.head_eq]; omega
    | ⟨1, _⟩ => exact False.elim (hj rfl)
    | ⟨2, _⟩ => change (initTapes tArgA).head < bound tArgA; rw [hMatchA.head_eq]; omega
    | ⟨3, _⟩ => change (initTapes tArgB).head < bound tArgB; rw [hMatchB.head_eq]; omega
    | ⟨4, _⟩ => change (initTapes tScratch).head < bound tScratch; rw [hMatchS.head_eq]; omega
  let backtrackBranch :=
    (incFirstRegBelowMax InputAlphabet).mapExit fun hasNext =>
      if hasNext then (.inl () : Unit ⊕ Bool) else (.inr false : Unit ⊕ Bool)
  let accTrueBranch :=
    TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay)
  let accFalseBranch :=
    bindComponent (clearTape InputAlphabet tArgB) fun _ =>
      (findFirstUntaggedAndTag InputAlphabet).mapExit fun _ => (.inl () : Unit ⊕ Bool)
  let reachTrueBranch := (checkAccepting M).branch accTrueBranch accFalseBranch
  let reachFalseBranch := bindComponent (clearTape InputAlphabet tArgB) fun _ => backtrackBranch
  let foundUntaggedBranch :=
    bindComponent (copyRegBitsTo InputAlphabet tArgB) fun _ =>
      bindComponent (rewindTape InputAlphabet tRegs) fun _ =>
        (checkReachableLoop M).branch reachTrueBranch reachFalseBranch
  have hBacktrack : ∀ (tapes : Fin 5 → OneSidedTape SimSym) (ih : Fin (n + 2)),
      TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 →
      TapeMatches (tapes tRegs) (zdRegsContents W cfg) 1 →
      TapeMatches (tapes tArgA) [.leftMark] 1 →
      TapeMatches (tapes tArgB) [.leftMark] 1 →
      TapeMatches (tapes tScratch) [.leftMark] 1 →
      ∃ (res : Unit ⊕ Bool) (finalTapes : Fin 5 → OneSidedTape SimSym),
        backtrackBranch.ReachesExit input bound tapes ih res finalTapes ih ∧
        match zdBacktrack hN cfg with
        | none => res = .inr false
        | some next =>
          res = .inl () ∧
          ValidZDTags Q Γ n S next ∧
          TapeMatches (finalTapes tRuler)
            (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
          TapeMatches (finalTapes tRegs) (zdRegsContents W next) 1 ∧
          TapeMatches (finalTapes tArgA) [.leftMark] 1 ∧
          TapeMatches (finalTapes tArgB) [.leftMark] 1 ∧
          TapeMatches (finalTapes tScratch) [.leftMark] 1 := by
    intro tapes ih hMR hMRegs hMA hMB hMS
    have hOth : ∀ j, j ≠ tRegs → (tapes j).head < bound j := by
      intro j hj
      match j with
      | ⟨0, _⟩ => change (tapes tRuler).head < bound tRuler; rw [hMR.head_eq]; omega
      | ⟨1, _⟩ => exact False.elim (hj rfl)
      | ⟨2, _⟩ => change (tapes tArgA).head < bound tArgA; rw [hMA.head_eq]; omega
      | ⟨3, _⟩ => change (tapes tArgB).head < bound tArgB; rw [hMB.head_eq]; omega
      | ⟨4, _⟩ => change (tapes tScratch).head < bound tScratch; rw [hMS.head_eq]; omega
    rcases incFirstRegBelowMax_reachesExit input bound W hW work src hWorkBits hSrcLen
        (by rw [hWorkLen]; exact hBoundRegs) tapes ih hOth hMRegs with
      ⟨pref, cur, suf, hSplit, hCurF, hPrefNo, ft, hInc, hFM⟩ |
      ⟨hNoF, ft, hInc, hFM⟩
    · obtain ⟨hLt, hFBM, hCurBits, hLtN⟩ := firstBelowMax_some_of_split cfg pref cur suf hSplit hCurF hPrefNo
      have hValLt : (cfg.x ⟨pref.length, by omega⟩).val < 2 ^ W - 1 := hLtN
      let next := updateAndReset hN cfg ⟨pref.length, hLt⟩
        ⟨(cfg.x ⟨pref.length, by omega⟩).val + 1, by omega⟩ false
      have hBackSome : zdBacktrack hN cfg = some next := by
        have hLtN' : (cfg.x (Fin.castSucc ⟨pref.length, hLt⟩)).val < 2 ^ W - 1 := hLtN
        unfold zdBacktrack; rw [hFBM]; dsimp only; simp only [hLtN', ↓reduceDIte]; rfl
      have hIncVal : natToBits W ((cfg.x ⟨pref.length, by omega⟩).val + 1) = incBits cur.2 := by
        rw [hCurBits, incBits_natToBits hLtN]
      have hRegsNext : encodeZDRegs W next =
          pref.map (fun _ => (false, natToBits W 1)) ++ (false, incBits cur.2) :: suf :=
        encodeZDRegs_updateAndReset hN cfg pref cur suf hSplit hLt false _
          (by simpa [W] using hIncVal)
      have hSrcNext : encodeZDSrc W next = src := by
        simp only [src, encodeZDSrc]
        rw [(updateAndReset_preserves_source hN cfg _ _ _).1]
      have hValidNext : ValidZDTags Q Γ n S next := by
        refine ⟨?_, ?_⟩
        · rw [(updateAndReset_preserves_source hN cfg _ _ _).2]; exact hValid.1
        · intro i hi
          have hI : i.val ≠ pref.length ∧ ¬ i.val < pref.length := by
            by_cases h1 : i.val = pref.length
            · simp [next, updateAndReset, h1] at hi
            · by_cases h2 : i.val < pref.length
              · simp [next, updateAndReset, h1, h2] at hi
              · exact ⟨h1, h2⟩
          have hTagOld : cfg.tag i = true := by simpa [next, updateAndReset, hI.1, hI.2] using hi
          obtain ⟨c, hc⟩ := hValid.2 i hTagOld
          exact ⟨c, by simpa [next, updateAndReset, hI.1, hI.2] using hc⟩
      refine ⟨.inl (), fun j => if j = tRegs then ft else tapes j,
        TMComponent.mapExit_reachesExit _ _ input bound hInc, ?_⟩
      rw [hBackSome]
      refine ⟨rfl, hValidNext,
        by simpa [show tRuler ≠ tRegs by decide] using hMR,
        by simpa [zdRegsContents, hRegsNext, hSrcNext] using hFM,
        by simpa [show tArgA ≠ tRegs by decide] using hMA,
        by simpa [show tArgB ≠ tRegs by decide] using hMB,
        by simpa [show tScratch ≠ tRegs by decide] using hMS⟩
    · have hFBM : firstBelowMax cfg = none := (firstBelowMax_none_iff cfg).mpr hNoF
      have hBackNone : zdBacktrack hN cfg = none := by simp [zdBacktrack, hFBM]
      refine ⟨.inr false, fun j => if j = tRegs then ft else tapes j,
        TMComponent.mapExit_reachesExit _ _ input bound hInc, ?_⟩
      rw [hBackNone]
  rcases findFirstUntagged_reachesExit input bound W work src hWorkBits hSrcLen
      (by rw [hWorkLen]; exact hBoundRegs) initTapes inHead hBounds0 hMatchRegs with
    ⟨hAllT, ft0, hFindF, hM0⟩ | ⟨pref, cur, suf, hSplit, hCurF, hPrefT, ft0, hFindT, hM0⟩
  · have hFU : firstUntagged cfg = none := (firstUntagged_none_iff cfg).mpr hAllT
    let t0 := fun j => if j = tRegs then ft0 else initTapes j
    obtain ⟨res, finalTapes, hBT, hPostBT⟩ := hBacktrack t0 inHead
      (by simpa [t0, show tRuler ≠ tRegs by decide] using hMatchR)
      (by simpa [t0, zdRegsContents, work, src] using hM0)
      (by simpa [t0, show tArgA ≠ tRegs by decide] using hMatchA)
      (by simpa [t0, show tArgB ≠ tRegs by decide] using hMatchB)
      (by simpa [t0, show tScratch ≠ tRegs by decide] using hMatchS)
    refine ⟨res, finalTapes, inHead,
      TMComponent.branch_reachesExit _ foundUntaggedBranch backtrackBranch input bound false hFindF hBT, ?_⟩
    simp only [zdAcceptingStep, hFU]
    cases hBTRes : zdBacktrack hN cfg <;> simp [hBTRes] at hPostBT ⊢ <;> exact hPostBT
  · obtain ⟨hLt, hFUSome, hCurBits⟩ := firstUntagged_some_of_split cfg pref cur suf hSplit hCurF hPrefT
    let t0 := fun j => if j = tRegs then ft0 else initTapes j
    have hCurLen : cur.2.length = W := hWorkBits cur (by rw [hSplit]; simp)
    have hPrefBits : ∀ r' ∈ pref, r'.2.length = W := fun r' hr' => hWorkBits r' (by rw [hSplit]; simp [hr'])
    have hSufBits : ∀ r' ∈ suf, r'.2.length = W := fun r' hr' => hWorkBits r' (by rw [hSplit]; simp [hr'])
    have hPrefPos : (encodeRegsPrefix pref).length = 1 + pref.length * (W + 2) :=
      encodeRegsPrefix_length W pref hPrefBits
    have hSplitLen : pref.length + 1 + suf.length = r := by
      have := congrArg List.length hSplit
      simp [hWorkLen] at this
      omega
    have hTapeSplit : encodeRegsTape work src =
        encodeRegsPrefix pref ++ .tag cur.1 :: cur.2.map SimSym.bit ++
          SimSym.sep :: (suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src) := by
      rw [hSplit]
      simp [encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hNotBitTail : ∀ x : Bool, SimSym.sep ≠ .bit x := fun _ h => by cases h
    have hBoundCopy : (encodeRegsPrefix pref).length + cur.2.length + 2 ≤ bound tRegs := by
      rw [hPrefPos, hCurLen]
      have hMul : pref.length * (W + 2) + (W + 2) ≤ r * (W + 2) := by
        rw [← Nat.add_one_mul]
        exact Nat.mul_le_mul_right _ hLt
      dsimp only [W] at hMul ⊢; omega
    have hT0Other : ∀ j, j ≠ tRegs → j ≠ tArgB → (t0 j).head < bound j := by
      intro j hjR hjB; simp [t0, hjR, hBounds0 j hjR]
    obtain ⟨ftB1, hCopyB, hFB1⟩ :=
      copyRegBitsTo_reachesExit tArgB (by decide) input bound (encodeRegsPrefix pref)
        (suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src) cur.1 cur.2
        .sep hNotBitTail t0 inHead hBoundCopy
        (by rw [hCurLen]; exact hBoundB) hT0Other
        (by simpa [t0, ← hTapeSplit] using hM0)
        (by simpa [t0, show tArgB ≠ tRegs by decide] using hMatchB)
    let t1 := fun j => if j = tRegs then t0 tRegs else if j = tArgB then ftB1 else t0 j
    have hT1OtherRegs : ∀ j, j ≠ tRegs → (t1 j).head < bound j := by
      intro j hjR
      by_cases hjB : j = tArgB
      · subst hjB; simp [t1, show tArgB ≠ tRegs by decide, hFB1.head_eq]
        exact Nat.lt_of_lt_of_le (by omega) hBoundB
      · simp [t1, hjR, hjB, hT0Other j hjR hjB]
    have hFullLen : (encodeRegsTape work src).length = 1 + r * (W + 2) + (W + 3) := by
      rw [encodeRegsTape_length W work src hWorkBits hSrcLen, hWorkLen]
    have hMulPos : pref.length * (W + 2) ≤ r * (W + 2) :=
      Nat.mul_le_mul_right _ hLt.le
    obtain ⟨t2, hRew, hFM2, hOthers2⟩ :=
      rewindTape_reachesExit tRegs input bound (encodeRegsTape work src)
        (by rw [hFullLen]; omega) (encodeRegsTape_head_leftMark work src)
        (encodeRegsTape_no_other_leftMark work src) (by rw [hFullLen]; exact hBoundRegs)
        t1 inHead hT1OtherRegs (encodeRegsPrefix pref).length
        (by rw [hPrefPos]; omega) (by rw [hPrefPos, hFullLen]; dsimp only [W] at hMulPos ⊢; omega)
        (by simpa [t1, t0] using hM0)
    have hT2R : TapeMatches (t2 tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
      rw [hOthers2 tRuler (by decide)]
      simpa [t1, t0, show tRuler ≠ tRegs by decide, show tRuler ≠ tArgB by decide] using hMatchR
    have hT2A : TapeMatches (t2 tArgA) [.leftMark] 1 := by
      rw [hOthers2 tArgA (by decide)]
      simpa [t1, t0, show tArgA ≠ tRegs by decide, show tArgA ≠ tArgB by decide] using hMatchA
    have hT2B : TapeMatches (t2 tArgB) (.leftMark :: cur.2.map SimSym.bit ++ [.endMark]) 1 := by
      rw [hOthers2 tArgB (by decide)]
      simpa [t1, show tArgB ≠ tRegs by decide] using hFB1
    have hT2S : TapeMatches (t2 tScratch) [.leftMark] 1 := by
      rw [hOthers2 tScratch (by decide)]
      simpa [t1, t0, show tScratch ≠ tRegs by decide, show tScratch ≠ tArgB by decide] using hMatchS
    let xJ : Fin ((2 ^ W - 1) + 1) := cfg.x ⟨pref.length, by omega⟩
    have hT2B' : TapeMatches (t2 tArgB)
        (.leftMark :: (natToBits W xJ.val).map SimSym.bit ++ [.endMark]) 1 := by
      simpa [xJ, hCurBits] using hT2B
    obtain ⟨reachOk, t3, in3, hReach, hReachIff, hR3, hRegs3, hA3, hB3, hS3⟩ :=
      checkReachableLoop_reachesExit M input bound S hS hInput r hr cfg hValid xJ
        hBoundR hBoundRegs hBoundA hBoundB hBoundS t2 inHead
        hT2R (by simpa [zdRegsContents] using hFM2) hT2A hT2B' hT2S
    have hT3OtherB : ∀ j, j ≠ tArgB → (t3 j).head < bound j := by
      intro j hjB
      match j with
      | ⟨0, _⟩ => change (t3 tRuler).head < bound tRuler; rw [hR3.head_eq]; omega
      | ⟨1, _⟩ => change (t3 tRegs).head < bound tRegs; rw [hRegs3.head_eq]; omega
      | ⟨2, _⟩ => change (t3 tArgA).head < bound tArgA; rw [hA3.head_eq]; omega
      | ⟨3, _⟩ => exact False.elim (hjB rfl)
      | ⟨4, _⟩ => change (t3 tScratch).head < bound tScratch; rw [hS3.head_eq]; omega
    cases hROk : reachOk
    · have hNotReach : ¬ ∃ i : Fin (r + 1), cfg.tag i = true ∧
          (cfg.x i = xJ ∨ (bitProblem M input S).step (cfg.x i) xJ) := by
        intro hEx; have := hReachIff.mpr hEx; rw [hROk] at this; cases this
      obtain ⟨ftB4, hClrB, hFB4⟩ :=
        clearTape_reachesExit tArgB input bound ((natToBits W xJ.val).map SimSym.bit)
          (by simp [natToBits_length]; exact hBoundB)
          (by intro s hs; rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
          t3 in3 hT3OtherB hB3
      let t4 := fun j => if j = tArgB then ftB4 else t3 j
      obtain ⟨res, finalTapes, hBT, hPostBT⟩ := hBacktrack t4 in3
        (by simpa [t4, show tRuler ≠ tArgB by decide] using hR3)
        (by simpa [t4, show tRegs ≠ tArgB by decide] using hRegs3)
        (by simpa [t4, show tArgA ≠ tArgB by decide] using hA3)
        (by simpa [t4] using hFB4)
        (by simpa [t4, show tScratch ≠ tArgB by decide] using hS3)
      have hBindClr := bindComponent_reachesExit (clearTape InputAlphabet tArgB)
        (fun _ => backtrackBranch) input bound hClrB hBT
      have hBranchReach := TMComponent.branch_reachesExit (checkReachableLoop M)
        reachTrueBranch reachFalseBranch
        input bound false (by rw [hROk] at hReach; exact hReach) hBindClr
      have hBindRew := bindComponent_reachesExit (rewindTape InputAlphabet tRegs)
        (fun _ => (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hRew hBranchReach
      have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgB)
        (fun _ => bindComponent (rewindTape InputAlphabet tRegs) fun _ =>
          (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hCopyB hBindRew
      refine ⟨res, finalTapes, in3,
        TMComponent.branch_reachesExit _ foundUntaggedBranch backtrackBranch input bound true hFindT hBindCopy, ?_⟩
      have hNotReach' : ¬ ∃ i, cfg.tag i = true ∧
          (cfg.x i = cfg.x (Fin.castSucc ⟨pref.length, hLt⟩) ∨
            (bitProblem M input S).step (cfg.x i) (cfg.x (Fin.castSucc ⟨pref.length, hLt⟩))) :=
        hNotReach
      simp only [zdAcceptingStep, hFUSome, hNotReach', ↓reduceDIte]
      cases hBTRes : zdBacktrack hN cfg <;> simp [hBTRes] at hPostBT ⊢ <;> exact hPostBT
    · have hExReach : ∃ i : Fin (r + 1), cfg.tag i = true ∧
          (cfg.x i = xJ ∨ (bitProblem M input S).step (cfg.x i) xJ) :=
        hReachIff.mp hROk
      obtain ⟨i, hiTag, hiRel⟩ := hExReach
      have hExReach' : ∃ i, cfg.tag i = true ∧
          (cfg.x i = cfg.x (Fin.castSucc ⟨pref.length, hLt⟩) ∨
            (bitProblem M input S).step (cfg.x i) (cfg.x (Fin.castSucc ⟨pref.length, hLt⟩))) :=
        ⟨i, hiTag, hiRel⟩
      obtain ⟨cI, hcI⟩ := hValid.2 i hiTag
      have hcJEx : ∃ cJ : TMConfig Q Γ k n S, xJ = (bitEncodeConfig Q Γ cJ).val := by
        rcases hiRel with hEq | hSt
        · exact ⟨cI, hEq.symm.trans hcI⟩
        · rcases hSt with ⟨b', a', _, ha', _⟩
          exact ⟨a', ha'.symm⟩
      obtain ⟨cJ, hcJ⟩ := hcJEx
      have hBsJCfg : natToBits W xJ.val = encodeConfigBits Q Γ cJ := by
        rw [hcJ, bitEncodeConfig_val_natToBits']
      have hBitAcc : bitIsAccepting M n S xJ = decide (M.accepting cJ.state) := by
        unfold bitIsAccepting
        simp only [decide_eq_decide]
        constructor
        · rintro ⟨c', hc', hAcc⟩
          have hEqC : c' = cJ :=
            bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext (hc'.trans hcJ))
          rwa [hEqC] at hAcc
        · intro hAcc
          exact ⟨cJ, hcJ.symm, hAcc⟩
      obtain ⟨ftB4, hAccRun, hFB4⟩ :=
        checkAccepting_reachesExit M input bound S cJ hBoundB
          t3 in3 hT3OtherB (by dsimp only [W] at hBsJCfg; simpa [hBsJCfg] using hB3)
      let t4 := fun j => if j = tArgB then ftB4 else t3 j
      have hT4Bounds : ∀ j, (t4 j).head < bound j := by
        intro j
        by_cases hj : j = tArgB
        · subst hj; simp [t4, hFB4.head_eq]; exact Nat.lt_of_lt_of_le (by omega) hBoundB
        · simp [t4, hj, hT3OtherB j hj]
      by_cases hAcc : M.accepting cJ.state
      · have hAccTrue : decide (M.accepting cJ.state) = true := decide_eq_true hAcc
        have hAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay)).ReachesExit
            input bound t4 in3 (.inr true) t4 in3 := by
          convert TMComponent.atom_reachesExit _ input bound t4 in3 hT4Bounds in3
            _ t4 _ hT4Bounds
          · simp [mkWorkAction]
          · simp [mkWorkAction, moveHead]
          · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (t4 j)
        have hBranchAcc := TMComponent.branch_reachesExit (checkAccepting M) accTrueBranch accFalseBranch
          input bound true (by rw [hAccTrue] at hAccRun; exact hAccRun) hAtom
        have hBranchReach := TMComponent.branch_reachesExit (checkReachableLoop M)
          reachTrueBranch reachFalseBranch
          input bound true (by rw [hROk] at hReach; exact hReach) hBranchAcc
        have hBindRew := bindComponent_reachesExit (rewindTape InputAlphabet tRegs)
          (fun _ => (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hRew hBranchReach
        have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgB)
          (fun _ => bindComponent (rewindTape InputAlphabet tRegs) fun _ =>
            (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hCopyB hBindRew
        refine ⟨.inr true, t4, in3,
          TMComponent.branch_reachesExit _ foundUntaggedBranch backtrackBranch input bound true hFindT hBindCopy, ?_⟩
        simp only [zdAcceptingStep, hFUSome, hExReach', ↓reduceDIte]
        rw [show bitIsAccepting M n S (cfg.x (Fin.castSucc ⟨pref.length, hLt⟩)) = true by
          simpa [xJ, hBitAcc] using hAccTrue]
        simp
      · have hAccFalse : decide (M.accepting cJ.state) = false := decide_eq_false hAcc
        have hT4OtherRegs : ∀ j, j ≠ tRegs → (t4 j).head < bound j := fun j _ => hT4Bounds j
        obtain ⟨ftB5, hClrB, hFB5⟩ :=
          clearTape_reachesExit tArgB input bound ((encodeConfigBits Q Γ cJ).map SimSym.bit)
            (by simp [encodeConfigBits_length]; exact hBoundB)
            (by intro s hs; rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
            t4 in3 (fun j hj => hT4Bounds j) hFB4
        let t5 := fun j => if j = tArgB then ftB5 else t4 j
        have hT5OtherRegs : ∀ j, j ≠ tRegs → (t5 j).head < bound j := by
          intro j hjR
          by_cases hjB : j = tArgB
          · subst hjB; simp [t5, hFB5.head_eq]; exact Nat.lt_of_lt_of_le (by omega) hBoundB
          · simp [t5, hjB, hT4Bounds j]
        have hT5Split : encodeRegsTape (pref ++ cur :: suf) src =
            encodeRegsTape work src := by rw [hSplit]
        obtain ⟨ftRegs, hTag, hFRegs⟩ :=
          findFirstUntaggedAndTag_reachesExit input bound W hW pref cur suf src
            hPrefBits hPrefT hCurLen hCurF hSufBits hSrcLen
            (by rw [hSplitLen]; exact hBoundRegs) t5 in3 hT5OtherRegs
            (by
              unfold zdRegsContents at hRegs3
              dsimp only [W, work, src] at hT5Split
              simpa [t5, t4, show tRegs ≠ tArgB by decide, ← hT5Split] using hRegs3)
        let t6 := fun j => if j = tRegs then ftRegs else t5 j
        have hBindTag := bindComponent_reachesExit (clearTape InputAlphabet tArgB)
          (fun _ => (findFirstUntaggedAndTag InputAlphabet).mapExit fun _ => (.inl () : Unit ⊕ Bool))
          input bound hClrB (TMComponent.mapExit_reachesExit _ _ input bound hTag)
        have hBranchAcc := TMComponent.branch_reachesExit (checkAccepting M) accTrueBranch accFalseBranch
          input bound false (by rw [hAccFalse] at hAccRun; exact hAccRun) hBindTag
        have hBranchReach := TMComponent.branch_reachesExit (checkReachableLoop M)
          reachTrueBranch reachFalseBranch
          input bound true (by rw [hROk] at hReach; exact hReach) hBranchAcc
        have hBindRew := bindComponent_reachesExit (rewindTape InputAlphabet tRegs)
          (fun _ => (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hRew hBranchReach
        have hBindCopy := bindComponent_reachesExit (copyRegBitsTo InputAlphabet tArgB)
          (fun _ => bindComponent (rewindTape InputAlphabet tRegs) fun _ =>
            (checkReachableLoop M).branch reachTrueBranch reachFalseBranch) input bound hCopyB hBindRew
        let next := updateAndReset hN cfg ⟨pref.length, hLt⟩ xJ true
        have hRegsNext : encodeZDRegs W next =
            pref.map (fun _ => (false, natToBits W 1)) ++ (true, cur.2) :: suf :=
          encodeZDRegs_updateAndReset hN cfg pref cur suf hSplit hLt true xJ (by simpa [xJ] using hCurBits.symm)
        have hSrcNext : encodeZDSrc W next = src := by
          simp only [src, encodeZDSrc]
          rw [(updateAndReset_preserves_source hN cfg _ _ _).1]
        have hValidNext : ValidZDTags Q Γ n S next := by
          refine ⟨?_, ?_⟩
          · rw [(updateAndReset_preserves_source hN cfg _ _ _).2]; exact hValid.1
          · intro i' hi'
            by_cases hEq : i'.val = pref.length
            · exact ⟨cJ, by simp [next, updateAndReset, hEq, hcJ]⟩
            · have hNotLt : ¬ i'.val < pref.length := by
                intro hLt'; simp [next, updateAndReset, hEq, hLt'] at hi'
              have hTagOld : cfg.tag i' = true := by simpa [next, updateAndReset, hEq, hNotLt] using hi'
              obtain ⟨c', hc'⟩ := hValid.2 i' hTagOld
              exact ⟨c', by simpa [next, updateAndReset, hEq, hNotLt] using hc'⟩
        refine ⟨.inl (), t6, in3,
          TMComponent.branch_reachesExit _ foundUntaggedBranch backtrackBranch input bound true hFindT hBindCopy, ?_⟩
        simp only [zdAcceptingStep, hFUSome, hExReach', ↓reduceDIte]
        rw [show bitIsAccepting M n S (cfg.x (Fin.castSucc ⟨pref.length, hLt⟩)) = false by
          simpa [xJ, hBitAcc] using hAccFalse]
        simp only [Bool.false_eq_true]
        dsimp only [W, next, xJ] at hRegsNext hSrcNext hValidNext
        refine ⟨trivial, hValidNext,
          by simpa [t6, t5, t4, show tRuler ≠ tRegs by decide, show tRuler ≠ tArgB by decide] using hR3,
          by simpa [t6, zdRegsContents, Fin.castSucc_mk, hRegsNext, hSrcNext] using hFRegs,
          by simpa [t6, t5, t4, show tArgA ≠ tRegs by decide, show tArgA ≠ tArgB by decide] using hA3,
          by simpa [t6, t5, show tArgB ≠ tRegs by decide] using hFB5,
          by simpa [t6, t5, t4, show tScratch ≠ tRegs by decide, show tScratch ≠ tArgB by decide] using hS3⟩

end SavitchLemma

module

public import SavitchLemma.Simulator.Step.StepScanner

@[expose] public section

/-!
# Acceptance and configuration-validity checkers on `tArgB`

Implements:
- `readFixedBits1`: single-tape fixed-width bit reader.
- `checkAccepting`: reads `qBits Q` from `tArgB`, rewinds `tArgB`, and tests
  `M.accepting`.
- `checkTailAndHeads`: verifies that `tArgB` has valid `< S` work-tape head
  fields and the `[true, false]` valid-ID suffix.
-/

namespace SavitchLemma

/-! ## 1. Single-tape fixed-width bit reader -/

/-- Read `m` bits from tape `t`, advancing `t` by `m` without modifying cells. -/
def readFixedBits1 (InputAlphabet : Type*) {k : ℕ} (m : ℕ) (t : Fin k) :
    TMComponent (Fin (m + 1) × (Fin m → Bool)) InputAlphabet SimSym k
      (Option (Fin m → Bool)) where
  start := (⟨0, Nat.zero_lt_succ m⟩, fun _ => false)
  step s _ scanned :=
    let idx := s.1
    let a := s.2
    if h : idx.val < m then
      match scanned t with
      | .bit b =>
        let a' : Fin m → Bool := fun j => if j.val = idx.val then b else a j
        if hNext : idx.val + 1 = m then
          singleTapeAction (.inr (some a')) t (.bit b) .right scanned
        else
          singleTapeAction (.inl (⟨idx.val + 1, by omega⟩, a')) t (.bit b) .right scanned
      | sym =>
        singleTapeAction (.inr none) t sym .stay scanned
    else
      singleTapeAction (.inr (some a)) t (scanned t) .stay scanned

theorem readFixedBits1_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (m : ℕ) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (pref suf : List SimSym) (slice : List Bool)
    (hLen : slice.length = m) (hBound : pref.length + m < bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) (pref ++ slice.map SimSym.bit ++ suf) pref.length) :
    ∃ ft,
      (readFixedBits1 InputAlphabet m t).ReachesExit input bound initTapes inHead
        (some (fun i : Fin m => slice[i.val]'(by omega)))
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ slice.map SimSym.bit ++ suf) (pref.length + m) := by
  have hStep : ∀ (idx : ℕ) (hIdx : idx ≤ m) (acc : Fin m → Bool),
      (∀ (j : Fin m), j.val < idx → acc j = slice[j.val]'(by omega)) →
      ∀ tape, TapeMatches tape (pref ++ slice.map SimSym.bit ++ suf) (pref.length + idx) →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (readFixedBits1 InputAlphabet m t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl (⟨idx, by omega⟩, acc), inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr (some (fun i : Fin m => slice[i.val]'(by omega))), inHead,
            fun j => if j = t then ft else initTapes j⟩ ∧
        TapeMatches ft (pref ++ slice.map SimSym.bit ++ suf) (pref.length + m) := by
    have hRem : ∀ rem idx (hSum : idx + rem = m) (acc : Fin m → Bool),
        (∀ (j : Fin m), j.val < idx → acc j = slice[j.val]'(by omega)) →
        ∀ tape, TapeMatches tape (pref ++ slice.map SimSym.bit ++ suf) (pref.length + idx) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (readFixedBits1 InputAlphabet m t).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl (⟨idx, by omega⟩, acc), inHead, fun j => if j = t then tape else initTapes j⟩
            ⟨.inr (some (fun i : Fin m => slice[i.val]'(by omega))), inHead,
              fun j => if j = t then ft else initTapes j⟩ ∧
          TapeMatches ft (pref ++ slice.map SimSym.bit ++ suf) (pref.length + m) := by
      intro rem
      induction rem with
      | zero =>
        intro idx hSum acc hAcc tape hMT
        have hIdxEq : idx = m := by omega
        have hFun : acc = fun i : Fin m => slice[i.val]'(by omega) :=
          funext fun j => hAcc j (by omega)
        have hMT' : TapeMatches tape (pref ++ slice.map SimSym.bit ++ suf) (pref.length + m) := by
          simpa [hIdxEq] using hMT
        have hMove : moveOneSidedHead (pref.length + m) .stay = some (pref.length + m) := rfl
        obtain ⟨ft, hUpd, hFM⟩ := hMT'.update_keep .stay hMove
        refine ⟨ft, ?_, hFM⟩
        have hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j := by
          intro j; by_cases hj : j = t
          · simp only [hj, ↓reduceIte]; rw [hMT'.head_eq]; exact hBound
          · simp [hj, hOtherBounds j hj]
        exact singleTape_compStep_exit_override (readFixedBits1 InputAlphabet m t) t input bound
          initTapes tape ft (⟨idx, by omega⟩, acc) hHeads (by rw [hFM.head_eq]; exact hBound) hUpd
          (by simp [readFixedBits1, hIdxEq, hFun])
      | succ rem' ih =>
        intro idx hSum acc hAcc tape hMT
        have hIdxLt : idx < m := by omega
        have hFullLen : pref.length + idx < (pref ++ slice.map SimSym.bit ++ suf).length := by
          simp [hLen]; omega
        let b := slice[idx]'(by omega)
        have hRead : tape.cells tape.head = .bit b := by
          rw [hMT.read_lt hFullLen]
          rw [List.getElem_append_left (by simp [hLen]; omega),
            List.getElem_append_right (by simp)]
          simp only [Nat.add_sub_cancel_left, List.getElem_map]
          rfl
        have hMove : moveOneSidedHead (pref.length + idx) .right = some (pref.length + idx + 1) := by
          simp [moveOneSidedHead]
        obtain ⟨nt, hUpd, hNM⟩ := hMT.update_keep .right hMove
        have hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j := by
          intro j; by_cases hj : j = t
          · simp only [hj, ↓reduceIte]; rw [hMT.head_eq]; omega
          · simp [hj, hOtherBounds j hj]
        let acc' : Fin m → Bool := fun j => if j.val = idx then b else acc j
        have hAcc' : ∀ (j : Fin m), j.val < idx + 1 → acc' j = slice[j.val]'(by omega) := by
          intro j hj
          dsimp only [acc']
          by_cases hjEq : j.val = idx
          · simp [hjEq, b]
          · simp [hjEq, hAcc j (by omega)]
        by_cases hNext : idx + 1 = m
        · have hFun : acc' = fun i : Fin m => slice[i.val]'(by omega) :=
            funext fun j => hAcc' j (by omega)
          refine ⟨nt, ?_, by simpa [hNext, Nat.add_assoc] using hNM⟩
          exact singleTape_compStep_exit_override (readFixedBits1 InputAlphabet m t) t input bound
            initTapes tape nt (⟨idx, by omega⟩, acc) hHeads (by rw [hNM.head_eq]; omega)
            (by simpa [hRead] using hUpd)
            (by simp [readFixedBits1, hIdxLt, hRead, hNext, acc', hFun])
        · obtain ⟨ft, hRest, hFM⟩ := ih (idx + 1) (by omega) acc' hAcc' nt
            (by simpa [Nat.add_assoc] using hNM)
          refine ⟨ft, ?_, hFM⟩
          exact singleTape_compStep_head_override (readFixedBits1 InputAlphabet m t) t input bound
            initTapes tape nt ft (⟨idx, by omega⟩, acc) (⟨idx + 1, by omega⟩, acc')
            hHeads (by rw [hNM.head_eq]; omega) (by simpa [hRead] using hUpd) hRest
            (by simp [readFixedBits1, hIdxLt, hRead, hNext, acc'])
    exact fun idx hIdx acc hAcc tape hMT => hRem (m - idx) idx (by omega) acc hAcc tape hMT
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j; by_cases hj : j = t <;> simp [hj]
  obtain ⟨ft, hRun, hFM⟩ := hStep 0 (Nat.zero_le m) (fun _ => false)
    (fun j hj => by omega) (initTapes t) (by simpa using hMatch)
  rw [hTapesSelf] at hRun
  exact ⟨ft, hRun, hFM⟩

/-! ## 2. Acceptance checker on `tArgB` -/

/-- Check whether the configuration serialized on `tArgB` has an accepting
control state in `M`, rewinding `tArgB` back to cell `1`. -/
noncomputable def checkAccepting {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  letI := Classical.propDecidable
  bindComponent (readFixedBits1 InputAlphabet (qBits Q) tArgB) fun fOpt =>
    (rewindTape InputAlphabet tArgB).mapExit fun _ =>
      match fOpt with
      | none => false
      | some f =>
        match decodeBitsOpt (qBits Q) Q f with
        | none => false
        | some q => decide (M.accepting q)

theorem checkAccepting_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (cfg : TMConfig Q Γ k n S)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchB : TapeMatches (initTapes tArgB)
      (.leftMark :: (encodeConfigBits Q Γ cfg).map SimSym.bit ++ [.endMark]) 1) :
    ∃ ftB,
      (checkAccepting M).ReachesExit input bound initTapes inHead
        (letI := Classical.propDecidable; decide (M.accepting cfg.state))
        (fun j => if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftB
        (.leftMark :: (encodeConfigBits Q Γ cfg).map SimSym.bit ++ [.endMark]) 1 := by
  classical
  let qSlice := natToBits (qBits Q) (Fintype.equivFin Q cfg.state).val
  let tailBits := natToBits (S + 2) cfg.inputHead.val ++
    (List.finRange k).flatMap (fun t => encodeTapeBits Γ (cfg.workTapes t)) ++ [true, false]
  let fullB := SimSym.leftMark :: (encodeConfigBits Q Γ cfg).map SimSym.bit ++ [SimSym.endMark]
  have hFullLen : fullB.length = configBitWidth Q Γ k S + 2 := by
    simp [fullB, encodeConfigBits_length]
  have hFullEq : fullB = [SimSym.leftMark] ++ qSlice.map SimSym.bit ++
      (tailBits.map SimSym.bit ++ [SimSym.endMark]) := by
    simp [fullB, encodeConfigBits, qSlice, tailBits, List.append_assoc]
  have hBoundQ : ([SimSym.leftMark] : List SimSym).length + qBits Q < bound tArgB := by
    simp only [List.length_singleton, configBitWidth] at *
    omega
  obtain ⟨ftB1, hRead, hFM1⟩ := readFixedBits1_reachesExit (qBits Q) tArgB input bound
    [SimSym.leftMark] (tailBits.map SimSym.bit ++ [SimSym.endMark]) qSlice
    (natToBits_length _ _) hBoundQ initTapes inHead hOtherBounds
    (by
      have hM := hMatchB
      change TapeMatches (initTapes tArgB) fullB 1 at hM
      rw [hFullEq] at hM
      simpa [List.append_assoc] using hM)
  let t1 := fun j => if j = tArgB then ftB1 else initTapes j
  have hNoLeft : ∀ i, 1 ≤ i → i < fullB.length → fullB[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i =>
      simp only [fullB, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at hiLt
      by_cases hiB : i < (encodeConfigBits Q Γ cfg).length
      · simp only [fullB]
        rw [List.getElem?_append_left (by simp [hiB]), List.getElem?_eq_getElem (by simp [hiB])]
        simp
      · have hiEq : i = (encodeConfigBits Q Γ cfg).length := by omega
        subst hiEq
        simp only [fullB]
        rw [List.getElem?_append_right (by simp)]
        simp
  have hT1Other : ∀ j, j ≠ tArgB → (t1 j).head < bound j := by
    intro j hj; simp [t1, hj, hOtherBounds j hj]
  obtain ⟨t2, hRew, hFM2, hOthers2⟩ := rewindTape_reachesExit (InputAlphabet := InputAlphabet)
    tArgB input bound fullB (by simp [fullB]) (by simp [fullB]) hNoLeft
    (by rw [hFullLen]; exact hBoundB) t1 inHead hT1Other (1 + qBits Q) (by omega)
    (by rw [hFullLen]; simp [configBitWidth]; omega)
    (by change TapeMatches ftB1 _ _; rw [hFullEq]; simpa [List.append_assoc] using hFM1)
  let f : Fin (qBits Q) → Bool := fun i => qSlice[i.val]'(by rw [natToBits_length]; exact i.isLt)
  have hPow : Fintype.card Q + 1 ≤ 2 ^ qBits Q :=
    Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card Q + 1)
  have hDec : decodeBitsOpt (qBits Q) Q f = some cfg.state := by
    apply (decodeBitsOpt_eq_some_iff hPow f cfg.state).mpr
    exact (List.ext_getElem (by simp [natToBits_length]) (fun i h1 _ => by simp [f, qSlice])).symm
  have hMap := TMComponent.mapExit_reachesExit (rewindTape InputAlphabet tArgB)
    (fun _ => decide (M.accepting cfg.state)) input bound hRew
  have hBind := bindComponent_reachesExit (readFixedBits1 InputAlphabet (qBits Q) tArgB)
    (fun fOpt => (rewindTape InputAlphabet tArgB).mapExit fun _ =>
      match fOpt with
      | none => false
      | some f =>
        match decodeBitsOpt (qBits Q) Q f with
        | none => false
        | some q => decide (M.accepting q))
    input bound hRead (by simpa [f, hDec] using hMap)
  have hT2Eq : t2 = fun j => if j = tArgB then t2 tArgB else initTapes j := by
    funext j
    by_cases hj : j = tArgB
    · subst hj; rfl
    · rw [hOthers2 j hj]; simp [t1, hj]
  rw [hT2Eq] at hBind
  exact ⟨t2 tArgB, hBind, hFM2⟩

end SavitchLemma

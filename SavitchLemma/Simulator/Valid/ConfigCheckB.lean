module

public import SavitchLemma.Simulator.Valid.ValidConfigB

@[expose] public section

/-!
# Full `checkValidB` configuration-validity checker on `tArgB`

1. `checkCellsDecode`: scans `S` cells of `gammaBits Γ` bits on `tArgB`
   using `tRuler`, checking each decodes via `decodeBitsOpt (gammaBits Γ) Γ`.
2. `checkValidB`: checks that a `configBitWidth Q Γ k S`-bit list on `tArgB`
   has a valid `Q` state, `k` valid work-tape heads (`< S`) and cell symbols,
   and the `[true, false]` valid-ID suffix, rewinding `tArgB` afterward.
-/

namespace SavitchLemma

/-! ## 1. Checking `S` cell blocks of `gammaBits Γ` bits on `tArgB` -/

/-- Scan `S` cell blocks of `gammaBits Γ` bits on `tArgB` guided by `tRuler`,
returning `true` iff every cell block decodes in `Γ`. Rewinds `tRuler` to `1`. -/
noncomputable def checkCellsDecode (InputAlphabet Γ : Type*) [Fintype Γ] :=
  bindComponent
    (loopWithState true fun (ok : Bool) =>
      TMComponent.branch
        (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay))
        (bindComponent (readFixedBits1 InputAlphabet (gammaBits Γ) tArgB) fun fOpt =>
          TMComponent.atom fun _ scanned =>
            let cellOk := match fOpt with
              | some f => (decodeBitsOpt (gammaBits Γ) Γ f).isSome
              | none => false
            mkWorkAction (.inl (ok && cellOk) : Bool ⊕ Bool) scanned
              (fun j => if j = tRuler then .right else .stay))
        (TMComponent.atom fun _ scanned =>
          mkWorkAction (.inr ok : Bool ⊕ Bool) scanned (fun _ => .stay)))
    fun res =>
      (rewindTape InputAlphabet tRuler).mapExit (fun _ => res)

theorem checkCellsDecode_reachesExit {InputAlphabet Γ : Type*} {n : ℕ} [Fintype Γ]
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pB sB : List SimSym) (slice : List Bool)
    (hLen : slice.length = S * gammaBits Γ)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundB : pB.length + S * gammaBits Γ < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchB : TapeMatches (initTapes tArgB)
      (pB ++ slice.map SimSym.bit ++ sB) pB.length) :
    ∃ (res : Bool) (ftR ftB : OneSidedTape SimSym),
      (checkCellsDecode InputAlphabet Γ).ReachesExit input bound initTapes inHead res
        (fun j => if j = tRuler then ftR else if j = tArgB then ftB else initTapes j)
        inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB (pB ++ slice.map SimSym.bit ++ sB) (pB.length + S * gammaBits Γ) ∧
      (res = true ↔ ∃ cells : Fin S → Γ,
        slice = (List.finRange S).flatMap (fun c =>
          natToBits (gammaBits Γ) (Fintype.equivFin Γ (cells c)).val)) := by
  classical
  let rulerList := SimSym.leftMark :: List.replicate S (SimSym.bit true) ++ [SimSym.endMark]
  let fullB := pB ++ slice.map SimSym.bit ++ sB
  have hRLen : rulerList.length = S + 2 := by simp [rulerList]
  let g := gammaBits Γ
  let cellAt : ℕ → List Bool := fun j => (slice.drop (j * g)).take g
  let peekAtom : TMComponent Unit InputAlphabet SimSym 5 Bool :=
    TMComponent.atom fun _ scanned =>
      mkWorkAction (decide (scanned tRuler = .bit true)) scanned (fun _ => .stay)
  let trueBranch : Bool → _ := fun ok =>
    bindComponent (readFixedBits1 InputAlphabet g tArgB) fun fOpt =>
      TMComponent.atom fun _ scanned =>
        let cellOk := match fOpt with
          | some f => (decodeBitsOpt g Γ f).isSome
          | none => false
        mkWorkAction (.inl (ok && cellOk) : Bool ⊕ Bool) scanned
          (fun j => if j = tRuler then .right else .stay)
  let falseBranch : Bool → TMComponent Unit InputAlphabet SimSym 5 (Bool ⊕ Bool) := fun ok =>
    TMComponent.atom fun _ scanned =>
      mkWorkAction (.inr ok : Bool ⊕ Bool) scanned (fun _ => .stay)
  let body : Bool → _ := fun ok =>
    TMComponent.branch peekAtom (trueBranch ok) (falseBranch ok)
  let cellValid : ℕ → Prop := fun j =>
    ∃ c : Γ, cellAt j = natToBits g (Fintype.equivFin Γ c).val
  let Inv : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun ok tapes curInHead =>
      ∃ i : ℕ, i ≤ S ∧ curInHead = inHead ∧
        (ok = true ↔ ∀ j, j < i → cellValid j) ∧
        TapeMatches (tapes tRuler) rulerList (1 + i) ∧
        TapeMatches (tapes tArgB) fullB (pB.length + i * g) ∧
        (∀ j, j ≠ tRuler → j ≠ tArgB → tapes j = initTapes j)
  let measure : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ :=
    fun _ tapes _ => (1 + S) - (tapes tRuler).head
  let Post : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop :=
    fun res tapes curInHead =>
      curInHead = inHead ∧
      (res = true ↔ ∀ j, j < S → cellValid j) ∧
      TapeMatches (tapes tRuler) rulerList (1 + S) ∧
      TapeMatches (tapes tArgB) fullB (pB.length + S * g) ∧
      (∀ j, j ≠ tRuler → j ≠ tArgB → tapes j = initTapes j)
  have hStep : ∀ st tapes curInHead, Inv st tapes curInHead →
      (∃ st' tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inl st') tapes' curInHead' ∧
        Inv st' tapes' curInHead' ∧
        measure st' tapes' curInHead' < measure st tapes curInHead) ∨
      (∃ e tapes' curInHead',
        (body st).ReachesExit input bound tapes curInHead (.inr e) tapes' curInHead' ∧
        Post e tapes' curInHead') := by
    intro ok tapes curInHead ⟨i, hiLe, hCurIn, hOkIff, hMR, hMB, hOthers⟩
    cases hCurIn
    have hBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hMR.head_eq]; omega
      · by_cases hjB : j = tArgB
        · subst hjB; rw [hMB.head_eq]
          have hLe : i * g ≤ S * g := Nat.mul_le_mul_right _ hiLe
          dsimp only [g] at hLe ⊢
          omega
        · rw [hOthers j hjR hjB]; exact hOtherBounds j hjR hjB
    by_cases hiLt : i < S
    · left
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ]
        simp
      have hPeek : peekAtom.ReachesExit input bound tapes inHead true tapes inHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hCellLen : (cellAt i).length = g := by
        simp only [cellAt, List.length_take, List.length_drop, hLen]
        have hLe : (i + 1) * g ≤ S * g := Nat.mul_le_mul_right g hiLt
        rw [Nat.add_mul, Nat.one_mul] at hLe
        dsimp only [g] at hLe ⊢
        omega
      let pCur := pB ++ (slice.take (i * g)).map SimSym.bit
      let sCur := (slice.drop ((i + 1) * g)).map SimSym.bit ++ sB
      have hSliceSplit : slice = slice.take (i * g) ++ cellAt i ++ slice.drop ((i + 1) * g) := by
        have h1 : i * g + g = (i + 1) * g := (Nat.succ_mul i g).symm
        conv_lhs =>
          rw [← List.take_append_drop (i * g) slice,
            ← List.take_append_drop g (slice.drop (i * g)), List.drop_drop, h1]
        simp only [cellAt, List.append_assoc]
      have hPCurLen : pCur.length = pB.length + i * g := by
        simp only [pCur, List.length_append, List.length_map, List.length_take, hLen]
        have hLe : i * g ≤ S * g := Nat.mul_le_mul_right g hiLe
        dsimp only [g] at hLe ⊢
        omega
      have hFullBEq : fullB = pCur ++ (cellAt i).map SimSym.bit ++ sCur := by
        simp only [fullB, pCur, sCur]
        conv_lhs => rw [hSliceSplit]
        simp [List.map_append, List.append_assoc]
      have hMB' : TapeMatches (tapes tArgB) (pCur ++ (cellAt i).map SimSym.bit ++ sCur) pCur.length := by
        rw [← hFullBEq, hPCurLen]; exact hMB
      have hOtherB : ∀ j, j ≠ tArgB → (tapes j).head < bound j := fun j _ => hBounds j
      have hBoundCur : pCur.length + g < bound tArgB := by
        rw [hPCurLen]
        have hLe : (i + 1) * g ≤ S * g := Nat.mul_le_mul_right g hiLt
        rw [Nat.add_mul, Nat.one_mul] at hLe
        dsimp only [g] at hLe ⊢
        omega
      obtain ⟨ftB, hReadB, hFB⟩ :=
        readFixedBits1_reachesExit g tArgB input bound pCur sCur (cellAt i) hCellLen hBoundCur
          tapes inHead hOtherB hMB'
      let t1 := fun j => if j = tArgB then ftB else tapes j
      have hT1Bounds : ∀ j, (t1 j).head < bound j := by
        intro j
        by_cases hjB : j = tArgB
        · subst hjB; simpa [t1, hFB.head_eq, hPCurLen] using hBoundCur
        · simp [t1, hjB, hBounds j]
      have hT1MR : TapeMatches (t1 tRuler) rulerList (1 + i) := by
        have hNe : tRuler ≠ tArgB := by decide
        simpa [t1, hNe] using hMR
      obtain ⟨ntR, hUpdR, hFR⟩ := hT1MR.update_keep .right rfl
      let t2 := fun j => if j = tRuler then ntR else t1 j
      have hT2Bounds : ∀ j, (t2 j).head < bound j := by
        intro j
        by_cases hjR : j = tRuler
        · subst hjR; simpa [t2, hFR.head_eq] using (by omega : 1 + i + 1 < bound tRuler)
        · simp [t2, hjR, hT1Bounds j]
      let fCell : Fin g → Bool := fun idx => (cellAt i)[idx.val]'(by rw [hCellLen]; exact idx.isLt)
      let cellOk := (decodeBitsOpt g Γ fCell).isSome
      have hAtom : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (.inl (ok && cellOk) : Bool ⊕ Bool) scanned
            (fun j => if j = tRuler then .right else .stay)).ReachesExit
          input bound t1 inHead (.inl (ok && cellOk)) t2 inHead := by
        convert TMComponent.atom_reachesExit _ input bound t1 inHead hT1Bounds inHead _ t2 _ hT2Bounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j
          simp only [mkWorkAction]
          by_cases hjR : j = tRuler
          · subst hjR; simpa [t2] using hUpdR
          · simp [t2, hjR, OneSidedTape.updateAndMove_stay_self]
      have hInner := bindComponent_reachesExit (readFixedBits1 InputAlphabet g tArgB)
        (fun fOpt => TMComponent.atom fun _ scanned =>
          let cellOk' := match fOpt with
            | some f => (decodeBitsOpt g Γ f).isSome
            | none => false
          mkWorkAction (.inl (ok && cellOk') : Bool ⊕ Bool) scanned
            (fun j => if j = tRuler then .right else .stay))
        input bound hReadB (by simpa [cellOk] using hAtom)
      have hOuter := TMComponent.branch_reachesExit peekAtom (trueBranch ok) (falseBranch ok)
        input bound true hPeek hInner
      have hCellValidIff : cellOk = true ↔ cellValid i := by
        have hPow : Fintype.card Γ + 1 ≤ 2 ^ g := Nat.le_pow_clog (by decide) _
        have hOfFn : List.ofFn fCell = cellAt i := by
          apply List.ext_getElem
          · simp [hCellLen]
          · intro idx h1 h2; simp [fCell]
        simp only [cellOk, Option.isSome_iff_exists, decodeBitsOpt_eq_some_iff hPow, hOfFn, cellValid]
        constructor
        · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
        · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
      have hOkIff' : (ok && cellOk) = true ↔ ∀ j, j < i + 1 → cellValid j := by
        simp only [Bool.and_eq_true, hOkIff, hCellValidIff]
        constructor
        · rintro ⟨hPrev, hCur⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjLt | rfl
          · exact hPrev j hjLt
          · exact hCur
        · intro hAll
          exact ⟨fun j hj => hAll j (Nat.lt_succ_of_lt hj), hAll i (Nat.lt_succ_self i)⟩
      have hT2FB : TapeMatches (t2 tArgB) fullB (pB.length + (i + 1) * g) := by
        have hNe : tArgB ≠ tRuler := by decide
        have hEqPos : pCur.length + g = pB.length + (i + 1) * g := by
          rw [hPCurLen, Nat.succ_mul, Nat.add_assoc]
        simpa [t2, t1, hNe, ← hFullBEq, hEqPos] using hFB
      refine ⟨ok && cellOk, t2, inHead, hOuter,
        ⟨i + 1, by omega, rfl, hOkIff', by simpa [t2, Nat.add_assoc] using hFR, hT2FB,
          fun j hjR hjB => by simp [t2, t1, hjR, hjB, hOthers j hjR hjB]⟩, ?_⟩
      change 1 + S - (t2 tRuler).head < 1 + S - (tapes tRuler).head
      have hHead2 : (t2 tRuler).head = 1 + i + 1 := by simp [t2, hFR.head_eq]
      rw [hHead2, hMR.head_eq]
      omega
    · right
      have hiS : i = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [hMR.read_lt (by rw [hRLen]; omega)]
        simp only [rulerList, Nat.add_comm 1 i]
        rw [List.getElem_append_right (by simp [hiS])]
        simp [hiS]
      have hPeek : peekAtom.ReachesExit input bound tapes inHead false tapes inHead := by
        dsimp only [peekAtom]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction, hReadR]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hFalse : (falseBranch ok).ReachesExit input bound tapes inHead (.inr ok) tapes inHead := by
        dsimp only [falseBranch]
        convert TMComponent.atom_reachesExit _ input bound tapes inHead hBounds inHead _ tapes _ hBounds
        · simp [mkWorkAction]
        · simp [mkWorkAction, moveHead]
        · intro j; simpa [mkWorkAction] using OneSidedTape.updateAndMove_stay_self (tapes j)
      have hOuter := TMComponent.branch_reachesExit peekAtom (trueBranch ok) (falseBranch ok)
        input bound false hPeek hFalse
      refine ⟨ok, tapes, inHead, hOuter, rfl, by simpa [hiS] using hOkIff,
        by simpa [hiS] using hMR, by simpa [hiS] using hMB, hOthers⟩
  obtain ⟨res, tLoop, finalInHead, hLoop, hHead, hResIff, hRL, hBL, hOthersL⟩ :=
    loopWithState_reachesExit true body input bound Inv measure Post hStep initTapes inHead
      ⟨0, Nat.zero_le S, rfl, by simp, hMatchR, by simpa [fullB] using hMatchB, fun _ _ _ => rfl⟩
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
  obtain ⟨tRewR, hRewR, hRFin, hOthersR⟩ :=
    rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
      rulerList (by simp [rulerList]) (by simp [rulerList]) hRulerNoLeft
      (by rw [hRLen]; exact hBoundR) tLoop inHead hTLoopOtherR (1 + S) (by omega)
      (by rw [hRLen]; omega) hRL
  have hMap := TMComponent.mapExit_reachesExit (rewindTape InputAlphabet tRuler)
    (fun _ => res) input bound hRewR
  dsimp only [body, peekAtom, trueBranch, falseBranch, g] at hLoop
  have hFull : (checkCellsDecode InputAlphabet Γ).ReachesExit input bound initTapes inHead res
      (fun j => if j = tRuler then tRewR tRuler else if j = tArgB then tLoop tArgB else initTapes j)
      inHead := by
    dsimp only [checkCellsDecode]
    have hEndEq : tRewR = fun j => if j = tRuler then tRewR tRuler
        else if j = tArgB then tLoop tArgB else initTapes j := by
      funext j
      by_cases hjR : j = tRuler
      · subst hjR; simp
      · rw [hOthersR j hjR]
        by_cases hjB : j = tArgB
        · subst hjB; simp [hjR]
        · simp [hjR, hjB, hOthersL j hjR hjB]
    rw [← hEndEq]
    convert bindComponent_reachesExit _ (fun r => (rewindTape InputAlphabet tRuler).mapExit (fun _ => r))
      input bound hLoop hMap
    cases ‹Option (Fin (gammaBits Γ) → Bool)› <;> rfl
  have hBL' : TapeMatches (tLoop tArgB) (pB ++ slice.map SimSym.bit ++ sB)
      (pB.length + S * g) := hBL
  refine ⟨res, tRewR tRuler, tLoop tArgB, hFull, hRFin, hBL', ?_⟩
  rw [hResIff]
  constructor
  · intro hAll
    choose cells hCells using fun c : Fin S => hAll c.val c.isLt
    refine ⟨cells, ?_⟩
    have hFinRangeSucc : ∀ m, List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
      intro m; apply List.ext_getElem
      · simp
      · intro idx hi1 hi2
        by_cases hIdx : idx < m
        · simp [List.getElem_append_left, hIdx]
        · have hEq : idx = m := by simp at hi1; omega
          subst hEq
          rw [List.getElem_append_right (by simp)]
          simp [Fin.ext_iff]
    have hTakeEq : ∀ (m : ℕ) (hm : m ≤ S),
        slice.take (m * g) = (List.finRange m).flatMap (fun c =>
          natToBits g (Fintype.equivFin Γ (cells ⟨c.val, by have := c.isLt; omega⟩)).val) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        rw [hFinRangeSucc, List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
        have hEqTake : slice.take ((m + 1) * g) = slice.take (m * g) ++ cellAt m := by
          rw [show (m + 1) * g = m * g + g from Nat.succ_mul m g]
          rw [← List.take_append_drop (m * g) (slice.take (m * g + g))]
          congr 1
          · rw [List.take_take, Nat.min_eq_left (by omega)]
          · rw [List.drop_take, show m * g + g - m * g = g by omega]
        rw [hEqTake, ih (by omega), hCells ⟨m, by omega⟩]
        rfl
    have hTakeAll : slice.take (S * g) = slice := List.take_of_length_le (by rw [hLen])
    have hResEq := hTakeEq S (le_refl S)
    rw [hTakeAll] at hResEq
    exact hResEq
  · rintro ⟨cells, rfl⟩ j hj
    dsimp only [cellValid, cellAt]
    have hFlatTake : ∀ m, m ≤ S →
        ((List.finRange S).flatMap (fun c =>
          natToBits g (Fintype.equivFin Γ (cells c)).val)).drop (m * g) =
        ((List.finRange S).drop m).flatMap (fun c =>
          natToBits g (Fintype.equivFin Γ (cells c)).val) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show (m + 1) * g = m * g + g from Nat.succ_mul m g, ← List.drop_drop, ih (by omega)]
        have hDropCons : (List.finRange S).drop m = ⟨m, by omega⟩ :: (List.finRange S).drop (m + 1) := by
          rw [← List.getElem_cons_drop (by simp; omega)]
          simp
        rw [hDropCons, List.flatMap_cons, List.drop_append_of_le_length (by simp [natToBits_length])]
        simp [natToBits_length]
    rw [hFlatTake j hj.le]
    have hDropCons : (List.finRange S).drop j = ⟨j, hj⟩ :: (List.finRange S).drop (j + 1) := by
      rw [← List.getElem_cons_drop (by simp; omega)]
      simp
    rw [hDropCons, List.flatMap_cons, List.take_left' (natToBits_length _ _)]
    exact ⟨cells ⟨j, hj⟩, rfl⟩

end SavitchLemma

module

public import SavitchLemma.RegisterTape.Advance

@[expose] public section

/-!
# Register tagging

Tags the first untagged register and resets the prefix to its left.
-/

namespace SavitchLemma

/-- Find the first untagged register on Tape 1 (from cell `1`), set its tag to `true`,
and reset all working registers to its left to untagged `firstCode = 1`.
Returns `true` if an untagged register existed (leaving Tape 1 at cell `1`), or `false`
if all working registers were already tagged. -/
def findFirstUntaggedAndTag (InputAlphabet : Type*) :=
  (findFirstUntagged InputAlphabet).branch
    (((TMComponent.atom fun _ scanned =>
        singleTapeAction () tRegs (.tag true) .stay scanned).seq
      (resetLeftRegs InputAlphabet)).mapExit fun _ => true)
    (TMComponent.atom fun _ scanned => singleTapeAction false tRegs (scanned tRegs) .stay scanned)

theorem findFirstUntaggedAndTag_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hPrefT : ∀ r ∈ pref, r.1 = true)
    (hCurLen : cur.2.length = W) (hCurF : cur.1 = false)
    (hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src) 1) :
    ∃ ft,
      (findFirstUntaggedAndTag InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft (encodeRegsTape
        (pref.map (fun _ => (false, natToBits W 1)) ++ (true, cur.2) :: suf) src) 1 := by
  have hAllWorkLen : ∀ r ∈ pref ++ cur :: suf, r.2.length = W := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact hPrefLen r h1
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hCurLen
      · exact hSufLen r h3
  have hBoundWork : 1 + (pref ++ cur :: suf).length * (W + 2) + (W + 3) ≤ bound tRegs := by
    simp only [List.length_append, List.length_cons]
    have : pref.length + (suf.length + 1) = pref.length + 1 + suf.length := by omega
    rw [this]; exact hBound
  have hFind := findFirstUntagged_reachesExit input bound W (pref ++ cur :: suf) src
    hAllWorkLen hSrcLen hBoundWork initTapes inHead hOtherBounds hMatch
  rcases hFind with ⟨hAllT, _⟩ | ⟨p₁, cur₁, p₂, hEq, hCur1F, hP1T, mt, hFindRun, hMT⟩
  · have hF := hAllT cur (by simp)
    rw [hCurF] at hF
    cases hF
  · have hP1LenEq : p₁.length = pref.length := by
      by_contra hNe
      rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
      · have hMem : (pref ++ cur :: suf)[p₁.length]'(by simp; omega) = cur₁ := by
          simp only [hEq, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        rw [List.getElem_append_left hLt] at hMem
        have hT : cur₁.1 = true := by rw [← hMem]; exact hPrefT _ (List.getElem_mem _)
        rw [hCur1F] at hT; cases hT
      · have hMem : (p₁ ++ cur₁ :: p₂)[pref.length]'(by rw [← hEq]; simp) = cur := by
          simp only [← hEq, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        rw [List.getElem_append_left hGt] at hMem
        have hT : cur.1 = true := by rw [← hMem]; exact hP1T _ (List.getElem_mem _)
        rw [hCurF] at hT; cases hT
    have hP1Eq : p₁ = pref := by
      have := congrArg (List.take pref.length) hEq
      symm
      simpa [List.take_left', hP1LenEq] using this
    subst p₁
    have hPL := encodeRegsPrefix_length W pref hPrefLen
    have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
    have hHeadsMT : ∀ j, (if j = tRegs then mt else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hMT.head_eq, hPL] using by omega
      · simpa [hj] using hOtherBounds j hj
    let tailSyms : List SimSym :=
      suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hSplit : encodeRegsTape (pref ++ cur :: suf) src =
        encodeRegsPrefix pref ++ SimSym.tag cur.1 :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms) := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    have hMT' : TapeMatches mt
        (encodeRegsPrefix pref ++ SimSym.tag cur.1 :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms))
        (encodeRegsPrefix pref).length := by
      rw [← hSplit]; exact hMT
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .stay =
        some (encodeRegsPrefix pref).length := rfl
    obtain ⟨nt, hUpd, hNM⟩ := hMT'.update_set (.tag true) .stay hMove (by simp)
    rw [list_set_append_mid] at hNM
    have hNextSplit : encodeRegsPrefix pref ++
        SimSym.tag true :: (cur.2.map SimSym.bit ++ SimSym.sep :: tailSyms) =
        encodeRegsTape (pref ++ (true, cur.2) :: suf) src := by
      simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
    rw [hNextSplit] at hNM
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ _ => ((), .tag true, .stay)) tRegs input bound
      (fun j => if j = tRegs then mt else initTapes j) inHead hHeadsMT
      (by simpa using hUpd) (by simpa [hNM.head_eq, hPL] using by omega)
    have hNtEq : (fun j => if j = tRegs then nt else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then nt else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hNtEq] at hAtom
    obtain ⟨ft, hReset, hFM⟩ := resetLeftRegs_reachesExit input bound W hW pref (true, cur.2) suf src
      hPrefLen hCurLen hSufLen hSrcLen hBound (fun j => if j = tRegs then nt else initTapes j)
      inHead (fun j hj => by simp [hj, hOtherBounds j hj]) (by simpa using hNM)
    have hFtEq : (fun j => if j = tRegs then ft else if j = tRegs then nt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hReset
    refine ⟨ft, ?_, hFM⟩
    have hSeq := TMComponent.seq_reachesExit _ _ input bound hAtom hReset
    have hMap := TMComponent.mapExit_reachesExit _ (fun _ => true) input bound hSeq
    exact (findFirstUntagged InputAlphabet).branch_reachesExit _ _ input bound true hFindRun hMap

end SavitchLemma

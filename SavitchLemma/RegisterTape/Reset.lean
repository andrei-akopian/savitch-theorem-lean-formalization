module

public import SavitchLemma.RegisterTape.Copy

@[expose] public section

/-!
# Register reset

Resets preceding working registers to the first valid code.
-/

namespace SavitchLemma

/-- Reset all working registers to the left of the current register on `tRegs`
to untagged `firstCode = 1` (`[true] ++ replicate (W - 1) false`), leaving `tRegs` at cell `1`. -/
inductive ResetLeftState where
  | stepInit
  | goLeft
  | wipeBits
  | fixLSB
  | backToTag
  deriving DecidableEq

def ResetLeftState.equivFin : ResetLeftState ≃ Fin 5 where
  toFun
    | .stepInit => 0 | .goLeft => 1 | .wipeBits => 2 | .fixLSB => 3 | .backToTag => 4
  invFun
    | 0 => .stepInit | 1 => .goLeft | 2 => .wipeBits | 3 => .fixLSB | _ => .backToTag
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype ResetLeftState := Fintype.ofEquiv (Fin 5) ResetLeftState.equivFin.symm

def resetLeftRegs (InputAlphabet : Type*) :
    TMComponent ResetLeftState InputAlphabet SimSym 5 Unit where
  start := .stepInit
  step s _ scanned :=
    match s with
    | .stepInit => singleTapeAction (.inl .goLeft) tRegs (scanned tRegs) .left scanned
    | .goLeft =>
      match scanned tRegs with
      | .leftMark => singleTapeAction (.inr ()) tRegs .leftMark .right scanned
      | .sep => singleTapeAction (.inl .wipeBits) tRegs .sep .left scanned
      | sym => singleTapeAction (.inl .goLeft) tRegs sym .left scanned
    | .wipeBits =>
      match scanned tRegs with
      | .bit _ => singleTapeAction (.inl .wipeBits) tRegs (.bit false) .left scanned
      | .tag _ => singleTapeAction (.inl .fixLSB) tRegs (.tag false) .right scanned
      | sym => singleTapeAction (.inl .goLeft) tRegs sym .left scanned
    | .fixLSB =>
      singleTapeAction (.inl .backToTag) tRegs (.bit true) .left scanned
    | .backToTag =>
      singleTapeAction (.inl .goLeft) tRegs (scanned tRegs) .left scanned

private theorem resetLeftRegs_wipeBits {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (b : Bool) (bits : List Bool) (hBitsLen : bits.length = W)
    (pref suf : List SimSym) (hPrefPos : 1 ≤ pref.length)
    (Post : OneSidedTape SimSym → Prop)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBound : pref.length + W + 2 ≤ bound tRegs)
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hAfter : ∀ tape, TapeMatches tape
        (pref ++ encodeRegEntry false (natToBits W 1) ++ suf) (pref.length - 1) →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
        Post ft) :
    ∀ pos, pos ≤ bits.length →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            ((bits.take pos).map SimSym.bit ++
              List.replicate (bits.length - pos) (SimSym.bit false) ++
              SimSym.sep :: suf))
          (pref.length + pos) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .wipeBits, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          Post ft := by
  intro pos
  induction pos with
  | zero =>
    intro _ tape hM
    let tailTail := List.replicate W (SimSym.bit false) ++ SimSym.sep :: suf
    have hMEq : pref ++ SimSym.tag b ::
        ((bits.take 0).map SimSym.bit ++
          List.replicate (bits.length - 0) (SimSym.bit false) ++ SimSym.sep :: suf) =
        pref ++ SimSym.tag b :: tailTail := by
      simp [tailTail, hBitsLen]
    have hM' : TapeMatches tape (pref ++ SimSym.tag b :: tailTail) pref.length := by
      rw [← hMEq]
      simpa using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid pref (.tag b) tailTail
    have hMove₁ : moveOneSidedHead pref.length .right = some (pref.length + 1) := by
      simp [moveOneSidedHead]
    obtain ⟨nt₁, hUpd₁, hNM₁⟩ := hM'.update_set (.tag false) .right hMove₁ (by simp)
    rw [list_set_append_mid] at hNM₁
    have hW1 : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
    rcases hW1 with ⟨W', hWEq⟩
    have hRepSplit : tailTail = SimSym.bit false :: (List.replicate W' (SimSym.bit false) ++ SimSym.sep :: suf) := by
      simp [tailTail, hWEq, List.replicate_succ]
    let pref₂ := pref ++ [SimSym.tag false]
    let suf₂ := List.replicate W' (SimSym.bit false) ++ SimSym.sep :: suf
    have hPref₂Len : pref₂.length = pref.length + 1 := by simp [pref₂]
    have hNM₁' : TapeMatches nt₁ (pref₂ ++ SimSym.bit false :: suf₂) pref₂.length := by
      rw [hPref₂Len]
      simpa [pref₂, suf₂, hRepSplit, List.append_assoc] using hNM₁
    have hMove₂ : moveOneSidedHead (pref.length + 1) .left = some pref.length := by
      simp [moveOneSidedHead]
    obtain ⟨nt₂, hUpd₂, hNM₂⟩ :=
      hNM₁'.update_set (.bit true) .left (by rw [hPref₂Len]; exact hMove₂) (by simp)
    rw [list_set_append_mid] at hNM₂
    have hEntryEq : pref₂ ++ SimSym.bit true :: suf₂ =
        pref ++ encodeRegEntry false (natToBits W 1) ++ suf := by
      have hOne := natToBits_one (by omega : 1 ≤ W' + 1)
      simp only [encodeRegEntry, hWEq, hOne, Nat.add_sub_cancel]
      simp [pref₂, suf₂, List.map_replicate, List.append_assoc]
    rw [hEntryEq] at hNM₂
    have hMove₃ : moveOneSidedHead pref.length .left = some (pref.length - 1) := by
      simp [moveOneSidedHead, show pref.length ≠ 0 by omega]
    obtain ⟨nt₃, hUpd₃, hNM₃⟩ := hNM₂.update_keep .left hMove₃
    obtain ⟨ft, hGo, hRes⟩ := hAfter nt₃ hNM₃
    have hHeads₁ : ∀ j, (if j = tRegs then nt₁ else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hNM₁'.head_eq, hPref₂Len] using Nat.lt_of_lt_of_le (by omega : pref.length + 1 < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hHeads₂ : ∀ j, (if j = tRegs then nt₂ else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hNM₂.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hStepBack := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes nt₂ nt₃ ft .backToTag .goLeft hHeads₂
      (by rw [hNM₃.head_eq]; omega) hUpd₃ hGo (by simp [resetLeftRegs])
    have hStepFix := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes nt₁ nt₂ ft .fixLSB .backToTag hHeads₁
      (by rw [hNM₂.head_eq]; omega) hUpd₂ hStepBack (by simp [resetLeftRegs])
    have hStepWipe := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt₁ ft .wipeBits .fixLSB hHeads
      (by rw [hNM₁'.head_eq, hPref₂Len]; omega) hUpd₁ hStepFix (by simp [resetLeftRegs, hRead])
    exact ⟨ft, hStepWipe, hRes⟩
  | succ p ih =>
    intro hpLe tape hM
    let midPref := pref ++ SimSym.tag b :: (bits.take p).map SimSym.bit
    let midSuf := List.replicate (bits.length - (p + 1)) (SimSym.bit false) ++ SimSym.sep :: suf
    have hMidPrefLen : midPref.length = pref.length + p + 1 := by
      simp [midPref, Nat.min_eq_left (by omega : p ≤ bits.length)]; omega
    have hTakeSucc : bits.take (p + 1) = bits.take p ++ [bits[p]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega : p < bits.length)]
      rfl
    have hRepSucc : List.replicate (bits.length - p) (SimSym.bit false) =
        SimSym.bit false :: List.replicate (bits.length - (p + 1)) (SimSym.bit false) := by
      rw [show bits.length - p = (bits.length - (p + 1)) + 1 by omega, List.replicate_succ]
    have hCurListEq : pref ++ SimSym.tag b ::
        ((bits.take (p + 1)).map SimSym.bit ++
          List.replicate (bits.length - (p + 1)) (SimSym.bit false) ++ SimSym.sep :: suf) =
        midPref ++ SimSym.bit (bits[p]'(by omega)) :: midSuf := by
      rw [hTakeSucc]
      simp only [List.map_append, List.map_cons, List.map_nil, midPref, midSuf,
        List.append_assoc, List.cons_append, List.nil_append]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit (bits[p]'(by omega)) :: midSuf)
        midPref.length := by
      rw [hMidPrefLen, ← hCurListEq]
      simpa [Nat.add_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using Nat.lt_of_lt_of_le (by omega : pref.length + (p + 1) < pref.length + W + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit (bits[p]'(by omega)) := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit _) midSuf
    have hMove : moveOneSidedHead (pref.length + (p + 1)) .left = some (pref.length + p) := by
      simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ :=
      hM'.update_set (.bit false) .left (by rw [hMidPrefLen]; simpa [Nat.add_assoc] using hMove)
        (by simp)
    rw [list_set_append_mid] at hNM
    have hNextListEq : midPref ++ SimSym.bit false :: midSuf =
        pref ++ SimSym.tag b ::
          ((bits.take p).map SimSym.bit ++
            List.replicate (bits.length - p) (SimSym.bit false) ++ SimSym.sep :: suf) := by
      simp [midPref, midSuf, hRepSucc, List.append_assoc]
    rw [hNextListEq] at hNM
    obtain ⟨ft, hRest, hRes⟩ := ih (by omega) nt hNM
    refine ⟨ft, ?_, hRes⟩
    exact singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt ft .wipeBits .wipeBits hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [resetLeftRegs, hRead])

private theorem resetLeftRegs_goLeft {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (revPref : List (Bool × List Bool)) (suf : List (Bool × List Bool)),
      (∀ r ∈ revPref, r.2.length = W) →
      1 + (revPref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (revPref.reverse ++ suf) src)
          ((encodeRegsPrefix revPref.reverse).length - 1) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (encodeRegsTape (revPref.reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src) 1 := by
  intro revPref
  induction revPref with
  | nil =>
    intro suf _ hBound tape hM
    have hPrefLen : (encodeRegsPrefix ([] : List (Bool × List Bool)).reverse).length = 1 := rfl
    rw [hPrefLen] at hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using Nat.lt_of_lt_of_le (by omega : 0 < 1 + (0 + suf.length) * (W + 2) + (W + 3)) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hM.read_lt (by simp [encodeRegsTape, encodeRegsPrefix])]
      rfl
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nt, hUpd, hNM⟩ := hM.update_set .leftMark .right hMove
      (by simp [encodeRegsTape, encodeRegsPrefix])
    have hSetSame : (encodeRegsTape ([] ++ suf) src).set 0 .leftMark = encodeRegsTape ([] ++ suf) src := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        cases i with
        | zero => simp [encodeRegsTape, encodeRegsPrefix]
        | succ i' => simp
    simp only [List.reverse_nil, Nat.sub_self] at hNM
    rw [hSetSame] at hNM
    refine ⟨nt, ?_, by simpa using hNM⟩
    exact singleTape_compStep_exit_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt .goLeft hHeads (by rw [hNM.head_eq]; omega)
      hUpd (by simp [resetLeftRegs, hRead])
  | cons cur rest ih =>
    intro suf hRevLen hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := hRevLen (b, bs) (by simp)
    have hRestLen : ∀ r ∈ rest, r.2.length = W := fun r hr => hRevLen r (by simp [hr])
    have hRestPrefixLen : (encodeRegsPrefix rest.reverse).length = 1 + rest.length * (W + 2) := by
      have := encodeRegsPrefix_length W rest.reverse (fun r hr => hRestLen r (by simpa using hr))
      simpa using this
    have hCurPrefixLen : (encodeRegsPrefix ((b, bs) :: rest).reverse).length =
        (encodeRegsPrefix rest.reverse).length + (W + 2) := by
      simp [List.reverse_cons, encodeRegsPrefix_snoc, encodeRegEntry_length, hBsLen]
    have hMulEq : ((b, bs) :: rest).length + suf.length = rest.length + (suf.length + 1) := by
      simp; omega
    have hBound' : 1 + rest.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simpa [hMulEq, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
    let prefSyms := encodeRegsPrefix rest.reverse
    let tailSyms : List SimSym := suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src
    have hTapeEq : encodeRegsTape (((b, bs) :: rest).reverse ++ suf) src =
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) ++ SimSym.sep :: tailSyms := by
      simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append,
        encodeRegEntry, List.reverse_cons, List.append_assoc]
    have hPrefSymLen : (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length =
        prefSyms.length + W + 1 := by
      simp [hBsLen]; omega
    have hSepPos : ((encodeRegsPrefix ((b, bs) :: rest).reverse).length - 1) =
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length := by
      rw [hCurPrefixLen]
      simp [prefSyms, hBsLen]
    have hM' : TapeMatches tape
        ((prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) ++ SimSym.sep :: tailSyms)
        (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length := by
      rw [← hTapeEq, ← hSepPos]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j
      by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefSymLen, hRestPrefixLen] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit) .sep tailSyms
    have hMove : moveOneSidedHead (prefSyms ++ SimSym.tag b :: bs.map SimSym.bit).length .left =
        some (prefSyms.length + bs.length) := by
      simp [moveOneSidedHead, hBsLen]
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .left hMove
    have hNM' : TapeMatches nt
        (prefSyms ++ SimSym.tag b ::
          ((bs.take bs.length).map SimSym.bit ++
            List.replicate (bs.length - bs.length) (SimSym.bit false) ++
            SimSym.sep :: tailSyms))
        (prefSyms.length + bs.length) := by
      rw [List.take_length, Nat.sub_self, List.replicate_zero]
      simpa [List.append_assoc] using hNM
    have hPost : ∀ tape₂, TapeMatches tape₂
        (prefSyms ++ encodeRegEntry false (natToBits W 1) ++ tailSyms) (prefSyms.length - 1) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (resetLeftRegs InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .goLeft, inHead, fun j => if j = tRegs then tape₂ else initTapes j⟩
            ⟨.inr (), inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (encodeRegsTape (((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src)
            1 := by
      intro tape₂ hM₂
      have hList₂ : prefSyms ++ encodeRegEntry false (natToBits W 1) ++ tailSyms =
          encodeRegsTape (rest.reverse ++ (false, natToBits W 1) :: suf) src := by
        simp [prefSyms, tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry,
          List.append_assoc]
      rw [hList₂] at hM₂
      have hBoundRec : 1 + (rest.length + ((false, natToBits W 1) :: suf).length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      obtain ⟨ft, hRun, hFM⟩ := ih ((false, natToBits W 1) :: suf) hRestLen hBoundRec tape₂ hM₂
      have hFinalEq : (rest.reverse.map (fun _ => (false, natToBits W 1)) ++
          (false, natToBits W 1) :: suf) =
          ((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hFinalEq] at hFM
      exact ⟨ft, hRun, hFM⟩
    obtain ⟨ft, hWipe, hRes⟩ := resetLeftRegs_wipeBits input bound W hW b bs hBsLen prefSyms tailSyms
      (by simp [prefSyms, encodeRegsPrefix])
      (fun ft => TapeMatches ft
        (encodeRegsTape (((b, bs) :: rest).reverse.map (fun _ => (false, natToBits W 1)) ++ suf) src) 1)
      initTapes inHead (by rw [hRestPrefixLen]; omega) hOtherBounds hPost
      bs.length le_rfl nt hNM'
    refine ⟨ft, ?_, hRes⟩
    exact singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
      input bound initTapes tape nt ft .goLeft .wipeBits hHeads
      (by rw [hNM'.head_eq, hRestPrefixLen, hBsLen]; omega)
      hUpd hWipe (by simp [resetLeftRegs, hRead])

theorem resetLeftRegs_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (pref : List (Bool × List Bool)) (cur : Bool × List Bool)
    (suf : List (Bool × List Bool)) (src : List Bool)
    (hPrefLen : ∀ r ∈ pref, r.2.length = W) (hCurLen : cur.2.length = W)
    (_hSufLen : ∀ r ∈ suf, r.2.length = W) (hSrcLen : src.length = W)
    (hBound : 1 + (pref.length + 1 + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape (pref ++ cur :: suf) src)
      (encodeRegsPrefix pref).length) :
    ∃ ft,
      (resetLeftRegs InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
      TapeMatches ft
        (encodeRegsTape (pref.map (fun _ => (false, natToBits W 1)) ++ cur :: suf) src) 1 := by
  have hPrefPos : 1 ≤ (encodeRegsPrefix pref).length := by simp [encodeRegsPrefix]
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = tRegs
    · subst hj
      have hPL := encodeRegsPrefix_length W pref hPrefLen
      have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
      simpa [hMatch.head_eq, hPL] using by omega
    · exact hOtherBounds j hj
  have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .left =
      some ((encodeRegsPrefix pref).length - 1) := by
    simp [moveOneSidedHead, show (encodeRegsPrefix pref).length ≠ 0 by omega]
  obtain ⟨nt, hUpd, hNM⟩ := hMatch.update_keep .left hMove
  have hRevEq : pref.reverse.reverse = pref := List.reverse_reverse pref
  have hNM' : TapeMatches nt (encodeRegsTape (pref.reverse.reverse ++ cur :: suf) src)
      ((encodeRegsPrefix pref.reverse.reverse).length - 1) := by
    simpa [hRevEq] using hNM
  have hBoundGo : 1 + (pref.reverse.length + (cur :: suf).length) * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simp only [List.length_reverse, List.length_cons]
    have hEqLen : pref.length + (suf.length + 1) = pref.length + 1 + suf.length := by omega
    rw [hEqLen]
    exact hBound
  obtain ⟨ft, hGo, hFM⟩ := resetLeftRegs_goLeft input bound W hW src hSrcLen initTapes inHead
    hOtherBounds pref.reverse (cur :: suf) (fun r hr => hPrefLen r (by simpa using hr))
    hBoundGo nt hNM'
  have hFM' : TapeMatches ft
      (encodeRegsTape (pref.map (fun _ => (false, natToBits W 1)) ++ cur :: suf) src) 1 := by
    simpa [hRevEq] using hFM
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  have hHeadsOv : ∀ j, (if j = tRegs then initTapes tRegs else initTapes j).head < bound j := by
    intro j; rw [congrFun hTapesSelf j]; exact hHeads j
  have hBoundExp : 1 + pref.length * (W + 2) + (W + 2) + suf.length * (W + 2) + (W + 3) ≤
      bound tRegs := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hBound
  have hStep := singleTape_compStep_head_override (resetLeftRegs InputAlphabet) tRegs
    input bound initTapes (initTapes tRegs) nt ft .stepInit .goLeft hHeadsOv
    (by rw [hNM.head_eq, encodeRegsPrefix_length W pref hPrefLen]; omega)
    hUpd hGo (by simp [resetLeftRegs])
  rw [hTapesSelf] at hStep
  exact ⟨ft, hStep, hFM'⟩

end SavitchLemma

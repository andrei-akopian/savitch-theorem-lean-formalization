module

public import SavitchLemma.RegisterTape.Tag

@[expose] public section

/-!
# Register increment

Implements the D3 search and increment operation on the register tape.
-/

namespace SavitchLemma

/-- D3 backtracking on Tape 1: find the least working register strictly below
the maximum code (`2^W - 1`, i.e., containing at least one `.bit false`),
increment it, clear its tag, reset all working registers to its left, and rewind
Tape 1 to cell `1`. If all working registers are at `2^W - 1`, rewind Tape 1 to
cell `1` and return `false`. -/
inductive IncRegState where
  | scanTag
  | tryInc
  | backZero
  deriving DecidableEq

def IncRegState.equivFin : IncRegState ≃ Fin 3 where
  toFun | .scanTag => 0 | .tryInc => 1 | .backZero => 2
  invFun | 0 => .scanTag | 1 => .tryInc | _ => .backZero
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype IncRegState := Fintype.ofEquiv (Fin 3) IncRegState.equivFin.symm

def incFirstBody (InputAlphabet : Type*) :
    TMComponent IncRegState InputAlphabet SimSym 5 Bool where
  start := .scanTag
  step s _ scanned :=
    match s with
    | .scanTag =>
      match scanned tRegs with
      | .tag b => singleTapeAction (.inl .tryInc) tRegs (.tag b) .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .tryInc =>
      match scanned tRegs with
      | .bit true => singleTapeAction (.inl .tryInc) tRegs (.bit true) .right scanned
      | .bit false => singleTapeAction (.inl .backZero) tRegs (.bit true) .left scanned
      | .sep => singleTapeAction (.inl .scanTag) tRegs .sep .right scanned
      | sym => singleTapeAction (.inr false) tRegs sym .stay scanned
    | .backZero =>
      match scanned tRegs with
      | .tag _ => singleTapeAction (.inr true) tRegs (.tag false) .stay scanned
      | _ => singleTapeAction (.inl .backZero) tRegs (.bit false) .left scanned

def incFirstRegBelowMax (InputAlphabet : Type*) :=
  (incFirstBody InputAlphabet).branch
    ((resetLeftRegs InputAlphabet).mapExit fun _ => true)
    ((rewindTape InputAlphabet tRegs).mapExit fun _ => false)

private theorem incFirstBody_backZero {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ pos (sufBits : List Bool),
      pref.length + pos + sufBits.length + 2 ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            (List.replicate pos (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
            SimSym.sep :: suf)
          (pref.length + pos) →
        ∃ ft,
          Relation.ReflTransGen
            (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .backZero, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
          TapeMatches ft
            (pref ++ SimSym.tag false ::
              (List.replicate pos (SimSym.bit false) ++ sufBits.map SimSym.bit) ++
              SimSym.sep :: suf)
            pref.length := by
  intro pos
  induction pos with
  | zero =>
    intro sufBits hBound tape hM
    let tailSyms := sufBits.map SimSym.bit ++ SimSym.sep :: suf
    have hMEq : pref ++ SimSym.tag b ::
        (List.replicate 0 (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
        SimSym.sep :: suf = pref ++ SimSym.tag b :: tailSyms := by
      simp [tailSyms, List.append_assoc]
    have hM' : TapeMatches tape (pref ++ SimSym.tag b :: tailSyms) pref.length := by
      rw [← hMEq]; simpa using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .tag b := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid pref (.tag b) tailSyms
    have hMove : moveOneSidedHead pref.length .stay = some pref.length := rfl
    obtain ⟨ft, hUpd, hFM⟩ := hM'.update_set (.tag false) .stay hMove (by simp)
    rw [list_set_append_mid] at hFM
    have hOutEq : pref ++ SimSym.tag false :: tailSyms =
        pref ++ SimSym.tag false ::
          (List.replicate 0 (SimSym.bit false) ++ sufBits.map SimSym.bit) ++
          SimSym.sep :: suf := by
      simp [tailSyms, List.append_assoc]
    rw [hOutEq] at hFM
    refine ⟨ft, ?_, hFM⟩
    exact singleTape_compStep_exit_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape ft .backZero hHeads (by rw [hFM.head_eq]; omega)
      hUpd (by simp [incFirstBody, hRead])
  | succ p ih =>
    intro sufBits hBound tape hM
    let midPref := pref ++ SimSym.tag b :: List.replicate p (SimSym.bit true)
    let midSuf := sufBits.map SimSym.bit ++ SimSym.sep :: suf
    have hMidPrefLen : midPref.length = pref.length + (p + 1) := by simp [midPref]
    have hCurEq : pref ++ SimSym.tag b ::
        (List.replicate (p + 1) (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
        SimSym.sep :: suf = midPref ++ SimSym.bit true :: midSuf := by
      simp [midPref, midSuf, List.replicate_succ', List.append_assoc]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit true :: midSuf) midPref.length := by
      rw [hMidPrefLen, ← hCurEq]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit true := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit true) midSuf
    have hMove : moveOneSidedHead (pref.length + (p + 1)) .left = some (pref.length + p) := by
      simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ :=
      hM'.update_set (.bit false) .left (by rw [hMidPrefLen]; exact hMove) (by simp)
    rw [list_set_append_mid] at hNM
    have hNextEq : midPref ++ SimSym.bit false :: midSuf =
        pref ++ SimSym.tag b ::
          (List.replicate p (SimSym.bit true) ++ (false :: sufBits).map SimSym.bit) ++
          SimSym.sep :: suf := by
      simp [midPref, midSuf, List.append_assoc]
    rw [hNextEq] at hNM
    obtain ⟨ft, hRest, hFM⟩ := ih (false :: sufBits) (by simp; omega) nt hNM
    have hRepOut : List.replicate (p + 1) (SimSym.bit false) ++ sufBits.map SimSym.bit =
        List.replicate p (SimSym.bit false) ++ (false :: sufBits).map SimSym.bit := by
      simp [List.replicate_succ', List.append_assoc]
    rw [← hRepOut] at hFM
    refine ⟨ft, ?_, hFM⟩
    exact singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape nt ft .backZero .backZero hHeads
      (by rw [hNM.head_eq]; omega) hUpd hRest (by simp [incFirstBody, hRead])

private theorem incFirstBody_tryInc {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref suf : List SimSym) (b : Bool)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (sufBits : List Bool) (nOnes : ℕ),
      pref.length + nOnes + sufBits.length + 3 ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape
          (pref ++ SimSym.tag b ::
            (List.replicate nOnes (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
            SimSym.sep :: suf)
          (pref.length + 1 + nOnes) →
        (∃ ft,
          (false ∈ sufBits ∧
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (pref ++ SimSym.tag false ::
                (incBits (List.replicate nOnes true ++ sufBits)).map SimSym.bit ++
                SimSym.sep :: suf)
              pref.length) ∨
          (false ∉ sufBits ∧
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (pref ++ SimSym.tag b ::
                (List.replicate nOnes (SimSym.bit true) ++ sufBits.map SimSym.bit) ++
                SimSym.sep :: suf)
              (pref.length + nOnes + sufBits.length + 2))) := by
  intro sufBits
  induction sufBits with
  | nil =>
    intro nOnes hBound tape hM
    let prefSyms := pref ++ SimSym.tag b :: List.replicate nOnes (SimSym.bit true)
    have hPrefLen : prefSyms.length = pref.length + 1 + nOnes := by simp [prefSyms]; omega
    have hM' : TapeMatches tape (prefSyms ++ SimSym.sep :: suf) prefSyms.length := by
      simpa [prefSyms, hPrefLen, List.append_assoc] using hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM'.head_eq, hPrefLen] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .sep := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid prefSyms .sep suf
    have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .right =
        some (pref.length + nOnes + ([] : List Bool).length + 2) := by
      simp [moveOneSidedHead]; omega
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hPrefLen]; exact hMove)
    have hNM' : TapeMatches nt
        (pref ++ SimSym.tag b :: (List.replicate nOnes (SimSym.bit true) ++ ([] : List Bool).map SimSym.bit) ++
          SimSym.sep :: suf)
        (pref.length + nOnes + ([] : List Bool).length + 2) := by
      simpa [prefSyms, List.append_assoc] using hNM
    refine ⟨nt, Or.inr ⟨by simp, ?_, hNM'⟩⟩
    refine Relation.ReflTransGen.single ⟨?_, hHeads, fun j => ?_⟩
    · have hNext : ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
          (fun j => (if j = tRegs then tape else initTapes j).cells
            (if j = tRegs then tape else initTapes j).head)).nextState = .inl .scanTag := by
        simp [incFirstBody, singleTapeAction, hRead]
      have hInMove : moveHead (n + 2) inHead
          ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
            (fun j => (if j = tRegs then tape else initTapes j).cells
              (if j = tRegs then tape else initTapes j).head)).inputMove = some inHead := by
        simp [incFirstBody, singleTapeAction, hRead, moveHead]
      have hWork : ∀ j,
          (if j = tRegs then tape else initTapes j).updateAndMove
            (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
              (fun j => (if j = tRegs then tape else initTapes j).cells
                (if j = tRegs then tape else initTapes j).head)).write j)
            (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
              (fun j => (if j = tRegs then tape else initTapes j).cells
                (if j = tRegs then tape else initTapes j).head)).workMove j) =
            some (if j = tRegs then nt else initTapes j) := by
        intro j
        have hStepEq : (incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
            (fun y => (if y = tRegs then tape else initTapes y).cells
              (if y = tRegs then tape else initTapes y).head) =
            singleTapeAction (.inl .scanTag) tRegs .sep .right
              (fun y => (if y = tRegs then tape else initTapes y).cells
                (if y = tRegs then tape else initTapes y).head) := by
          simp [incFirstBody, hRead]
        rw [hStepEq]
        have hApp := singleTapeAction_apply (Sum.inl IncRegState.scanTag : IncRegState ⊕ Bool)
          tRegs .sep .right (fun y => if y = tRegs then tape else initTapes y)
          (by simpa [hRead] using hUpd) j
        by_cases hj : j = tRegs
        · subst hj; simpa using hApp
        · simpa [hj] using hApp
      exact ⟨.tryInc, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
    · by_cases hj : j = tRegs
      · subst hj; simpa [hNM'.head_eq] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
  | cons x xs ih =>
    intro nOnes hBound tape hM
    let midPref := pref ++ SimSym.tag b :: List.replicate nOnes (SimSym.bit true)
    let midSuf := xs.map SimSym.bit ++ SimSym.sep :: suf
    have hMidLen : midPref.length = pref.length + 1 + nOnes := by simp [midPref]; omega
    have hCurEq : pref ++ SimSym.tag b ::
        (List.replicate nOnes (SimSym.bit true) ++ (x :: xs).map SimSym.bit) ++
        SimSym.sep :: suf = midPref ++ SimSym.bit x :: midSuf := by
      simp [midPref, midSuf, List.append_assoc]
    have hM' : TapeMatches tape (midPref ++ SimSym.bit x :: midSuf) midPref.length := by
      rw [hMidLen, ← hCurEq]; exact hM
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
      · subst hj; simpa [hM.head_eq] using by simp at hBound; omega
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit x := by
      rw [hM'.read_lt (by simp)]
      exact list_get_append_mid midPref (.bit x) midSuf
    cases x with
    | false =>
      have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .left =
          some (pref.length + nOnes) := by simp [moveOneSidedHead]
      obtain ⟨nt, hUpd, hNM⟩ :=
        hM'.update_set (.bit true) .left (by rw [hMidLen]; exact hMove) (by simp)
      rw [list_set_append_mid] at hNM
      have hNextEq : midPref ++ SimSym.bit true :: midSuf =
          pref ++ SimSym.tag b ::
            (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
            SimSym.sep :: suf := by
        simp [midPref, midSuf, List.append_assoc]
      rw [hNextEq] at hNM
      obtain ⟨ft, hBack, hFM⟩ := incFirstBody_backZero input bound pref suf b initTapes inHead
        hOtherBounds nOnes (true :: xs) (by simp at hBound ⊢; omega) nt hNM
      have hIncRep : ∀ m (r : List Bool),
          incBits (List.replicate m true ++ false :: r) =
            List.replicate m false ++ true :: r := by
        intro m r
        induction m with
        | zero => simp [incBits]
        | succ m ihm => simp [List.replicate_succ, incBits, ihm]
      have hIncEq : (incBits (List.replicate nOnes true ++ false :: xs)).map SimSym.bit =
          List.replicate nOnes (SimSym.bit false) ++ (true :: xs).map SimSym.bit := by
        rw [hIncRep]
        simp [List.map_replicate]
      rw [← hIncEq] at hFM
      have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
        input bound initTapes tape nt ft .tryInc .backZero hHeads
        (by rw [hNM.head_eq]; simp at hBound; omega) hUpd hBack (by simp [incFirstBody, hRead])
      exact ⟨ft, Or.inl ⟨by simp, hStep, hFM⟩⟩
    | true =>
      have hMove : moveOneSidedHead (pref.length + 1 + nOnes) .right =
          some (pref.length + 1 + (nOnes + 1)) := by simp [moveOneSidedHead]; omega
      obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right (by rw [hMidLen]; exact hMove)
      have hNextEq : midPref ++ SimSym.bit true :: midSuf =
          pref ++ SimSym.tag b ::
            (List.replicate (nOnes + 1) (SimSym.bit true) ++ xs.map SimSym.bit) ++
            SimSym.sep :: suf := by
        simp [midPref, midSuf, List.replicate_succ', List.append_assoc]
      rw [hNextEq] at hNM
      obtain ⟨ft, hBranch⟩ := ih (nOnes + 1) (by simp at hBound ⊢; omega) nt hNM
      rcases hBranch with ⟨hMemXs, hWin, hFM⟩ | ⟨hNoXs, hCont, hFM⟩
      · have hIncEq : incBits (List.replicate nOnes true ++ true :: xs) =
            incBits (List.replicate (nOnes + 1) true ++ xs) := by
          simp [List.replicate_succ', List.append_assoc]
        rw [← hIncEq] at hFM
        have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
          input bound initTapes tape nt ft .tryInc .tryInc hHeads
          (by rw [hNM.head_eq]; simp at hBound ⊢; omega) hUpd hWin (by simp [incFirstBody, hRead])
        exact ⟨ft, Or.inl ⟨by simp [hMemXs], hStep, hFM⟩⟩
      · have hOutEq : pref ++ SimSym.tag b ::
            (List.replicate (nOnes + 1) (SimSym.bit true) ++ xs.map SimSym.bit) ++
            SimSym.sep :: suf =
            pref ++ SimSym.tag b ::
              (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
              SimSym.sep :: suf := by
          simp [List.replicate_succ', List.append_assoc]
        rw [hOutEq] at hFM
        have hFM' : TapeMatches ft
            (pref ++ SimSym.tag b ::
              (List.replicate nOnes (SimSym.bit true) ++ (true :: xs).map SimSym.bit) ++
              SimSym.sep :: suf)
            (pref.length + nOnes + (true :: xs).length + 2) := by
          simpa [Nat.add_assoc, Nat.add_comm 1] using hFM
        have hStep : Relation.ReflTransGen
            (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
              (∀ j, (a.workTapes j).head < bound j) ∧
              (∀ j, (b.workTapes j).head < bound j))
            ⟨.inl .tryInc, inHead, fun j => if j = tRegs then tape else initTapes j⟩
            ⟨.inl .scanTag, inHead, fun j => if j = tRegs then ft else initTapes j⟩ := by
          refine Relation.ReflTransGen.head ⟨?_, hHeads, fun j => ?_⟩ hCont
          · have hNext : ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head)).nextState = .inl .tryInc := by
              simp [incFirstBody, singleTapeAction, hRead]
            have hInMove : moveHead (n + 2) inHead
                ((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).inputMove = some inHead := by
              simp [incFirstBody, singleTapeAction, hRead, moveHead]
            have hWork : ∀ j,
                (if j = tRegs then tape else initTapes j).updateAndMove
                  (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head)).write j)
                  (((incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head)).workMove j) =
                  some (if j = tRegs then nt else initTapes j) := by
              intro j
              have hStepEq : (incFirstBody InputAlphabet).step .tryInc (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head) =
                  singleTapeAction (.inl .tryInc) tRegs (.bit true) .right
                    (fun y => (if y = tRegs then tape else initTapes y).cells
                      (if y = tRegs then tape else initTapes y).head) := by
                simp [incFirstBody, hRead]
              rw [hStepEq]
              have hApp := singleTapeAction_apply (Sum.inl IncRegState.tryInc : IncRegState ⊕ Bool)
                tRegs (.bit true) .right (fun y => if y = tRegs then tape else initTapes y)
                (by simpa [hRead] using hUpd) j
              by_cases hj : j = tRegs
              · subst hj; simpa using hApp
              · simpa [hj] using hApp
            exact ⟨.tryInc, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
          · by_cases hj : j = tRegs
            · subst hj; simpa [hNM.head_eq] using by simp at hBound; omega
            · simpa [hj] using hOtherBounds j hj
        exact ⟨ft, Or.inr ⟨by simp [hNoXs], hStep, hFM'⟩⟩

private theorem incFirstBody_scan {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (src : List Bool) (hSrc : src.length = W)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j) :
    ∀ (suf pref : List (Bool × List Bool)),
      (∀ r ∈ pref, r.2.length = W ∧ false ∉ r.2) →
      (∀ r ∈ suf, r.2.length = W) →
      1 + (pref.length + suf.length) * (W + 2) + (W + 3) ≤ bound tRegs →
      ∀ tape,
        TapeMatches tape (encodeRegsTape (pref ++ suf) src) (encodeRegsPrefix pref).length →
        (∃ p₁ cur p₂, suf = p₁ ++ cur :: p₂ ∧
          false ∈ cur.2 ∧ (∀ r ∈ p₁, false ∉ r.2) ∧
          ∃ ft,
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr true, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft
              (encodeRegsTape (pref ++ p₁ ++ (false, incBits cur.2) :: p₂) src)
              (encodeRegsPrefix (pref ++ p₁)).length) ∨
        ((∀ r ∈ suf, false ∉ r.2) ∧
          ∃ ft,
            Relation.ReflTransGen
              (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
                (∀ j, (a.workTapes j).head < bound j) ∧
                (∀ j, (b.workTapes j).head < bound j))
              ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
              ⟨.inr false, inHead, fun j => if j = tRegs then ft else initTapes j⟩ ∧
            TapeMatches ft (encodeRegsTape (pref ++ suf) src)
              (encodeRegsPrefix (pref ++ suf)).length) := by
  intro suf
  induction suf with
  | nil =>
    intro pref hPref _ hBound tape hM
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
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
    right
    refine ⟨by simp, ft, ?_, by simpa [encodeRegsTape, encodeSrcEntry] using hFM⟩
    exact singleTape_compStep_exit_override (incFirstBody InputAlphabet) tRegs
      input bound initTapes tape ft .scanTag hHeads
      (by rw [hFM.head_eq, hPL]; simp at hBound; omega) hUpd (by simp [incFirstBody, hRead])
  | cons cur rs ih =>
    intro pref hPref hSuf hBound tape hM
    rcases cur with ⟨b, bs⟩
    have hBsLen : bs.length = W := hSuf (b, bs) (by simp)
    have hPL := encodeRegsPrefix_length W pref (fun r hr => (hPref r hr).1)
    have hBound' : 1 + pref.length * (W + 2) + (W + 2) + rs.length * (W + 2) + (W + 3) ≤
        bound tRegs := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hBound ⊢
      omega
    have hHeads : ∀ j, (if j = tRegs then tape else initTapes j).head < bound j := by
      intro j; by_cases hj : j = tRegs
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
    have hMove : moveOneSidedHead (encodeRegsPrefix pref).length .right =
        some ((encodeRegsPrefix pref).length + 1) := by simp [moveOneSidedHead]
    obtain ⟨nt, hUpd, hNM⟩ := hM'.update_keep .right hMove
    have hNM' : TapeMatches nt
        (encodeRegsPrefix pref ++ SimSym.tag b ::
          (List.replicate 0 (SimSym.bit true) ++ bs.map SimSym.bit) ++ SimSym.sep :: tailSyms)
        ((encodeRegsPrefix pref).length + 1 + 0) := by
      simpa [List.append_assoc] using hNM
    obtain ⟨mt, hBranch⟩ := incFirstBody_tryInc input bound (encodeRegsPrefix pref) tailSyms b
      initTapes inHead hOtherBounds bs 0 (by rw [hPL, hBsLen]; omega) nt hNM'
    rcases hBranch with ⟨hMemBs, hWin, hFM⟩ | ⟨hNoBs, hCont, hFM⟩
    · have hOutEq : encodeRegsPrefix pref ++ SimSym.tag false ::
          (incBits (List.replicate 0 true ++ bs)).map SimSym.bit ++ SimSym.sep :: tailSyms =
          encodeRegsTape (pref ++ [] ++ (false, incBits bs) :: rs) src := by
        simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
      rw [hOutEq] at hFM
      have hStep := singleTape_compStep_head_override (incFirstBody InputAlphabet) tRegs
        input bound initTapes tape nt mt .scanTag .tryInc hHeads
        (by rw [hNM.head_eq, hPL]; omega) hUpd hWin (by simp [incFirstBody, hRead])
      left
      exact ⟨[], (b, bs), rs, rfl, hMemBs, by simp, mt, hStep, by simpa using hFM⟩
    · have hMtEq : encodeRegsPrefix pref ++ SimSym.tag b ::
          (List.replicate 0 (SimSym.bit true) ++ bs.map SimSym.bit) ++ SimSym.sep :: tailSyms =
          encodeRegsTape ((pref ++ [(b, bs)]) ++ rs) src := by
        simp [tailSyms, encodeRegsTape, encodeRegsPrefix_append, encodeRegEntry, List.append_assoc]
      rw [hMtEq] at hFM
      have hHeadNext : (encodeRegsPrefix pref).length + 0 + bs.length + 2 =
          (encodeRegsPrefix (pref ++ [(b, bs)])).length := by
        simp [encodeRegsPrefix_snoc, encodeRegEntry_length]
        omega
      rw [hHeadNext] at hFM
      have hPrefNext : ∀ r ∈ pref ++ [(b, bs)], r.2.length = W ∧ false ∉ r.2 := by
        intro r hr
        rcases List.mem_append.mp hr with hMem | hSingle
        · exact hPref r hMem
        · simp at hSingle; subst hSingle; exact ⟨hBsLen, hNoBs⟩
      have hBoundNext : 1 + ((pref ++ [(b, bs)]).length + rs.length) * (W + 2) + (W + 3) ≤
          bound tRegs := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have : pref.length + 1 + rs.length = pref.length + (rs.length + 1) := by omega
        rw [this]; exact hBound
      have hSufNext : ∀ r ∈ rs, r.2.length = W := fun r hr => hSuf r (by simp [hr])
      have hStepHead : Relation.ReflTransGen
          (fun a b => (incFirstBody InputAlphabet).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .scanTag, inHead, fun j => if j = tRegs then tape else initTapes j⟩
          ⟨.inl .scanTag, inHead, fun j => if j = tRegs then mt else initTapes j⟩ := by
        refine Relation.ReflTransGen.head ⟨?_, hHeads, fun j => ?_⟩ hCont
        · have hNext : ((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
              (fun y => (if y = tRegs then tape else initTapes y).cells
                (if y = tRegs then tape else initTapes y).head)).nextState = .inl .tryInc := by
            simp [incFirstBody, singleTapeAction, hRead]
          have hInMove : moveHead (n + 2) inHead
              ((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head)).inputMove = some inHead := by
            simp [incFirstBody, singleTapeAction, hRead, moveHead]
          have hWork : ∀ j,
              (if j = tRegs then tape else initTapes j).updateAndMove
                (((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).write j)
                (((incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head)).workMove j) =
                some (if j = tRegs then nt else initTapes j) := by
            intro j
            have hStepEq : (incFirstBody InputAlphabet).step .scanTag (readInput input inHead)
                (fun y => (if y = tRegs then tape else initTapes y).cells
                  (if y = tRegs then tape else initTapes y).head) =
                singleTapeAction (.inl .tryInc) tRegs (.tag b) .right
                  (fun y => (if y = tRegs then tape else initTapes y).cells
                    (if y = tRegs then tape else initTapes y).head) := by
              simp [incFirstBody, hRead]
            rw [hStepEq]
            have hApp := singleTapeAction_apply (Sum.inl IncRegState.tryInc : IncRegState ⊕ Bool)
              tRegs (.tag b) .right (fun y => if y = tRegs then tape else initTapes y)
              (by simpa [hRead] using hUpd) j
            by_cases hj : j = tRegs
            · subst hj; simpa using hApp
            · simpa [hj] using hApp
          exact ⟨.scanTag, rfl, hNext.symm, inHead, hInMove, rfl, hWork⟩
        · by_cases hj : j = tRegs
          · subst hj; simpa [hNM.head_eq, hPL] using by omega
          · simpa [hj] using hOtherBounds j hj
      rcases ih (pref ++ [(b, bs)]) hPrefNext hSufNext hBoundNext mt hFM with
        ⟨p₁, cur, p₂, hEqRs, hMemCur, hNoP1, ft, hRec, hF⟩ |
        ⟨hNoRs, ft, hRec, hF⟩
      · left
        refine ⟨(b, bs) :: p₁, cur, p₂, by simp [hEqRs], hMemCur, fun r hr => ?_, ft,
          hStepHead.trans hRec, by simpa [List.append_assoc] using hF⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · exact hNoBs
        · exact hNoP1 r hMem
      · right
        refine ⟨fun r hr => ?_, ft, hStepHead.trans hRec, by simpa [List.append_assoc] using hF⟩
        rcases List.mem_cons.mp hr with rfl | hMem
        · exact hNoBs
        · exact hNoRs r hMem

theorem incFirstRegBelowMax_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (W : ℕ) (hW : 1 ≤ W) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W)
    (hBound : 1 + work.length * (W + 2) + (W + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRegs → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes tRegs) (encodeRegsTape work src) 1) :
    (∃ pref cur suf, work = pref ++ cur :: suf ∧ false ∈ cur.2 ∧
      (∀ r ∈ pref, false ∉ r.2) ∧
      ∃ ft, (incFirstRegBelowMax InputAlphabet).ReachesExit input bound initTapes inHead true
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape
          (pref.map (fun _ => (false, natToBits W 1)) ++ (false, incBits cur.2) :: suf) src) 1) ∨
    ((∀ r ∈ work, false ∉ r.2) ∧
      ∃ ft, (incFirstRegBelowMax InputAlphabet).ReachesExit input bound initTapes inHead false
        (fun j => if j = tRegs then ft else initTapes j) inHead ∧
        TapeMatches ft (encodeRegsTape work src) 1) := by
  have hTapesSelf : (fun j => if j = tRegs then initTapes tRegs else initTapes j) = initTapes := by
    funext j; by_cases hj : j = tRegs <;> simp [hj]
  rcases incFirstBody_scan input bound W src hSrc initTapes inHead hOtherBounds work []
      (by simp) hWork (by simpa using hBound) (initTapes tRegs)
      (by simpa [encodeRegsPrefix] using hMatch) with
    ⟨p₁, cur, p₂, hEqW, hCurF, hNoP1, mt, hBody, hMT⟩ |
    ⟨hNoW, mt, hBody, hMT⟩
  · simp only [List.nil_append] at hEqW hMT
    rw [hTapesSelf] at hBody
    have hP1Len : ∀ r ∈ p₁, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
    have hCurLen : cur.2.length = W := hWork cur (by rw [hEqW]; simp)
    have hP2Len : ∀ r ∈ p₂, r.2.length = W := fun r hr => hWork r (by rw [hEqW]; simp [hr])
    have hBoundReset : 1 + (p₁.length + 1 + p₂.length) * (W + 2) + (W + 3) ≤ bound tRegs := by
      have hLenEq : p₁.length + 1 + p₂.length = work.length := by
        rw [hEqW]; simp; omega
      rw [hLenEq]; exact hBound
    obtain ⟨ft, hReset, hFM⟩ := resetLeftRegs_reachesExit input bound W hW p₁
      (false, incBits cur.2) p₂ src hP1Len (by simp [incBits_length, hCurLen]) hP2Len hSrc
      hBoundReset (fun j => if j = tRegs then mt else initTapes j) inHead
      (fun j hj => by simp [hj, hOtherBounds j hj]) hMT
    have hFtEq : (fun j => if j = tRegs then ft else if j = tRegs then mt else initTapes j) =
        (fun j => if j = tRegs then ft else initTapes j) := by
      funext j; by_cases hj : j = tRegs <;> simp [hj]
    rw [hFtEq] at hReset
    left
    refine ⟨p₁, cur, p₂, hEqW, hCurF, hNoP1, ft, ?_, hFM⟩
    exact (incFirstBody InputAlphabet).branch_reachesExit _ _ input bound true hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => true) input bound hReset)
  · simp only [List.nil_append] at hMT
    rw [hTapesSelf] at hBody
    have hWL := encodeRegsPrefix_length W work hWork
    have hWorkLen : (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) :=
      encodeRegsTape_length W work src hWork hSrc
    have hRewBounds : ∀ j, j ≠ tRegs →
        ((fun j => if j = tRegs then mt else initTapes j) j).head < bound j := by
      intro j hj; simpa [hj] using hOtherBounds j hj
    obtain ⟨finalTapes, hRew, hFM, hOth⟩ := rewindTape_reachesExit tRegs input bound
      (encodeRegsTape work src) (by rw [hWorkLen]; omega) (encodeRegsTape_head_leftMark work src)
      (encodeRegsTape_no_other_leftMark work src) (by rw [hWorkLen]; exact hBound)
      (fun j => if j = tRegs then mt else initTapes j) inHead hRewBounds
      (encodeRegsPrefix work).length (by rw [hWL]; omega)
      (by rw [hWorkLen, hWL]; omega) hMT
    have hFinalEq : finalTapes = fun j => if j = tRegs then finalTapes tRegs else initTapes j := by
      funext j; by_cases hj : j = tRegs
      · subst hj; simp
      · rw [hOth j hj]; simp [hj]
    rw [hFinalEq] at hRew
    right
    refine ⟨hNoW, finalTapes tRegs, ?_, hFM⟩
    exact (incFirstBody InputAlphabet).branch_reachesExit _ _ input bound false hBody
      (TMComponent.mapExit_reachesExit _ (fun _ => false) input bound hRew)

theorem false_mem_natToBits_iff_lt {W v : ℕ} (hv : v < 2 ^ W) :
    false ∈ natToBits W v ↔ v < 2 ^ W - 1 := by
  constructor
  · intro hMem
    by_contra hGe
    have hvEq : v = 2 ^ W - 1 := by omega
    subst hvEq
    have hRep : natToBits W (2 ^ W - 1) = List.replicate W true := by
      calc
        natToBits W (2 ^ W - 1)
          = natToBits (List.replicate W true).length (bitsToNat (List.replicate W true)) := by
            simp [bitsToNat_replicate_true]
        _ = List.replicate W true := natToBits_bitsToNat _
    rw [hRep] at hMem
    simp at hMem
  · intro hLt
    by_contra hNo
    have hAllT : ∀ b ∈ natToBits W v, b = true := by
      intro b hb; cases b with
      | false => exact (hNo hb).elim
      | true => rfl
    have hRep : natToBits W v = List.replicate W true := by
      apply List.eq_replicate_iff.mpr
      exact ⟨natToBits_length W v, hAllT⟩
    have hVal : v = 2 ^ W - 1 := by
      calc
        v = bitsToNat (natToBits W v) := (bitsToNat_natToBits_of_lt hv).symm
        _ = bitsToNat (List.replicate W true) := by rw [hRep]
        _ = 2 ^ W - 1 := bitsToNat_replicate_true W
    omega

theorem incBits_natToBits {W v : ℕ} (hLt : v < 2 ^ W - 1) :
    incBits (natToBits W v) = natToBits W (v + 1) := by
  have hv : v < 2 ^ W := by omega
  have hFalse : false ∈ natToBits W v := (false_mem_natToBits_iff_lt hv).mpr hLt
  calc
    incBits (natToBits W v)
      = natToBits (incBits (natToBits W v)).length (bitsToNat (incBits (natToBits W v))) :=
        (natToBits_bitsToNat _).symm
    _ = natToBits W (v + 1) := by
      rw [incBits_length, natToBits_length, bitsToNat_incBits hFalse, bitsToNat_natToBits_of_lt hv]

end SavitchLemma

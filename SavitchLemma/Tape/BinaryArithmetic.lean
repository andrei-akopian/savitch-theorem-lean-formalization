module

public import SavitchLemma.Tape.BasicOperations

@[expose] public section

/-!
# Tape binary arithmetic

Implements decrement on serialized bit tapes and proves its bit-list behavior.
-/

namespace SavitchLemma

/-- Decrement an LSB-first binary number on tape `t` (`[.leftMark] ++ bits ++ [.endMark]`).
Returns `true` if the value was positive (and decrements it by 1); returns `false`
if the value was `0` (leaving it `0`). In both cases tape `t` ends at cell `1`. -/
inductive DecState where
  | scanZero
  | rewindTrue
  | restore
  deriving DecidableEq

def DecState.equivFin : DecState ≃ Fin 3 where
  toFun | .scanZero => 0 | .rewindTrue => 1 | .restore => 2
  invFun | 0 => .scanZero | 1 => .rewindTrue | _ => .restore
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype DecState := Fintype.ofEquiv (Fin 3) DecState.equivFin.symm

def decScratch (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent DecState InputAlphabet SimSym k Bool where
  start := .scanZero
  step s _ scanned :=
    match s with
    | .scanZero =>
      match scanned t with
      | .bit false => singleTapeAction (.inl .scanZero) t (.bit true) .right scanned
      | .bit true => singleTapeAction (.inl .rewindTrue) t (.bit false) .left scanned
      | sym => singleTapeAction (.inl .restore) t sym .left scanned
    | .rewindTrue =>
      match scanned t with
      | .leftMark => singleTapeAction (.inr true) t .leftMark .right scanned
      | sym => singleTapeAction (.inl .rewindTrue) t sym .left scanned
    | .restore =>
      match scanned t with
      | .leftMark => singleTapeAction (.inr false) t .leftMark .right scanned
      | _ => singleTapeAction (.inl .restore) t (.bit false) .left scanned

/-- Decrement an LSB-first bit list by one (all-zeros wraps to all-ones). -/
def decBits : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: decBits bs

theorem decBits_length (bs : List Bool) : (decBits bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [decBits, ih]

theorem bitsToNat_decBits {bs : List Bool} (hHasTrue : true ∈ bs) :
    bitsToNat (decBits bs) + 1 = bitsToNat bs := by
  induction bs with
  | nil => simp at hHasTrue
  | cons b bs ih =>
    cases b
    · rcases List.mem_cons.mp hHasTrue with hEq | hMem
      · cases hEq
      · have ih' := ih hMem
        simp [decBits, bitsToNat]
        have hPos : 1 ≤ bitsToNat bs := by
          have : 0 < bitsToNat bs := by
            by_contra h0
            have hZ : bitsToNat bs = 0 := by omega
            have : ∀ l, bitsToNat l = 0 → true ∉ l := by
              intro l hl
              induction l with
              | nil => simp
              | cons x xs ihx =>
                cases x
                · have hxs : bitsToNat xs = 0 := by simpa [bitsToNat] using hl
                  intro hMem'
                  rcases List.mem_cons.mp hMem' with hEq | hIn
                  · cases hEq
                  · exact ihx hxs hIn
                · simp [bitsToNat] at hl
            exact this bs hZ hMem
          omega
        omega
    · simp [decBits, bitsToNat]
      omega

private theorem decScratch_rewindTrue {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (bits : List Bool) (hBound : bits.length + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j) :
    ∀ pos, pos < bits.length + 2 →
      ∀ tape, TapeMatches tape (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) pos →
      Relation.ReflTransGen
        (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
          (∀ j, (a.workTapes j).head < bound j) ∧
          (∀ j, (b.workTapes j).head < bound j))
        ⟨.inl .rewindTrue, inHead, fun j => if j = t then tape else initTapes j⟩
        ⟨.inr true, inHead, fun j => if j = t then ⟨tape.cells, 1⟩ else initTapes j⟩ := by
  let contents : List SimSym := SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]
  have hLen : contents.length = bits.length + 2 := by simp [contents]
  intro pos
  induction pos with
  | zero =>
    intro hLt tape hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le hLt hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; exact hLt)]
      simp
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch.update_set .leftMark .right hMove (by rw [hLen]; exact hLt)
    have hNextEq : nextTape = ⟨tape.cells, 1⟩ := by
      have hCells : nextTape.cells = tape.cells := by
        funext i
        rw [hNextMatch.2 i, hMatch.2 i]
        by_cases hi : i = 0
        · subst hi; simp
        · simp
      have hHead : nextTape.head = 1 := hNextMatch.head_eq
      cases nextTape
      simp only [OneSidedTape.mk.injEq]
      exact ⟨hCells, hHead⟩
    rw [hNextEq] at hUpd hNextMatch
    exact singleTape_compStep_exit_override (decScratch InputAlphabet t) t input bound
      initTapes tape ⟨tape.cells, 1⟩ .rewindTrue hHeadBounds
      (by simp; omega)
      (by simpa using hUpd)
      (by simp [decScratch, hRead])
  | succ p ih =>
    intro hLt tape hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le hLt hBound
      · simpa [hj] using hOtherBounds j hj
    have hReadNotLeft : tape.cells tape.head ≠ .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; exact hLt)]
      simp only [List.cons_append, List.getElem_cons_succ]
      by_cases hp : p < bits.length
      · rw [List.getElem_append_left (by simp [hp])]
        simp
      · have hpEq : p = bits.length := by omega
        rw [List.getElem_append_right (by simp [hpEq])]
        simp [hpEq]
    have hMove : moveOneSidedHead (p + 1) .left = some p := by simp [moveOneSidedHead]
    obtain ⟨nextTape, hUpd, hNextMatch⟩ := hMatch.update_keep .left hMove
    have hNextCells : nextTape.cells = tape.cells := by
      funext i
      rw [hNextMatch.2 i, hMatch.2 i]
    have hRest := ih (by omega) nextTape hNextMatch
    have hTargetEq : (⟨nextTape.cells, 1⟩ : OneSidedTape SimSym) = ⟨tape.cells, 1⟩ := by
      rw [hNextCells]
    rw [hTargetEq] at hRest
    have hStepEq : (decScratch InputAlphabet t).step .rewindTrue (readInput input inHead)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
        singleTapeAction (Sum.inl DecState.rewindTrue) t
          (tape.cells tape.head) .left
          (fun j => (if j = t then tape else initTapes j).cells
            (if j = t then tape else initTapes j).head) := by
      simp only [decScratch, ↓reduceIte]
    exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape ⟨tape.cells, 1⟩ .rewindTrue .rewindTrue hHeadBounds
      (by rw [hNextMatch.head_eq]; omega) hUpd hRest hStepEq

private theorem decScratch_restore {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (m : ℕ) (hBound : m + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j) :
    ∀ pos, pos ≤ m →
      ∀ tape, TapeMatches tape
        (SimSym.leftMark :: List.replicate pos (SimSym.bit true) ++
          List.replicate (m - pos) (SimSym.bit false) ++ [SimSym.endMark]) pos →
      ∃ finalTape,
        Relation.ReflTransGen
          (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .restore, inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr false, inHead, fun j => if j = t then finalTape else initTapes j⟩ ∧
        TapeMatches finalTape (SimSym.leftMark :: List.replicate m (SimSym.bit false) ++ [SimSym.endMark]) 1 := by
  intro pos
  induction pos with
  | zero =>
    intro _ tape hMatch
    have hLen : (SimSym.leftMark :: List.replicate 0 (SimSym.bit true) ++
        List.replicate (m - 0) (SimSym.bit false) ++ [SimSym.endMark]).length = m + 2 := by simp
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : 0 < m + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .leftMark := by
      rw [hMatch.read_lt (by rw [hLen]; omega)]
      simp
    have hMove : moveOneSidedHead 0 .right = some 1 := rfl
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch.update_set .leftMark .right hMove (by rw [hLen]; omega)
    have hSetEq :
        (SimSym.leftMark :: List.replicate 0 (SimSym.bit true) ++
          List.replicate (m - 0) (SimSym.bit false) ++ [SimSym.endMark]).set 0 .leftMark =
        SimSym.leftMark :: List.replicate m (SimSym.bit false) ++ [SimSym.endMark] := by
      simp
    rw [hSetEq] at hNextMatch
    refine ⟨nextTape, ?_, hNextMatch⟩
    exact singleTape_compStep_exit_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
      hUpd (by simp [decScratch, hRead])
  | succ p ih =>
    intro hpLe tape hMatch
    let pref : List SimSym := SimSym.leftMark :: List.replicate p (SimSym.bit true)
    let suf : List SimSym := List.replicate (m - (p + 1)) (SimSym.bit false) ++ [SimSym.endMark]
    have hPrefLen : pref.length = p + 1 := by simp [pref]
    have hCurEq : SimSym.leftMark :: List.replicate (p + 1) (SimSym.bit true) ++
        List.replicate (m - (p + 1)) (SimSym.bit false) ++ [SimSym.endMark] =
        pref ++ SimSym.bit true :: suf := by
      simp [pref, suf, List.replicate_succ', List.append_assoc]
    have hpLt : p + 1 < (pref ++ SimSym.bit true :: suf).length := by
      rw [← hPrefLen]; simp
    have hMatch' : TapeMatches tape (pref ++ SimSym.bit true :: suf) pref.length := by
      rw [hPrefLen, ← hCurEq]; exact hMatch
    have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; simpa [hMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : p + 1 < m + 2) hBound
      · simpa [hj] using hOtherBounds j hj
    have hRead : tape.cells tape.head = .bit true := by
      rw [hMatch'.read_lt (by simp)]
      exact list_get_append_mid pref (.bit true) suf
    have hMove : moveOneSidedHead (p + 1) .left = some p := by simp [moveOneSidedHead]
    obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
      hMatch'.update_set (.bit false) .left (by rw [hPrefLen]; exact hMove) (by simp)
    rw [list_set_append_mid] at hNextMatch
    have hNextEq : pref ++ SimSym.bit false :: suf =
        SimSym.leftMark :: List.replicate p (SimSym.bit true) ++
          List.replicate (m - p) (SimSym.bit false) ++ [SimSym.endMark] := by
      have hRep : List.replicate (m - p) (SimSym.bit false) =
          SimSym.bit false :: List.replicate (m - (p + 1)) (SimSym.bit false) := by
        rw [show m - p = (m - (p + 1)) + 1 by omega, List.replicate_succ]
      simp [pref, suf, hRep, List.append_assoc]
    rw [hNextEq] at hNextMatch
    obtain ⟨finalTape, hRest, hFinalMatch⟩ := ih (by omega) nextTape hNextMatch
    refine ⟨finalTape, ?_, hFinalMatch⟩
    exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
      initTapes tape nextTape finalTape .restore .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
      hUpd hRest (by simp [decScratch, hRead])

theorem decScratch_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (bits : List Bool) (hBound : bits.length + 2 ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) (SimSym.leftMark :: bits.map SimSym.bit ++ [SimSym.endMark]) 1) :
    ∃ res finalTape bits',
      bits'.length = bits.length ∧
      (decScratch InputAlphabet t).ReachesExit input bound initTapes inHead res
        (fun j => if j = t then finalTape else initTapes j) inHead ∧
      TapeMatches finalTape (SimSym.leftMark :: bits'.map SimSym.bit ++ [SimSym.endMark]) 1 ∧
      (res = true ↔ true ∈ bits) ∧
      (res = true → bitsToNat bits' + 1 = bitsToNat bits) ∧
      (res = false → bits' = bits) := by
  have hScan : ∀ (suf pref : List Bool),
      pref = List.replicate pref.length false →
      pref.length + suf.length = bits.length →
      ∀ tape, TapeMatches tape
        (SimSym.leftMark :: ((List.replicate pref.length true ++ suf).map SimSym.bit) ++ [SimSym.endMark])
        (1 + pref.length) →
      ∃ res finalTape bits',
        bits'.length = bits.length ∧
        Relation.ReflTransGen
          (fun a b => (decScratch InputAlphabet t).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl .scanZero, inHead, fun j => if j = t then tape else initTapes j⟩
          ⟨.inr res, inHead, fun j => if j = t then finalTape else initTapes j⟩ ∧
        TapeMatches finalTape (SimSym.leftMark :: bits'.map SimSym.bit ++ [SimSym.endMark]) 1 ∧
        (res = true ↔ true ∈ pref ++ suf) ∧
        (res = true → bitsToNat bits' + 1 = bitsToNat (pref ++ suf)) ∧
        (res = false → bits' = pref ++ suf) := by
    intro suf
    induction suf with
    | nil =>
      intro pref hPrefFalse hLenSum tape hTapMatch
      have hLenPref : pref.length = bits.length := by simpa using hLenSum
      let prefSyms : List SimSym :=
        SimSym.leftMark :: List.replicate pref.length (SimSym.bit true)
      have hPrefLen : prefSyms.length = 1 + pref.length := by simp [prefSyms]; omega
      have hListEq :
          SimSym.leftMark :: ((List.replicate pref.length true ++ []).map SimSym.bit) ++ [SimSym.endMark] =
          prefSyms ++ SimSym.endMark :: [] := by
        simp [prefSyms, List.map_replicate]
      have hTapMatch' : TapeMatches tape (prefSyms ++ SimSym.endMark :: []) prefSyms.length := by
        rw [hPrefLen, ← hListEq]; exact hTapMatch
      have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
        intro j
        by_cases hj : j = t
        · subst hj; simpa [hTapMatch.head_eq] using Nat.lt_of_lt_of_le (by omega : 1 + pref.length < bits.length + 2) hBound
        · simpa [hj] using hOtherBounds j hj
      have hRead : tape.cells tape.head = .endMark := by
        rw [hTapMatch'.read_lt (by simp)]
        exact list_get_append_mid prefSyms .endMark []
      have hMove : moveOneSidedHead (1 + pref.length) .left = some pref.length := by
        simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hTapMatch.update_keep .left hMove
      have hNextMatch' : TapeMatches nextTape
          (SimSym.leftMark :: List.replicate pref.length (SimSym.bit true) ++
            List.replicate (bits.length - pref.length) (SimSym.bit false) ++ [SimSym.endMark])
          pref.length := by
        simpa [hLenPref, List.map_replicate] using hNextMatch
      obtain ⟨finalTape, hRest, hFinalMatch⟩ :=
        decScratch_restore t input bound bits.length hBound initTapes inHead hOtherBounds
          pref.length (by omega) nextTape hNextMatch'
      refine ⟨false, finalTape, pref, hLenPref, ?_, ?_, ?_, ?_, ?_⟩
      · exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape finalTape .scanZero .restore hHeadBounds (by rw [hNextMatch.head_eq]; omega)
          hUpd hRest (by simp [decScratch, hRead])
      · have hMap : pref.map SimSym.bit = List.replicate bits.length (SimSym.bit false) := by
          conv_lhs => rw [hPrefFalse]
          rw [hLenPref, List.map_replicate]
        rw [hMap]
        exact hFinalMatch
      · have hNotMem : true ∉ pref := by
          conv => rhs; rw [hPrefFalse]
          simp
        simp [hNotMem]
      · intro hBad; cases hBad
      · intro _; simp
    | cons b bs ih =>
      intro pref hPrefFalse hLenSum tape hTapMatch
      let prefSyms : List SimSym :=
        SimSym.leftMark :: List.replicate pref.length (SimSym.bit true)
      let sufSyms : List SimSym := bs.map SimSym.bit ++ [SimSym.endMark]
      have hPrefLen : prefSyms.length = 1 + pref.length := by simp [prefSyms]; omega
      have hListEq :
          SimSym.leftMark :: ((List.replicate pref.length true ++ (b :: bs)).map SimSym.bit) ++ [SimSym.endMark] =
          prefSyms ++ SimSym.bit b :: sufSyms := by
        simp [prefSyms, sufSyms, List.map_replicate, List.append_assoc]
      have hTapMatch' : TapeMatches tape (prefSyms ++ SimSym.bit b :: sufSyms) prefSyms.length := by
        rw [hPrefLen, ← hListEq]; exact hTapMatch
      have hHeadBounds : ∀ j, ((fun j => if j = t then tape else initTapes j) j).head < bound j := by
        intro j
        by_cases hj : j = t
        · subst hj; simpa [hTapMatch.head_eq] using Nat.lt_of_lt_of_le (by simp at hLenSum; omega : 1 + pref.length < bits.length + 2) hBound
        · simpa [hj] using hOtherBounds j hj
      have hRead : tape.cells tape.head = .bit b := by
        rw [hTapMatch'.read_lt (by simp)]
        exact list_get_append_mid prefSyms (.bit b) sufSyms
      cases b with
      | true =>
        let resBits := List.replicate pref.length true ++ false :: bs
        have hResLen : resBits.length = bits.length := by
          simp [resBits]; simp at hLenSum; omega
        have hMove : moveOneSidedHead (1 + pref.length) .left = some pref.length := by
          simp [moveOneSidedHead]
        obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
          hTapMatch'.update_set (.bit false) .left (by rw [hPrefLen]; exact hMove) (by simp)
        rw [list_set_append_mid] at hNextMatch
        have hNextEq : prefSyms ++ SimSym.bit false :: sufSyms =
            SimSym.leftMark :: resBits.map SimSym.bit ++ [SimSym.endMark] := by
          simp [prefSyms, sufSyms, resBits, List.map_replicate, List.append_assoc]
        rw [hNextEq] at hNextMatch
        have hRew := decScratch_rewindTrue t input bound resBits (by rw [hResLen]; exact hBound)
          initTapes inHead hOtherBounds pref.length (by simp at hLenSum; omega) nextTape hNextMatch
        have hFinalMatch : TapeMatches ⟨nextTape.cells, 1⟩
            (SimSym.leftMark :: resBits.map SimSym.bit ++ [SimSym.endMark]) 1 := by
          refine ⟨rfl, fun i => hNextMatch.2 i⟩
        have hStep := singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape ⟨nextTape.cells, 1⟩ .scanZero .rewindTrue hHeadBounds
          (by rw [hNextMatch.head_eq]; simp at hLenSum; omega)
          hUpd hRew (by simp [decScratch, hRead])
        refine ⟨true, ⟨nextTape.cells, 1⟩, resBits, hResLen, hStep, hFinalMatch, ?_, ?_, ?_⟩
        · simp
        · intro _
          have hDecRep : ∀ m (r : List Bool),
              decBits (List.replicate m false ++ true :: r) =
                List.replicate m true ++ false :: r := by
            intro m r
            induction m with
            | zero => simp [decBits]
            | succ m ihm => simp [List.replicate_succ, decBits, ihm]
          have hDecEq : decBits (pref ++ true :: bs) = resBits := by
            calc
              decBits (pref ++ true :: bs)
                = decBits (List.replicate pref.length false ++ true :: bs) := by rw [← hPrefFalse]
              _ = resBits := hDecRep pref.length bs
          rw [← hDecEq]
          exact bitsToNat_decBits (by simp)
        · intro hBad; cases hBad
      | false =>
        have hMove : moveOneSidedHead (1 + pref.length) .right = some (1 + (pref.length + 1)) := by
          simp [moveOneSidedHead]; omega
        obtain ⟨nextTape, hUpd, hNextMatch⟩ :=
          hTapMatch'.update_set (.bit true) .right (by rw [hPrefLen]; exact hMove) (by simp)
        rw [list_set_append_mid] at hNextMatch
        have hNextEq : prefSyms ++ SimSym.bit true :: sufSyms =
            SimSym.leftMark :: ((List.replicate (pref ++ [false]).length true ++ bs).map SimSym.bit) ++
              [SimSym.endMark] := by
          simp [prefSyms, sufSyms, List.replicate_succ', List.map_replicate, List.append_assoc]
        rw [hNextEq] at hNextMatch
        have hPrefNext : pref ++ [false] = List.replicate (pref ++ [false]).length false := by
          conv_lhs => rw [hPrefFalse]
          simp [List.replicate_succ']
        have hNextMatch' : TapeMatches nextTape
            (SimSym.leftMark :: ((List.replicate (pref ++ [false]).length true ++ bs).map SimSym.bit) ++
              [SimSym.endMark])
            (1 + (pref ++ [false]).length) := by
          simpa [Nat.add_assoc] using hNextMatch
        obtain ⟨res, finalTape, resBits, hRLen, hRest, hFM, hResIff, hDec, hKeep⟩ :=
          ih (pref ++ [false]) hPrefNext (by simp; simp at hLenSum; omega) nextTape hNextMatch'
        have hPrefAssoc : (pref ++ [false]) ++ bs = pref ++ false :: bs := by simp
        rw [hPrefAssoc] at hResIff hDec hKeep
        refine ⟨res, finalTape, resBits, hRLen, ?_, hFM, hResIff, hDec, hKeep⟩
        exact singleTape_compStep_head_override (decScratch InputAlphabet t) t input bound
          initTapes tape nextTape finalTape .scanZero .scanZero hHeadBounds
          (by rw [hNextMatch.head_eq]; simp at hLenSum; omega)
          hUpd hRest (by simp [decScratch, hRead])
  rcases hScan bits [] rfl (by simp) (initTapes t) (by simpa using hMatch) with
    ⟨res, finalTape, bits', hLen', hRun', hFM', hResIff, hDec, hKeep⟩
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j
    by_cases hj : j = t <;> simp [hj]
  rw [hTapesSelf] at hRun'
  exact ⟨res, finalTape, bits', hLen', hRun', hFM',
    by simpa using hResIff, by simpa using hDec, by simpa using hKeep⟩

end SavitchLemma

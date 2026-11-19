module

public import SavitchLemma.Simulator.SavitchDriver
public import SavitchLemma.Model.SpaceAnalysis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Iterative deepening for non-measurable space bounds

When `L : ℕ → ℕ` satisfies `1 ≤ L n` and `n ≤ 2 ^ L n` without being space-measurable,
Savitch's deterministic simulator tries capacities `S = 1, 2, 3, ...` in order:
1. Initialize `tRuler` to `.leftMark :: [.bit true, .endMark]` (`S = 1`) and the other
   four tapes to `[.leftMark]`.
2. Check whether `n ≤ 2 ^ S` using an `S`-bit binary counter on `tScratch` bounded by
   `tRuler`, then clear `tScratch` and rewind `inputHead` to `0`.
3. If `n ≤ 2 ^ S`, run `savitchSimulator M`. If it returns `true`, accept; otherwise
   rewind `inputHead`, clear `tRegs`, extend `tRuler` from `1^S` to `1^(S+1)`, and
   continue to `S + 1`.
4. If `n > 2 ^ S`, extend `tRuler` from `1^S` to `1^(S+1)` and continue to `S + 1`.
-/

namespace SavitchLemma

/-! ### Clean-tape invariant -/

/-- All 5 simulator tapes and the input head are in clean initial configuration for
capacity `S`: `tRuler` holds `1^S ++ [.endMark]`, the other 4 tapes hold `[.leftMark]`,
all work heads are at `1`, and `inputHead` is at `0`. -/
def CleanTapesFor {n : ℕ} (S : ℕ) (tapes : Fin 5 → OneSidedTape SimSym)
    (inHead : Fin (n + 2)) : Prop :=
  inHead.val = 0 ∧
  TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
  TapeMatches (tapes tRegs) [.leftMark] 1 ∧
  TapeMatches (tapes tArgA) [.leftMark] 1 ∧
  TapeMatches (tapes tArgB) [.leftMark] 1 ∧
  TapeMatches (tapes tScratch) [.leftMark] 1

/-! ### Tape-0 initialization (`idInit`) -/

def idInit (InputAlphabet : Type*) :
    TMComponent (Fin 3) InputAlphabet SimSym 5 Unit where
  start := 0
  step s _ scanned :=
    if s.val = 0 then
      { nextState := .inl 1
        inputMove := .stay
        write := fun _ => .leftMark
        workMove := fun _ => .right }
    else if s.val = 1 then
      { nextState := .inl 2
        inputMove := .stay
        write := fun t => if t = tRuler then .bit true else scanned t
        workMove := fun t => if t = tRuler then .right else .stay }
    else
      { nextState := .inr ()
        inputMove := .stay
        write := fun t => if t = tRuler then .endMark else scanned t
        workMove := fun t => if t = tRuler then .left else .stay }

theorem idInit_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (hBR : 3 ≤ bound tRuler) (hBOth : ∀ t, t ≠ tRuler → 2 ≤ bound t) :
    ∃ finalTapes,
      (idInit InputAlphabet).ReachesExit input bound
        (fun _ => ⟨fun _ => .blank, 0⟩) ⟨0, by omega⟩ () finalTapes ⟨0, by omega⟩ ∧
      CleanTapesFor (n := n) 1 finalTapes ⟨0, by omega⟩ := by
  let t0 : Fin 5 → OneSidedTape SimSym := fun _ => ⟨fun _ => .blank, 0⟩
  let t1 : Fin 5 → OneSidedTape SimSym := fun _ =>
    ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩
  let t2 : Fin 5 → OneSidedTape SimSym := fun j =>
    if j = tRuler then
      ⟨fun i => if i = 1 then .bit true else if i = 0 then .leftMark else .blank, 2⟩
    else t1 j
  let t3 : Fin 5 → OneSidedTape SimSym := fun j =>
    if j = tRuler then
      ⟨fun i => if i = 2 then .endMark else if i = 1 then .bit true else
        if i = 0 then .leftMark else .blank, 1⟩
    else t1 j
  have hB0 : ∀ t, (t0 t).head < bound t := fun t => by
    by_cases ht : t = tRuler
    · subst ht; simp [t0]; omega
    · simp [t0]; have := hBOth t ht; omega
  have hB1 : ∀ t, (t1 t).head < bound t := fun t => by
    by_cases ht : t = tRuler
    · subst ht; simp [t1]; omega
    · simp [t1]; have := hBOth t ht; omega
  have hB2 : ∀ t, (t2 t).head < bound t := fun t => by
    by_cases ht : t = tRuler
    · subst ht; simp [t2]; omega
    · simp [t2, t1, ht]; have := hBOth t ht; omega
  have hB3 : ∀ t, (t3 t).head < bound t := fun t => by
    by_cases ht : t = tRuler
    · subst ht; simp [t3]; omega
    · simp [t3, t1, ht]; have := hBOth t ht; omega
  have hs0 := TMComponent.step_one (idInit InputAlphabet) input bound 0
    ⟨0, by omega⟩ ⟨0, by omega⟩ t0 t1 (.inl 1) rfl (by simp [moveHead, idInit])
    (fun t => by
      simp only [t0, t1, OneSidedTape.updateAndMove, moveOneSidedHead, idInit]
      rfl)
    hB0 hB1
  have hs1 := TMComponent.step_one (idInit InputAlphabet) input bound 1
    ⟨0, by omega⟩ ⟨0, by omega⟩ t1 t2 (.inl 2) rfl (by simp [moveHead, idInit])
    (fun t => by
      by_cases ht : t = tRuler
      · subst ht
        simp [t1, t2, OneSidedTape.updateAndMove, moveOneSidedHead, idInit]
      · dsimp only [t1, t2, idInit]
        simp [ht]
        exact OneSidedTape.updateAndMove_stay_self _)
    hB1 hB2
  have hs2 := TMComponent.step_one (idInit InputAlphabet) input bound 2
    ⟨0, by omega⟩ ⟨0, by omega⟩ t2 t3 (.inr ()) rfl (by simp [moveHead, idInit])
    (fun t => by
      by_cases ht : t = tRuler
      · subst ht
        simp [t2, t3, OneSidedTape.updateAndMove, moveOneSidedHead, idInit]
      · dsimp only [t2, t3, idInit]
        simp [ht]
        exact OneSidedTape.updateAndMove_stay_self _)
    hB2 hB3
  refine ⟨t3, (hs0.trans hs1).trans hs2, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [t3], fun i => ?_⟩
    simp only [t3, ↓reduceIte]
    rcases i with _ | _ | _ | i <;> simp
  · refine ⟨by simp [t3, t1, tRegs, tRuler], fun i => ?_⟩
    simp only [t3, t1, show tRegs ≠ tRuler by decide, ↓reduceIte]
    rcases i with _ | i <;> simp
  · refine ⟨by simp [t3, t1, tArgA, tRuler], fun i => ?_⟩
    simp only [t3, t1, show tArgA ≠ tRuler by decide, ↓reduceIte]
    rcases i with _ | i <;> simp
  · refine ⟨by simp [t3, t1, tArgB, tRuler], fun i => ?_⟩
    simp only [t3, t1, show tArgB ≠ tRuler by decide, ↓reduceIte]
    rcases i with _ | i <;> simp
  · refine ⟨by simp [t3, t1, tScratch, tRuler], fun i => ?_⟩
    simp only [t3, t1, show tScratch ≠ tRuler by decide, ↓reduceIte]
    rcases i with _ | i <;> simp

/-! ### Input head rewinding (`rewindInputHead`) -/

def rewindInputHead (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ inSym scanned :=
    match inSym with
    | .leftEnd => { nextState := .inr (), inputMove := .stay, write := scanned, workMove := fun _ => .stay }
    | .symbol _ => { nextState := .inl (), inputMove := .left, write := scanned, workMove := fun _ => .stay }
    | .rightEnd => { nextState := .inl (), inputMove := .left, write := scanned, workMove := fun _ => .stay }

theorem rewindInputHead_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (tapes : Fin 5 → OneSidedTape SimSym) (hBounds : ∀ t, (tapes t).head < bound t)
    (inHead : Fin (n + 2)) :
    (rewindInputHead InputAlphabet).ReachesExit input bound tapes inHead () tapes ⟨0, by omega⟩ := by
  rcases inHead with ⟨hv, hlt⟩
  induction hv with
  | zero =>
    exact TMComponent.step_one (rewindInputHead InputAlphabet) input bound ()
      ⟨0, hlt⟩ ⟨0, by omega⟩ tapes tapes (.inr ())
      (by simp [rewindInputHead, readInput]) (by simp [rewindInputHead, readInput, moveHead])
      (fun t => by simp [rewindInputHead, readInput, OneSidedTape.updateAndMove_stay_self])
      hBounds hBounds
  | succ k ih =>
    have hNot0 : k + 1 ≠ 0 := by omega
    have hMv : moveHead (n + 2) ⟨k + 1, hlt⟩ .left = some ⟨k, by omega⟩ := by
      simp [moveHead]
    have hStep : Relation.ReflTransGen
        (fun a b => (rewindInputHead InputAlphabet).CompStep input a b ∧
          (∀ t, (a.workTapes t).head < bound t) ∧
          (∀ t, (b.workTapes t).head < bound t))
        ⟨.inl (), ⟨k + 1, hlt⟩, tapes⟩ ⟨.inl (), ⟨k, by omega⟩, tapes⟩ := by
      by_cases hLe : k + 1 ≤ n
      · have hRead : readInput input ⟨k + 1, hlt⟩ = .symbol (input ⟨k, by omega⟩) := by
          simp [readInput, show k ≠ n by omega]
        exact TMComponent.step_one (rewindInputHead InputAlphabet) input bound ()
          ⟨k + 1, hlt⟩ ⟨k, by omega⟩ tapes tapes (.inl ())
          (by simp [rewindInputHead, hRead]) (by simp [rewindInputHead, hRead, hMv])
          (fun t => by simp [rewindInputHead, hRead, OneSidedTape.updateAndMove_stay_self])
          hBounds hBounds
      · have hEq : k + 1 = n + 1 := by omega
        have hRead : readInput input ⟨k + 1, hlt⟩ = .rightEnd := by
          simp [readInput, hEq]
        exact TMComponent.step_one (rewindInputHead InputAlphabet) input bound ()
          ⟨k + 1, hlt⟩ ⟨k, by omega⟩ tapes tapes (.inl ())
          (by simp [rewindInputHead, hRead]) (by simp [rewindInputHead, hRead, hMv])
          (fun t => by simp [rewindInputHead, hRead, OneSidedTape.updateAndMove_stay_self])
          hBounds hBounds
    exact hStep.trans (ih (by omega))

/-! ### Ruler extension (`extendRuler`: `1^S → 1^(S+1)`) -/

def extendRulerBody (InputAlphabet : Type*) :
    TMComponent (Fin 2) InputAlphabet SimSym 5 Unit where
  start := 0
  step s _ scanned :=
    if s.val = 0 then
      match scanned tRuler with
      | .bit true =>
        { nextState := .inl 0
          inputMove := .stay
          write := scanned
          workMove := fun t => if t = tRuler then .right else .stay }
      | .endMark =>
        { nextState := .inl 1
          inputMove := .stay
          write := fun t => if t = tRuler then .bit true else scanned t
          workMove := fun t => if t = tRuler then .right else .stay }
      | _ => mkWorkAction (.inr ()) scanned (fun _ => .stay)
    else
      { nextState := .inr ()
        inputMove := .stay
        write := fun t => if t = tRuler then .endMark else scanned t
        workMove := fun t => if t = tRuler then .left else .stay }

def extendRuler (InputAlphabet : Type*) :=
  (extendRulerBody InputAlphabet).seq (rewindTape InputAlphabet tRuler)

theorem extendRuler_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ)
    (hBR : S + 3 ≤ bound tRuler)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBOth : ∀ j, j ≠ tRuler → (tapes j).head < bound j)
    (hMR : TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1) :
    ∃ ftR,
      (extendRuler InputAlphabet).ReachesExit input bound tapes inHead ()
        (fun j => if j = tRuler then ftR else tapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate (S + 1) (.bit true) ++ [.endMark]) 1 := by
  let contents := SimSym.leftMark :: List.replicate S (.bit true) ++ [.endMark]
  have hLen : contents.length = S + 2 := by simp [contents]
  have hScan : ∀ p, 1 ≤ p → p ≤ S + 1 →
      ∀ tp : OneSidedTape SimSym, TapeMatches tp contents p →
      ∃ ft,
        (extendRulerBody InputAlphabet).ReachesExit input bound
          (fun j => if j = tRuler then tp else tapes j) inHead ()
          (fun j => if j = tRuler then ft else tapes j) inHead ∧
        TapeMatches ft (.leftMark :: List.replicate (S + 1) (.bit true) ++ [.endMark]) (S + 1) := by
    intro p hp1 hp2
    obtain ⟨k, hk⟩ : ∃ k, p + k = S + 1 := ⟨S + 1 - p, by omega⟩
    induction k generalizing p with
    | zero =>
      intro tp hTP
      have hpEq : p = S + 1 := by omega
      subst hpEq
      have hRead : tp.cells tp.head = .endMark := by
        rw [hTP.read_lt (by omega)]
        simp [contents, List.getElem_append_right]
      obtain ⟨tp1, hUp1, hMatch1⟩ := hTP.update_set (.bit true) .right
        (by simp [moveOneSidedHead]; rfl) (by omega)
      have hSet1 : contents.set (S + 1) (.bit true) =
          .leftMark :: List.replicate (S + 1) (.bit true) := by
        have hEq : contents = (.leftMark :: List.replicate S (.bit true)) ++ .endMark :: [] := rfl
        rw [hEq]
        have hLenEq : (.leftMark :: List.replicate S (SimSym.bit true)).length = S + 1 := by simp
        rw [← hLenEq, list_set_append_mid]
        simp [List.replicate_succ']
      rw [hSet1] at hMatch1
      have hLen1 : (.leftMark :: List.replicate (S + 1) (SimSym.bit true)).length = S + 1 + 1 := by
        simp
      obtain ⟨tp2, hUp2, hMatch2⟩ := TapeMatches.update_append_left
        (hLen1 ▸ hMatch1) (by simp [hLen1]) .endMark
      rw [hLen1] at hMatch2
      have hBtp : ∀ t, ((fun j => if j = tRuler then tp else tapes j) t).head < bound t := fun t => by
        by_cases ht : t = tRuler
        · subst ht; simp [hTP.head_eq]; omega
        · simp [ht, hBOth t ht]
      have hBtp1 : ∀ t, ((fun j => if j = tRuler then tp1 else tapes j) t).head < bound t := fun t => by
        by_cases ht : t = tRuler
        · subst ht; simp [hMatch1.head_eq]; omega
        · simp [ht, hBOth t ht]
      have hBtp2 : ∀ t, ((fun j => if j = tRuler then tp2 else tapes j) t).head < bound t := fun t => by
        by_cases ht : t = tRuler
        · subst ht; simp [hMatch2.head_eq]; omega
        · simp [ht, hBOth t ht]
      have hs1 := TMComponent.step_one (extendRulerBody InputAlphabet) input bound 0
        inHead inHead (fun j => if j = tRuler then tp else tapes j)
        (fun j => if j = tRuler then tp1 else tapes j) (.inl 1)
        (by simp [extendRulerBody, hRead]) (by simp [extendRulerBody, hRead, moveHead])
        (fun t => by
          by_cases ht : t = tRuler
          · subst ht; simpa [extendRulerBody, hRead] using hUp1
          · simp [extendRulerBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
        hBtp hBtp1
      have hs2 := TMComponent.step_one (extendRulerBody InputAlphabet) input bound 1
        inHead inHead (fun j => if j = tRuler then tp1 else tapes j)
        (fun j => if j = tRuler then tp2 else tapes j) (.inr ())
        rfl (by simp [extendRulerBody, moveHead])
        (fun t => by
          by_cases ht : t = tRuler
          · subst ht; simpa [extendRulerBody] using hUp2
          · simp [extendRulerBody, ht, OneSidedTape.updateAndMove_stay_self])
        hBtp1 hBtp2
      exact ⟨tp2, hs1.trans hs2, by simpa using hMatch2⟩
    | succ m ih =>
      intro tp hTP
      have hpLt : p < S + 1 := by omega
      have hRead : tp.cells tp.head = .bit true := by
        rw [hTP.read_lt (by omega)]
        rcases p with _ | q
        · omega
        · simp only [contents, List.cons_append, List.getElem_cons_succ]
          rw [List.getElem_append_left (by simp; omega)]
          simp
      obtain ⟨tp1, hUp1, hMatch1⟩ := hTP.update_keep .right (by simp [moveOneSidedHead]; rfl)
      have hBtp : ∀ t, ((fun j => if j = tRuler then tp else tapes j) t).head < bound t := fun t => by
        by_cases ht : t = tRuler
        · subst ht; simp [hTP.head_eq]; omega
        · simp [ht, hBOth t ht]
      have hBtp1 : ∀ t, ((fun j => if j = tRuler then tp1 else tapes j) t).head < bound t := fun t => by
        by_cases ht : t = tRuler
        · subst ht; simp [hMatch1.head_eq]; omega
        · simp [ht, hBOth t ht]
      have hs1 := TMComponent.step_one (extendRulerBody InputAlphabet) input bound 0
        inHead inHead (fun j => if j = tRuler then tp else tapes j)
        (fun j => if j = tRuler then tp1 else tapes j) (.inl 0)
        (by simp [extendRulerBody, hRead]) (by simp [extendRulerBody, hRead, moveHead])
        (fun t => by
          by_cases ht : t = tRuler
          · subst ht; simpa [extendRulerBody, hRead] using hUp1
          · simp [extendRulerBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
        hBtp hBtp1
      obtain ⟨ft, hRest, hMatchRest⟩ := ih (p + 1) (by omega) (by omega) (by omega) tp1 hMatch1
      exact ⟨ft, hs1.trans hRest, hMatchRest⟩
  obtain ⟨ft1, hBody, hMatch1⟩ := hScan 1 (by omega) (by omega) (tapes tRuler)
    (by simpa [contents] using hMR)
  have hTapesSelf : (fun j => if j = tRuler then tapes tRuler else tapes j) = tapes := by
    funext j; split_ifs with h <;> simp [h]
  rw [hTapesSelf] at hBody
  let nextContents : List SimSym := .leftMark :: List.replicate (S + 1) (.bit true) ++ [.endMark]
  have hRew := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler input bound
    nextContents (by simp [nextContents]) (by simp [nextContents])
    (fun i hi1 _ hEq => by
      rcases i with _ | j
      · omega
      · simp only [nextContents, List.cons_append, List.getElem?_cons_succ] at hEq
        have hMem := List.mem_of_getElem? hEq
        simp at hMem)
    (by simp [nextContents]; omega)
    (fun j => if j = tRuler then ft1 else tapes j) inHead
    (fun j hj => by simp [hj, hBOth j hj])
    (S + 1) (by omega) (by simp [nextContents]) (by simpa [nextContents] using hMatch1)
  obtain ⟨ftMap, hRewRun, hRewMatch, hRewOth⟩ := hRew
  refine ⟨ftMap tRuler, ?_, hRewMatch⟩
  have hMapEq : (fun j => if j = tRuler then ftMap tRuler else tapes j) = ftMap := by
    funext j
    by_cases hj : j = tRuler
    · subst hj; rfl
    · rw [hRewOth j hj]; simp [hj]
  rw [hMapEq]
  exact TMComponent.seq_reachesExit _ _ input bound hBody hRewRun


end SavitchLemma

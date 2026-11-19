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

/-! ### General component combinator helpers -/

private theorem component_step_one {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (C : TMComponent Q InputAlphabet Γ k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (q : Q) (inHead nextInHead : Fin (n + 2))
    (tapes nextTapes : Fin k → OneSidedTape Γ)
    (nextState : Q ⊕ Exit)
    (hNextState : (C.step q (readInput input inHead)
      (fun t => (tapes t).cells (tapes t).head)).nextState = nextState)
    (hIn : moveHead (n + 2) inHead
      (C.step q (readInput input inHead)
        (fun t => (tapes t).cells (tapes t).head)).inputMove = some nextInHead)
    (hTapes : ∀ t, (tapes t).updateAndMove
      ((C.step q (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).write t)
      ((C.step q (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).workMove t) =
      some (nextTapes t))
    (hBounds : ∀ t, (tapes t).head < bound t)
    (hNextBounds : ∀ t, (nextTapes t).head < bound t) :
    Relation.ReflTransGen
      (fun a b => C.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, inHead, tapes⟩ ⟨nextState, nextInHead, nextTapes⟩ :=
  Relation.ReflTransGen.single ⟨⟨q, rfl, hNextState.symm, nextInHead, hIn, rfl, hTapes⟩, hBounds, hNextBounds⟩

private theorem reachesExit_mono {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    {C : TMComponent Q InputAlphabet Γ k Exit} {input : Fin n → InputAlphabet}
    {bound bound' : Fin k → ℕ} (hB : ∀ t, bound t ≤ bound' t)
    {initTapes finalTapes : Fin k → OneSidedTape Γ} {inHead finalInHead : Fin (n + 2)}
    {e : Exit}
    (hR : C.ReachesExit input bound initTapes inHead e finalTapes finalInHead) :
    C.ReachesExit input bound' initTapes inHead e finalTapes finalInHead := by
  have key : ∀ cfg,
      Relation.ReflTransGen
        (fun a b => C.CompStep input a b ∧
          (∀ t, (a.workTapes t).head < bound t) ∧
          (∀ t, (b.workTapes t).head < bound t))
        ⟨.inl C.start, inHead, initTapes⟩ cfg →
      Relation.ReflTransGen
        (fun a b => C.CompStep input a b ∧
          (∀ t, (a.workTapes t).head < bound' t) ∧
          (∀ t, (b.workTapes t).head < bound' t))
        ⟨.inl C.start, inHead, initTapes⟩ cfg := by
    intro cfg h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h ih =>
      exact ih.tail ⟨h.1, fun t => lt_of_lt_of_le (h.2.1 t) (hB t),
        fun t => lt_of_lt_of_le (h.2.2 t) (hB t)⟩
  exact key _ hR

private theorem tapeMatches_append_left {tape : OneSidedTape SimSym} {contents : List SimSym}
    (h : TapeMatches tape contents contents.length) (hPos : 1 ≤ contents.length) (sym : SimSym) :
    ∃ nextTape, tape.updateAndMove sym .left = some nextTape ∧
      TapeMatches nextTape (contents ++ [sym]) (contents.length - 1) := by
  have hMove : moveOneSidedHead tape.head .left = some (contents.length - 1) := by
    simp [moveOneSidedHead, h.1, show contents.length ≠ 0 by omega]
  refine ⟨⟨fun i => if i = tape.head then sym else tape.cells i, contents.length - 1⟩,
    ?_, rfl, ?_⟩
  · simp [OneSidedTape.updateAndMove, hMove]
  · intro i
    dsimp only
    rw [h.1]
    by_cases hi : i = contents.length
    · subst hi; simp
    · simp only [hi, ↓reduceIte]
      rw [h.2 i]
      by_cases hLt : i < contents.length
      · rw [List.getElem?_append_left hLt]
      · have hGt : contents.length < i := by omega
        have hNone1 : contents[i]? = none := List.getElem?_eq_none (by omega)
        have hNone2 : (contents ++ [sym])[i]? = none := by
          apply List.getElem?_eq_none; simp; omega
        rw [hNone1, hNone2]

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
  have hs0 := component_step_one (idInit InputAlphabet) input bound 0
    ⟨0, by omega⟩ ⟨0, by omega⟩ t0 t1 (.inl 1) rfl (by simp [moveHead, idInit])
    (fun t => by
      simp only [t0, t1, OneSidedTape.updateAndMove, moveOneSidedHead, idInit]
      rfl)
    hB0 hB1
  have hs1 := component_step_one (idInit InputAlphabet) input bound 1
    ⟨0, by omega⟩ ⟨0, by omega⟩ t1 t2 (.inl 2) rfl (by simp [moveHead, idInit])
    (fun t => by
      by_cases ht : t = tRuler
      · subst ht
        simp [t1, t2, OneSidedTape.updateAndMove, moveOneSidedHead, idInit]
      · dsimp only [t1, t2, idInit]
        simp [ht]
        exact OneSidedTape.updateAndMove_stay_self _)
    hB1 hB2
  have hs2 := component_step_one (idInit InputAlphabet) input bound 2
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
    exact component_step_one (rewindInputHead InputAlphabet) input bound ()
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
        exact component_step_one (rewindInputHead InputAlphabet) input bound ()
          ⟨k + 1, hlt⟩ ⟨k, by omega⟩ tapes tapes (.inl ())
          (by simp [rewindInputHead, hRead]) (by simp [rewindInputHead, hRead, hMv])
          (fun t => by simp [rewindInputHead, hRead, OneSidedTape.updateAndMove_stay_self])
          hBounds hBounds
      · have hEq : k + 1 = n + 1 := by omega
        have hRead : readInput input ⟨k + 1, hlt⟩ = .rightEnd := by
          simp [readInput, hEq]
        exact component_step_one (rewindInputHead InputAlphabet) input bound ()
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
      obtain ⟨tp2, hUp2, hMatch2⟩ := tapeMatches_append_left
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
      have hs1 := component_step_one (extendRulerBody InputAlphabet) input bound 0
        inHead inHead (fun j => if j = tRuler then tp else tapes j)
        (fun j => if j = tRuler then tp1 else tapes j) (.inl 1)
        (by simp [extendRulerBody, hRead]) (by simp [extendRulerBody, hRead, moveHead])
        (fun t => by
          by_cases ht : t = tRuler
          · subst ht; simpa [extendRulerBody, hRead] using hUp1
          · simp [extendRulerBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
        hBtp hBtp1
      have hs2 := component_step_one (extendRulerBody InputAlphabet) input bound 1
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
      have hs1 := component_step_one (extendRulerBody InputAlphabet) input bound 0
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

/-! ### Binary counter input-length check (`checkInputLenComp`: `n ≤ 2 ^ S`) -/

/-- Little-endian binary value of a bit list (`LSB` first). -/
def fromBitsLE : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * fromBitsLE bs

private theorem fromBitsLE_replicate_false (S : ℕ) :
    fromBitsLE (List.replicate S false) = 0 := by
  induction S with
  | zero => rfl
  | succ S ih => simp [List.replicate_succ, fromBitsLE, ih]

private theorem fromBitsLE_lt_two_pow (bs : List Bool) :
    fromBitsLE bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [fromBitsLE]
  | cons b bs ih =>
    simp only [fromBitsLE, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

private theorem fromBitsLE_replicate_true (S : ℕ) :
    fromBitsLE (List.replicate S true) = 2 ^ S - 1 := by
  induction S with
  | zero => rfl
  | succ S ih =>
    simp only [List.replicate_succ, fromBitsLE, ih, pow_succ', ↓reduceIte]
    have : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    omega

private theorem fromBitsLE_split_inc (p : ℕ) (suf : List Bool) :
    fromBitsLE (List.replicate p false ++ true :: suf) =
      fromBitsLE (List.replicate p true ++ false :: suf) + 1 := by
  induction p with
  | zero => simp [fromBitsLE]; omega
  | succ p ih =>
    simp [List.replicate_succ, fromBitsLE, ih]; omega

private theorem bits_split_of_lt (bs : List Bool) (hLt : fromBitsLE bs < 2 ^ bs.length - 1) :
    ∃ p suf, bs = List.replicate p true ++ false :: suf := by
  induction bs with
  | nil => simp [fromBitsLE] at hLt
  | cons b bs ih =>
    cases b
    · exact ⟨0, bs, rfl⟩
    · simp only [fromBitsLE, List.length_cons, pow_succ', ↓reduceIte] at hLt
      have hSub : fromBitsLE bs < 2 ^ bs.length - 1 := by
        have := Nat.one_le_two_pow (n := bs.length)
        omega
      obtain ⟨p, suf, hEq⟩ := ih hSub
      exact ⟨p + 1, suf, by simp [List.replicate_succ, hEq]⟩

private theorem bits_eq_replicate_true (bs : List Bool) (hEq : fromBitsLE bs = 2 ^ bs.length - 1) :
    bs = List.replicate bs.length true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [fromBitsLE, List.length_cons, pow_succ'] at hEq
    have hLt := fromBitsLE_lt_two_pow bs
    have h1 : 1 ≤ 2 ^ bs.length := Nat.one_le_two_pow
    cases b
    · simp at hEq; omega
    · simp only [↓reduceIte] at hEq
      have hSub : fromBitsLE bs = 2 ^ bs.length - 1 := by omega
      simp only [List.length_cons, List.replicate_succ]
      rw [← ih hSub]

/-! #### Step 1: initialize `S`-bit zero counter on `tScratch` -/

def initZeroBody (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    match scanned tRuler with
    | .bit true =>
      { nextState := .inl ()
        inputMove := .stay
        write := fun t => if t = tScratch then .bit false else scanned t
        workMove := fun t => if t = tRuler ∨ t = tScratch then .right else .stay }
    | .endMark =>
      { nextState := .inr ()
        inputMove := .stay
        write := fun t => if t = tScratch then .endMark else scanned t
        workMove := fun t => if t = tRuler ∨ t = tScratch then .left else .stay }
    | _ => mkWorkAction (.inr ()) scanned (fun _ => .stay)

def initZeroCounter (InputAlphabet : Type*) :=
  (initZeroBody InputAlphabet).seq
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch))

theorem initZeroCounter_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hBR : S + 2 ≤ bound tRuler) (hBS : S + 2 ≤ bound tScratch)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBOth : ∀ j, j ≠ tRuler → j ≠ tScratch → (tapes j).head < bound j)
    (hMR : TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMS : TapeMatches (tapes tScratch) [.leftMark] 1) :
    ∃ ftR ftS,
      (initZeroCounter InputAlphabet).ReachesExit input bound tapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tScratch then ftS else tapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftS (.leftMark :: List.replicate S (.bit false) ++ [.endMark]) 1 := by
  let rCont : List SimSym := .leftMark :: List.replicate S (.bit true) ++ [.endMark]
  have hRLen : rCont.length = S + 2 := by simp [rCont]
  have hBody : ∀ p, 1 ≤ p → p ≤ S + 1 →
      ∀ tpR tpS : OneSidedTape SimSym,
      TapeMatches tpR rCont p →
      TapeMatches tpS (.leftMark :: List.replicate (p - 1) (.bit false)) p →
      ∃ ftR ftS,
        (initZeroBody InputAlphabet).ReachesExit input bound
          (fun j => if j = tRuler then tpR else if j = tScratch then tpS else tapes j) inHead ()
          (fun j => if j = tRuler then ftR else if j = tScratch then ftS else tapes j) inHead ∧
        TapeMatches ftR rCont S ∧
        TapeMatches ftS (.leftMark :: List.replicate S (.bit false) ++ [.endMark]) S := by
    intro p hp1 hp2
    obtain ⟨k, hk⟩ : ∃ k, p + k = S + 1 := ⟨S + 1 - p, by omega⟩
    induction k generalizing p with
    | zero =>
      intro tpR tpS hTPR hTPS
      have hpEq : p = S + 1 := by omega
      subst hpEq
      have hReadR : tpR.cells tpR.head = .endMark := by
        rw [hTPR.read_lt (by omega)]; simp [rCont, List.getElem_append_right]
      obtain ⟨ftR, hUpR, hMatchR⟩ := hTPR.update_keep .left (by simp [moveOneSidedHead]; rfl)
      have hTPS' : TapeMatches tpS (.leftMark :: List.replicate S (SimSym.bit false)) (S + 1) := by
        simpa using hTPS
      have hLenS : (.leftMark :: List.replicate S (SimSym.bit false)).length = S + 1 := by simp
      obtain ⟨ftS, hUpS, hMatchS⟩ := tapeMatches_append_left
        (hLenS.symm ▸ hTPS') (by simp [hLenS]) .endMark
      rw [hLenS] at hMatchS
      have hB0 : ∀ t, ((fun j => if j = tRuler then tpR else if j = tScratch then tpS else tapes j) t).head < bound t :=
        fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simp [hTPR.head_eq]; omega
          · by_cases h2 : t = tScratch
            · subst h2; simp [h1, hTPS.head_eq]; omega
            · simp [h1, h2, hBOth t h1 h2]
      have hB1 : ∀ t, ((fun j => if j = tRuler then ftR else if j = tScratch then ftS else tapes j) t).head < bound t :=
        fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simp [hMatchR.head_eq]; omega
          · by_cases h2 : t = tScratch
            · subst h2; simp [h1, hMatchS.head_eq]; omega
            · simp [h1, h2, hBOth t h1 h2]
      refine ⟨ftR, ftS, component_step_one (initZeroBody InputAlphabet) input bound ()
        inHead inHead _ _ (.inr ()) (by simp [initZeroBody, hReadR]) (by simp [initZeroBody, hReadR, moveHead])
        (fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simpa [initZeroBody, hReadR, show tRuler ≠ tScratch by decide] using hUpR
          · by_cases h2 : t = tScratch
            · subst h2; simpa [initZeroBody, hReadR, h1] using hUpS
            · simp [initZeroBody, hReadR, h1, h2, OneSidedTape.updateAndMove_stay_self])
        hB0 hB1, by simpa using hMatchR, by simpa using hMatchS⟩
    | succ m ih =>
      intro tpR tpS hTPR hTPS
      have hpLt : p < S + 1 := by omega
      have hReadR : tpR.cells tpR.head = .bit true := by
        rw [hTPR.read_lt (by omega)]
        rcases p with _ | q
        · omega
        · simp only [rCont, List.cons_append, List.getElem_cons_succ]
          rw [List.getElem_append_left (by simp; omega)]
          simp
      obtain ⟨tpR1, hUpR, hMatchR1⟩ := hTPR.update_keep .right (by simp [moveOneSidedHead]; rfl)
      have hLenS : (SimSym.leftMark :: List.replicate (p - 1) (SimSym.bit false)).length = p := by
        simp; omega
      have hTPS' : TapeMatches tpS (SimSym.leftMark :: List.replicate (p - 1) (SimSym.bit false))
          (SimSym.leftMark :: List.replicate (p - 1) (SimSym.bit false)).length := by
        simpa [hLenS] using hTPS
      obtain ⟨tpS1, hUpS, hMatchS1⟩ := hTPS'.update_append (.bit false)
      rw [hLenS] at hMatchS1
      have hS1Eq : (SimSym.leftMark :: List.replicate (p - 1) (SimSym.bit false) ++ [.bit false]) =
          SimSym.leftMark :: List.replicate p (.bit false) := by
        have hp' : p - 1 + 1 = p := by omega
        rw [← hp', List.replicate_succ']
        simp
      rw [hS1Eq] at hMatchS1
      have hB0 : ∀ t, ((fun j => if j = tRuler then tpR else if j = tScratch then tpS else tapes j) t).head < bound t :=
        fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simp [hTPR.head_eq]; omega
          · by_cases h2 : t = tScratch
            · subst h2; simp [h1, hTPS.head_eq]; omega
            · simp [h1, h2, hBOth t h1 h2]
      have hB1 : ∀ t, ((fun j => if j = tRuler then tpR1 else if j = tScratch then tpS1 else tapes j) t).head < bound t :=
        fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simp [hMatchR1.head_eq]; omega
          · by_cases h2 : t = tScratch
            · subst h2; simp [h1, hMatchS1.head_eq]; omega
            · simp [h1, h2, hBOth t h1 h2]
      have hStep := component_step_one (initZeroBody InputAlphabet) input bound ()
        inHead inHead _ _ (.inl ()) (by simp [initZeroBody, hReadR]) (by simp [initZeroBody, hReadR, moveHead])
        (fun t => by
          by_cases h1 : t = tRuler
          · subst h1; simpa [initZeroBody, hReadR, show tRuler ≠ tScratch by decide] using hUpR
          · by_cases h2 : t = tScratch
            · subst h2; simpa [initZeroBody, hReadR, h1] using hUpS
            · simp [initZeroBody, hReadR, h1, h2, OneSidedTape.updateAndMove_stay_self])
        hB0 hB1
      obtain ⟨ftR, ftS, hRest, hMR', hMS'⟩ :=
        ih (p + 1) (by omega) (by omega) (by omega) tpR1 tpS1 hMatchR1 (by simpa using hMatchS1)
      exact ⟨ftR, ftS, hStep.trans hRest, hMR', hMS'⟩
  obtain ⟨ftR1, ftS1, hRun1, hMR1, hMS1⟩ := hBody 1 (by omega) (by omega) (tapes tRuler) (tapes tScratch)
    hMR (by simpa using hMS)
  have hTapes0 : (fun j => if j = tRuler then tapes tRuler else if j = tScratch then tapes tScratch else tapes j) = tapes := by
    funext j; split_ifs <;> simp_all
  rw [hTapes0] at hRun1
  let sCont : List SimSym := .leftMark :: List.replicate S (.bit false) ++ [.endMark]
  obtain ⟨tRewR, hRewR, hMatchRR, hOthR⟩ := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tRuler
    input bound rCont (by simp [rCont]) (by simp [rCont])
    (fun i hi1 _ hEq => by
      rcases i with _ | j; · omega
      simp only [rCont, List.cons_append, List.getElem?_cons_succ] at hEq
      have hMem := List.mem_of_getElem? hEq
      simp at hMem)
    (by simp [rCont]; omega)
    (fun j => if j = tRuler then ftR1 else if j = tScratch then ftS1 else tapes j) inHead
    (fun j hj => by
      by_cases hjS : j = tScratch
      · subst hjS; simp [hj, hMS1.head_eq]; omega
      · simp [hj, hjS, hBOth j hj hjS])
    S hS (by simp [rCont]; omega) (by simpa [rCont] using hMR1)
  obtain ⟨tRewS, hRewS, hMatchRS, hOthS⟩ := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tScratch
    input bound sCont (by simp [sCont]) (by simp [sCont])
    (fun i hi1 _ hEq => by
      rcases i with _ | j; · omega
      simp only [sCont, List.cons_append, List.getElem?_cons_succ] at hEq
      have hMem := List.mem_of_getElem? hEq
      simp at hMem)
    (by simp [sCont]; omega)
    tRewR inHead
    (fun j hj => by
      by_cases hjR : j = tRuler
      · subst hjR; simp [hMatchRR.head_eq]; omega
      · rw [hOthR j hjR]; simp [hjR, hj, hBOth j hjR hj])
    S hS (by simp [sCont]; omega)
    (by
      rw [hOthR tScratch (by decide)]
      simpa [sCont, show tScratch ≠ tRuler by decide] using hMS1)
  refine ⟨tRewR tRuler, tRewS tScratch, ?_, ?_, hMatchRS⟩
  · have hEqFinal : tRewS =
        (fun j => if j = tRuler then tRewR tRuler else if j = tScratch then tRewS tScratch else tapes j) := by
      funext j
      by_cases hjR : j = tRuler
      · subst hjR; rw [hOthS tRuler (by decide)]; simp
      · by_cases hjS : j = tScratch
        · subst hjS; simp [hjR]
        · rw [hOthS j hjS, hOthR j hjR]; simp [hjR, hjS]
    have hSeq := TMComponent.seq_reachesExit _ _ input bound hRun1
      (TMComponent.seq_reachesExit _ _ input bound hRewR hRewS)
    rw [hEqFinal] at hSeq
    exact hSeq
  · simpa [rCont] using hMatchRR

/-! #### Step 2: increment `S`-bit counter on `tScratch` -/

def incCounterBody (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool where
  start := ()
  step _ _ scanned :=
    match scanned tScratch with
    | .bit true =>
      { nextState := .inl ()
        inputMove := .stay
        write := fun t => if t = tScratch then .bit false else scanned t
        workMove := fun t => if t = tScratch then .right else .stay }
    | .bit false =>
      { nextState := .inr true
        inputMove := .stay
        write := fun t => if t = tScratch then .bit true else scanned t
        workMove := fun t => if t = tScratch then .stay else .stay }
    | _ => mkWorkAction (.inr false) scanned (fun _ => .stay)

def incCounter (InputAlphabet : Type*) :=
  (incCounterBody InputAlphabet).branch
    ((rewindTape InputAlphabet tScratch).mapExit fun _ => true)
    ((rewindTape InputAlphabet tScratch).mapExit fun _ => false)

theorem incCounter_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hBS : S + 2 ≤ bound tScratch)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBOth : ∀ j, j ≠ tScratch → (tapes j).head < bound j)
    (bs : List Bool) (hLen : bs.length = S)
    (hMS : TapeMatches (tapes tScratch) (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1) :
    ∃ (ok : Bool) (ftS : OneSidedTape SimSym) (bs' : List Bool),
      bs'.length = S ∧
      (incCounter InputAlphabet).ReachesExit input bound tapes inHead ok
        (fun j => if j = tScratch then ftS else tapes j) inHead ∧
      TapeMatches ftS (.leftMark :: bs'.map SimSym.bit ++ [.endMark]) 1 ∧
      (if fromBitsLE bs < 2 ^ S - 1 then ok = true ∧ fromBitsLE bs' = fromBitsLE bs + 1
       else ok = false ∧ bs' = List.replicate S false) := by
  by_cases hLt : fromBitsLE bs < 2 ^ S - 1
  · obtain ⟨p, suf, hSplit⟩ := bits_split_of_lt bs (by rw [hLen]; exact hLt)
    have hpLt : p < S := by
      have := congrArg List.length hSplit
      simp [hLen] at this; omega
    let bs' := List.replicate p false ++ true :: suf
    have hBs'Len : bs'.length = S := by
      have := congrArg List.length hSplit
      simp [bs', hLen] at this ⊢; omega
    have hVal : fromBitsLE bs' = fromBitsLE bs + 1 := by
      rw [hSplit]; exact fromBitsLE_split_inc p suf
    let target := SimSym.leftMark :: bs'.map SimSym.bit ++ [.endMark]
    have hWalk : ∀ i, i ≤ p →
        ∀ tpS : OneSidedTape SimSym,
        TapeMatches tpS (.leftMark :: List.replicate i (.bit false) ++
          List.replicate (p - i) (.bit true) ++ .bit false :: suf.map SimSym.bit ++ [.endMark]) (1 + i) →
        ∃ ftS,
          (incCounterBody InputAlphabet).ReachesExit input bound
            (fun j => if j = tScratch then tpS else tapes j) inHead true
            (fun j => if j = tScratch then ftS else tapes j) inHead ∧
          TapeMatches ftS target (1 + p) := by
      intro i hi
      obtain ⟨d, hd⟩ : ∃ d, i + d = p := ⟨p - i, by omega⟩
      induction d generalizing i with
      | zero =>
        intro tpS hTPS
        have hiEq : i = p := by omega
        subst hiEq
        have hContEq : (.leftMark :: List.replicate i (.bit false) ++
            List.replicate (i - i) (.bit true) ++ .bit false :: suf.map SimSym.bit ++ [.endMark]) =
            (.leftMark :: List.replicate i (.bit false)) ++ .bit false :: (suf.map SimSym.bit ++ [.endMark]) := by
          simp
        rw [hContEq] at hTPS
        have hRead : tpS.cells tpS.head = .bit false := by
          rw [hTPS.read_lt (by simp; omega)]
          rw [List.getElem_append_right]
          · simp [Nat.add_comm 1 i]
          · simp; omega
        obtain ⟨ftS, hUp, hMatch⟩ := hTPS.update_set (.bit true) .stay
          (by simp [moveOneSidedHead]; rfl) (by simp; omega)
        have hSetEq : ((SimSym.leftMark :: List.replicate i (SimSym.bit false)) ++ SimSym.bit false ::
            (suf.map SimSym.bit ++ [SimSym.endMark])).set (1 + i) (SimSym.bit true) = target := by
          have hLen1 : (SimSym.leftMark :: List.replicate i (SimSym.bit false)).length = 1 + i := by simp; omega
          rw [← hLen1, list_set_append_mid]
          simp [target, bs']
        rw [hSetEq] at hMatch
        have hB0 : ∀ t, ((fun j => if j = tScratch then tpS else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hTPS.head_eq]; omega
          · simp [ht, hBOth t ht]
        have hB1 : ∀ t, ((fun j => if j = tScratch then ftS else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hMatch.head_eq]; omega
          · simp [ht, hBOth t ht]
        exact ⟨ftS, component_step_one (incCounterBody InputAlphabet) input bound ()
          inHead inHead _ _ (.inr true) (by simp [incCounterBody, hRead]) (by simp [incCounterBody, hRead, moveHead])
          (fun t => by
            by_cases ht : t = tScratch
            · subst ht; simpa [incCounterBody, hRead] using hUp
            · simp [incCounterBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
          hB0 hB1, hMatch⟩
      | succ d ih =>
        intro tpS hTPS
        have hiLt : i < p := by omega
        have hSub : p - i = (p - (i + 1)) + 1 := by omega
        have hContEq : (.leftMark :: List.replicate i (.bit false) ++
            List.replicate (p - i) (.bit true) ++ .bit false :: suf.map SimSym.bit ++ [.endMark]) =
            (.leftMark :: List.replicate i (.bit false)) ++ .bit true ::
              (List.replicate (p - (i + 1)) (.bit true) ++ .bit false :: suf.map SimSym.bit ++ [.endMark]) := by
          rw [hSub, List.replicate_succ]; simp [List.append_assoc]
        rw [hContEq] at hTPS
        have hRead : tpS.cells tpS.head = .bit true := by
          rw [hTPS.read_lt (by simp; omega)]
          rw [List.getElem_append_right]
          · simp [Nat.add_comm 1 i]
          · simp; omega
        obtain ⟨tpS1, hUp, hMatch1⟩ := hTPS.update_set (.bit false) .right
          (by simp [moveOneSidedHead]; rfl) (by simp; omega)
        have hSetEq : ((SimSym.leftMark :: List.replicate i (SimSym.bit false)) ++ SimSym.bit true ::
            (List.replicate (p - (i + 1)) (SimSym.bit true) ++ SimSym.bit false :: suf.map SimSym.bit ++
              [SimSym.endMark])).set
            (1 + i) (SimSym.bit false) =
            SimSym.leftMark :: List.replicate (i + 1) (SimSym.bit false) ++
              List.replicate (p - (i + 1)) (SimSym.bit true) ++ SimSym.bit false :: suf.map SimSym.bit ++
              [SimSym.endMark] := by
          have hLen1 : (SimSym.leftMark :: List.replicate i (SimSym.bit false)).length = 1 + i := by simp; omega
          rw [← hLen1, list_set_append_mid]
          simp [List.replicate_succ', List.append_assoc]
        rw [hSetEq] at hMatch1
        have hB0 : ∀ t, ((fun j => if j = tScratch then tpS else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hTPS.head_eq]; omega
          · simp [ht, hBOth t ht]
        have hB1 : ∀ t, ((fun j => if j = tScratch then tpS1 else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hMatch1.head_eq]; omega
          · simp [ht, hBOth t ht]
        have hStep := component_step_one (incCounterBody InputAlphabet) input bound ()
          inHead inHead _ _ (.inl ()) (by simp [incCounterBody, hRead]) (by simp [incCounterBody, hRead, moveHead])
          (fun t => by
            by_cases ht : t = tScratch
            · subst ht; simpa [incCounterBody, hRead] using hUp
            · simp [incCounterBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
          hB0 hB1
        obtain ⟨ftS, hRest, hMatchRest⟩ := ih (i + 1) (by omega) (by omega) tpS1 hMatch1
        exact ⟨ftS, hStep.trans hRest, hMatchRest⟩
    have hInitEq : (.leftMark :: bs.map SimSym.bit ++ [.endMark]) =
        .leftMark :: List.replicate 0 (.bit false) ++ List.replicate (p - 0) (.bit true) ++
          .bit false :: suf.map SimSym.bit ++ [.endMark] := by
      rw [hSplit]; simp [List.append_assoc]
    obtain ⟨ft1, hBody, hMatch1⟩ := hWalk 0 (by omega) (tapes tScratch) (by rw [← hInitEq]; exact hMS)
    have hTapesSelf : (fun j => if j = tScratch then tapes tScratch else tapes j) = tapes := by
      funext j; split_ifs with h <;> simp [h]
    rw [hTapesSelf] at hBody
    obtain ⟨ftMap, hRew, hMatchRew, hOth⟩ := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tScratch
      input bound target (by simp [target]) (by simp [target])
      (fun j hj1 _ hEq => by
        rcases j with _ | m; · omega
        simp only [target, List.cons_append, List.getElem?_cons_succ] at hEq
        have hMem := List.mem_of_getElem? hEq
        simp [bs'] at hMem)
      (by simp [target, hBs'Len]; omega)
      (fun j => if j = tScratch then ft1 else tapes j) inHead
      (fun j hj => by simp [hj, hBOth j hj])
      (1 + p) (by omega) (by simp [target, hBs'Len]; omega) hMatch1
    have hMapEq : (fun j => if j = tScratch then ftMap tScratch else tapes j) = ftMap := by
      funext j
      by_cases hj : j = tScratch
      · subst hj; rfl
      · have := hOth j hj; simpa [hj] using this.symm
    refine ⟨true, ftMap tScratch, bs', hBs'Len, ?_, hMatchRew, by simp [hLt, hVal]⟩
    rw [hMapEq]
    exact TMComponent.branch_reachesExit _ _ _ input bound true hBody
      (TMComponent.mapExit_reachesExit _ _ input bound hRew)
  · have hEqMax : fromBitsLE bs = 2 ^ S - 1 := by
      have := fromBitsLE_lt_two_pow bs
      rw [hLen] at this
      omega
    have hRep : bs = List.replicate S true := by
      have := bits_eq_replicate_true bs (by rw [hLen]; exact hEqMax)
      simpa [hLen] using this
    let bs' := List.replicate S false
    let target := SimSym.leftMark :: bs'.map SimSym.bit ++ [.endMark]
    have hWalk : ∀ i, i ≤ S →
        ∀ tpS : OneSidedTape SimSym,
        TapeMatches tpS (.leftMark :: List.replicate i (.bit false) ++
          List.replicate (S - i) (.bit true) ++ [.endMark]) (1 + i) →
        ∃ ftS,
          (incCounterBody InputAlphabet).ReachesExit input bound
            (fun j => if j = tScratch then tpS else tapes j) inHead false
            (fun j => if j = tScratch then ftS else tapes j) inHead ∧
          TapeMatches ftS target (1 + S) := by
      intro i hi
      obtain ⟨d, hd⟩ : ∃ d, i + d = S := ⟨S - i, by omega⟩
      induction d generalizing i with
      | zero =>
        intro tpS hTPS
        have hiEq : i = S := by omega
        have hContEq : (.leftMark :: List.replicate i (.bit false) ++
            List.replicate (S - i) (.bit true) ++ [.endMark]) = target := by
          rw [hiEq]; simp [target, bs']
        have hTPS' : TapeMatches tpS target (1 + S) := by
          simpa [target, bs', List.map_replicate, hiEq] using hTPS
        have hRead : tpS.cells tpS.head = .endMark := by
          rw [hTPS'.read_lt (by simp [target, bs']; omega)]
          simp only [target, bs', List.map_replicate]
          rw [List.getElem_append_right]
          · simp
          · simp; omega
        have hB0 : ∀ t, ((fun j => if j = tScratch then tpS else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hTPS'.head_eq]; omega
          · simp [ht, hBOth t ht]
        exact ⟨tpS, component_step_one (incCounterBody InputAlphabet) input bound ()
          inHead inHead _ _ (.inr false) (by simp [incCounterBody, hRead, mkWorkAction])
          (by simp [incCounterBody, hRead, mkWorkAction, moveHead])
          (fun t => by simp [incCounterBody, hRead, mkWorkAction, OneSidedTape.updateAndMove_stay_self]) hB0 hB0, hTPS'⟩
      | succ d ih =>
        intro tpS hTPS
        have hiLt : i < S := by omega
        have hSub : S - i = (S - (i + 1)) + 1 := by omega
        have hContEq : (SimSym.leftMark :: List.replicate i (.bit false) ++
            List.replicate (S - i) (.bit true) ++ [.endMark]) =
            (SimSym.leftMark :: List.replicate i (.bit false)) ++ .bit true ::
              (List.replicate (S - (i + 1)) (.bit true) ++ [.endMark]) := by
          rw [hSub, List.replicate_succ]; simp [List.append_assoc]
        rw [hContEq] at hTPS
        have hRead : tpS.cells tpS.head = .bit true := by
          rw [hTPS.read_lt (by simp; omega)]
          rw [List.getElem_append_right]
          · simp [Nat.add_comm 1 i]
          · simp; omega
        obtain ⟨tpS1, hUp, hMatch1⟩ := hTPS.update_set (.bit false) .right
          (by simp [moveOneSidedHead]; rfl) (by simp; omega)
        have hSetEq : ((SimSym.leftMark :: List.replicate i (SimSym.bit false)) ++ SimSym.bit true ::
            (List.replicate (S - (i + 1)) (SimSym.bit true) ++ [SimSym.endMark])).set
            (1 + i) (SimSym.bit false) =
            SimSym.leftMark :: List.replicate (i + 1) (SimSym.bit false) ++
              List.replicate (S - (i + 1)) (SimSym.bit true) ++ [SimSym.endMark] := by
          have hLen1 : (SimSym.leftMark :: List.replicate i (SimSym.bit false)).length = 1 + i := by simp; omega
          rw [← hLen1, list_set_append_mid]
          simp [List.replicate_succ', List.append_assoc]
        rw [hSetEq] at hMatch1
        have hB0 : ∀ t, ((fun j => if j = tScratch then tpS else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hTPS.head_eq]; omega
          · simp [ht, hBOth t ht]
        have hB1 : ∀ t, ((fun j => if j = tScratch then tpS1 else tapes j) t).head < bound t := fun t => by
          by_cases ht : t = tScratch
          · subst ht; simp [hMatch1.head_eq]; omega
          · simp [ht, hBOth t ht]
        have hStep := component_step_one (incCounterBody InputAlphabet) input bound ()
          inHead inHead _ _ (.inl ()) (by simp [incCounterBody, hRead]) (by simp [incCounterBody, hRead, moveHead])
          (fun t => by
            by_cases ht : t = tScratch
            · subst ht; simpa [incCounterBody, hRead] using hUp
            · simp [incCounterBody, hRead, ht, OneSidedTape.updateAndMove_stay_self])
          hB0 hB1
        obtain ⟨ftS, hRest, hMatchRest⟩ := ih (i + 1) (by omega) (by omega) tpS1 hMatch1
        exact ⟨ftS, hStep.trans hRest, hMatchRest⟩
    have hInitEq : (.leftMark :: bs.map SimSym.bit ++ [.endMark]) =
        .leftMark :: List.replicate 0 (.bit false) ++ List.replicate (S - 0) (.bit true) ++ [.endMark] := by
      rw [hRep]; simp
    obtain ⟨ft1, hBody, hMatch1⟩ := hWalk 0 (by omega) (tapes tScratch) (by rw [← hInitEq]; exact hMS)
    have hTapesSelf : (fun j => if j = tScratch then tapes tScratch else tapes j) = tapes := by
      funext j; split_ifs with h <;> simp [h]
    rw [hTapesSelf] at hBody
    obtain ⟨ftMap, hRew, hMatchRew, hOth⟩ := rewindTape_reachesExit (InputAlphabet := InputAlphabet) tScratch
      input bound target (by simp [target]) (by simp [target])
      (fun j hj1 _ hEq => by
        rcases j with _ | m; · omega
        simp only [target, List.cons_append, List.getElem?_cons_succ] at hEq
        have hMem := List.mem_of_getElem? hEq
        simp [bs'] at hMem)
      (by simp [target, bs']; omega)
      (fun j => if j = tScratch then ft1 else tapes j) inHead
      (fun j hj => by simp [hj, hBOth j hj])
      (1 + S) (by omega) (by simp [target, bs']; omega) hMatch1
    have hMapEq : (fun j => if j = tScratch then ftMap tScratch else tapes j) = ftMap := by
      funext j
      by_cases hj : j = tScratch
      · subst hj; rfl
      · have := hOth j hj; simpa [hj] using this.symm
    refine ⟨false, ftMap tScratch, bs', by simp [bs'], ?_, hMatchRew, by simp [hLt, bs']⟩
    rw [hMapEq]
    exact TMComponent.branch_reachesExit _ _ _ input bound false hBody
      (TMComponent.mapExit_reachesExit _ _ input bound hRew)

/-! #### Step 3: full `checkInputLenComp` -/

def isInputSym {InputAlphabet : Type*} : InputSymbol InputAlphabet → Bool
  | .symbol _ => true
  | _ => false

def checkInputLoopBody (InputAlphabet : Type*) :=
  (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
    mkWorkAction (isInputSym inSym) scanned (fun _ => .stay)).branch
    ((incCounter InputAlphabet).branch
      (TMComponent.atom fun _ scanned =>
        { nextState := (.inl () : Unit ⊕ Bool), inputMove := .right, write := scanned, workMove := fun _ => .stay })
      (TMComponent.atom fun _ scanned => mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay)))
    (TMComponent.atom fun _ scanned => mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay))

def skipFirstAndLoop (InputAlphabet : Type*) :=
  (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
    { nextState := (), inputMove := .right, write := scanned, workMove := fun _ => .stay }).seq
    ((TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      { nextState := isInputSym inSym
        inputMove := if isInputSym inSym then .right else .stay
        write := scanned
        workMove := fun _ => .stay }).branch
      (checkInputLoopBody InputAlphabet).loop
      (TMComponent.atom fun _ scanned => mkWorkAction true scanned (fun _ => .stay)))

def checkInputLenComp (InputAlphabet : Type*) :=
  (initZeroCounter InputAlphabet).seq
    ((skipFirstAndLoop InputAlphabet).branch
      (((rewindInputHead InputAlphabet).seq (clearTape InputAlphabet tScratch)).mapExit fun _ => true)
      (((rewindInputHead InputAlphabet).seq (clearTape InputAlphabet tScratch)).mapExit fun _ => false))

theorem checkInputLenComp_reachesExit {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hBR : S + 2 ≤ bound tRuler) (hBS : S + 2 ≤ bound tScratch)
    (tapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hInHead : inHead.val = 0)
    (hBOth : ∀ j, j ≠ tRuler → j ≠ tScratch → (tapes j).head < bound j)
    (hMR : TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMS : TapeMatches (tapes tScratch) [.leftMark] 1) :
    ∃ ftR ftS,
      (checkInputLenComp InputAlphabet).ReachesExit input bound tapes inHead
        (decide (n ≤ 2 ^ S))
        (fun j => if j = tRuler then ftR else if j = tScratch then ftS else tapes j)
        ⟨0, by omega⟩ ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftS [.leftMark] 1 := by
  have hInEq : inHead = ⟨0, by omega⟩ := Fin.ext hInHead
  rw [hInEq]
  obtain ⟨ftR0, ftS0, hInit0, hMR0, hMS0⟩ :=
    initZeroCounter_reachesExit input bound S hS hBR hBS tapes ⟨0, by omega⟩ hBOth hMR hMS
  let t1 := fun j => if j = tRuler then ftR0 else if j = tScratch then ftS0 else tapes j
  have hT1Bounds : ∀ j, (t1 j).head < bound j := fun j => by
    by_cases h1 : j = tRuler
    · subst h1; simp [t1, hMR0.head_eq]; omega
    · by_cases h2 : j = tScratch
      · subst h2; simp [t1, h1, hMS0.head_eq]; omega
      · simp [t1, h1, h2, hBOth j h1 h2]
  have hStep0 : (TMComponent.atom fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
      { nextState := (), inputMove := .right, write := scanned, workMove := fun _ => .stay }).ReachesExit
      input bound t1 ⟨0, by omega⟩ () t1 ⟨1, by omega⟩ :=
    TMComponent.atom_reachesExit _ input bound t1 ⟨0, by omega⟩ hT1Bounds ⟨1, by omega⟩
      (by simp [moveHead]) t1 (fun j => OneSidedTape.updateAndMove_stay_self _) hT1Bounds
  have hLoopMain : ∃ (ok : Bool) (finalInHead : Fin (n + 2)) (ftS1 : OneSidedTape SimSym) (bs' : List Bool),
      bs'.length = S ∧
      (skipFirstAndLoop InputAlphabet).ReachesExit input bound t1 ⟨0, by omega⟩ ok
        (fun j => if j = tScratch then ftS1 else t1 j) finalInHead ∧
      TapeMatches ftS1 (.leftMark :: bs'.map SimSym.bit ++ [.endMark]) 1 ∧
      ok = decide (n ≤ 2 ^ S) := by
    by_cases hn0 : n = 0
    · subst hn0
      have hStep1 : (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          { nextState := isInputSym inSym
            inputMove := if isInputSym inSym then .right else .stay
            write := scanned
            workMove := fun _ => .stay }).ReachesExit
          input bound t1 ⟨1, by omega⟩ false t1 ⟨1, by omega⟩ := by
        have hAt := TMComponent.atom_reachesExit
          (fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            { nextState := isInputSym inSym
              inputMove := if isInputSym inSym then .right else .stay
              write := scanned
              workMove := fun _ => .stay })
          input bound t1 ⟨1, by omega⟩ hT1Bounds ⟨1, by omega⟩
          (by simp [readInput, isInputSym, moveHead]) t1
          (fun j => OneSidedTape.updateAndMove_stay_self _) hT1Bounds
        simpa [readInput, isInputSym] using hAt
      have hAtomT : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
          mkWorkAction true scanned (fun _ => .stay)).ReachesExit
          input bound t1 ⟨1, by omega⟩ true t1 ⟨1, by omega⟩ :=
        TMComponent.atom_reachesExit _ input bound t1 ⟨1, by omega⟩ hT1Bounds ⟨1, by omega⟩
          (by simp [mkWorkAction, moveHead]) t1 (fun j => OneSidedTape.updateAndMove_stay_self _) hT1Bounds
      have hT1Self : (fun j => if j = tScratch then ftS0 else t1 j) = t1 := by
        funext j; split_ifs with h <;> simp [h, t1, show tScratch ≠ tRuler by decide]
      refine ⟨true, ⟨1, by omega⟩, ftS0, List.replicate S false, by simp, ?_, ?_, ?_⟩
      · rw [hT1Self]
        exact TMComponent.seq_reachesExit _ _ input bound hStep0
          (TMComponent.branch_reachesExit _ _ _ input bound false hStep1 hAtomT)
      · simpa [t1, List.map_replicate, show tScratch ≠ tRuler by decide] using hMS0
      · simp
    · have hnPos : 1 ≤ n := by omega
      have hStep1 : (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          { nextState := isInputSym inSym
            inputMove := if isInputSym inSym then .right else .stay
            write := scanned
            workMove := fun _ => .stay }).ReachesExit
          input bound t1 ⟨1, by omega⟩ true t1 ⟨2, by omega⟩ := by
        have hAt := TMComponent.atom_reachesExit
          (fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
            { nextState := isInputSym inSym
              inputMove := if isInputSym inSym then .right else .stay
              write := scanned
              workMove := fun _ => .stay })
          input bound t1 ⟨1, by omega⟩ hT1Bounds ⟨2, by omega⟩
          (by simp [readInput, hn0, isInputSym, moveHead]; omega) t1
          (fun j => OneSidedTape.updateAndMove_stay_self _) hT1Bounds
        simpa [readInput, hn0, isInputSym] using hAt
      let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tp ih =>
        ∃ (i : ℕ) (hi : i ≤ n - 1), i ≤ 2 ^ S - 1 ∧ ih = ⟨2 + i, by omega⟩ ∧
        ∃ bs : List Bool, bs.length = S ∧ fromBitsLE bs = i ∧
          TapeMatches (tp tScratch) (.leftMark :: bs.map SimSym.bit ++ [.endMark]) 1 ∧
          (∀ j, j ≠ tScratch → tp j = t1 j)
      let meas : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → ℕ := fun _ ih => n + 1 - ih.val
      let Post : Bool → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun ok tp _ =>
        ∃ bs' : List Bool, bs'.length = S ∧
          TapeMatches (tp tScratch) (.leftMark :: bs'.map SimSym.bit ++ [.endMark]) 1 ∧
          (∀ j, j ≠ tScratch → tp j = t1 j) ∧
          ok = decide (n ≤ 2 ^ S)
      have hLoopRes := TMComponent.loop_reachesExit (checkInputLoopBody InputAlphabet) input bound
        Inv meas Post
        (fun tp ih ⟨i, hi, hiBound, hihEq, bs, hbsLen, hVal, hTpS, hTpOth⟩ => by
          rw [hihEq] at *
          have hBcur : ∀ t, (tp t).head < bound t := fun t => by
            by_cases ht : t = tScratch
            · subst ht; simp [hTpS.head_eq]; omega
            · rw [hTpOth t ht]; exact hT1Bounds t
          by_cases hiEnd : i = n - 1
          · subst hiEnd
            have hIdxEq : 2 + (n - 1) = n + 1 := by omega
            have hCheck : (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                mkWorkAction (isInputSym inSym) scanned (fun _ => .stay)).ReachesExit
                input bound tp ⟨2 + (n - 1), by omega⟩ false tp ⟨2 + (n - 1), by omega⟩ := by
              simpa [readInput, hIdxEq, isInputSym, mkWorkAction] using TMComponent.atom_reachesExit _ input bound tp
                ⟨2 + (n - 1), by omega⟩ hBcur ⟨2 + (n - 1), by omega⟩ (by simp [moveHead]) tp
                (fun j => OneSidedTape.updateAndMove_stay_self _) hBcur
            have hAtomDone : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
                mkWorkAction (.inr true : Unit ⊕ Bool) scanned (fun _ => .stay)).ReachesExit
                input bound tp ⟨2 + (n - 1), by omega⟩ (.inr true) tp ⟨2 + (n - 1), by omega⟩ :=
              TMComponent.atom_reachesExit _ input bound tp ⟨2 + (n - 1), by omega⟩
                hBcur ⟨2 + (n - 1), by omega⟩ (by simp [mkWorkAction, moveHead]) tp
                (fun j => OneSidedTape.updateAndMove_stay_self _) hBcur
            exact Or.inr ⟨true, tp, ⟨2 + (n - 1), by omega⟩,
              TMComponent.branch_reachesExit _ _ _ input bound false hCheck hAtomDone,
              bs, hbsLen, hTpS, hTpOth, by have := Nat.one_le_two_pow (n := S); simp; omega⟩
          · have hiLt : i < n - 1 := by omega
            have hIdxLt : 2 + i < n + 1 := by omega
            have hCheck : (TMComponent.atom fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                mkWorkAction (isInputSym inSym) scanned (fun _ => .stay)).ReachesExit
                input bound tp ⟨2 + i, by omega⟩ true tp ⟨2 + i, by omega⟩ := by
              simpa [readInput, show 2 + i ≠ 0 by omega, show 2 + i ≠ n + 1 by omega,
                isInputSym, mkWorkAction] using
                TMComponent.atom_reachesExit
                  (fun (inSym : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
                    mkWorkAction (isInputSym inSym) scanned (fun _ => .stay))
                  input bound tp ⟨2 + i, by omega⟩ hBcur ⟨2 + i, by omega⟩
                  (by simp [mkWorkAction, moveHead]) tp
                  (fun j => OneSidedTape.updateAndMove_stay_self _) hBcur
            obtain ⟨ok, ftS', bs', hbs'Len, hInc, hMS', hIncVal⟩ :=
              incCounter_reachesExit input bound S hS hBS tp ⟨2 + i, by omega⟩
                (fun j hj => by rw [hTpOth j hj]; exact hT1Bounds j) bs hbsLen hTpS
            let tp' := fun j => if j = tScratch then ftS' else tp j
            have hBnext : ∀ t, (tp' t).head < bound t := fun t => by
              by_cases ht : t = tScratch
              · subst ht; simp [tp', hMS'.head_eq]; omega
              · simp [tp', ht, hTpOth t ht, hT1Bounds t]
            by_cases hiMax : i < 2 ^ S - 1
            · rw [hVal] at hIncVal
              simp only [hiMax, ↓reduceIte] at hIncVal
              rcases hIncVal with ⟨rfl, hVal'⟩
              have hMvNext : moveHead (n + 2) ⟨2 + i, by omega⟩ .right = some ⟨2 + (i + 1), by omega⟩ := by
                simp [moveHead, hIdxLt]; omega
              have hAtomCont : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
                  { nextState := (.inl () : Unit ⊕ Bool), inputMove := .right, write := scanned, workMove := fun _ => .stay }).ReachesExit
                  input bound tp' ⟨2 + i, by omega⟩ (.inl ()) tp' ⟨2 + (i + 1), by omega⟩ :=
                TMComponent.atom_reachesExit _ input bound tp' ⟨2 + i, by omega⟩
                  hBnext ⟨2 + (i + 1), by omega⟩ hMvNext tp'
                  (fun j => OneSidedTape.updateAndMove_stay_self _) hBnext
              refine Or.inl ⟨tp', ⟨2 + (i + 1), by omega⟩,
                TMComponent.branch_reachesExit _ _ _ input bound true hCheck
                  (TMComponent.branch_reachesExit _ _ _ input bound true hInc hAtomCont),
                ⟨i + 1, by omega, by omega, rfl, bs', hbs'Len, hVal', by simpa [tp'] using hMS',
                  fun j hj => by simp [tp', hj, hTpOth j hj]⟩,
                by simp [meas]; omega⟩
            · rw [hVal] at hIncVal
              simp only [hiMax, ↓reduceIte] at hIncVal
              rcases hIncVal with ⟨rfl, _⟩
              have hAtomStop : (TMComponent.atom fun _ (scanned : Fin 5 → SimSym) =>
                  mkWorkAction (.inr false : Unit ⊕ Bool) scanned (fun _ => .stay)).ReachesExit
                  input bound tp' ⟨2 + i, by omega⟩ (.inr false) tp' ⟨2 + i, by omega⟩ :=
                TMComponent.atom_reachesExit _ input bound tp' ⟨2 + i, by omega⟩
                  hBnext ⟨2 + i, by omega⟩ (by simp [mkWorkAction, moveHead]) tp'
                  (fun j => OneSidedTape.updateAndMove_stay_self _) hBnext
              exact Or.inr ⟨false, tp', ⟨2 + i, by omega⟩,
                TMComponent.branch_reachesExit _ _ _ input bound true hCheck
                  (TMComponent.branch_reachesExit _ _ _ input bound false hInc hAtomStop),
                bs', hbs'Len, by simpa [tp'] using hMS', fun j hj => by simp [tp', hj, hTpOth j hj],
                by simp; omega⟩)
        t1 ⟨2, by omega⟩ ⟨0, by omega, by have := Nat.one_le_two_pow (n := S); omega, rfl,
          List.replicate S false, by simp, fromBitsLE_replicate_false S,
          by simpa [t1, show tScratch ≠ tRuler by decide] using hMS0, fun _ _ => rfl⟩
      obtain ⟨ok, tpEnd, finalInHead, hLRun, bs', hbs'Len, hMSEnd, hOthEnd, hOkEq⟩ := hLoopRes
      have hTpEndEq : tpEnd = fun j => if j = tScratch then tpEnd tScratch else t1 j := by
        funext j
        by_cases hj : j = tScratch
        · subst hj; rfl
        · simp [hj, hOthEnd j hj]
      refine ⟨ok, finalInHead, tpEnd tScratch, bs', hbs'Len, ?_, hMSEnd, hOkEq⟩
      rw [← hTpEndEq]
      exact TMComponent.seq_reachesExit _ _ input bound hStep0
        (TMComponent.branch_reachesExit _ _ _ input bound true hStep1 hLRun)
  obtain ⟨ok, finalInHead, ftS1, bs', hbs'Len, hSkipRun, hMS1, hOkEq⟩ := hLoopMain
  let t2 := fun j => if j = tScratch then ftS1 else t1 j
  have hT2Bounds : ∀ j, (t2 j).head < bound j := fun j => by
    by_cases ht : j = tScratch
    · subst ht; simp [t2, hMS1.head_eq]; omega
    · simp [t2, ht, hT1Bounds j]
  have hRewIn := rewindInputHead_reachesExit input bound t2 hT2Bounds finalInHead
  obtain ⟨ftS2, hClrS, hMS2⟩ := clearTape_reachesExit tScratch input bound (bs'.map SimSym.bit)
    (by simp [hbs'Len]; omega)
    (fun s hs => by rcases List.mem_map.mp hs with ⟨b, _, rfl⟩; simp)
    t2 ⟨0, by omega⟩ (fun j hj => by simp [t2, hj, hT1Bounds j]) (by simpa [t2] using hMS1)
  have hPostRun := TMComponent.mapExit_reachesExit _ (fun _ => ok) input bound
    (TMComponent.seq_reachesExit _ _ input bound hRewIn hClrS)
  have hFinalTapes : (fun j => if j = tScratch then ftS2 else t2 j) =
      (fun j => if j = tRuler then ftR0 else if j = tScratch then ftS2 else tapes j) := by
    funext j
    by_cases hjS : j = tScratch
    · subst hjS; simp [show tScratch ≠ tRuler by decide]
    · by_cases hjR : j = tRuler
      · subst hjR; simp [t2, t1, hjS]
      · simp [t2, t1, hjS, hjR]
  refine ⟨ftR0, ftS2, ?_, hMR0, hMS2⟩
  rw [← hOkEq, ← hFinalTapes]
  exact TMComponent.seq_reachesExit _ _ input bound hInit0
    (by
      cases ok
      · exact TMComponent.branch_reachesExit _ _ _ input bound false hSkipRun hPostRun
      · exact TMComponent.branch_reachesExit _ _ _ input bound true hSkipRun hPostRun)


end SavitchLemma

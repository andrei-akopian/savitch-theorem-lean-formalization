module

public import SavitchLemma.Tape.Actions

@[expose] public section

/-!
# Tape traversal primitives

Builds verified initialization, rewind, scan, clear, and input-head traversal components.
-/

namespace SavitchLemma

/-- Initialize cell `0` on all `k` work tapes to `.leftMark` and move each head
to cell `1`. -/
def initLeftMarksComp (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  TMComponent.atom fun _ _ =>
    { nextState := ()
      inputMove := .stay
      write := fun _ => .leftMark
      workMove := fun _ => .right }

theorem initLeftMarksComp_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ) (hBound : ∀ t, 2 ≤ bound t)
    (inHead : Fin (n + 2)) :
    (initLeftMarksComp InputAlphabet k).ReachesExit input bound
      (fun _ => ⟨fun _ => .blank, 0⟩) inHead ()
      (fun _ => ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩) inHead := by
  apply TMComponent.atom_reachesExit
  · intro t; exact Nat.lt_of_lt_of_le (by decide) (hBound t)
  · simp [moveHead]
  · intro t
    simp [OneSidedTape.updateAndMove, moveOneSidedHead]
  · intro t; exact Nat.lt_of_lt_of_le (by decide) (hBound t)

theorem tapeMatches_after_leftMark :
    TapeMatches ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩ [.leftMark] 1 := by
  refine ⟨rfl, fun i => ?_⟩
  cases i with
  | zero => simp
  | succ i' => simp

/-- Rewind tape `t` left until `.leftMark`, then step right once to cell `1`. -/
def rewindStepFn {InputAlphabet : Type*} (_ : InputSymbol InputAlphabet) :
    SimSym → ((Unit ⊕ Unit) × SimSym × TapeMove)
  | .leftMark => (.inr (), .leftMark, .right)
  | sym => (.inl (), sym, .left)

def rewindComp (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent Unit InputAlphabet SimSym k (Unit ⊕ Unit) :=
  TMComponent.atom fun inSym scanned =>
    let res := rewindStepFn inSym (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned

def rewindTape (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  (rewindComp InputAlphabet t).loop

theorem rewindTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (contents : List SimSym) (_hNonEmpty : 1 ≤ contents.length)
    (hLeftMark : contents[0] = .leftMark)
    (hNoOtherLeft : ∀ i, 1 ≤ i → i < contents.length → contents[i]? ≠ some .leftMark)
    (hBound : contents.length ≤ bound t)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (pos : ℕ) (_hPos : 1 ≤ pos) (hPosLt : pos < contents.length)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ finalTapes,
      (rewindTape InputAlphabet t).ReachesExit input bound initTapes inHead () finalTapes inHead ∧
      TapeMatches (finalTapes t) contents 1 ∧
      (∀ j, j ≠ t → finalTapes j = initTapes j) := by
  let Inv : (Fin k → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ t → tapes j = initTapes j) ∧
    ∃ p, p < contents.length ∧ TapeMatches (tapes t) contents p
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (rewindComp InputAlphabet t).ReachesExit input bound tapes ih (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧ (tapes' t).head < (tapes t).head) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (rewindComp InputAlphabet t).ReachesExit input bound tapes ih (.inr e) tapes' ih' ∧
        ih' = inHead ∧ TapeMatches (tapes' t) contents 1 ∧
        (∀ j, j ≠ t → tapes' j = initTapes j)) := by
    intro tapes ih hInv
    rcases hInv with ⟨hIhEq, hOthers, p, hpLt, hpMatch⟩
    subst ih
    have hHeadBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; rw [hpMatch.head_eq]; exact Nat.lt_of_lt_of_le hpLt hBound
      · rw [hOthers j hj]; exact hOtherBounds j hj
    cases p with
    | zero =>
      have hRead : (tapes t).cells (tapes t).head = .leftMark := by
        rw [hpMatch.read_lt hpLt]
        exact hLeftMark
      have hMove : moveOneSidedHead 0 .right = some 1 := rfl
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .leftMark .right hMove hpLt
      have hSetSame : contents.set 0 .leftMark = contents := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp [hLeftMark]
          | succ i' => simp
      rw [hSetSame] at hNextMatch
      right
      refine ⟨(), fun j => if j = t then nextTape else tapes j, inHead, ?_, rfl, ?_, ?_⟩
      · have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet) rewindStepFn
          t input bound tapes inHead hHeadBounds
          (by simpa [rewindStepFn, hRead] using hUpd)
          (by rw [hNextMatch.head_eq]; omega)
        simpa [rewindComp, rewindStepFn, hRead] using hAtom
      · simpa using hNextMatch
      · intro j hj
        simp [hj, hOthers j hj]
    | succ p' =>
      have hSymNe : contents[p' + 1] ≠ .leftMark := by
        have h := hNoOtherLeft (p' + 1) (by omega) hpLt
        rw [List.getElem?_eq_getElem hpLt] at h
        simpa using h
      have hRead : (tapes t).cells (tapes t).head = contents[p' + 1] :=
        hpMatch.read_lt hpLt
      have hNotLeft : (tapes t).cells (tapes t).head ≠ .leftMark := by
        rw [hRead]; exact hSymNe
      have hMove : moveOneSidedHead (p' + 1) .left = some p' := by
        simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_keep .left hMove
      have hFnEq : rewindStepFn (readInput input inHead) ((tapes t).cells (tapes t).head) =
          (.inl (), (tapes t).cells (tapes t).head, .left) := by
        cases hC : (tapes t).cells (tapes t).head
        · rfl
        · exact (hNotLeft hC).elim
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      left
      refine ⟨fun j => if j = t then nextTape else tapes j, inHead, ?_, ?_, ?_⟩
      · have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet) rewindStepFn
          t input bound tapes inHead hHeadBounds
          (by simpa [hFnEq] using hUpd)
          (by rw [hNextMatch.head_eq]; omega)
        simpa [rewindComp, hFnEq] using hAtom
      · refine ⟨rfl, fun j hj => by simp [hj, hOthers j hj], p', by omega, by simpa using hNextMatch⟩
      · simp [hpMatch.head_eq, hNextMatch.head_eq]
  have hInitInv : Inv initTapes inHead :=
    ⟨rfl, fun _ _ => rfl, pos, hPosLt, hMatch⟩
  obtain ⟨_, finalTapes, _, hLoop, rfl, hFinalMatch, hOthers⟩ :=
    TMComponent.loop_reachesExit (rewindComp InputAlphabet t) input bound Inv
      (fun tapes _ => (tapes t).head)
      (fun _ tapes ih => ih = inHead ∧ TapeMatches (tapes t) contents 1 ∧
        (∀ j, j ≠ t → tapes j = initTapes j))
      hStep initTapes inHead hInitInv
  exact ⟨finalTapes, hLoop, hFinalMatch, hOthers⟩

/-- Generic single-tape scan loop on tape `t`: each step reads the scanned symbol
on `t` and either continues (`.inl ()`) or exits (`.inr e`) with a write and move. -/
def scanTape {InputAlphabet : Type*} {k : ℕ} {Exit : Type*} (t : Fin k)
    (f : SimSym → (Unit ⊕ Exit) × SimSym × TapeMove) :
    TMComponent Unit InputAlphabet SimSym k Exit :=
  (TMComponent.atom fun _ scanned =>
    let res := f (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned).loop

theorem scanTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (t : Fin k) (f : SimSym → (Unit ⊕ Exit) × SimSym × TapeMove)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (Inv : OneSidedTape SimSym → Prop)
    (measure : OneSidedTape SimSym → ℕ)
    (Post : Exit → OneSidedTape SimSym → Prop)
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hStep : ∀ tape, Inv tape → tape.head < bound t →
      ∃ nextTape,
        tape.updateAndMove (f (tape.cells tape.head)).2.1 (f (tape.cells tape.head)).2.2 =
          some nextTape ∧
        nextTape.head < bound t ∧
        ((f (tape.cells tape.head)).1 = .inl () → Inv nextTape ∧ measure nextTape < measure tape) ∧
        (∀ e, (f (tape.cells tape.head)).1 = .inr e → Post e nextTape))
    (hInit : Inv (initTapes t)) (hInitBound : (initTapes t).head < bound t) :
    ∃ e finalTape,
      (scanTape (InputAlphabet := InputAlphabet) t f).ReachesExit input bound
        initTapes inHead e (fun j => if j = t then finalTape else initTapes j) inHead ∧
      Post e finalTape := by
  let FullInv : (Fin k → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧ (∀ j, j ≠ t → tapes j = initTapes j) ∧
    Inv (tapes t) ∧ (tapes t).head < bound t
  let Body := TMComponent.atom (InputAlphabet := InputAlphabet) fun _ scanned =>
    let res := f (scanned t)
    singleTapeAction res.1 t res.2.1 res.2.2 scanned
  have hBodyStep : ∀ tapes ih, FullInv tapes ih →
      (∃ tapes' ih', Body.ReachesExit input bound tapes ih (.inl ()) tapes' ih' ∧
        FullInv tapes' ih' ∧ measure (tapes' t) < measure (tapes t)) ∨
      (∃ e : Exit, ∃ tapes' ih', Body.ReachesExit input bound tapes ih (.inr e) tapes' ih' ∧
        ih' = inHead ∧ (∀ j, j ≠ t → tapes' j = initTapes j) ∧ Post e (tapes' t)) := by
    intro tapes ih hInv
    rcases hInv with ⟨hIhEq, hOthers, hInvT, hHeadT⟩
    subst ih
    have hHeadBounds : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases hj : j = t
      · subst hj; exact hHeadT
      · rw [hOthers j hj]; exact hOtherBounds j hj
    obtain ⟨nextTape, hUpd, hNextHead, hInl, hInr⟩ := hStep (tapes t) hInvT hHeadT
    have hAtom := singleTape_atom_reachesExit (InputAlphabet := InputAlphabet)
      (fun _ s => f s) t input bound tapes inHead hHeadBounds hUpd hNextHead
    cases hExit : (f ((tapes t).cells (tapes t).head)).1 with
    | inl u =>
      cases u
      rw [hExit] at hAtom
      obtain ⟨hInvNext, hMeas⟩ := hInl hExit
      left
      refine ⟨fun j => if j = t then nextTape else tapes j, inHead, hAtom, ?_, ?_⟩
      · refine ⟨rfl, fun j hj => by simp [hj, hOthers j hj], ?_⟩
        simpa using And.intro hInvNext hNextHead
      · simpa using hMeas
    | inr e =>
      rw [hExit] at hAtom
      right
      refine ⟨e, fun j => if j = t then nextTape else tapes j, inHead, hAtom, rfl, ?_, ?_⟩
      · intro j hj; simp [hj, hOthers j hj]
      · simpa using hInr e hExit
  obtain ⟨e, finalTapes, _, hLoop, rfl, hOthers, hPost⟩ :=
    TMComponent.loop_reachesExit Body input bound FullInv
      (fun tapes _ => measure (tapes t))
      (fun e tapes ih => ih = inHead ∧ (∀ j, j ≠ t → tapes j = initTapes j) ∧ Post e (tapes t))
      hBodyStep initTapes inHead ⟨rfl, fun _ _ => rfl, hInit, hInitBound⟩
  have hTapesEq : finalTapes = fun j => if j = t then finalTapes t else initTapes j := by
    funext j
    by_cases hj : j = t
    · subst hj; simp
    · simp [hj, hOthers j hj]
  rw [hTapesEq] at hLoop
  exact ⟨e, finalTapes t, hLoop, hPost⟩

/-- Scan tape `t` right until `.endMark` (overwriting cells `≥ 1` with `.blank`,
keeping `.leftMark` at cell `0`), then rewind to cell `1`. -/
def clearRightStep : SimSym → (Unit ⊕ Unit) × SimSym × TapeMove
  | .endMark => (.inr (), .blank, .stay)
  | _ => (.inl (), .blank, .right)

def clearTape (InputAlphabet : Type*) {k : ℕ} (t : Fin k) :
    TMComponent (Unit ⊕ Unit) InputAlphabet SimSym k Unit :=
  (scanTape (InputAlphabet := InputAlphabet) t clearRightStep).seq (rewindTape InputAlphabet t)

theorem clearTape_reachesExit {InputAlphabet : Type*} {k n : ℕ} (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (prefixSyms : List SimSym) (hBound : prefixSyms.length + 2 ≤ bound t)
    (hNoEnd : ∀ s ∈ prefixSyms, s ≠ .endMark)
    (initTapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) (.leftMark :: prefixSyms ++ [.endMark]) 1) :
    ∃ finalTape,
      (clearTape InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then finalTape else initTapes j) inHead ∧
      TapeMatches finalTape [.leftMark] 1 := by
  let orig : List SimSym := .leftMark :: prefixSyms ++ [.endMark]
  let L := orig.length
  have hL : L = prefixSyms.length + 2 := by
    simp [L, orig]
  let blankList : List SimSym := (List.replicate L SimSym.blank).set 0 .leftMark
  let Inv : OneSidedTape SimSym → Prop := fun tape =>
    ∃ p, 1 ≤ p ∧ p < L ∧
      TapeMatches tape ((List.replicate p SimSym.blank).set 0 .leftMark ++ orig.drop p) p
  let Post : Unit → OneSidedTape SimSym → Prop := fun _ tape => TapeMatches tape blankList (L - 1)
  have hStep : ∀ tape, Inv tape → tape.head < bound t →
      ∃ nextTape,
        tape.updateAndMove (clearRightStep (tape.cells tape.head)).2.1
          (clearRightStep (tape.cells tape.head)).2.2 = some nextTape ∧
        nextTape.head < bound t ∧
        ((clearRightStep (tape.cells tape.head)).1 = .inl () →
          Inv nextTape ∧ (L - nextTape.head) < (L - tape.head)) ∧
        (∀ e, (clearRightStep (tape.cells tape.head)).1 = .inr e → Post e nextTape) := by
    intro tape ⟨p, hp1, hpLt, hpMatch⟩ hHeadLt
    let curList : List SimSym := (List.replicate p SimSym.blank).set 0 .leftMark ++ orig.drop p
    have hCurLen : curList.length = L := by
      simp [curList, L]
      omega
    have hpCur : p < curList.length := by rw [hCurLen]; exact hpLt
    have hRead : tape.cells tape.head = orig[p] := by
      rw [hpMatch.read_lt hpCur]
      have hPrefLen : ((List.replicate p SimSym.blank).set 0 .leftMark).length = p := by simp
      have hGe : ((List.replicate p SimSym.blank).set 0 .leftMark).length ≤ p := hPrefLen.le
      simp [curList, List.getElem_append_right hGe, hPrefLen]
    by_cases hpLast : p = L - 1
    · have hpVal : p = prefixSyms.length + 1 := by omega
      have hEnd : orig[p] = .endMark := by
        simp only [orig, hpVal, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        simp
      have hReadEnd : tape.cells tape.head = .endMark := hRead.trans hEnd
      have hMove : moveOneSidedHead p .stay = some p := rfl
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .blank .stay hMove hpCur
      have hSetEq : curList.set p .blank = blankList := by
        apply List.ext_getElem
        · simp [hCurLen, blankList]
        · intro i hi1 hi2
          have hiL : i < L := by simpa [hCurLen] using hi1
          by_cases hip : i = p
          · simp [hip, blankList, List.getElem_set_ne (by omega : 0 ≠ p)]
          · rw [List.getElem_set_ne (Ne.symm hip)]
            have hiLtP : i < p := by omega
            have hiPref : i < ((List.replicate p SimSym.blank).set 0 .leftMark).length := by
              simp; omega
            simp only [curList, List.getElem_append_left hiPref]
            by_cases hi0 : i = 0
            · subst hi0; simp [blankList]
            · simp [blankList, List.getElem_set_ne (Ne.symm hi0)]
      rw [hSetEq, hpLast] at hNextMatch
      refine ⟨nextTape, by simpa [clearRightStep, hReadEnd] using hUpd,
        by rw [hNextMatch.head_eq]; omega, ?_, ?_⟩
      · intro hBad; simp [clearRightStep, hReadEnd] at hBad
      · intro e _; simpa [Post] using hNextMatch
    · have hpLtLast : p < prefixSyms.length + 1 := by omega
      have hNotEnd : orig[p] ≠ .endMark := by
        have hMem : orig[p] ∈ prefixSyms := by
          have hp0 : p - 1 < prefixSyms.length := by omega
          have hEq : orig[p] = prefixSyms[p - 1] := by
            cases p with
            | zero => omega
            | succ p' =>
              simp only [orig, List.cons_append, List.getElem_cons_succ]
              rw [List.getElem_append_left (by omega)]
              rfl
          rw [hEq]
          exact List.getElem_mem hp0
        exact hNoEnd _ hMem
      have hReadNotEnd : tape.cells tape.head ≠ .endMark := by rw [hRead]; exact hNotEnd
      have hFnEq : clearRightStep (tape.cells tape.head) = (.inl (), .blank, .right) := by
        cases hC : tape.cells tape.head
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hReadNotEnd hC).elim
      have hMove : moveOneSidedHead p .right = some (p + 1) := by simp [moveOneSidedHead]
      obtain ⟨nextTape, hUpd, hNextMatch⟩ := hpMatch.update_set .blank .right hMove hpCur
      have hSetEq : curList.set p .blank =
          (List.replicate (p + 1) SimSym.blank).set 0 .leftMark ++ orig.drop (p + 1) := by
        apply List.ext_getElem
        · simp [hCurLen, L]
          omega
        · intro i hi1 hi2
          have hiL : i < L := by simpa [hCurLen] using hi1
          by_cases hip : i = p
          · subst hip
            rw [List.getElem_set_self (by simpa [List.length_set] using hpCur)]
            have hPrefLen : ((List.replicate (i + 1) SimSym.blank).set 0 .leftMark).length = i + 1 := by simp
            rw [List.getElem_append_left (by omega : i < ((List.replicate (i + 1) SimSym.blank).set 0 .leftMark).length)]
            rw [List.getElem_set_ne (by omega : 0 ≠ i), List.getElem_replicate]
          · rw [List.getElem_set_ne (Ne.symm hip)]
            by_cases hiLtP : i < p
            · have hiLt1 : i < ((List.replicate p SimSym.blank).set 0 .leftMark).length := by simp; omega
              have hiLt2 : i < ((List.replicate (p + 1) SimSym.blank).set 0 .leftMark).length := by simp; omega
              rw [List.getElem_append_left hiLt1, List.getElem_append_left hiLt2]
              by_cases hi0 : i = 0
              · subst hi0; simp
              · simp [List.getElem_set_ne (Ne.symm hi0)]
            · have hiGtP : p < i := by omega
              have hGe1 : ((List.replicate p SimSym.blank).set 0 .leftMark).length ≤ i := by simp; omega
              have hGe2 : ((List.replicate (p + 1) SimSym.blank).set 0 .leftMark).length ≤ i := by simp; omega
              rw [List.getElem_append_right hGe1, List.getElem_append_right hGe2]
              simp only [List.length_set, List.length_replicate, List.getElem_drop]
              congr 1
              omega
      rw [hSetEq] at hNextMatch
      refine ⟨nextTape, by simpa [hFnEq] using hUpd, by rw [hNextMatch.head_eq]; omega, ?_, ?_⟩
      · intro _
        refine ⟨⟨p + 1, by omega, by omega, hNextMatch⟩, ?_⟩
        rw [hpMatch.head_eq, hNextMatch.head_eq]
        omega
      · intro e hBad; simp [hFnEq] at hBad
  have hInitInv : Inv (initTapes t) := by
    refine ⟨1, by omega, by omega, ?_⟩
    simpa [orig] using hMatch
  have hInitHead : (initTapes t).head < bound t := by
    rw [hMatch.head_eq]; omega
  obtain ⟨_, midTape, hScan, hMidMatch⟩ := scanTape_reachesExit (Exit := Unit) t clearRightStep
    input bound initTapes inHead Inv (fun tape => L - tape.head) Post
    hOtherBounds hStep hInitInv hInitHead
  obtain ⟨finalTapes, hR, hFM, hO⟩ := rewindTape_reachesExit t input bound blankList
    (by simp [blankList]; omega) (by simp [blankList])
    (fun i hi1 hi2 => by
      have hiL : i < L := by simpa [blankList] using hi2
      simp [blankList, hiL, List.getElem_set_ne (by omega : 0 ≠ i)])
    (by simp [blankList]; omega)
    (fun j => if j = t then midTape else initTapes j) inHead
    (fun j hj => by simp [hj, hOtherBounds j hj]) (L - 1) (by omega)
    (by simp [blankList]; omega) (by simpa using hMidMatch)
  have hFM' : TapeMatches (finalTapes t) [.leftMark] 1 := by
    refine ⟨hFM.1, fun i => ?_⟩
    rw [hFM.2 i]
    cases i with
    | zero => simp [blankList, show 0 < L by omega]
    | succ i' =>
      by_cases hiL : i' + 1 < L
      · simp [blankList, hiL, List.getElem_set_ne (by omega : 0 ≠ i' + 1)]
      · have hNone : blankList[i' + 1]? = none := List.getElem?_eq_none (by simp [blankList]; omega)
        simp [hNone]
  have hFinalEq : finalTapes = fun j => if j = t then finalTapes t else initTapes j := by
    funext j
    by_cases hj : j = t
    · subst hj; simp
    · simp [hj, hO j hj]
  rw [hFinalEq] at hR
  exact ⟨finalTapes t, (TMComponent.seq_reachesExit _ _ input bound hScan hR), hFM'⟩

/-- Prepend one internal `CompStep` onto a `ReachesExit` derivation. -/
theorem compStep_head_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (bound : Fin k → ℕ)
    {q q' : Q} {tapes tapes' finalTapes : Fin k → OneSidedTape Γ}
    {ih ih' finalIh : Fin (n + 2)} {e : Exit}
    (hHeads : ∀ j, (tapes j).head < bound j)
    (hHeads' : ∀ j, (tapes' j).head < bound j)
    (hNext : (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).nextState =
      .inl q')
    (hInMove : moveHead (n + 2) ih
      (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).inputMove =
        some ih')
    (hWork : ∀ j, (tapes j).updateAndMove
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).write j)
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).workMove j) =
        some (tapes' j))
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q', ih', tapes'⟩ ⟨.inr e, finalIh, finalTapes⟩) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, ih, tapes⟩ ⟨.inr e, finalIh, finalTapes⟩ := by
  refine Relation.ReflTransGen.head ⟨?_, hHeads, hHeads'⟩ hRest
  exact ⟨q, rfl, hNext.symm, ih', hInMove, rfl, hWork⟩

/-- Finish a `ReachesExit` derivation in one `CompStep` to `.inr e`. -/
theorem compStep_exit_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (bound : Fin k → ℕ)
    {q : Q} {tapes tapes' : Fin k → OneSidedTape Γ}
    {ih ih' : Fin (n + 2)} {e : Exit}
    (hHeads : ∀ j, (tapes j).head < bound j)
    (hHeads' : ∀ j, (tapes' j).head < bound j)
    (hNext : (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).nextState =
      .inr e)
    (hInMove : moveHead (n + 2) ih
      (M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).inputMove =
        some ih')
    (hWork : ∀ j, (tapes j).updateAndMove
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).write j)
      ((M.step q (readInput input ih) (fun j => (tapes j).cells (tapes j).head)).workMove j) =
        some (tapes' j)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, ih, tapes⟩ ⟨.inr e, ih', tapes'⟩ := by
  refine Relation.ReflTransGen.single ⟨?_, hHeads, hHeads'⟩
  exact ⟨q, rfl, hNext.symm, ih', hInMove, rfl, hWork⟩

/-- Helper to prepend one single-tape `CompStep` when the tape array overrides
tape `t` with `tape` / `nextTape`. -/
theorem singleTape_compStep_head_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (tape nextTape finalTape : OneSidedTape SimSym)
    (q q' : Q) {ih finalIh : Fin (n + 2)} {e : Exit}
    {w : SimSym} {mv : TapeMove}
    (hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j)
    (hNextHead : nextTape.head < bound t)
    (hUpd : tape.updateAndMove w mv = some nextTape)
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', ih, fun j => if j = t then nextTape else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t then finalTape else initTapes j⟩)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
      singleTapeAction (Sum.inl q') t w mv
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t then tape else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t then finalTape else initTapes j⟩ := by
  refine compStep_head_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_ hRest
  · by_cases hj : j = t
    · subst hj; simpa using hNextHead
    · simp only [hj, ↓reduceIte]; exact by simpa [hj] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [singleTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := singleTapeAction_apply (Sum.inl q' : Q ⊕ Exit) t w mv
      (fun y => if y = t then tape else initTapes y) (by simpa using hUpd) j
    by_cases hj : j = t
    · subst hj; simpa using hApp
    · simpa [hj] using hApp

theorem singleTape_compStep_exit_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t : Fin k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym) (tape nextTape : OneSidedTape SimSym)
    (q : Q) {ih : Fin (n + 2)} {e : Exit}
    {w : SimSym} {mv : TapeMove}
    (hHeads : ∀ j, (if j = t then tape else initTapes j).head < bound j)
    (hNextHead : nextTape.head < bound t)
    (hUpd : tape.updateAndMove w mv = some nextTape)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head) =
      singleTapeAction (Sum.inr e) t w mv
        (fun j => (if j = t then tape else initTapes j).cells
          (if j = t then tape else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t then tape else initTapes j⟩
      ⟨.inr e, ih, fun j => if j = t then nextTape else initTapes j⟩ := by
  refine compStep_exit_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_
  · by_cases hj : j = t
    · subst hj; simpa using hNextHead
    · simp only [hj, ↓reduceIte]; exact by simpa [hj] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [singleTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := singleTapeAction_apply (Sum.inr e : Q ⊕ Exit) t w mv
      (fun y => if y = t then tape else initTapes y) (by simpa using hUpd) j
    by_cases hj : j = t
    · subst hj; simpa using hApp
    · simpa [hj] using hApp

theorem twoTape_compStep_head_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym)
    (tape₁ tape₂ nt₁ nt₂ ft₁ ft₂ : OneSidedTape SimSym)
    (q q' : Q) {ih finalIh : Fin (n + 2)} {e : Exit}
    {w₁ w₂ : SimSym} {m₁ m₂ : TapeMove}
    (hHeads : ∀ j, (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j)
    (hNH₁ : nt₁.head < bound t₁) (hNH₂ : nt₂.head < bound t₂)
    (hUpd₁ : tape₁.updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : tape₂.updateAndMove w₂ m₂ = some nt₂)
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', ih, fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j⟩)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
      twoTapeAction (Sum.inl q') t₁ t₂ w₁ w₂ m₁ m₂
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j⟩
      ⟨.inr e, finalIh, fun j => if j = t₁ then ft₁ else if j = t₂ then ft₂ else initTapes j⟩ := by
  refine compStep_head_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_ hRest
  · by_cases h1 : j = t₁
    · subst h1; simpa using hNH₁
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hNH₂
      · simp only [h1, h2, ↓reduceIte]; exact by simpa [h1, h2] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [twoTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := twoTapeAction_apply (Sum.inl q' : Q ⊕ Exit) t₁ t₂ hNe w₁ w₂ m₁ m₂
      (fun y => if y = t₁ then tape₁ else if y = t₂ then tape₂ else initTapes y)
      (by simpa using hUpd₁) (by simpa [hNe.symm] using hUpd₂) j
    by_cases h1 : j = t₁
    · subst h1; simpa using hApp
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hApp
      · simpa [h1, h2] using hApp

theorem twoTape_compStep_exit_override {Q InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet SimSym k Exit) (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape SimSym)
    (tape₁ tape₂ nt₁ nt₂ : OneSidedTape SimSym)
    (q : Q) {ih : Fin (n + 2)} {e : Exit}
    {w₁ w₂ : SimSym} {m₁ m₂ : TapeMove}
    (hHeads : ∀ j, (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head < bound j)
    (hNH₁ : nt₁.head < bound t₁) (hNH₂ : nt₂.head < bound t₂)
    (hUpd₁ : tape₁.updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : tape₂.updateAndMove w₂ m₂ = some nt₂)
    (hStepEq : M.step q (readInput input ih)
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head) =
      twoTapeAction (Sum.inr e) t₁ t₂ w₁ w₂ m₁ m₂
        (fun j => (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).cells
          (if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j).head)) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, ih, fun j => if j = t₁ then tape₁ else if j = t₂ then tape₂ else initTapes j⟩
      ⟨.inr e, ih, fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else initTapes j⟩ := by
  refine compStep_exit_reachesExit M input bound hHeads (fun j => ?_) ?_ ?_ ?_
  · by_cases h1 : j = t₁
    · subst h1; simpa using hNH₁
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hNH₂
      · simp only [h1, h2, ↓reduceIte]; exact by simpa [h1, h2] using hHeads j
  · rw [hStepEq]; rfl
  · rw [hStepEq]; simp [twoTapeAction, moveHead]
  · intro j
    rw [hStepEq]
    have hApp := twoTapeAction_apply (Sum.inr e : Q ⊕ Exit) t₁ t₂ hNe w₁ w₂ m₁ m₂
      (fun y => if y = t₁ then tape₁ else if y = t₂ then tape₂ else initTapes y)
      (by simpa using hUpd₁) (by simpa [hNe.symm] using hUpd₂) j
    by_cases h1 : j = t₁
    · subst h1; simpa using hApp
    · by_cases h2 : j = t₂
      · subst h2; simpa [h1] using hApp
      · simpa [h1, h2] using hApp

/-- Rewind the input head to `.leftEnd` (position `0`) without modifying any
work tapes. -/
def rewindInputBody (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k (Unit ⊕ Unit) :=
  TMComponent.atom fun inSym scanned =>
    match inSym with
    | .leftEnd => TMAction.mk (Sum.inr ()) TapeMove.stay scanned (fun _ => TapeMove.stay)
    | _ => TMAction.mk (Sum.inl ()) TapeMove.left scanned (fun _ => TapeMove.stay)

def rewindInput (InputAlphabet : Type*) (k : ℕ) :
    TMComponent Unit InputAlphabet SimSym k Unit :=
  (rewindInputBody InputAlphabet k).loop

private theorem stay_all_tapes {k : ℕ} (tapes : Fin k → OneSidedTape SimSym) :
    ∀ j : Fin k,
      (tapes j).updateAndMove ((tapes j).cells (tapes j).head) .stay = some (tapes j) := by
  intro j
  cases hT : tapes j with
  | mk cells head =>
    simp only [OneSidedTape.updateAndMove, moveOneSidedHead]
    congr 1
    simp only [OneSidedTape.mk.injEq, and_true]
    funext i
    by_cases hi : i = head <;> simp [hi]

theorem rewindInput_reachesExit {InputAlphabet : Type*} {k n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym)
    (hBounds : ∀ j, (tapes j).head < bound j) (inHead : Fin (n + 2)) :
    (rewindInput InputAlphabet k).ReachesExit input bound tapes inHead ()
      tapes ⟨0, by omega⟩ := by
  have hInd : ∀ p, ∀ ih : Fin (n + 2), ih.val = p →
      (rewindInput InputAlphabet k).ReachesExit input bound tapes ih () tapes ⟨0, by omega⟩ := by
    intro p
    induction p with
    | zero =>
      intro ih hPos
      have hIh0 : ih = ⟨0, by omega⟩ := Fin.ext hPos
      have hRead : readInput input ih = .leftEnd := by simp [readInput, hPos]
      have hStepEq : (rewindInput InputAlphabet k).step () (readInput input ih)
          (fun j => (tapes j).cells (tapes j).head) =
          TMAction.mk (Sum.inr ()) TapeMove.stay
            (fun j => (tapes j).cells (tapes j).head) (fun _ => TapeMove.stay) := by
        simp [rewindInput, rewindInputBody, TMComponent.loop, TMComponent.atom, hRead,
          TMAction.mapState]
      refine compStep_exit_reachesExit (rewindInput InputAlphabet k) input bound hBounds hBounds
        (by rw [hStepEq])
        (by rw [hStepEq]; simp [moveHead, hIh0])
        (fun j => by rw [hStepEq]; exact stay_all_tapes tapes j)
    | succ p' ihRec =>
      intro ih hPos
      have hNotLeft : readInput input ih ≠ .leftEnd := by
        simp [readInput, hPos]
        split <;> simp
      have hStepEq : (rewindInput InputAlphabet k).step () (readInput input ih)
          (fun j => (tapes j).cells (tapes j).head) =
          TMAction.mk (Sum.inl ()) TapeMove.left
            (fun j => (tapes j).cells (tapes j).head) (fun _ => TapeMove.stay) := by
        simp only [rewindInput, rewindInputBody, TMComponent.loop, TMComponent.atom,
          TMAction.mapState]
      have hLt : p' < n + 2 := by have := ih.isLt; omega
      have hMove : moveHead (n + 2) ih .left = some ⟨p', hLt⟩ := by
        simp [moveHead, hPos]
      exact compStep_head_reachesExit (rewindInput InputAlphabet k) input bound hBounds hBounds
        (by rw [hStepEq]) (by rw [hStepEq]; exact hMove)
        (fun j => by rw [hStepEq]; exact stay_all_tapes tapes j)
        (ihRec ⟨p', hLt⟩ rfl)
  exact hInd inHead.val inHead rfl

end SavitchLemma

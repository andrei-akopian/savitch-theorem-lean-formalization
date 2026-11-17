module

public import SavitchLemma.Simulator.MainBridge
import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-!
# Ruler writer from a measuring machine

Given a single-tape deterministic machine `D` over the simulator alphabet `SimSym` that
halts after scanning exactly `S` squares, `rwComp D` runs `D` on `tScratch` (shifted one
cell right) while marking every visited cell on `tRuler`; it then clears `tScratch`,
caps the ruler with `endMark`, and rewinds, leaving exactly the tapes expected by
`PrefixPrepares`.
-/

namespace SavitchLemma

/-- Control states of the ruler writer. -/
inductive RWState (QD : Type) where
  | pre
  | sim (q : QD)
  | goLeft
  | clear
  | back
  deriving Fintype

/-- Action writing `r` / `s` (with moves) on the ruler / scratch tapes and `o t` on the others. -/
def mk5 {St : Type*} (next : St) (im : TapeMove) (r s : SimSym × TapeMove)
    (o : Fin 5 → SimSym × TapeMove) : TMAction St SimSym 5 where
  nextState := next
  inputMove := im
  write t := if t = tRuler then r.1 else if t = tScratch then s.1 else (o t).1
  workMove t := if t = tRuler then r.2 else if t = tScratch then s.2 else (o t).2

/-- The ruler-writer component. -/
def rwComp {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1) :
    TMComponent (RWState QD) I SimSym 5 Unit where
  start := .pre
  step st inSym works :=
    let keep : Fin 5 → SimSym × TapeMove := fun t => (works t, .stay)
    match st with
    | .pre =>
      mk5 (.inl (.sim D.startState)) .stay (.leftMark, .right) (.leftMark, .right)
        (fun _ => (.leftMark, .right))
    | .sim q =>
      match D.transition q inSym (fun _ => works tScratch) with
      | some a =>
        mk5 (.inl (.sim a.nextState)) a.inputMove (.bit true, a.workMove 0)
          (a.write 0, a.workMove 0) keep
      | none => mk5 (.inl .goLeft) .stay (.bit true, .stay) (works tScratch, .stay) keep
    | .goLeft =>
      if works tRuler = .leftMark then
        mk5 (.inl .clear) .stay (.leftMark, .right) (works tScratch, .right) keep
      else mk5 (.inl .goLeft) .stay (works tRuler, .left) (works tScratch, .left) keep
    | .clear =>
      if works tRuler = .bit true then
        mk5 (.inl .clear) .stay (.bit true, .right) (.blank, .right) keep
      else mk5 (.inl .back) .stay (.endMark, .stay) (.blank, .stay) keep
    | .back =>
      if works tRuler = .leftMark then
        mk5 (.inr ()) .stay (.leftMark, .right) (works tScratch, .right) keep
      else mk5 (.inl .back) .stay (works tRuler, .left) (works tScratch, .left) keep

/-- Tape family: ruler `R`, scratch `Sc`, and `F` on the other three tapes. -/
def tapes5 (R Sc F : OneSidedTape SimSym) : Fin 5 → OneSidedTape SimSym :=
  fun t => if t = tRuler then R else if t = tScratch then Sc else F

theorem OneSidedTape.stay_same (T : OneSidedTape SimSym) :
    T.updateAndMove (T.cells T.head) .stay = some T := by
  simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]
  congr 1
  funext i
  by_cases h : i = T.head <;> simp [h]

theorem tapes5_update (R Sc F R' Sc' : OneSidedTape SimSym) {St : Type*} (nx : St)
    (im : TapeMove) (r s : SimSym × TapeMove)
    (hR : R.updateAndMove r.1 r.2 = some R') (hS : Sc.updateAndMove s.1 s.2 = some Sc') :
    ∀ t, (tapes5 R Sc F t).updateAndMove
      ((mk5 nx im r s (fun t => ((tapes5 R Sc F t).cells (tapes5 R Sc F t).head, .stay))).write t)
      ((mk5 nx im r s (fun t => ((tapes5 R Sc F t).cells (tapes5 R Sc F t).head, .stay))).workMove t)
      = some (tapes5 R' Sc' F t) := by
  intro t
  by_cases h1 : t = tRuler
  · subst h1; simpa [mk5, tapes5, tRuler, tScratch] using hR
  · by_cases h2 : t = tScratch
    · subst h2; simpa [mk5, tapes5, tRuler, tScratch] using hS
    · simpa [mk5, tapes5, h1, h2] using OneSidedTape.stay_same (tapes5 R Sc F t)

theorem tapes5_head_lt (R Sc F : OneSidedTape SimSym) (B : ℕ)
    (hR : R.head < B) (hS : Sc.head < B) (hF : F.head < B) (t : Fin 5) :
    (tapes5 R Sc F t).head < B := by
  unfold tapes5; split_ifs <;> assumption

theorem compStep_mk5 {St I : Type*} {n : ℕ} (P : TMComponent St I SimSym 5 Unit)
    (input : Fin n → I) (q : St) (ih ih' : Fin (n + 2))
    (R Sc F R' Sc' : OneSidedTape SimSym) (nx : St ⊕ Unit) (im : TapeMove)
    (r s : SimSym × TapeMove)
    (hAct : P.step q (readInput input ih)
        (fun t => (tapes5 R Sc F t).cells (tapes5 R Sc F t).head) =
      mk5 nx im r s (fun t => ((tapes5 R Sc F t).cells (tapes5 R Sc F t).head, .stay)))
    (hIn : moveHead (n + 2) ih im = some ih')
    (hR : R.updateAndMove r.1 r.2 = some R') (hS : Sc.updateAndMove s.1 s.2 = some Sc') :
    P.CompStep input ⟨.inl q, ih, tapes5 R Sc F⟩ ⟨nx, ih', tapes5 R' Sc' F⟩ := by
  refine ⟨q, rfl, ?_⟩
  have hW : (OneSidedTMConfig.scannedWork
      (⟨.inl q, ih, tapes5 R Sc F⟩ : OneSidedTMConfig (St ⊕ Unit) SimSym 5 n)) =
      fun t => (tapes5 R Sc F t).cells (tapes5 R Sc F t).head := rfl
  show nx = (P.step q (readInput input ih) (OneSidedTMConfig.scannedWork
      (⟨.inl q, ih, tapes5 R Sc F⟩ : OneSidedTMConfig (St ⊕ Unit) SimSym 5 n))).nextState ∧ _
  rw [hW, hAct]
  exact ⟨rfl, ih', hIn, rfl, tapes5_update R Sc F R' Sc' nx im r s hR hS⟩

/-- Ruler with `m` marks and head `h`. -/
def rulerTape (m h : ℕ) : OneSidedTape SimSym :=
  ⟨fun i => if i = 0 then .leftMark else if i ≤ m then .bit true else .blank, h⟩

/-- Ruler with `S` marks, a closing `endMark`, and head `h`. -/
def rulerCap (S h : ℕ) : OneSidedTape SimSym :=
  ⟨fun i => if i = 0 then .leftMark else if i ≤ S then .bit true
    else if i = S + 1 then .endMark else .blank, h⟩

/-- Scratch tape holding `D`'s tape shifted one cell right. -/
def scratchTape (c : OneSidedTape SimSym) : OneSidedTape SimSym :=
  ⟨fun i => if i = 0 then .leftMark else c.cells (i - 1), c.head + 1⟩

/-- The three untouched tapes after the initial `leftMark`. -/
def fixedTape : OneSidedTape SimSym :=
  ⟨fun i => if i = 0 then .leftMark else .blank, 1⟩

/-- Correspondence between a `D` configuration and a `rwComp D` configuration. -/
def rwCfg {QD : Type} {n : ℕ} (c : OneSidedTMConfig QD SimSym 1 n) (m : ℕ) :
    OneSidedTMConfig (RWState QD ⊕ Unit) SimSym 5 n :=
  ⟨.inl (.sim c.state), c.inputHead,
    tapes5 (rulerTape m ((c.workTapes 0).head + 1)) (scratchTape (c.workTapes 0)) fixedTape⟩

theorem rw_pre_step {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (hBlank : D.blank = .blank) :
    (rwComp D).CompStep input
      ⟨.inl .pre, ⟨0, by omega⟩, fun _ => ⟨fun _ => .blank, 0⟩⟩
      (rwCfg (n := n) (D.toNTM.oneSidedInitialConfig) 0) := by
  refine ⟨.pre, rfl, ?_⟩
  refine ⟨rfl, ⟨0, by omega⟩, rfl, rfl, ?_⟩
  intro t
  simp [rwComp, mk5, OneSidedTape.updateAndMove, moveOneSidedHead, rwCfg, tapes5,
    rulerTape, scratchTape, fixedTape, MultitapeNTM.oneSidedInitialConfig]
  have hb : D.toNTM.blank = .blank := hBlank
  split_ifs <;> (congr 1 <;> (try (funext i; by_cases hi : i = 0 <;> simp [hi, hb])))

theorem updateAndMove_eq {T T' : OneSidedTape SimSym} {w : SimSym} {mv : TapeMove}
    (h : T.updateAndMove w mv = some T') :
    ∃ h', moveOneSidedHead T.head mv = some h' ∧
      T' = ⟨fun i => if i = T.head then w else T.cells i, h'⟩ := by
  unfold OneSidedTape.updateAndMove at h
  cases hm : moveOneSidedHead T.head mv with
  | none => simp [hm] at h
  | some h' =>
    simp only [hm, Option.some.injEq] at h
    exact ⟨h', rfl, h.symm⟩

theorem move_shift {h h' : ℕ} {mv : TapeMove} (hm : moveOneSidedHead h mv = some h') :
    moveOneSidedHead (h + 1) mv = some (h' + 1) := by
  cases mv <;> simp [moveOneSidedHead] at hm ⊢ <;> omega

theorem scratch_update {T T' : OneSidedTape SimSym} {w : SimSym} {mv : TapeMove}
    (h : T.updateAndMove w mv = some T') :
    (scratchTape T).updateAndMove w mv = some (scratchTape T') := by
  obtain ⟨h', hm, rfl⟩ := updateAndMove_eq h
  have := move_shift hm
  simp only [OneSidedTape.updateAndMove, scratchTape, this, Option.some.injEq]
  congr 1
  funext i
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases hi : i = T.head + 1
    · simp [hi]
    · have : i - 1 ≠ T.head := by omega
      simp [h0, hi, this]

theorem ruler_update {m h h' : ℕ} {mv : TapeMove} (hm : moveOneSidedHead h mv = some h')
    (hh : h ≤ m) :
    (rulerTape m (h + 1)).updateAndMove (.bit true) mv =
      some (rulerTape (max m (h + 1)) (h' + 1)) := by
  have := move_shift hm
  simp only [OneSidedTape.updateAndMove, rulerTape, this, Option.some.injEq]
  congr 1
  funext i
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases hi : i = h + 1
    · simp [hi]
    · simp only [h0, hi, ↓reduceIte]
      by_cases h1 : i ≤ m
      · simp [h1, show i ≤ max m (h + 1) from le_max_of_le_left h1]
      · have : ¬ i ≤ max m (h + 1) := by omega
        simp [h1, this]

theorem scratch_read (T : OneSidedTape SimSym) :
    (scratchTape T).cells (scratchTape T).head = T.cells T.head := by
  simp [scratchTape]

theorem rw_sim_step {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) {c c' : OneSidedTMConfig QD SimSym 1 n}
    (hstep : D.toNTM.oneSidedStep input c c') (m : ℕ) (hm : (c.workTapes 0).head ≤ m) :
    (rwComp D).CompStep input (rwCfg c m)
      (rwCfg c' (max m ((c.workTapes 0).head + 1))) := by
  obtain ⟨a, ha, hst, ih', hmv, hih, hup⟩ := hstep
  have hTrans : D.transition c.state (readInput input c.inputHead) c.scannedWork = some a := by
    simpa [MultitapeDTM.toNTM] using ha
  have hup0 := hup 0
  obtain ⟨h', hmove, hT'⟩ := updateAndMove_eq hup0
  have hScan : (fun _ : Fin 1 => (scratchTape (c.workTapes 0)).cells
      (scratchTape (c.workTapes 0)).head) = c.scannedWork := by
    funext t
    have : t = 0 := Subsingleton.elim _ _
    subst this
    simpa [OneSidedTMConfig.scannedWork] using scratch_read (c.workTapes 0)
  have hAct : (rwComp D).step (.sim c.state) (readInput input c.inputHead)
      (fun t => (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).head) =
      mk5 (.inl (.sim a.nextState)) a.inputMove (.bit true, a.workMove 0)
        (a.write 0, a.workMove 0)
        (fun t => ((tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).head, .stay)) := by
    have : (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape tScratch).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape tScratch).head =
        (scratchTape (c.workTapes 0)).cells (scratchTape (c.workTapes 0)).head := by
      simp [tapes5, tScratch, tRuler]
    simp only [rwComp]
    rw [this, hScan, hTrans]
  have hS := scratch_update hup0
  have hR := ruler_update hmove hm
  have key := compStep_mk5 (rwComp D) input (.sim c.state) c.inputHead ih'
    (rulerTape m ((c.workTapes 0).head + 1)) (scratchTape (c.workTapes 0)) fixedTape _ _
    (.inl (.sim a.nextState)) a.inputMove (.bit true, a.workMove 0) (a.write 0, a.workMove 0)
    hAct hmv hR hS
  have hEq : rwCfg c' (max m ((c.workTapes 0).head + 1)) =
      ⟨.inl (.sim a.nextState), ih', tapes5 (rulerTape (max m ((c.workTapes 0).head + 1)) (h' + 1))
        (scratchTape (c'.workTapes 0)) fixedTape⟩ := by
    have hh : (c'.workTapes 0).head = h' := by rw [hT']
    simp only [rwCfg, hst, hih, hh]
  rw [hEq]
  exact key

theorem rw_mark_step {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) {c : OneSidedTMConfig QD SimSym 1 n}
    (hNone : D.transition c.state (readInput input c.inputHead) c.scannedWork = none)
    (m : ℕ) (hm : (c.workTapes 0).head ≤ m) :
    (rwComp D).CompStep input (rwCfg c m)
      ⟨.inl .goLeft, c.inputHead,
        tapes5 (rulerTape (max m ((c.workTapes 0).head + 1)) ((c.workTapes 0).head + 1))
          (scratchTape (c.workTapes 0)) fixedTape⟩ := by
  have hScan : (fun _ : Fin 1 => (scratchTape (c.workTapes 0)).cells
      (scratchTape (c.workTapes 0)).head) = c.scannedWork := by
    funext t
    have : t = 0 := Subsingleton.elim _ _
    subst this
    simpa [OneSidedTMConfig.scannedWork] using scratch_read (c.workTapes 0)
  have hAct : (rwComp D).step (.sim c.state) (readInput input c.inputHead)
      (fun t => (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).head) =
      mk5 (.inl .goLeft) .stay (.bit true, .stay)
        ((scratchTape (c.workTapes 0)).cells (scratchTape (c.workTapes 0)).head, .stay)
        (fun t => ((tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape t).head, .stay)) := by
    have : (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape tScratch).cells
        (tapes5 (rulerTape m ((c.workTapes 0).head + 1))
        (scratchTape (c.workTapes 0)) fixedTape tScratch).head =
        (scratchTape (c.workTapes 0)).cells (scratchTape (c.workTapes 0)).head := by
      simp [tapes5, tScratch, tRuler]
    simp only [rwComp]
    rw [this, hScan, hNone]
  have hR := ruler_update (mv := .stay) (h := (c.workTapes 0).head) (h' := (c.workTapes 0).head)
    (by simp [moveOneSidedHead]) hm
  have hS : (scratchTape (c.workTapes 0)).updateAndMove
      ((scratchTape (c.workTapes 0)).cells (scratchTape (c.workTapes 0)).head) .stay =
      some (scratchTape (c.workTapes 0)) := OneSidedTape.stay_same _
  exact compStep_mk5 (rwComp D) input (.sim c.state) c.inputHead c.inputHead
    (rulerTape m ((c.workTapes 0).head + 1)) (scratchTape (c.workTapes 0)) fixedTape _ _
    (.inl .goLeft) .stay (.bit true, .stay)
    ((scratchTape (c.workTapes 0)).cells (scratchTape (c.workTapes 0)).head, .stay)
    hAct (by simp [moveHead]) hR hS

/-- Bounded run of a component (all work heads below `B`). -/
abbrev RWRun {St I : Type*} {n : ℕ} (P : TMComponent St I SimSym 5 Unit) (input : Fin n → I)
    (B : ℕ) := Relation.ReflTransGen
  (fun a b : OneSidedTMConfig (St ⊕ Unit) SimSym 5 n => P.CompStep input a b ∧
    (∀ t, (a.workTapes t).head < B) ∧ (∀ t, (b.workTapes t).head < B))

/-- Scanned symbols of a `tapes5` family. -/
def scanned5 (R Sc F : OneSidedTape SimSym) : Fin 5 → SimSym :=
  fun t => (tapes5 R Sc F t).cells (tapes5 R Sc F t).head

theorem write_same_move (T : OneSidedTape SimSym) {mv : TapeMove} {h' : ℕ}
    (hm : moveOneSidedHead T.head mv = some h') :
    T.updateAndMove (T.cells T.head) mv = some ⟨T.cells, h'⟩ := by
  simp only [OneSidedTape.updateAndMove, hm, Option.some.injEq]
  congr 1
  funext i
  by_cases h : i = T.head <;> simp [h]

theorem rw_step_one {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (B : ℕ) (q : RWState QD) (ih ih' : Fin (n + 2))
    (R Sc F R' Sc' : OneSidedTape SimSym) (nx : RWState QD ⊕ Unit) (im : TapeMove)
    (r s : SimSym × TapeMove)
    (hAct : (rwComp D).step q (readInput input ih) (scanned5 R Sc F) =
      mk5 nx im r s (fun t => (scanned5 R Sc F t, .stay)))
    (hIn : moveHead (n + 2) ih im = some ih')
    (hR : R.updateAndMove r.1 r.2 = some R') (hS : Sc.updateAndMove s.1 s.2 = some Sc')
    (hF : F.head < B) (h1 : R.head < B) (h2 : Sc.head < B) (h3 : R'.head < B) (h4 : Sc'.head < B) :
    RWRun (rwComp D) input B ⟨.inl q, ih, tapes5 R Sc F⟩ ⟨nx, ih', tapes5 R' Sc' F⟩ :=
  Relation.ReflTransGen.single ⟨compStep_mk5 (rwComp D) input q ih ih' R Sc F R' Sc' nx im r s
    hAct hIn hR hS, tapes5_head_lt _ _ _ _ h1 h2 hF, tapes5_head_lt _ _ _ _ h3 h4 hF⟩

theorem rw_goLeft_act {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    (inSym : InputSymbol I) (R Sc F : OneSidedTape SimSym) :
    (rwComp D).step .goLeft inSym (scanned5 R Sc F) =
      if R.cells R.head = .leftMark then
        mk5 (.inl .clear) .stay (.leftMark, .right) (Sc.cells Sc.head, .right)
          (fun t => (scanned5 R Sc F t, .stay))
      else mk5 (.inl .goLeft) .stay (R.cells R.head, .left) (Sc.cells Sc.head, .left)
          (fun t => (scanned5 R Sc F t, .stay)) := by
  simp [rwComp, scanned5, tapes5, tRuler, tScratch]

theorem rw_clear_act {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    (inSym : InputSymbol I) (R Sc F : OneSidedTape SimSym) :
    (rwComp D).step .clear inSym (scanned5 R Sc F) =
      if R.cells R.head = .bit true then
        mk5 (.inl .clear) .stay (.bit true, .right) (.blank, .right)
          (fun t => (scanned5 R Sc F t, .stay))
      else mk5 (.inl .back) .stay (.endMark, .stay) (.blank, .stay)
          (fun t => (scanned5 R Sc F t, .stay)) := by
  simp [rwComp, scanned5, tapes5, tRuler, tScratch]

theorem rw_back_act {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    (inSym : InputSymbol I) (R Sc F : OneSidedTape SimSym) :
    (rwComp D).step .back inSym (scanned5 R Sc F) =
      if R.cells R.head = .leftMark then
        mk5 (.inr ()) .stay (.leftMark, .right) (Sc.cells Sc.head, .right)
          (fun t => (scanned5 R Sc F t, .stay))
      else mk5 (.inl .back) .stay (R.cells R.head, .left) (Sc.cells Sc.head, .left)
          (fun t => (scanned5 R Sc F t, .stay)) := by
  simp [rwComp, scanned5, tapes5, tRuler, tScratch]

theorem rw_goLeft {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (ih : Fin (n + 2)) (S B : ℕ) (hB : S + 1 < B)
    (sc : ℕ → SimSym) :
    ∀ h, h ≤ S →
      RWRun (rwComp D) input B ⟨.inl .goLeft, ih, tapes5 (rulerTape S h) ⟨sc, h⟩ fixedTape⟩
        ⟨.inl .clear, ih, tapes5 (rulerTape S 1) ⟨sc, 1⟩ fixedTape⟩ := by
  intro h
  induction h with
  | zero =>
    intro _
    refine rw_step_one D input B .goLeft ih ih _ _ _ _ _ _ .stay (.leftMark, .right)
      (sc 0, .right) ?_ (by simp [moveHead]) ?_ ?_ (by simp [fixedTape]; omega)
      (by simp [rulerTape]; omega) (by simp; omega) (by simp [rulerTape]; omega)
      (by simp; omega)
    · rw [rw_goLeft_act]; simp [rulerTape]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead, rulerTape]
      funext i; by_cases hi : i = 0 <;> simp [hi]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead]
      funext i; by_cases hi : i = 0 <;> simp [hi]
  | succ h ih' =>
    intro hh
    have hStep := rw_step_one D input B .goLeft ih ih (rulerTape S (h + 1)) ⟨sc, h + 1⟩ fixedTape (rulerTape S h) ⟨sc, h⟩ (.inl .goLeft) .stay
      ((rulerTape S (h + 1)).cells (rulerTape S (h + 1)).head, .left) (sc (h + 1), .left)
      ?_ (by simp [moveHead]) ?_ ?_
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) (by simp; omega)
      (by simp [rulerTape]; omega) (by simp; omega)
    · exact hStep.trans (ih' (by omega))
    · rw [rw_goLeft_act]
      simp [rulerTape, hh]
    · simpa [rulerTape] using write_same_move (rulerTape S (h + 1)) (mv := .left) (h' := h)
        (by simp [rulerTape, moveOneSidedHead])
    · simpa using write_same_move (⟨sc, h + 1⟩ : OneSidedTape SimSym) (mv := .left) (h' := h)
        (by simp [moveOneSidedHead])

theorem rw_clear {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (ih : Fin (n + 2)) (S B : ℕ) (hB : S + 1 < B) :
    ∀ d c (g : ℕ → SimSym), c + d = S + 1 → 1 ≤ c →
      RWRun (rwComp D) input B ⟨.inl .clear, ih, tapes5 (rulerTape S c) ⟨g, c⟩ fixedTape⟩
        ⟨.inl .back, ih, tapes5 (rulerCap S (S + 1))
          ⟨fun i => if c ≤ i ∧ i ≤ S + 1 then .blank else g i, S + 1⟩ fixedTape⟩ := by
  intro d
  induction d with
  | zero =>
    intro c g hc h1
    have hc' : c = S + 1 := by omega
    subst hc'
    refine rw_step_one D input B .clear ih ih (rulerTape S (S + 1)) ⟨g, S + 1⟩ fixedTape
      (rulerCap S (S + 1)) ⟨fun i => if S + 1 ≤ i ∧ i ≤ S + 1 then .blank else g i, S + 1⟩
      (.inl .back) .stay (.endMark, .stay) (.blank, .stay) ?_ (by simp [moveHead]) ?_ ?_
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) (by simp; omega)
      (by simp [rulerCap]; omega) (by simp; omega)
    · rw [rw_clear_act]; simp [rulerTape]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead, rulerTape, rulerCap]
      funext i
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases hi : i = S + 1
        · simp [hi]
        · have : ¬ i ≤ S ∨ i ≤ S := by omega
          simp [h0, hi]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead]
      funext i
      by_cases hi : i = S + 1
      · simp [hi]
      · have : ¬ (S + 1 ≤ i ∧ i ≤ S + 1) := by omega
        simp [hi, this]
  | succ d ih' =>
    intro c g hc h1
    have hcS : c ≤ S := by omega
    have hc0 : c ≠ 0 := by omega
    have hStep := rw_step_one D input B .clear ih ih (rulerTape S c) ⟨g, c⟩ fixedTape
      (rulerTape S (c + 1)) ⟨fun i => if i = c then .blank else g i, c + 1⟩
      (.inl .clear) .stay (.bit true, .right) (.blank, .right) ?_ (by simp [moveHead]) ?_ ?_
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) (by simp; omega)
      (by simp [rulerTape]; omega) (by simp; omega)
    · refine hStep.trans ?_
      have := ih' (c + 1) (fun i => if i = c then .blank else g i) (by omega) (by omega)
      convert this using 4
      funext i
      by_cases h : i = c <;> by_cases h2 : c + 1 ≤ i <;> by_cases h3 : c ≤ i <;> simp [h, h2, h3] <;>
        omega
    · rw [rw_clear_act]; simp [rulerTape, hcS, hc0]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead, rulerTape]
      funext i
      by_cases h0 : i = 0
      · simp [h0]; omega
      · by_cases hi : i = c
        · simp [hi, h0, hcS, hc0]
        · simp [hi, h0]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead]

theorem rw_back {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (ih : Fin (n + 2)) (S B : ℕ) (hB : S + 1 < B)
    (g : ℕ → SimSym) :
    ∀ c, c ≤ S + 1 →
      RWRun (rwComp D) input B ⟨.inl .back, ih, tapes5 (rulerCap S c) ⟨g, c⟩ fixedTape⟩
        ⟨.inr (), ih, tapes5 (rulerCap S 1) ⟨g, 1⟩ fixedTape⟩ := by
  intro c
  induction c with
  | zero =>
    intro _
    refine rw_step_one D input B .back ih ih (rulerCap S 0) ⟨g, 0⟩ fixedTape
      (rulerCap S 1) ⟨g, 1⟩ (.inr ()) .stay (.leftMark, .right) (g 0, .right) ?_
      (by simp [moveHead]) ?_ ?_
      (by simp [fixedTape]; omega) (by simp [rulerCap]; omega) (by simp; omega)
      (by simp [rulerCap]; omega) (by simp; omega)
    · rw [rw_back_act]; simp [rulerCap]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead, rulerCap]
      funext i; by_cases hi : i = 0 <;> simp [hi]
    · simp [OneSidedTape.updateAndMove, moveOneSidedHead]
      funext i; by_cases hi : i = 0 <;> simp [hi]
  | succ c ih' =>
    intro hc
    have hStep := rw_step_one D input B .back ih ih (rulerCap S (c + 1)) ⟨g, c + 1⟩ fixedTape
      (rulerCap S c) ⟨g, c⟩ (.inl .back) .stay
      ((rulerCap S (c + 1)).cells (rulerCap S (c + 1)).head, .left) (g (c + 1), .left) ?_
      (by simp [moveHead]) ?_ ?_
      (by simp [fixedTape]; omega) (by simp [rulerCap]; omega) (by simp; omega)
      (by simp [rulerCap]; omega) (by simp; omega)
    · exact hStep.trans (ih' (by omega))
    · rw [rw_back_act]; simp [rulerCap]
      intro h; split_ifs at h <;> simp at h
    · simpa [rulerCap] using write_same_move (rulerCap S (c + 1)) (mv := .left) (h' := c)
        (by simp [rulerCap, moveOneSidedHead])
    · simpa using write_same_move (⟨g, c + 1⟩ : OneSidedTape SimSym) (mv := .left) (h' := c)
        (by simp [moveOneSidedHead])

/-- The good-step relation of `HaltsScanningExactly`. -/
abbrev DGood {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (S : ℕ) :=
  fun a b : OneSidedTMConfig QD SimSym 1 n =>
    D.oneSidedStep input a b ∧ a.HeadsWithin S ∧ b.HeadsWithin S

theorem step_head_le {T T' : OneSidedTape SimSym} {w : SimSym} {mv : TapeMove}
    (h : T.updateAndMove w mv = some T') : T'.head ≤ T.head + 1 := by
  obtain ⟨h', hm, rfl⟩ := updateAndMove_eq h
  cases mv <;> simp [moveOneSidedHead] at hm <;> simp <;> omega

theorem rw_sim_path {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (S B : ℕ) (hB : S + 1 < B)
    {a b : OneSidedTMConfig QD SimSym 1 n}
    (hab : Relation.ReflTransGen (DGood D input S) a b) (m : ℕ)
    (hm : (a.workTapes 0).head ≤ m) (hmS : m ≤ S) :
    ∃ m', RWRun (rwComp D) input B (rwCfg a m) (rwCfg b m') ∧ m ≤ m' ∧
      (a ≠ b → (a.workTapes 0).head + 1 ≤ m') ∧ (b.workTapes 0).head ≤ m' ∧ m' ≤ S := by
  induction hab with
  | refl => exact ⟨m, Relation.ReflTransGen.refl, le_rfl, fun h => absurd rfl h, hm, hmS⟩
  | @tail b c hab hbc ih =>
    obtain ⟨m', hRun, hmm, hne, hbm, hm'S⟩ := ih
    obtain ⟨hstep, hb, hc⟩ := hbc
    have hb0 := hb 0
    have hbS : (b.workTapes 0).head + 1 ≤ S := by omega
    have hcs := rw_sim_step D input hstep m' hbm
    have hHead : (c.workTapes 0).head ≤ (b.workTapes 0).head + 1 := by
      obtain ⟨_, _, _, _, _, _, hup⟩ := hstep
      exact step_head_le (hup 0)
    have hcl : (c.workTapes 0).head ≤ max m' ((b.workTapes 0).head + 1) := by
      have := hHead
      omega
    refine ⟨max m' ((b.workTapes 0).head + 1), ?_, le_trans hmm (le_max_left _ _), ?_, hcl,
      max_le hm'S hbS⟩
    · refine hRun.tail ⟨hcs, ?_, ?_⟩
      · exact tapes5_head_lt _ _ _ _ (by simp [rwCfg, rulerTape]; omega)
          (by simp [rwCfg, scratchTape]; omega) (by simp [fixedTape]; omega)
      · exact tapes5_head_lt _ _ _ _ (by
          have := hc 0
          simp [rwCfg, rulerTape]; omega)
          (by have := hc 0; simp [rwCfg, scratchTape]; omega) (by simp [fixedTape]; omega)
    · intro hac
      by_cases hab' : a = b
      · subst hab'; exact le_trans (by omega) (le_max_right _ _)
      · exact le_trans (hne hab') (le_max_left _ _)

theorem dgood_blank {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    {n : ℕ} (input : Fin n → I) (S : ℕ)
    {a b : OneSidedTMConfig QD SimSym 1 n}
    (hab : Relation.ReflTransGen (DGood D input S) a b)
    (ha : ∀ i, S ≤ i → (a.workTapes 0).cells i = .blank) :
    ∀ i, S ≤ i → (b.workTapes 0).cells i = .blank := by
  induction hab with
  | refl => exact ha
  | @tail b c _ hbc ih =>
    obtain ⟨hstep, hb, _⟩ := hbc
    obtain ⟨_, _, _, _, _, _, hup⟩ := hstep
    obtain ⟨h', _, hT⟩ := updateAndMove_eq (hup 0)
    intro i hi
    have hb0 := hb 0
    rw [hT]
    have : i ≠ (b.workTapes 0).head := by omega
    simp [this, ih i hi]

theorem rulerCap_matches (S : ℕ) :
    TapeMatches (rulerCap S 1)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
  refine ⟨rfl, fun i => ?_⟩
  simp only [rulerCap]
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i ≤ S
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have e : (SimSym.leftMark :: List.replicate S (SimSym.bit true) ++
          [SimSym.endMark])[j+1]? = some (SimSym.bit true) := by
        rw [List.cons_append, List.getElem?_cons_succ,
          List.getElem?_append_left (by simpa using by omega)]
        simp [List.getElem?_replicate]; omega
      rw [e]; simp [h1]
    · by_cases h2 : i = S + 1
      · subst h2
        simp [List.getElem?_append]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have e : (SimSym.leftMark :: List.replicate S (SimSym.bit true) ++
            [SimSym.endMark])[j+1]? = none := by
          rw [List.getElem?_eq_none]; simp; omega
        rw [e]; simp [h1, h2]; omega

theorem fixedTape_matches : TapeMatches fixedTape [.leftMark] 1 := by
  refine ⟨rfl, fun i => ?_⟩
  by_cases h0 : i = 0
  · simp [fixedTape, h0]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [fixedTape]

/-- A measuring machine over `SimSym` yields a prefix that builds the clean simulator tapes. -/
theorem rw_prefix {QD I : Type} [Fintype QD] [Fintype I] (D : MultitapeDTM QD I SimSym 1)
    (hBlank : D.blank = .blank) {n : ℕ} (input : Fin n → I) (S : ℕ) (hS : 1 ≤ S) (B : ℕ)
    (hB : S + 1 < B) (hHalt : D.HaltsScanningExactly input S) :
    ∃ (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2)),
      PrefixPrepares (rwComp D) input S B initTapes inHead := by
  obtain ⟨final, hRun, hNone, hMidEx⟩ := hHalt
  obtain ⟨mid, hMidRun, hMidHead⟩ := hMidEx (by omega)
  have hU : Relator.RightUnique (DGood D input S) :=
    fun a b c h1 h2 => D.oneSidedStep_deterministic input h1.1 h2.1
  have hMF : Relation.ReflTransGen (DGood D input S) mid final := by
    rcases Relation.ReflTransGen.total_of_right_unique hU hMidRun hRun with h | h
    · exact h
    · rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hs, _⟩
      · rw [h']
      · exfalso
        obtain ⟨a, ha, _⟩ := hs.1
        simp [MultitapeDTM.toNTM, hNone] at ha
  have hb : D.toNTM.blank = .blank := hBlank
  have hInitBlank : ∀ i, S ≤ i →
      (D.toNTM.oneSidedInitialConfig (n := n).workTapes 0).cells i = .blank := by
    intro i _
    simp [MultitapeNTM.oneSidedInitialConfig, hb]
  have hFinBlank := dgood_blank D input S hRun hInitBlank
  have hInitHead : ((D.toNTM.oneSidedInitialConfig (n := n)).workTapes 0).head = 0 := rfl
  have hfS : (final.workTapes 0).head < S := by
    rcases Relation.ReflTransGen.cases_tail hRun with h | ⟨c, _, hc⟩
    · subst h; simp [MultitapeNTM.oneSidedInitialConfig]; omega
    · exact hc.2.2 0
  -- preamble
  have hPre : RWRun (rwComp D) input B
      ⟨.inl .pre, ⟨0, by omega⟩, fun _ => ⟨fun _ => .blank, 0⟩⟩
      (rwCfg (D.toNTM.oneSidedInitialConfig) 0) := by
    refine Relation.ReflTransGen.single ⟨rw_pre_step D input hBlank, ?_, ?_⟩
    · intro t; simp; omega
    · intro t
      simp only [rwCfg]
      exact tapes5_head_lt _ _ _ _ (by simp [rulerTape, MultitapeNTM.oneSidedInitialConfig]; omega)
        (by simp [scratchTape, MultitapeNTM.oneSidedInitialConfig]; omega)
        (by simp [fixedTape]; omega) t
  obtain ⟨m1, hR1, _, _, hm1, hm1S⟩ :=
    rw_sim_path D input S B hB hMidRun 0 (by simp [MultitapeNTM.oneSidedInitialConfig]) (by omega)
  obtain ⟨m2, hR2, _, hne2, hm2, hm2S⟩ := rw_sim_path D input S B hB hMF m1 hm1 hm1S
  have hMark := rw_mark_step D input (c := final)
    hNone m2 hm2
  have hm3 : max m2 ((final.workTapes 0).head + 1) = S := by
    have hle : max m2 ((final.workTapes 0).head + 1) ≤ S := max_le hm2S (by omega)
    have hge : S ≤ max m2 ((final.workTapes 0).head + 1) := by
      by_cases hmf : mid = final
      · subst hmf; omega
      · have := hne2 hmf; omega
    omega
  rw [hm3] at hMark
  have hMarkRun : RWRun (rwComp D) input B (rwCfg final m2)
      ⟨.inl .goLeft, final.inputHead,
        tapes5 (rulerTape S ((final.workTapes 0).head + 1)) (scratchTape (final.workTapes 0))
          fixedTape⟩ := by
    refine Relation.ReflTransGen.single ⟨hMark, ?_, ?_⟩
    · intro t
      exact tapes5_head_lt _ _ _ _ (by simp [rwCfg, rulerTape]; omega)
        (by simp [rwCfg, scratchTape]; omega) (by simp [fixedTape]; omega) t
    · intro t
      exact tapes5_head_lt _ _ _ _ (by simp [rulerTape]; omega)
        (by simp [scratchTape]; omega) (by simp [fixedTape]; omega) t
  have hGo := rw_goLeft D input final.inputHead S B hB (scratchTape (final.workTapes 0)).cells
    ((final.workTapes 0).head + 1) (by omega)
  have hClear := rw_clear D input final.inputHead S B hB S 1
    (scratchTape (final.workTapes 0)).cells (by omega) le_rfl
  have hBack := rw_back D input final.inputHead S B hB
    (fun i => if 1 ≤ i ∧ i ≤ S + 1 then .blank else (scratchTape (final.workTapes 0)).cells i)
    (S + 1) le_rfl
  have hTotal := hPre.trans (hR1.trans (hR2.trans (hMarkRun.trans
    (hGo.trans (hClear.trans hBack)))))
  refine ⟨tapes5 (rulerCap S 1)
    ⟨fun i => if 1 ≤ i ∧ i ≤ S + 1 then .blank else (scratchTape (final.workTapes 0)).cells i, 1⟩
    fixedTape, final.inputHead, hTotal, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [tapes5] using rulerCap_matches S
  · simpa [tapes5, tRegs, tRuler, tScratch] using fixedTape_matches
  · simpa [tapes5, tArgA, tRuler, tScratch] using fixedTape_matches
  · simpa [tapes5, tArgB, tRuler, tScratch] using fixedTape_matches
  · have : tapes5 (rulerCap S 1)
        ⟨fun i => if 1 ≤ i ∧ i ≤ S + 1 then .blank
          else (scratchTape (final.workTapes 0)).cells i, 1⟩ fixedTape tScratch =
        ⟨fun i => if 1 ≤ i ∧ i ≤ S + 1 then .blank
          else (scratchTape (final.workTapes 0)).cells i, 1⟩ := by simp [tapes5, tScratch, tRuler]
    rw [this]
    refine ⟨rfl, fun i => ?_⟩
    by_cases h0 : i = 0
    · simp [h0, scratchTape]
    · by_cases hi : i ≤ S + 1
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp [hi]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have := hFinBlank j (by omega)
        simp [scratchTape, hi, this]

end SavitchLemma

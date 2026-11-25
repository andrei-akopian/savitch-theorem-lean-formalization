module

public import Mathlib.Data.Fintype.Sum
public import SavitchLemma.Model.MachineModel

@[expose] public section

/-!
# Structured deterministic Turing machine components

This module provides composable finite-state components (`TMComponent`) that
compile directly to `MultitapeDTM`, together with bounded-space reachability
lemmas (`ReachesExit`) for sequential composition, branching, and bounded loops.
-/

namespace SavitchLemma

/-- Map the next-state type of a `TMAction`. -/
def TMAction.mapState {Q₁ Q₂ Γ : Type*} {k : ℕ} (f : Q₁ → Q₂)
    (action : TMAction Q₁ Γ k) : TMAction Q₂ Γ k where
  nextState := f action.nextState
  inputMove := action.inputMove
  write := action.write
  workMove := action.workMove

/-- Map the tape indices of a `TMAction` into a larger machine, leaving all
other work tapes untouched (`stay`, rewriting the scanned symbol). -/
def TMAction.liftTapes {Q Γ : Type*} {k₁ k₂ : ℕ} (inj : Fin k₁ → Fin k₂)
    (action : TMAction Q Γ k₁) (scanned : Fin k₂ → Γ) : TMAction Q Γ k₂ where
  nextState := action.nextState
  inputMove := action.inputMove
  write t₂ :=
    match (List.finRange k₁).find? (fun t₁ : Fin k₁ => decide (inj t₁ = t₂)) with
    | some t₁ => action.write t₁
    | none => scanned t₂
  workMove t₂ :=
    match (List.finRange k₁).find? (fun t₁ : Fin k₁ => decide (inj t₁ = t₂)) with
    | some t₁ => action.workMove t₁
    | none => .stay

/-- A composable deterministic Turing machine component: every internal state
executes one `TMAction` and transitions either to another internal state or to
an exit value in `Exit`. -/
structure TMComponent (Q InputAlphabet Γ : Type*) (k : ℕ) (Exit : Type*) where
  start : Q
  step : Q → InputSymbol InputAlphabet → (Fin k → Γ) → TMAction (Q ⊕ Exit) Γ k

/-- A `TMComponent` with its state type and `Fintype` instance existentially packaged,
hiding deep `Sum`/`Prod` state trees so downstream `Fintype` synthesis is O(1). -/
structure SealedTMComponent (InputAlphabet Γ : Type*) (k : ℕ) (Exit : Type*) where
  State : Type*
  [fintype : Fintype State]
  comp : TMComponent State InputAlphabet Γ k Exit

attribute [instance] SealedTMComponent.fintype

/-- One step of a `TMComponent` on one-sided work tapes, with states in
`Q ⊕ Exit` where exit states have no outgoing transitions. -/
def TMComponent.CompStep {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (cfg next : OneSidedTMConfig (Q ⊕ Exit) Γ k n) : Prop :=
  ∃ q : Q, cfg.state = .inl q ∧
    let action := M.step q (readInput input cfg.inputHead) cfg.scannedWork
    next.state = action.nextState ∧
    ∃ inputHead, moveHead (n + 2) cfg.inputHead action.inputMove = some inputHead ∧
      next.inputHead = inputHead ∧
      ∀ tape : Fin k,
        (cfg.workTapes tape).updateAndMove (action.write tape) (action.workMove tape) =
          some (next.workTapes tape)

/-- `M` executes from `initInHead, initTapes` to `e, finalInHead, finalTapes`
while keeping every work-tape head strictly below `bound t`. -/
def TMComponent.ReachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (input : Fin n → InputAlphabet)
    (bound : Fin k → ℕ)
    (initTapes : Fin k → OneSidedTape Γ) (initInHead : Fin (n + 2))
    (e : Exit) (finalTapes : Fin k → OneSidedTape Γ) (finalInHead : Fin (n + 2)) : Prop :=
  Relation.ReflTransGen
    (fun a b => M.CompStep input a b ∧
      (∀ t, (a.workTapes t).head < bound t) ∧
      (∀ t, (b.workTapes t).head < bound t))
    ⟨.inl M.start, initInHead, initTapes⟩
    ⟨.inr e, finalInHead, finalTapes⟩

/-- Monotonicity of `ReachesExit` in the per-tape head bound. -/
theorem TMComponent.ReachesExit.mono {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    {M : TMComponent Q InputAlphabet Γ k Exit} {input : Fin n → InputAlphabet}
    {bound bound' : Fin k → ℕ} (hB : ∀ t, bound t ≤ bound' t)
    {initTapes finalTapes : Fin k → OneSidedTape Γ} {initInHead finalInHead : Fin (n + 2)}
    {e : Exit}
    (hR : M.ReachesExit input bound initTapes initInHead e finalTapes finalInHead) :
    M.ReachesExit input bound' initTapes initInHead e finalTapes finalInHead := by
  have key : ∀ cfg,
      Relation.ReflTransGen
        (fun a b => M.CompStep input a b ∧
          (∀ t, (a.workTapes t).head < bound t) ∧
          (∀ t, (b.workTapes t).head < bound t))
        ⟨.inl M.start, initInHead, initTapes⟩ cfg →
      Relation.ReflTransGen
        (fun a b => M.CompStep input a b ∧
          (∀ t, (a.workTapes t).head < bound' t) ∧
          (∀ t, (b.workTapes t).head < bound' t))
        ⟨.inl M.start, initInHead, initTapes⟩ cfg := by
    intro cfg h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h ih =>
      exact ih.tail ⟨h.1, fun t => lt_of_lt_of_le (h.2.1 t) (hB t),
        fun t => lt_of_lt_of_le (h.2.2 t) (hB t)⟩
  exact key _ hR

/-- Single bounded step of a `TMComponent` from internal state `q` to `nextState`. -/
theorem TMComponent.step_one {Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (q : Q) (inHead nextInHead : Fin (n + 2))
    (tapes nextTapes : Fin k → OneSidedTape Γ)
    (nextState : Q ⊕ Exit)
    (hNextState : (M.step q (readInput input inHead)
      (fun t => (tapes t).cells (tapes t).head)).nextState = nextState)
    (hIn : moveHead (n + 2) inHead
      (M.step q (readInput input inHead)
        (fun t => (tapes t).cells (tapes t).head)).inputMove = some nextInHead)
    (hTapes : ∀ t, (tapes t).updateAndMove
      ((M.step q (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).write t)
      ((M.step q (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).workMove t) =
      some (nextTapes t))
    (hBounds : ∀ t, (tapes t).head < bound t)
    (hNextBounds : ∀ t, (nextTapes t).head < bound t) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ t, (a.workTapes t).head < bound t) ∧
        (∀ t, (b.workTapes t).head < bound t))
      ⟨.inl q, inHead, tapes⟩ ⟨nextState, nextInHead, nextTapes⟩ :=
  Relation.ReflTransGen.single ⟨⟨q, rfl, hNextState.symm, nextInHead, hIn, rfl, hTapes⟩, hBounds, hNextBounds⟩

/-- Map the exit values of a component. -/
def TMComponent.mapExit {Q InputAlphabet Γ : Type*} {k : ℕ} {Exit₁ Exit₂ : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit₁) (f : Exit₁ → Exit₂) :
    TMComponent Q InputAlphabet Γ k Exit₂ where
  start := M.start
  step q inSym workSyms :=
    (M.step q inSym workSyms).mapState (Sum.map id f)

/-- Relabel the internal state type of a `TMComponent` along an equivalence `e : Q ≃ Q'`.
Used to seal large nested `Sum`/`Prod` state types behind a named `structure` with a
cached `Fintype` instance. -/
def TMComponent.relabel {Q Q' InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (e : Q ≃ Q') :
    TMComponent Q' InputAlphabet Γ k Exit where
  start := e M.start
  step q' inSym workSyms := (M.step (e.symm q') inSym workSyms).mapState (Sum.map e id)

/-- Single-step atomic component. -/
def TMComponent.atom {InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → (Fin k → Γ) → TMAction Exit Γ k) :
    TMComponent Unit InputAlphabet Γ k Exit where
  start := ()
  step _ inSym workSyms := (f inSym workSyms).mapState Sum.inr

/-- Sequential composition where the first component has `Unit` exit. -/
def TMComponent.seq {Q₁ Q₂ InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k Unit)
    (M₂ : TMComponent Q₂ InputAlphabet Γ k Exit) :
    TMComponent (Q₁ ⊕ Q₂) InputAlphabet Γ k Exit where
  start := .inl M₁.start
  step s inSym workSyms :=
    match s with
    | .inl q₁ =>
      (M₁.step q₁ inSym workSyms).mapState fun
        | .inl q₁' => .inl (.inl q₁')
        | .inr () => .inl (.inr M₂.start)
    | .inr q₂ =>
      (M₂.step q₂ inSym workSyms).mapState fun
        | .inl q₂' => .inl (.inr q₂')
        | .inr e => .inr e

/-- Branching composition after a `Bool`-valued test component. -/
def TMComponent.branch {Q₀ Q₁ Q₂ InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (M₀ : TMComponent Q₀ InputAlphabet Γ k Bool)
    (MTrue : TMComponent Q₁ InputAlphabet Γ k Exit)
    (MFalse : TMComponent Q₂ InputAlphabet Γ k Exit) :
    TMComponent (Q₀ ⊕ Q₁ ⊕ Q₂) InputAlphabet Γ k Exit where
  start := .inl M₀.start
  step s inSym workSyms :=
    match s with
    | .inl q₀ =>
      (M₀.step q₀ inSym workSyms).mapState fun
        | .inl q₀' => .inl (.inl q₀')
        | .inr true => .inl (.inr (.inl MTrue.start))
        | .inr false => .inl (.inr (.inr MFalse.start))
    | .inr (.inl q₁) =>
      (MTrue.step q₁ inSym workSyms).mapState fun
        | .inl q₁' => .inl (.inr (.inl q₁'))
        | .inr e => .inr e
    | .inr (.inr q₂) =>
      (MFalse.step q₂ inSym workSyms).mapState fun
        | .inl q₂' => .inl (.inr (.inr q₂'))
        | .inr e => .inr e

/-- Repeat a body component while it exits with `.inl ()`, terminating when it
exits with `.inr e`. -/
def TMComponent.loop {Q InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k (Unit ⊕ Exit)) :
    TMComponent Q InputAlphabet Γ k Exit where
  start := M.start
  step q inSym workSyms :=
    (M.step q inSym workSyms).mapState fun
      | .inl q' => .inl q'
      | .inr (.inl ()) => .inl M.start
      | .inr (.inr e) => .inr e

/-- Compile a `Bool`-exiting component into a `MultitapeDTM` whose accepting
state is `.inr true` and whose halted states are `.inr b`. -/
def TMComponent.toDTM {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ) :
    MultitapeDTM (Q ⊕ Bool) InputAlphabet Γ k where
  startState := .inl M.start
  blank := blank
  accepting s := s = .inr true
  transition s inSym workSyms :=
    match s with
    | .inl q => some (M.step q inSym workSyms)
    | .inr _ => none

private theorem map_compStep {Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit₁ Exit₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k Exit₁)
    (M₂ : TMComponent Q₂ InputAlphabet Γ k Exit₂)
    (input : Fin n → InputAlphabet)
    (f : Q₁ ⊕ Exit₁ → Q₂ ⊕ Exit₂)
    (hCompat : ∀ q inSym workSyms,
      ∃ q', f (.inl q) = .inl q' ∧
        M₂.step q' inSym workSyms = (M₁.step q inSym workSyms).mapState f)
    {cfg next : OneSidedTMConfig (Q₁ ⊕ Exit₁) Γ k n}
    (hStep : M₁.CompStep input cfg next) :
    M₂.CompStep input ⟨f cfg.state, cfg.inputHead, cfg.workTapes⟩
      ⟨f next.state, next.inputHead, next.workTapes⟩ := by
  rcases hStep with ⟨q, hState, hNextState, inputHead, hMove, hInHead, hTapes⟩
  obtain ⟨q', hFState, hMStep⟩ := hCompat q (readInput input cfg.inputHead) cfg.scannedWork
  have hScanned :
      ({ state := f cfg.state, inputHead := cfg.inputHead, workTapes := cfg.workTapes } :
        OneSidedTMConfig (Q₂ ⊕ Exit₂) Γ k n).scannedWork = cfg.scannedWork := rfl
  refine ⟨q', ?_, ?_, inputHead, ?_, hInHead, ?_⟩
  · simp [hState, hFState]
  · change f next.state = (M₂.step q' (readInput input cfg.inputHead) cfg.scannedWork).nextState
    rw [hMStep, hNextState]
    rfl
  · rw [hScanned, hMStep]
    exact hMove
  · rw [hScanned, hMStep]
    exact hTapes

private theorem lift_refTransGen_map {Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit₁ Exit₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k Exit₁)
    (M₂ : TMComponent Q₂ InputAlphabet Γ k Exit₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (f : Q₁ ⊕ Exit₁ → Q₂ ⊕ Exit₂)
    (hCompat : ∀ q inSym workSyms,
      ∃ q', f (.inl q) = .inl q' ∧
        M₂.step q' inSym workSyms = (M₁.step q inSym workSyms).mapState f)
    {a b : OneSidedTMConfig (Q₁ ⊕ Exit₁) Γ k n}
    (hRun : Relation.ReflTransGen
      (fun x y => M₁.CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t)) a b) :
    Relation.ReflTransGen
      (fun x y => M₂.CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t))
      ⟨f a.state, a.inputHead, a.workTapes⟩
      ⟨f b.state, b.inputHead, b.workTapes⟩ := by
  induction hRun with
  | refl => exact Relation.ReflTransGen.refl
  | @tail prev curr _ hStep ih =>
    refine Relation.ReflTransGen.tail ih ⟨?_, hStep.2.1, hStep.2.2⟩
    exact map_compStep M₁ M₂ input f hCompat hStep.1

/-- `atom` reaches exit `action.nextState` in a single step whenever the moves
succeed and the heads remain below `bound`. -/
theorem TMComponent.atom_reachesExit {InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → (Fin k → Γ) → TMAction Exit Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape Γ) (inHead : Fin (n + 2))
    (hHeads : ∀ t, (tapes t).head < bound t)
    (nextInHead : Fin (n + 2))
    (hInMove : moveHead (n + 2) inHead
      (f (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).inputMove =
        some nextInHead)
    (nextTapes : Fin k → OneSidedTape Γ)
    (hWorkMoves : ∀ t,
      (tapes t).updateAndMove
        ((f (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).write t)
        ((f (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).workMove t) =
          some (nextTapes t))
    (hNextHeads : ∀ t, (nextTapes t).head < bound t) :
    (TMComponent.atom f).ReachesExit input bound tapes inHead
      (f (readInput input inHead) (fun t => (tapes t).cells (tapes t).head)).nextState
      nextTapes nextInHead := by
  refine Relation.ReflTransGen.single ⟨?_, hHeads, hNextHeads⟩
  refine ⟨(), rfl, rfl, nextInHead, hInMove, rfl, hWorkMoves⟩

/-- `mapExit` preserves `ReachesExit` while transforming the exit value. -/
theorem TMComponent.mapExit_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit₁ Exit₂ : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit₁) (f : Exit₁ → Exit₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ : Fin k → OneSidedTape Γ} {in₀ in₁ : Fin (n + 2)} {e : Exit₁}
    (hRun : M.ReachesExit input bound tapes₀ in₀ e tapes₁ in₁) :
    (M.mapExit f).ReachesExit input bound tapes₀ in₀ (f e) tapes₁ in₁ := by
  exact lift_refTransGen_map M (M.mapExit f) input bound (Sum.map id f)
    (fun q _ _ => ⟨q, rfl, rfl⟩) hRun

/-- Sequential composition of `ReachesExit`. -/
theorem TMComponent.seq_reachesExit {Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k Unit)
    (M₂ : TMComponent Q₂ InputAlphabet Γ k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ tapes₂ : Fin k → OneSidedTape Γ} {in₀ in₁ in₂ : Fin (n + 2)}
    {e : Exit}
    (h₁ : M₁.ReachesExit input bound tapes₀ in₀ () tapes₁ in₁)
    (h₂ : M₂.ReachesExit input bound tapes₁ in₁ e tapes₂ in₂) :
    (M₁.seq M₂).ReachesExit input bound tapes₀ in₀ e tapes₂ in₂ := by
  have hLifted₁ := lift_refTransGen_map M₁ (M₁.seq M₂) input bound
    (fun | .inl q₁ => .inl (.inl q₁) | .inr () => .inl (.inr M₂.start))
    (fun q₁ _ _ => ⟨.inl q₁, rfl, rfl⟩) h₁
  have hLifted₂ := lift_refTransGen_map M₂ (M₁.seq M₂) input bound
    (fun | .inl q₂ => .inl (.inr q₂) | .inr e => .inr e)
    (fun q₂ _ _ => ⟨.inr q₂, rfl, rfl⟩) h₂
  exact hLifted₁.trans hLifted₂

/-- Relabeling the state type preserves `ReachesExit`. -/
theorem TMComponent.relabel_reachesExit {Q Q' InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k Exit) (e : Q ≃ Q')
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ : Fin k → OneSidedTape Γ} {in₀ in₁ : Fin (n + 2)} {exitVal : Exit}
    (h : M.ReachesExit input bound tapes₀ in₀ exitVal tapes₁ in₁) :
    (M.relabel e).ReachesExit input bound tapes₀ in₀ exitVal tapes₁ in₁ :=
  lift_refTransGen_map M (M.relabel e) input bound (Sum.map e id)
    (fun q _ _ => ⟨e q, rfl, by simp [TMComponent.relabel]⟩) h

/-- Branching composition of `ReachesExit`. -/
theorem TMComponent.branch_reachesExit {Q₀ Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit : Type*}
    (M₀ : TMComponent Q₀ InputAlphabet Γ k Bool)
    (MTrue : TMComponent Q₁ InputAlphabet Γ k Exit)
    (MFalse : TMComponent Q₂ InputAlphabet Γ k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ tapes₂ : Fin k → OneSidedTape Γ} {in₀ in₁ in₂ : Fin (n + 2)}
    (b : Bool) {e : Exit}
    (h₀ : M₀.ReachesExit input bound tapes₀ in₀ b tapes₁ in₁)
    (hBranch : if b then MTrue.ReachesExit input bound tapes₁ in₁ e tapes₂ in₂
      else MFalse.ReachesExit input bound tapes₁ in₁ e tapes₂ in₂) :
    (M₀.branch MTrue MFalse).ReachesExit input bound tapes₀ in₀ e tapes₂ in₂ := by
  have hLifted₀ := lift_refTransGen_map M₀ (M₀.branch MTrue MFalse) input bound
    (fun
      | .inl q₀ => .inl (.inl q₀)
      | .inr true => .inl (.inr (.inl MTrue.start))
      | .inr false => .inl (.inr (.inr MFalse.start)))
    (fun q₀ _ _ => ⟨.inl q₀, rfl, rfl⟩) h₀
  cases b with
  | true =>
    have hLifted₁ := lift_refTransGen_map MTrue (M₀.branch MTrue MFalse) input bound
      (fun | .inl q₁ => .inl (.inr (.inl q₁)) | .inr e => .inr e)
      (fun q₁ _ _ => ⟨.inr (.inl q₁), rfl, rfl⟩) hBranch
    exact hLifted₀.trans hLifted₁
  | false =>
    have hLifted₂ := lift_refTransGen_map MFalse (M₀.branch MTrue MFalse) input bound
      (fun | .inl q₂ => .inl (.inr (.inr q₂)) | .inr e => .inr e)
      (fun q₂ _ _ => ⟨.inr (.inr q₂), rfl, rfl⟩) hBranch
    exact hLifted₀.trans hLifted₂

/-- Well-founded loop execution preserving a loop invariant and head bounds. -/
theorem TMComponent.loop_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    {Exit : Type*}
    (M : TMComponent Q InputAlphabet Γ k (Unit ⊕ Exit))
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (Inv : (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (measure : (Fin k → OneSidedTape Γ) → Fin (n + 2) → ℕ)
    (Post : Exit → (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (hStep : ∀ tapes inHead, Inv tapes inHead →
      (∃ tapes' inHead',
        M.ReachesExit input bound tapes inHead (.inl ()) tapes' inHead' ∧
        Inv tapes' inHead' ∧ measure tapes' inHead' < measure tapes inHead) ∨
      (∃ e tapes' inHead',
        M.ReachesExit input bound tapes inHead (.inr e) tapes' inHead' ∧
        Post e tapes' inHead')) :
    ∀ tapes inHead, Inv tapes inHead →
      ∃ e tapes' inHead',
        (M.loop).ReachesExit input bound tapes inHead e tapes' inHead' ∧
        Post e tapes' inHead' := by
  intro tapes inHead hInv
  have hWF : ∀ m tapes inHead, measure tapes inHead = m → Inv tapes inHead →
      ∃ e tapes' inHead',
        (M.loop).ReachesExit input bound tapes inHead e tapes' inHead' ∧
        Post e tapes' inHead' := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro tapes inHead hm hInvCur
      rcases hStep tapes inHead hInvCur with
        ⟨tapesMid, inMid, hCont, hInvMid, hDec⟩ | ⟨e, tapesEnd, inEnd, hDone, hPost⟩
      · have hLifted := lift_refTransGen_map M M.loop input bound
          (fun | .inl q => .inl q | .inr (.inl ()) => .inl M.start | .inr (.inr e) => .inr e)
          (fun q _ _ => ⟨q, rfl, rfl⟩) hCont
        have hm' : measure tapesMid inMid < m := hm ▸ hDec
        obtain ⟨e, tapesEnd, inEnd, hRest, hPost⟩ :=
          ih (measure tapesMid inMid) hm' tapesMid inMid rfl hInvMid
        exact ⟨e, tapesEnd, inEnd, hLifted.trans hRest, hPost⟩
      · have hLifted := lift_refTransGen_map M M.loop input bound
          (fun | .inl q => .inl q | .inr (.inl ()) => .inl M.start | .inr (.inr e) => .inr e)
          (fun q _ _ => ⟨q, rfl, rfl⟩) hDone
        exact ⟨e, tapesEnd, inEnd, hLifted, hPost⟩
  exact hWF (measure tapes inHead) tapes inHead rfl hInv

/-- Any halted exit configuration of a `Bool`-exiting component has no outgoing
transition in `toDTM`. -/
theorem TMComponent.toDTM_exit_stuck {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ)
    (input : Fin n → InputAlphabet) (b : Bool)
    {cfg next : OneSidedTMConfig (Q ⊕ Bool) Γ k n}
    (hState : cfg.state = .inr b)
    (hStep : (M.toDTM blank).oneSidedStep input cfg next) : False := by
  rcases hStep with ⟨action, hAction, _⟩
  simp only [MultitapeDTM.toNTM, TMComponent.toDTM, hState] at hAction
  simp at hAction

/-- Deterministic path uniqueness: if two configurations are both reachable from
`start` in a `MultitapeDTM`, and the second has no outgoing step, then the first
must reach the second (in particular it cannot be a different halted state). -/
theorem MultitapeDTM.stuck_reachable_unique {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    {start cfg₁ cfg₂ : OneSidedTMConfig Q Γ k n}
    (h₁ : Relation.ReflTransGen (D.oneSidedStep input) start cfg₁)
    (h₂ : Relation.ReflTransGen (D.oneSidedStep input) start cfg₂)
    (hStuck₁ : ∀ next, ¬ D.oneSidedStep input cfg₁ next)
    (hStuck₂ : ∀ next, ¬ D.oneSidedStep input cfg₂ next) :
    cfg₁ = cfg₂ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on generalizing cfg₂ with
  | refl =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hStep _ => exact (hStuck₁ _ hStep).elim
  | head hStep₁ _ ih =>
    cases h₂ using Relation.ReflTransGen.head_induction_on with
    | refl => exact (hStuck₂ _ hStep₁).elim
    | head hStep₂ hRest₂ =>
      have hEq := D.oneSidedStep_deterministic input hStep₁ hStep₂
      subst hEq
      exact ih hRest₂ hStuck₂

private theorem compRun_to_dtmRun {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {a b : OneSidedTMConfig (Q ⊕ Bool) Γ k n}
    (hRun : Relation.ReflTransGen
      (fun x y => M.CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t)) a b) :
    Relation.ReflTransGen ((M.toDTM blank).oneSidedStep input) a b := by
  induction hRun with
  | refl => exact Relation.ReflTransGen.refl
  | @tail prev curr _ hStep ih =>
    rcases hStep.1 with ⟨q, hState, hNext, inH, hMove, hInH, hTapes⟩
    refine Relation.ReflTransGen.tail ih
      ⟨M.step q (readInput input prev.inputHead) prev.scannedWork, ?_, hNext, inH, hMove, hInH, hTapes⟩
    simp [MultitapeDTM.toNTM, TMComponent.toDTM, hState]

private theorem compRun_to_dtmRun_within {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ) (S : ℕ)
    (hBound : ∀ t, bound t ≤ S)
    {a b : OneSidedTMConfig (Q ⊕ Bool) Γ k n}
    (hRun : Relation.ReflTransGen
      (fun x y => M.CompStep input x y ∧
        (∀ t, (x.workTapes t).head < bound t) ∧
        (∀ t, (y.workTapes t).head < bound t)) a b) :
    Relation.ReflTransGen
      (fun x y => (M.toDTM blank).oneSidedStep input x y ∧ x.HeadsWithin S ∧ y.HeadsWithin S)
      a b := by
  induction hRun with
  | refl => exact Relation.ReflTransGen.refl
  | @tail prev curr _ hStep ih =>
    rcases hStep.1 with ⟨q, hState, hNext, inH, hMove, hInH, hTapes⟩
    refine Relation.ReflTransGen.tail ih ⟨⟨M.step q (readInput input prev.inputHead) prev.scannedWork,
      ?_, hNext, inH, hMove, hInH, hTapes⟩, ?_, ?_⟩
    · simp [MultitapeDTM.toNTM, TMComponent.toDTM, hState]
    · intro t; exact Nat.lt_of_lt_of_le (hStep.2.1 t) (hBound t)
    · intro t; exact Nat.lt_of_lt_of_le (hStep.2.2 t) (hBound t)

/-- If a `Bool`-exiting component reaches `true` within `bound` from the initial
configuration, its compiled `MultitapeDTM` accepts within space `S` (provided
all `bound t ≤ S`). -/
theorem TMComponent.toDTM_acceptsWithin {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ) (S : ℕ)
    (hBound : ∀ t, bound t ≤ S)
    {finalTapes : Fin k → OneSidedTape Γ} {finalInHead : Fin (n + 2)}
    (hReach : M.ReachesExit input bound (fun _ => ⟨fun _ => blank, 0⟩) ⟨0, by omega⟩
      true finalTapes finalInHead) :
    (M.toDTM blank).AcceptsOneSidedWithin input S := by
  let final : OneSidedTMConfig (Q ⊕ Bool) Γ k n :=
    ⟨.inr true, finalInHead, finalTapes⟩
  refine ⟨final, ?_, rfl, ?_⟩
  have hInit : (M.toDTM blank).toNTM.oneSidedInitialConfig (n := n) =
      ⟨.inl M.start, ⟨0, by omega⟩, fun _ => ⟨fun _ => blank, 0⟩⟩ := rfl
  rw [hInit]
  · exact compRun_to_dtmRun_within M blank input bound S hBound hReach
  · have hFinalWithin : final.HeadsWithin S := by
      rcases Relation.ReflTransGen.cases_tail hReach with hEq | ⟨_, _, hLast⟩
      · have hStateEq := congrArg OneSidedTMConfig.state hEq
        cases hStateEq
      · intro t
        exact Nat.lt_of_lt_of_le (hLast.2.2 t) (hBound t)
    exact hFinalWithin

/-- If a `Bool`-exiting component reaches `false` from the initial configuration,
its compiled `MultitapeDTM` never accepts `input`. -/
theorem TMComponent.toDTM_rejects {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k Bool) (blank : Γ)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {finalTapes : Fin k → OneSidedTape Γ} {finalInHead : Fin (n + 2)}
    (hReach : M.ReachesExit input bound (fun _ => ⟨fun _ => blank, 0⟩) ⟨0, by omega⟩
      false finalTapes finalInHead) :
    ¬ (M.toDTM blank).AcceptsOneSided input := by
  intro ⟨accCfg, hAccRun, hAccState⟩
  have hRejRun : Relation.ReflTransGen ((M.toDTM blank).oneSidedStep input)
      (M.toDTM blank).toNTM.oneSidedInitialConfig ⟨.inr false, finalInHead, finalTapes⟩ := by
    change Relation.ReflTransGen ((M.toDTM blank).oneSidedStep input)
      ⟨.inl M.start, ⟨0, by omega⟩, fun _ => ⟨fun _ => blank, 0⟩⟩
      ⟨.inr false, finalInHead, finalTapes⟩
    exact compRun_to_dtmRun M blank input bound hReach
  have hAccStuck : ∀ next, ¬ (M.toDTM blank).oneSidedStep input accCfg next :=
    fun _ h => M.toDTM_exit_stuck blank input true hAccState h
  have hRejStuck : ∀ next,
      ¬ (M.toDTM blank).oneSidedStep input ⟨.inr false, finalInHead, finalTapes⟩ next :=
    fun _ h => M.toDTM_exit_stuck blank input false rfl h
  have hEq := MultitapeDTM.stuck_reachable_unique (M.toDTM blank) input hAccRun hRejRun
    hAccStuck hRejStuck
  have hStateEq := congrArg OneSidedTMConfig.state hEq
  rw [hAccState] at hStateEq
  cases hStateEq

/-- Indexed deterministic execution path of exact length `m`. -/
inductive DtmPath {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet) :
    ℕ → OneSidedTMConfig Q Γ k n → OneSidedTMConfig Q Γ k n → Prop
  | zero (a : OneSidedTMConfig Q Γ k n) : DtmPath D input 0 a a
  | succ {m : ℕ} {a mid b : OneSidedTMConfig Q Γ k n} :
      D.oneSidedStep input a mid → DtmPath D input m mid b → DtmPath D input (m + 1) a b

theorem DtmPath.of_reflTransGen {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    {a b : OneSidedTMConfig Q Γ k n}
    (hRun : Relation.ReflTransGen (D.oneSidedStep input) a b) :
    ∃ m, DtmPath D input m a b := by
  induction hRun using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, DtmPath.zero _⟩
  | head hStep _ ih =>
    rcases ih with ⟨m, hm⟩
    exact ⟨m + 1, DtmPath.succ hStep hm⟩

theorem DtmPath.split {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    {m T : ℕ} {a b c : OneSidedTMConfig Q Γ k n}
    (hm : DtmPath D input m a b) (hT : DtmPath D input T a c) :
    (T ≤ m ∧ DtmPath D input T a c) ∨ (m < T ∧ DtmPath D input (T - m) b c) := by
  by_cases hLe : T ≤ m
  · exact Or.inl ⟨hLe, hT⟩
  · right
    have hGt : m < T := Nat.lt_of_not_ge hLe
    refine ⟨hGt, ?_⟩
    clear hLe
    induction hm generalizing T with
    | zero => simpa using hT
    | @succ m' a mid b hStep₁ hm' ih =>
      cases hT with
      | zero => omega
      | @succ T' _ mid₂ _ hStep₂ hT' =>
        have hEq := D.oneSidedStep_deterministic input hStep₁ hStep₂
        subst hEq
        have hGt' : m' < T' := by omega
        simpa [Nat.succ_sub_succ_eq_sub] using ih hT' hGt'

theorem DtmPath.trans {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (D : MultitapeDTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    {m₁ m₂ : ℕ} {a b c : OneSidedTMConfig Q Γ k n}
    (h₁ : DtmPath D input m₁ a b) (h₂ : DtmPath D input m₂ b c) :
    DtmPath D input (m₁ + m₂) a c := by
  induction h₁ with
  | zero => simpa using h₂
  | @succ m' _ _ _ hStep _ ih =>
    simpa [Nat.succ_add] using DtmPath.succ hStep (ih h₂)

private theorem loop_reachesExit_inl_path {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k (Unit ⊕ Bool)) (blank : Γ)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {initTapes nextTapes : Fin k → OneSidedTape Γ} {initInHead nextInHead : Fin (n + 2)}
    (hRun : M.ReachesExit input bound initTapes initInHead (.inl ()) nextTapes nextInHead) :
    ∃ m, 1 ≤ m ∧
      DtmPath (M.loop.toDTM blank) input m
        ⟨.inl M.start, initInHead, initTapes⟩
        ⟨.inl M.start, nextInHead, nextTapes⟩ ∧
      ∀ j cfg, j ≤ m →
        DtmPath (M.loop.toDTM blank) input j ⟨.inl M.start, initInHead, initTapes⟩ cfg →
        ∃ q, cfg.state = .inl q := by
  let mapS : Q ⊕ (Unit ⊕ Bool) → Q ⊕ Bool
    | .inl q => .inl q
    | .inr (.inl ()) => .inl M.start
    | .inr (.inr b) => .inr b
  let D := M.loop.toDTM blank
  have hStepMap : ∀ {x y : OneSidedTMConfig (Q ⊕ (Unit ⊕ Bool)) Γ k n},
      M.CompStep input x y → (∃ q, y.state = .inl q) ∨ y.state = .inr (.inl ()) →
      D.oneSidedStep input
        ⟨mapS x.state, x.inputHead, x.workTapes⟩
        ⟨mapS y.state, y.inputHead, y.workTapes⟩ ∧
      (∃ q, mapS y.state = .inl q) := by
    intro x y hStep hy
    rcases hStep with ⟨q, hState, hNext, inH, hMove, hInH, hTapes⟩
    have hDtm : D.oneSidedStep input
        ⟨mapS x.state, x.inputHead, x.workTapes⟩
        ⟨mapS y.state, y.inputHead, y.workTapes⟩ := by
      refine ⟨M.loop.step q (readInput input x.inputHead) x.scannedWork, ?_, ?_, inH, ?_, hInH, ?_⟩
      · simp [D, MultitapeDTM.toNTM, TMComponent.toDTM, hState, mapS]
        rfl
      · simp only [TMComponent.loop, TMAction.mapState]
        rw [hNext]
        cases (M.step q (readInput input x.inputHead) x.scannedWork).nextState with
        | inl q' => rfl
        | inr e => cases e with
          | inl u => cases u; rfl
          | inr b => rfl
      · simpa [TMComponent.loop, TMAction.mapState] using hMove
      · simpa [TMComponent.loop, TMAction.mapState] using hTapes
    refine ⟨hDtm, ?_⟩
    rcases hy with ⟨q', hq'⟩ | hUnit
    · exact ⟨q', by simp [mapS, hq']⟩
    · exact ⟨M.start, by simp [mapS, hUnit]⟩
  have hTail : ∀ {a b : OneSidedTMConfig (Q ⊕ (Unit ⊕ Bool)) Γ k n},
      Relation.ReflTransGen
        (fun x y => M.CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      (∃ q, a.state = .inl q) →
      ((∃ q, b.state = .inl q) ∨ b.state = .inr (.inl ())) →
      ∃ m, (a.state ≠ b.state → 1 ≤ m) ∧
        DtmPath D input m
          ⟨mapS a.state, a.inputHead, a.workTapes⟩
          ⟨mapS b.state, b.inputHead, b.workTapes⟩ ∧
        ∀ j cfg, j ≤ m →
          DtmPath D input j ⟨mapS a.state, a.inputHead, a.workTapes⟩ cfg →
          ∃ q, cfg.state = .inl q := by
    intro a b hR
    induction hR with
    | refl =>
      intro ⟨qa, hqa⟩ _
      refine ⟨0, fun hNe => (hNe rfl).elim, DtmPath.zero _, ?_⟩
      intro j cfg hj hDtm
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      cases hDtm
      exact ⟨qa, by simp [mapS, hqa]⟩
    | @tail prev curr _ hStep ih =>
      intro ha hb
      rcases hStep.1 with ⟨qp, hPrevState, _⟩
      obtain ⟨m, _, hmPath, hmInl⟩ := ih ha (Or.inl ⟨qp, hPrevState⟩)
      obtain ⟨hLastStep, _⟩ := hStepMap hStep.1 hb
      refine ⟨m + 1, fun _ => Nat.succ_le_succ (Nat.zero_le m),
        DtmPath.trans D input hmPath (DtmPath.succ hLastStep (DtmPath.zero _)), ?_⟩
      intro j cfg hj hDtm
      by_cases hjm : j ≤ m
      · exact hmInl j cfg hjm hDtm
      · have hEqJ : j = m + 1 := by omega
        subst hEqJ
        rcases DtmPath.split D input hmPath hDtm with ⟨hLe, _⟩ | ⟨_, hRem⟩
        · omega
        · have hOne : DtmPath D input 1
              ⟨mapS prev.state, prev.inputHead, prev.workTapes⟩ cfg := by
            simpa using hRem
          cases hOne with
          | @succ _ _ mid _ hS hZ =>
            cases hZ
            have hMidEq := D.oneSidedStep_deterministic input hS hLastStep
            rw [hMidEq]
            rcases hb with ⟨qc, hqc⟩ | hUnit
            · exact ⟨qc, by simp [mapS, hqc]⟩
            · exact ⟨M.start, by simp [mapS, hUnit]⟩
  obtain ⟨m, hmPos, hmPath, hmInl⟩ :=
    hTail hRun ⟨M.start, rfl⟩ (Or.inr rfl)
  exact ⟨m, hmPos (by simp), hmPath, hmInl⟩

/-- If an invariant `Inv` guarantees that every loop iteration from `Inv`
exits with `.inl ()` preserving `Inv`, then `M.loop.toDTM` never accepts. -/
theorem TMComponent.loop_toDTM_never_accepts {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : TMComponent Q InputAlphabet Γ k (Unit ⊕ Bool)) (blank : Γ)
    (input : Fin n → InputAlphabet)
    (Inv : (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (hInit : Inv (fun _ => ⟨fun _ => blank, 0⟩) ⟨0, by omega⟩)
    (hStep : ∀ tapes inHead, Inv tapes inHead →
      ∃ bound tapes' inHead',
        M.ReachesExit input bound tapes inHead (.inl ()) tapes' inHead' ∧
        Inv tapes' inHead') :
    ¬ (M.loop.toDTM blank).AcceptsOneSided input := by
  intro ⟨accCfg, hAccRun, hAccState⟩
  obtain ⟨T, hTPath⟩ := DtmPath.of_reflTransGen (M.loop.toDTM blank) input hAccRun
  have hNo : ∀ T tapes inHead, Inv tapes inHead →
      ∀ accCfg, DtmPath (M.loop.toDTM blank) input T ⟨.inl M.start, inHead, tapes⟩ accCfg →
      accCfg.state ≠ .inr true := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T ih =>
      intro tapes inHead hInv accCfg hPath hAcc
      obtain ⟨bound, tapes', inHead', hIter, hInv'⟩ := hStep tapes inHead hInv
      obtain ⟨m, hmPos, hmPath, hmInl⟩ :=
        loop_reachesExit_inl_path M blank input bound hIter
      rcases DtmPath.split (M.loop.toDTM blank) input hmPath hPath with
        ⟨hLe, hSub⟩ | ⟨hGt, hRem⟩
      · obtain ⟨q, hq⟩ := hmInl T accCfg hLe hSub
        rw [hq] at hAcc
        cases hAcc
      · have hLt : T - m < T := by omega
        exact ih (T - m) hLt tapes' inHead' hInv' accCfg hRem hAcc
  exact hNo T (fun _ => ⟨fun _ => blank, 0⟩) ⟨0, by omega⟩ hInit accCfg hTPath hAccState

end SavitchLemma

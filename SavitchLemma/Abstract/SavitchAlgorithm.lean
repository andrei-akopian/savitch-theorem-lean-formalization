module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Abstract register machine for Savitch's algorithm

This is the relation-level model recommended as the first formalization
milestone in `PLAN.md`.  A code is an element of `Fin (N + 1)`; codes 1 through
N - 1 are valid, while 0 and N are reserved non-ID codes.  The concrete
encoding of machine IDs will be connected to this model in a later module.
-/

namespace SavitchLemma

/-- A finite transition relation with no transition into the reserved maximum
code.  Decidability is supplied classically by the register-machine step. -/
structure AbstractProblem (N : ℕ) where
  step : Fin (N + 1) → Fin (N + 1) → Prop
  noStepToZero : ∀ x, ¬ step x ⟨0, Nat.zero_lt_succ N⟩
  noStepToMax : ∀ x, ¬ step x ⟨N, Nat.lt_succ_self N⟩

/-- Codes strictly between the two reserved codes are valid abstract IDs. -/
abbrev ValidCode (N : ℕ) := {code : Fin (N + 1) // 0 < code.val ∧ code.val < N}

/-- Savitch's registers and their one-bit tags.  The last slot is the
distinguished source register; the first `r` slots are working registers. -/
structure ZDConfig (r N : ℕ) where
  x : Fin (r + 1) → Fin (N + 1)
  tag : Fin (r + 1) → Bool

/-- The code representing the maximum value, which is not a valid ID. -/
def maxCode (N : ℕ) : Fin (N + 1) :=
  ⟨N, Nat.lt_succ_self N⟩

/-- The first ordinary register value.  `hN` ensures it exists strictly below
the reserved maximum. -/
def firstCode (N : ℕ) (hN : 1 < N) : Fin (N + 1) :=
  ⟨1, Nat.lt_trans hN (Nat.lt_succ_self N)⟩

/-- Initial configuration: working registers contain the first code and are
untagged; the final register contains the source and is tagged. -/
def zdInitial (r N : ℕ) (hN : 1 < N) (source : ValidCode N) : ZDConfig r N where
  x := fun i => if i.val = r then source.val else firstCode N hN
  tag := fun i => decide (i.val = r)

/-- The distinguished source register starts with the supplied source code. -/
theorem zdInitial_source (r N : ℕ) (hN : 1 < N) (source : ValidCode N) :
    (zdInitial r N hN source).x (Fin.last r) = source.val := by
  simp [zdInitial]

variable {r N : ℕ}

/-- The distinguished source register starts tagged. -/
theorem zdInitial_source_tag (r N : ℕ) (hN : 1 < N) (source : ValidCode N) :
    (zdInitial r N hN source).tag (Fin.last r) = true := by
  simp [zdInitial]

variable {r N : ℕ}

/-- Find the least untagged working register.  `List.finRange` is ordered by
the natural value of each `Fin`, so `find?` implements Savitch's least-index
selection. -/
def firstUntagged (cfg : ZDConfig r N) : Option (Fin r) :=
  (List.finRange r).find? (fun j => !cfg.tag j.castSucc)

/-- Find the least working register which has not yet reached the reserved
maximum code. -/
def firstBelowMax (cfg : ZDConfig r N) : Option (Fin r) :=
  (List.finRange r).find? (fun j => decide ((cfg.x j.castSucc).val < N))

/-- Reset all working registers to the left of `j`, then write `value` and
`newTag` into `j`.  The final/source register is untouched. -/
def updateAndReset (hN : 1 < N) (cfg : ZDConfig r N) (j : Fin r)
    (value : Fin (N + 1)) (newTag : Bool) : ZDConfig r N where
  x := fun i =>
    if i.val = j.val then value
    else if i.val < j.val then firstCode N hN
    else cfg.x i
  tag := fun i =>
    if i.val = j.val then newTag
    else if i.val < j.val then false
    else cfg.tag i

/-- Updating a working register never changes the distinguished source
register's value or tag. -/
theorem updateAndReset_preserves_source (hN : 1 < N) (cfg : ZDConfig r N)
    (j : Fin r) (value : Fin (N + 1)) (newTag : Bool) :
    (updateAndReset hN cfg j value newTag).x (Fin.last r) = cfg.x (Fin.last r) ∧
    (updateAndReset hN cfg j value newTag).tag (Fin.last r) = cfg.tag (Fin.last r) := by
  have hj : j.val < r := j.isLt
  have hne : r ≠ j.val := Nat.ne_of_gt hj
  have hnotlt : ¬ r < j.val := Nat.not_lt_of_ge (Nat.le_of_lt hj)
  constructor <;> simp [updateAndReset, hne, hnotlt]

/-- The D3 backtracking branch: increment the first working register below
the maximum code, clear its tag, and reset the registers to its left. -/
def zdBacktrack (hN : 1 < N) (cfg : ZDConfig r N) : Option (ZDConfig r N) :=
  match firstBelowMax cfg with
  | none => none
  | some j =>
    let old := cfg.x j.castSucc
    if h : old.val < N then
      some (updateAndReset hN cfg j ⟨old.val + 1, Nat.succ_lt_succ h⟩ false)
    else none

/-- One pass through D1 followed by modified D2 or D3.  D1 selects the least
untagged working register and tests whether any tagged register is equal to,
or has a one-step edge into, its value.  A successful test tags that register;
otherwise the machine backtracks.  When all working registers are tagged it
also backtracks. -/
noncomputable def zdStep (P : AbstractProblem N) (hN : 1 < N)
    (cfg : ZDConfig r N) : Option (ZDConfig r N) := by
  classical
  match firstUntagged cfg with
  | none => exact zdBacktrack hN cfg
  | some j =>
    if h : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc)) then
      exact some (updateAndReset hN cfg j (cfg.x j.castSucc) true)
    else
      exact zdBacktrack hN cfg

/-- A tag is sound when its register contains a code reachable from the
distinguished source in the abstract transition graph. -/
def TagsSound (P : AbstractProblem N) (source : Fin (N + 1))
    (cfg : ZDConfig r N) : Prop :=
  ∀ i, cfg.tag i = true → Relation.ReflTransGen P.step source (cfg.x i)

/-- Append one graph edge (or no edge, when the codes are equal) to a path. -/
theorem reaches_of_eq_or_step (P : AbstractProblem N) {source a b : Fin (N + 1)}
    (hReach : Relation.ReflTransGen P.step source a)
    (hNext : a = b ∨ P.step a b) :
    Relation.ReflTransGen P.step source b := by
  rcases hNext with hEq | hEdge
  · simpa [hEq] using hReach
  · exact hReach.trans (Relation.ReflTransGen.single hEdge)

/-- The update operation preserves soundness of all tags, provided any newly
set tag is justified by a path from the source. -/
theorem updateAndReset_preserves_tags (P : AbstractProblem N)
    (source : Fin (N + 1)) (cfg : ZDConfig r N)
    (hSound : TagsSound P source cfg) (hN : 1 < N) (j : Fin r)
    (value : Fin (N + 1)) (newTag : Bool)
    (hNew : newTag = true → Relation.ReflTransGen P.step source value) :
    TagsSound P source (updateAndReset hN cfg j value newTag) := by
  intro i hi
  by_cases hEq : i.val = j.val
  · have hTag : newTag = true := by
      simpa [updateAndReset, hEq] using hi
    simpa [updateAndReset, hEq] using hNew hTag
  · by_cases hLt : i.val < j.val
    · simp [updateAndReset, hEq, hLt] at hi
    · have hTag : cfg.tag i = true := by
        simpa [updateAndReset, hEq, hLt] using hi
      simpa [updateAndReset, hEq, hLt] using hSound i hTag

/-- D3 only clears tags (or leaves later registers untouched), so it cannot
introduce an unsound tag. -/
theorem zdBacktrack_preserves_tags (P : AbstractProblem N) (hN : 1 < N)
    (source : Fin (N + 1)) (cfg next : ZDConfig r N)
    (hSound : TagsSound P source cfg)
    (hNext : zdBacktrack hN cfg = some next) :
    TagsSound P source next := by
  unfold zdBacktrack at hNext
  cases hFind : firstBelowMax cfg with
  | none => simp [hFind] at hNext
  | some j =>
    by_cases hLt : (cfg.x j.castSucc).val < N
    · have hEq :
          updateAndReset hN cfg j
              ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false = next := by
        have hSome :
            some (updateAndReset hN cfg j
              ⟨(cfg.x j.castSucc).val + 1, Nat.succ_lt_succ hLt⟩ false) = some next := by
          simpa [hFind, hLt] using hNext
        exact Option.some.inj hSome
      rw [← hEq]
      apply updateAndReset_preserves_tags P source cfg hSound hN j _ false
      simp
    · simp [hFind, hLt] at hNext

/-- One D1/D2/D3 pass preserves soundness of every register tag. -/
theorem zdStep_preserves_tags (P : AbstractProblem N) (hN : 1 < N)
    (source : Fin (N + 1)) (cfg next : ZDConfig r N)
    (hSound : TagsSound P source cfg)
    (hNext : zdStep P hN cfg = some next) :
    TagsSound P source next := by
  classical
  unfold zdStep at hNext
  cases hFind : firstUntagged cfg with
  | none =>
    exact zdBacktrack_preserves_tags P hN source cfg next hSound
      (by simpa [hFind] using hNext)
  | some j =>
    by_cases hTest : ∃ i : Fin (r + 1), cfg.tag i = true ∧
        (cfg.x i = cfg.x j.castSucc ∨ P.step (cfg.x i) (cfg.x j.castSucc))
    · have hEq :
          updateAndReset hN cfg j (cfg.x j.castSucc) true = next := by
        have hSome :
            some (updateAndReset hN cfg j (cfg.x j.castSucc) true) = some next := by
          simpa [hFind, hTest] using hNext
        exact Option.some.inj hSome
      rw [← hEq]
      apply updateAndReset_preserves_tags P source cfg hSound hN j
        (cfg.x j.castSucc) true
      intro _
      rcases hTest with ⟨i, hiTag, hEdge⟩
      exact reaches_of_eq_or_step P (hSound i hiTag) hEdge
    · exact zdBacktrack_preserves_tags P hN source cfg next hSound
        (by simpa [hFind, hTest] using hNext)

/-- The initial D0 configuration has sound tags: only the source register is
tagged, and its value is reachable from itself by a zero-step path. -/
theorem zdInitial_tags_sound (P : AbstractProblem N) (r : ℕ) (hN : 1 < N)
    (source : ValidCode N) :
    TagsSound P source.val (zdInitial r N hN source) := by
  intro i hi
  by_cases hLast : i.val = r
  · have hIndex : i = Fin.last r := by
      apply Fin.ext
      simpa using hLast
    subst i
    rw [zdInitial_source]
  · simp [zdInitial, hLast] at hi

/-- Soundness holds throughout every finite execution of the abstract machine. -/
theorem zd_soundness (P : AbstractProblem N) (r : ℕ) (hN : 1 < N)
    (source : ValidCode N) {cfg : ZDConfig r N}
    (hRun : Relation.ReflTransGen
      (fun a b : ZDConfig r N => zdStep P hN a = some b)
      (zdInitial r N hN source) cfg) :
    TagsSound P source.val cfg := by
  induction hRun with
  | refl => exact zdInitial_tags_sound P r hN source
  | @tail prev current hRun hStep ih =>
    exact zdStep_preserves_tags P hN source.val prev current ih hStep

end SavitchLemma

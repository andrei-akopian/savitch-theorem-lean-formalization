module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Log
public import SavitchLemma.Abstract.BoundedReachability
public import SavitchLemma.Abstract.LemmasTwoThree
public import SavitchLemma.Model.MachineModel
public import SavitchLemma.Abstract.SavitchAlgorithm

import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Finite configurations as instantaneous-description codes

For any finite configuration type `C`, `finiteConfigCode` identifies its
elements with the valid codes `1` through `card C` in
`Fin (card C + 2)`.  This reserves zero and the maximum code exactly as required
by `AbstractProblem`.
-/

namespace SavitchLemma

/-- Shift `Fin n` into the valid-code interval for maximum code `n + 1`. -/
def finToValidCode (n : ℕ) : Fin n ≃ ValidCode (n + 1) where
  toFun i := ⟨(Fin.succ i).castSucc, by
    have hVal : ((Fin.succ i).castSucc).val = i.val + 1 := by simp
    constructor
    · rw [hVal]
      omega
    · rw [hVal]
      omega⟩
  invFun code := ⟨code.val.val - 1, by
    rcases code.property with ⟨hPos, hLt⟩
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv code := by
    apply Subtype.ext
    apply Fin.ext
    rcases code.property with ⟨hPos, hLt⟩
    simp
    omega

/-- Encode an arbitrary finite type by shifting its `Fintype.equivFin` index. -/
noncomputable def finiteConfigCode (C : Type*) [Fintype C] :
    C ≃ ValidCode (Fintype.card C + 1) :=
  (Fintype.equivFin C).trans (finToValidCode (Fintype.card C))

/-- The abstract transition system induced by a finite-capacity multitape
machine on a fixed input. -/
noncomputable def multitapeProblem {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) :
    AbstractProblem (Fintype.card (TMConfig Q Γ k n capacity) + 1) where
  step source target :=
    ∃ before after : TMConfig Q Γ k n capacity,
      (finiteConfigCode (TMConfig Q Γ k n capacity) before).val = source ∧
      (finiteConfigCode (TMConfig Q Γ k n capacity) after).val = target ∧
      M.step input capacity before after
  noStepToZero := by
    intro source hStep
    rcases hStep with ⟨before, after, _, hTarget, _⟩
    have hZero : (finiteConfigCode (TMConfig Q Γ k n capacity) after).val.val = 0 := by
      simpa using congrArg Fin.val hTarget
    have hPositive :=
      (finiteConfigCode (TMConfig Q Γ k n capacity) after).property.1
    omega
  noStepToMax := by
    intro source hStep
    rcases hStep with ⟨before, after, _, hTarget, _⟩
    have hMax : (finiteConfigCode (TMConfig Q Γ k n capacity) after).val.val =
        Fintype.card (TMConfig Q Γ k n capacity) + 1 := by
      simpa [maxCode] using congrArg Fin.val hTarget
    have hBelow :=
      (finiteConfigCode (TMConfig Q Γ k n capacity) after).property.2
    omega

/-- Abstract edges between the codes of two concrete configurations are
exactly the concrete machine's bounded transitions. -/
theorem multitapeProblem_step_iff {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ)
    (before after : TMConfig Q Γ k n capacity) :
    (multitapeProblem M input capacity).step
      (finiteConfigCode (TMConfig Q Γ k n capacity) before).val
      (finiteConfigCode (TMConfig Q Γ k n capacity) after).val ↔
      M.step input capacity before after := by
  constructor
  · rintro ⟨before', after', hBefore, hAfter, hStep⟩
    have hBeforeEq : before' = before :=
      (finiteConfigCode (TMConfig Q Γ k n capacity)).injective (Subtype.ext hBefore)
    have hAfterEq : after' = after :=
      (finiteConfigCode (TMConfig Q Γ k n capacity)).injective (Subtype.ext hAfter)
    subst before'
    subst after'
    exact hStep
  · intro hStep
    exact ⟨before, after, rfl, rfl, hStep⟩

/-- Every bounded machine run induces a short path in its abstract ID graph. -/
theorem multitapeProblem_run_short_path {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) {initial final : TMConfig Q Γ k n capacity}
    (hRun : Relation.ReflTransGen (M.step input capacity) initial final) :
    ReachesWithin (multitapeProblem M input capacity)
      (Fintype.card (TMConfig Q Γ k n capacity) + 1)
      (finiteConfigCode (TMConfig Q Γ k n capacity) initial).val
      (finiteConfigCode (TMConfig Q Γ k n capacity) final).val := by
  have hCodeRun : Relation.ReflTransGen (multitapeProblem M input capacity).step
      (finiteConfigCode (TMConfig Q Γ k n capacity) initial).val
      (finiteConfigCode (TMConfig Q Γ k n capacity) final).val := by
    induction hRun with
    | refl => exact Relation.ReflTransGen.refl
    | @tail previous current hPrevious hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ((multitapeProblem_step_iff M input capacity previous current).2 hStep)
  exact reachesWithin_of_reflTransGen _ hCodeRun

/-- The machine's finite configuration type is nonempty, so its reserved-code
parameter is strictly larger than one. -/
theorem tmConfig_card_succ_gt_one {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (inputLength : ℕ) (capacity : ℕ)
    (hCapacity : 0 < capacity) :
    1 < Fintype.card (TMConfig Q Γ k inputLength capacity) + 1 := by
  have hCard : 0 < Fintype.card (TMConfig Q Γ k inputLength capacity) :=
    Fintype.card_pos_iff.mpr ⟨M.initialConfig (n := inputLength) capacity hCapacity⟩
  omega

/-- An accepting bounded machine run leads the abstract register algorithm to
tag the code of its accepting configuration, provided the register budget
covers the finite configuration count. -/
theorem acceptingRun_is_tagged_abstractly {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity r : ℕ) (hCapacity : 0 < capacity)
    (target : TMConfig Q Γ k n capacity)
    (hRun : Relation.ReflTransGen (M.step input capacity)
      (M.initialConfig capacity hCapacity) target)
    (hAccept : M.accepting target.state)
    (hBudget : Fintype.card (TMConfig Q Γ k n capacity) + 1 ≤ 2 ^ r) :
    ∃ final : ZDConfig (r + 1) (Fintype.card (TMConfig Q Γ k n capacity) + 1),
      Relation.ReflTransGen
        (fun a b => zdStep (multitapeProblem M input capacity)
          (tmConfig_card_succ_gt_one M n capacity hCapacity) a = some b)
        (zdInitial (r + 1) (Fintype.card (TMConfig Q Γ k n capacity) + 1)
          (tmConfig_card_succ_gt_one M n capacity hCapacity)
          (finiteConfigCode (TMConfig Q Γ k n capacity)
            (M.initialConfig (n := n) capacity hCapacity))) final ∧
      final.tag (Fin.last r).castSucc = true ∧
      final.x (Fin.last r).castSucc =
        (finiteConfigCode (TMConfig Q Γ k n capacity) target).val ∧
      M.accepting target.state := by
  let Config := TMConfig Q Γ k n capacity
  let initial : TMConfig Q Γ k n capacity := M.initialConfig (n := n) capacity hCapacity
  let sourceCode := finiteConfigCode Config initial
  let targetCode := finiteConfigCode Config target
  let problem := multitapeProblem M input capacity
  have hN : 1 < Fintype.card Config + 1 :=
    tmConfig_card_succ_gt_one M n capacity hCapacity
  have hShort := multitapeProblem_run_short_path M input capacity hRun
  have hPath : ReachesWithin problem (2 ^ r) sourceCode.val targetCode.val :=
    ReachesWithin.mono problem hBudget hShort
  obtain ⟨final, hFinalRun, hTag, hCode⟩ :=
    savitch_abstract_completeness problem hN r sourceCode targetCode hPath
  exact ⟨final, hFinalRun, hTag, hCode, hAccept⟩

/-- Specialize the abstract completeness transfer to the ceiling logarithm of
the finite configuration count. -/
theorem acceptingRun_is_tagged_at_clog {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (hCapacity : 0 < capacity)
    (target : TMConfig Q Γ k n capacity)
    (hRun : Relation.ReflTransGen (M.step input capacity)
      (M.initialConfig capacity hCapacity) target)
    (hAccept : M.accepting target.state) :
    ∃ final : ZDConfig
        (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1) + 1)
        (Fintype.card (TMConfig Q Γ k n capacity) + 1),
      Relation.ReflTransGen
        (fun a b => zdStep (multitapeProblem M input capacity)
          (tmConfig_card_succ_gt_one M n capacity hCapacity) a = some b)
        (zdInitial
          (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1) + 1)
          (Fintype.card (TMConfig Q Γ k n capacity) + 1)
          (tmConfig_card_succ_gt_one M n capacity hCapacity)
          (finiteConfigCode (TMConfig Q Γ k n capacity)
            (M.initialConfig (n := n) capacity hCapacity))) final ∧
      final.tag
        (Fin.last (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))).castSucc = true ∧
      final.x
        (Fin.last (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))).castSucc =
          (finiteConfigCode (TMConfig Q Γ k n capacity) target).val ∧
      M.accepting target.state := by
  exact acceptingRun_is_tagged_abstractly M input capacity
    (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))
    hCapacity target hRun hAccept
    (Nat.le_pow_clog (by decide : 1 < 2) _)

/-- Any accepting bounded-capacity computation yields a tagged accepting ID in
the abstract deterministic register machine at the ceiling-log register
budget. -/
theorem acceptsWithinCapacity_abstractly {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (hCapacity : 0 < capacity)
    (hAccepts : M.AcceptsWithinCapacity input capacity hCapacity) :
    ∃ (target : TMConfig Q Γ k n capacity)
      (final : ZDConfig
        (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1) + 1)
        (Fintype.card (TMConfig Q Γ k n capacity) + 1)),
      M.accepting target.state ∧
      Relation.ReflTransGen
        (fun a b => zdStep (multitapeProblem M input capacity)
          (tmConfig_card_succ_gt_one M n capacity hCapacity) a = some b)
        (zdInitial
          (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1) + 1)
          (Fintype.card (TMConfig Q Γ k n capacity) + 1)
          (tmConfig_card_succ_gt_one M n capacity hCapacity)
          (finiteConfigCode (TMConfig Q Γ k n capacity)
            (M.initialConfig (n := n) capacity hCapacity))) final ∧
      final.tag
        (Fin.last (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))).castSucc = true ∧
      final.x
        (Fin.last (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))).castSucc =
          (finiteConfigCode (TMConfig Q Γ k n capacity) target).val := by
  rcases hAccepts with ⟨target, hRun, hAccept⟩
  obtain ⟨final, hDetRun, hTag, hCode, _⟩ :=
    acceptingRun_is_tagged_at_clog M input capacity hCapacity target hRun hAccept
  exact ⟨target, final, hAccept, hDetRun, hTag, hCode⟩

/-- The initial configuration has a valid abstract code. -/
noncomputable def initialConfigCode {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (inputLength : ℕ)
    (capacity : ℕ) (hCapacity : 0 < capacity) :
    ValidCode (Fintype.card (TMConfig Q Γ k inputLength capacity) + 1) :=
  finiteConfigCode (TMConfig Q Γ k inputLength capacity)
    (M.initialConfig capacity hCapacity)

end SavitchLemma

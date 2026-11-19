module

public import SavitchLemma.Simulator.MainBridge
public import SavitchLemma.Model.SpaceAnalysis
public import SavitchLemma.SpaceBounds.RulerWriter
public import SavitchLemma.SpaceBounds.AlphabetCompression
public import SavitchLemma.SpaceBounds.IterativeDeepening
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Theorem 1 (Savitch's Theorem)

Formalizes Savitch's Theorem (`NSPACE(L) ⊆ DSPACE(L^2)` for `L(n) ≥ 1` and `n ≤ 2^L(n)`):
- `savitch_theorem_one`: relative to a `RulerWriter` prefix component.
- `savitch_theorem_one_measurable`: for space functions measurable over `SimSym`.
- `savitch_theorem_one_of_measurable`: for space functions measurable over any finite alphabet
  (via `AlphabetCompression`).
- `savitch_theorem_one_full`: for arbitrary (non-measurable) space bounds `L` (via
  `IterativeDeepening`).
-/

namespace SavitchLemma

/-- The prefix component can build the clean simulator tapes (ruler `1^{L n}`) from blank
tapes within `c * (L n + 1)` work squares, on every input. -/
def RulerWriter (InputAlphabet : Type) [Fintype InputAlphabet] (L : ℕ → ℕ) : Prop :=
  ∃ (QP : Type) (_ : Fintype QP) (P : TMComponent QP InputAlphabet SimSym 5 Unit) (c : ℕ),
    ∀ (n : ℕ) (input : Fin n → InputAlphabet),
      ∃ (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2)),
        PrefixPrepares P input (L n) (c * (L n + 1)) initTapes inHead

theorem PrefixPrepares.mono {QP InputAlphabet : Type*} {n : ℕ}
    {P : TMComponent QP InputAlphabet SimSym 5 Unit} {input : Fin n → InputAlphabet}
    {S B B' : ℕ} {initTapes : Fin 5 → OneSidedTape SimSym} {inHead : Fin (n + 2)}
    (h : PrefixPrepares P input S B initTapes inHead) (hB : B ≤ B') :
    PrefixPrepares P input S B' initTapes inHead :=
  ⟨h.1.mono (fun _ => hB), h.2⟩

/-- Space used by the compiled deterministic machine at capacity `S`. -/
def savitchSpace (Q Γ : Type) [Fintype Q] [Fintype Γ] (k c S : ℕ) : ℕ :=
  c * (S + 1) + (S + 4) +
    (1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3)) + (configBitWidth Q Γ k S + 2)

theorem savitchSpace_quadratic (Q Γ : Type) [Fintype Q] [Fintype Γ] (k c : ℕ) :
    ∃ C, ∀ S, savitchSpace Q Γ k c S ≤ C * (S + 1) ^ 2 := by
  set m := (qBits Q + 4) + (1 + k * (1 + gammaBits Γ)) + 2 with hm
  refine ⟨c + 10 + m * m + m, fun S => ?_⟩
  have hW : configBitWidth Q Γ k S + 2 ≤ m * (S + 1) := by
    rw [configBitWidth_eq_linear]
    rw [hm]; nlinarith
  unfold savitchSpace
  generalize configBitWidth Q Γ k S = W at hW ⊢
  have hT : 1 ≤ S + 1 := by omega
  have h1 : S + 1 ≤ (S + 1) ^ 2 := by nlinarith
  have h2 : 1 ≤ (S + 1) ^ 2 := by nlinarith
  have h3 : (W + 2) * (W + 2) ≤ (m * m) * (S + 1) ^ 2 := by
    calc (W + 2) * (W + 2) ≤ (m * (S + 1)) * (m * (S + 1)) := Nat.mul_le_mul hW hW
      _ = (m * m) * (S + 1) ^ 2 := by ring
  have h4 : W + 2 ≤ m * (S + 1) ^ 2 := by
    calc W + 2 ≤ m * (S + 1) := hW
      _ ≤ m * (S + 1) ^ 2 := Nat.mul_le_mul_left _ h1
  have h5 : c * (S + 1) ≤ c * (S + 1) ^ 2 := Nat.mul_le_mul_left _ h1
  nlinarith

/-- **Theorem 1**, measurable case relative to a ruler writer. -/
theorem savitch_theorem_one {Q Γ InputAlphabet : Type} {k : ℕ}
    [Fintype Q] [Fintype Γ] [Fintype InputAlphabet]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ)
    (hRW : RulerWriter InputAlphabet L)
    (hL : ∀ n, 1 ≤ L n ∧ n ≤ 2 ^ L n)
    (hM : M.AcceptsLanguageWithinSpace A L) :
    ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD InputAlphabet SimSym 5)
      (L' : ℕ → ℕ) (C : ℕ),
      D.AcceptsLanguageWithinSpace A L' ∧ ∀ n, L' n ≤ C * (L n + 1) ^ 2 := by
  obtain ⟨QP, _, P, c, hP⟩ := hRW
  obtain ⟨C, hC⟩ := savitchSpace_quadratic Q Γ k c
  refine ⟨_, inferInstance, savitchDTM P M, fun n => savitchSpace Q Γ k c (L n), C,
    ⟨fun n input hA => ?_, fun n input hAcc => ?_⟩, fun n => hC (L n)⟩
  · obtain ⟨initTapes, inHead, hPrep⟩ := hP n input
    have hCap := (M.acceptsOneSidedWithin_iff_acceptsWithinCapacity input (L n)
      (by have := (hL n).1; omega)).1 (hM.1 n input hA)
    have hB := hPrep.mono (B' := savitchSpace Q Γ k c (L n)) (by unfold savitchSpace; omega)
    exact (savitchDTM_correct P M input (L n) _ (hL n).1 (hL n).2
      (by unfold savitchSpace; omega) (by unfold savitchSpace; omega)
      (by unfold savitchSpace; omega) (by unfold savitchSpace; omega)
      (by unfold savitchSpace; omega) hB).1 hCap
  · by_contra hNotA
    obtain ⟨initTapes, inHead, hPrep⟩ := hP n input
    have hNotM : ¬ M.AcceptsOneSided input := fun h => hNotA (hM.2 n input h)
    have hNotCap : ¬ M.AcceptsWithinCapacity input (L n) (by have := (hL n).1; omega) :=
      fun h => hNotM (M.acceptsOneSided_of_acceptsOneSidedWithin input (L n)
        ((M.acceptsOneSidedWithin_iff_acceptsWithinCapacity input (L n)
          (by have := (hL n).1; omega)).2 h))
    have hB := hPrep.mono (B' := savitchSpace Q Γ k c (L n)) (by unfold savitchSpace; omega)
    exact (savitchDTM_correct P M input (L n) _ (hL n).1 (hL n).2
      (by unfold savitchSpace; omega) (by unfold savitchSpace; omega)
      (by unfold savitchSpace; omega) (by unfold savitchSpace; omega)
      (by unfold savitchSpace; omega) hB).2 hNotCap hAcc

/-- `L` is measurable by a single-tape deterministic machine over the simulator alphabet
`SimSym` (with `SimSym.blank` as its blank). General finite alphabets reduce to this via
`AlphabetCompression` (`savitch_theorem_one_of_measurable`). -/
def IsMeasurableSim (InputAlphabet : Type) [Fintype InputAlphabet] (L : ℕ → ℕ) : Prop :=
  ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD InputAlphabet SimSym 1),
    D.blank = .blank ∧ ∀ (n : ℕ) (input : Fin n → InputAlphabet),
      D.HaltsScanningExactly input (L n)

theorem rulerWriter_of_measurableSim {InputAlphabet : Type} [Fintype InputAlphabet]
    {L : ℕ → ℕ} (hMeas : IsMeasurableSim InputAlphabet L) (hL : ∀ n, 1 ≤ L n) :
    RulerWriter InputAlphabet L := by
  obtain ⟨QD, _, D, hBlank, hHalt⟩ := hMeas
  refine ⟨RWState QD, inferInstance, rwComp D, 2, fun n input => ?_⟩
  exact rw_prefix D hBlank input (L n) (hL n) (2 * (L n + 1)) (by have := hL n; omega)
    (hHalt n input)

/-- **Theorem 1** for spaces measurable over the simulator alphabet. -/
theorem savitch_theorem_one_measurable {Q Γ InputAlphabet : Type} {k : ℕ}
    [Fintype Q] [Fintype Γ] [Fintype InputAlphabet]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ)
    (hMeas : IsMeasurableSim InputAlphabet L)
    (hL : ∀ n, 1 ≤ L n ∧ n ≤ 2 ^ L n)
    (hM : M.AcceptsLanguageWithinSpace A L) :
    ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD InputAlphabet SimSym 5)
      (L' : ℕ → ℕ) (C : ℕ),
      D.AcceptsLanguageWithinSpace A L' ∧ ∀ n, L' n ≤ C * (L n + 1) ^ 2 :=
  savitch_theorem_one M A L (rulerWriter_of_measurableSim hMeas fun n => (hL n).1) hL hM

theorem rulerWriter_of_measurable {InputAlphabet : Type} [Fintype InputAlphabet]
    {L : ℕ → ℕ} (hMeas : IsMeasurable InputAlphabet L) (hL : ∀ n, 1 ≤ L n) :
    RulerWriter InputAlphabet L := by
  obtain ⟨QD, Γ, _, _, D, hHalt⟩ := hMeas
  refine ⟨RWGState QD Γ, inferInstance, rwCompGen D, Fintype.card Γ + 2, fun n input => ?_⟩
  exact rwg_prefix D input (L n) (hL n) ((Fintype.card Γ + 2) * (L n + 1)) le_rfl (hHalt n input)

/-- **Theorem 1** for measurable space bounds `L` (over any finite tape alphabet). -/
theorem savitch_theorem_one_of_measurable {Q Γ InputAlphabet : Type} {k : ℕ}
    [Fintype Q] [Fintype Γ] [Fintype InputAlphabet]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ)
    (hMeas : IsMeasurable InputAlphabet L)
    (hL : ∀ n, 1 ≤ L n ∧ n ≤ 2 ^ L n)
    (hM : M.AcceptsLanguageWithinSpace A L) :
    ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD InputAlphabet SimSym 5)
      (L' : ℕ → ℕ) (C : ℕ),
      D.AcceptsLanguageWithinSpace A L' ∧ ∀ n, L' n ≤ C * (L n + 1) ^ 2 :=
  savitch_theorem_one M A L (rulerWriter_of_measurable hMeas fun n => (hL n).1) hL hM

/-- **Theorem 1 (Savitch's Theorem)**: `NSPACE(L) ⊆ DSPACE(L^2)` for every
space bound `L` satisfying `1 ≤ L n` and `n ≤ 2 ^ L n`, without assuming `L` is
tape-constructible ("measurable").

Given any `k`-work-tape nondeterministic Turing machine `M` accepting a language
`A` within space `L`, there exists a 5-work-tape deterministic Turing machine `D`
(over the fixed alphabet `SimSym`) and a constant `C` such that `D` accepts `A`
within space `L' n ≤ C * (L n + 1) ^ 2`. Writing `(L n + 1) ^ 2` rather than
`L n ^ 2` absorbs additive constants into `C` and is equivalent to `O(L(n)^2)`
since `1 ≤ L n`. -/
theorem savitch_theorem_one_full {Q Γ InputAlphabet : Type} {k : ℕ}
    [Fintype Q] [Fintype Γ] [Fintype InputAlphabet]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (A : ∀ n : ℕ, (Fin n → InputAlphabet) → Prop) (L : ℕ → ℕ)
    (hL : ∀ n, 1 ≤ L n ∧ n ≤ 2 ^ L n)
    (hM : M.AcceptsLanguageWithinSpace A L) :
    ∃ (QD : Type) (_ : Fintype QD) (D : MultitapeDTM QD InputAlphabet SimSym 5)
      (L' : ℕ → ℕ) (C : ℕ),
      D.AcceptsLanguageWithinSpace A L' ∧ ∀ n, L' n ≤ C * (L n + 1) ^ 2 := by
  obtain ⟨C, hAcc, hBd⟩ := savitchDTM_nonmeasurable_correct M A L hL hM
  exact ⟨_, inferInstance, savitchDTM_nonmeasurable M, _, C, hAcc, hBd⟩

end SavitchLemma

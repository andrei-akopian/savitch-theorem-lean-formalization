module

public import Mathlib.Data.Nat.Log
public import SavitchLemma.InstantaneousDesc

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Space usage of the abstract register storage

This module isolates the arithmetic needed after the configuration-count
bound is proved: a logarithmic number of registers, each holding a logarithmic
size ID and one tag bit, uses quadratic space in the tape-capacity parameter.
-/

namespace SavitchLemma

/-- Storage units for `r + 1` work registers, one source register, and one tag
bit per register. `codeWidth` is the number of bits per ID. -/
def abstractRegisterStorage (r codeWidth : ℕ) : ℕ :=
  (r + 2) * (codeWidth + 1)

/-- Configuration-count bound for a fixed finite-control machine.  The input
head ranges over `n + 2` positions, and each of the `k` work tapes has `S`
cells over the finite alphabet `Γ`. -/
theorem tmConfig_count_plus_one_le_pow (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    (k n S : ℕ) (hS : 0 < S) (hInput : n ≤ 2 ^ S) :
    Fintype.card (TMConfig Q Γ k n S) + 1 ≤
      2 ^ ((Nat.clog 2 (Fintype.card Q + 1) + 2) +
        (1 + (Nat.clog 2 (Fintype.card Γ + 1) + 1) * k) * S) := by
  let qBits := Nat.clog 2 (Fintype.card Q + 1)
  let gammaBits := Nat.clog 2 (Fintype.card Γ + 1)
  let tapeExp := (gammaBits + 1) * S
  have hQPlus : Fintype.card Q + 1 ≤ 2 ^ qBits :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have hQ : Fintype.card Q ≤ 2 ^ qBits := by omega
  have hGammaPlus : Fintype.card Γ + 1 ≤ 2 ^ gammaBits :=
    Nat.le_pow_clog (by decide : 1 < 2) _
  have hGamma : Fintype.card Γ ≤ 2 ^ gammaBits := by omega
  have hGammaPow : Fintype.card Γ ^ S ≤ (2 ^ gammaBits) ^ S :=
    Nat.pow_le_pow_left hGamma S
  have hSPow : S ≤ 2 ^ S := Nat.le_of_lt Nat.lt_two_pow_self
  have hTwoPow : 2 ≤ 2 ^ S := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hS
  have hInputPlus : n + 2 ≤ 2 ^ (S + 1) := by
    calc
      n + 2 ≤ 2 ^ S + 2 := Nat.add_le_add_right hInput 2
      _ ≤ 2 ^ S + 2 ^ S := Nat.add_le_add_left hTwoPow _
      _ = 2 ^ (S + 1) := by simp [pow_succ, Nat.mul_two]
  have hTape : Fintype.card Γ ^ S * S ≤ 2 ^ tapeExp := by
    calc
      Fintype.card Γ ^ S * S ≤ (2 ^ gammaBits) ^ S * 2 ^ S :=
        Nat.mul_le_mul hGammaPow hSPow
      _ = (2 ^ (gammaBits * S)) * 2 ^ S := by rw [← Nat.pow_mul]
      _ = 2 ^ (gammaBits * S + S) := by rw [← Nat.pow_add]
      _ = 2 ^ tapeExp := by
        congr 1
        dsimp [tapeExp]
        simp [Nat.add_mul]
  have hStateInput : Fintype.card Q * (n + 2) ≤ 2 ^ qBits * 2 ^ (S + 1) :=
    Nat.mul_le_mul hQ hInputPlus
  have hTapePower :
      (Fintype.card Γ ^ S * S) ^ k ≤ (2 ^ tapeExp) ^ k := Nat.pow_le_pow_left hTape k
  let configExp := qBits + (S + 1) + tapeExp * k
  have hConfig : Fintype.card (TMConfig Q Γ k n S) ≤ 2 ^ configExp := by
    rw [tmConfig_card]
    calc
      Fintype.card Q * (n + 2) * (Fintype.card Γ ^ S * S) ^ k ≤
          (2 ^ qBits * 2 ^ (S + 1)) * (2 ^ tapeExp) ^ k :=
        Nat.mul_le_mul hStateInput hTapePower
      _ = (2 ^ qBits * 2 ^ (S + 1)) * 2 ^ (tapeExp * k) := by rw [← Nat.pow_mul]
      _ = 2 ^ (qBits + (S + 1)) * 2 ^ (tapeExp * k) := by rw [← Nat.pow_add]
      _ = 2 ^ configExp := by rw [← Nat.pow_add]
  have hPowOne : 1 ≤ 2 ^ configExp := Nat.one_le_pow _ 2 (by decide)
  have hCountPlus : Fintype.card (TMConfig Q Γ k n S) + 1 ≤ 2 ^ (configExp + 1) := by
    calc
      Fintype.card (TMConfig Q Γ k n S) + 1 ≤ 2 ^ configExp + 1 :=
        Nat.add_le_add_right hConfig 1
      _ ≤ 2 ^ configExp + 2 ^ configExp := Nat.add_le_add_left hPowOne _
      _ = 2 ^ (configExp + 1) := by simp [pow_succ, Nat.mul_two]
  have hExponent : configExp + 1 =
      (qBits + 2) + (1 + (gammaBits + 1) * k) * S := by
    dsimp [configExp, tapeExp]
    ring
  rw [hExponent] at hCountPlus
  simpa [qBits, gammaBits] using hCountPlus

/-- If the configuration count plus one is bounded by an exponential whose
exponent is linear in `S`, then the ceiling-log register budget and code width
use at most quadratic space in `S + 1`. -/
theorem abstractRegisterStorage_quadratic (C S a b : ℕ) (hS : 1 ≤ S)
    (hCount : C + 1 ≤ 2 ^ (a + b * S)) :
    abstractRegisterStorage (Nat.clog 2 (C + 1)) (Nat.clog 2 (C + 2)) ≤
      ((a + b + 5) * (S + 1)) ^ 2 := by
  let exponent := a + b * S
  have hReg : Nat.clog 2 (C + 1) ≤ exponent :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (by simpa [exponent] using hCount)
  have hPowPos : 0 < 2 ^ exponent := Nat.pow_pos (by decide)
  have hPowOne : 1 ≤ 2 ^ exponent := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hPowPos)
  have hNextCount : C + 2 ≤ 2 ^ (exponent + 1) := by
    calc
      C + 2 ≤ 2 ^ exponent + 1 := by simpa [Nat.add_assoc] using Nat.add_le_add_right hCount 1
      _ ≤ 2 ^ exponent + 2 ^ exponent := Nat.add_le_add_left hPowOne _
      _ = 2 ^ (exponent + 1) := by simp [pow_succ, Nat.mul_two]
  have hWidth : Nat.clog 2 (C + 2) ≤ exponent + 1 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hNextCount
  have hRegSpace : Nat.clog 2 (C + 1) + 2 ≤ (a + b + 5) * (S + 1) := by
    dsimp [exponent] at hReg
    nlinarith [hReg, hS]
  have hWidthSpace : Nat.clog 2 (C + 2) + 1 ≤ (a + b + 5) * (S + 1) := by
    dsimp [exponent] at hWidth
    nlinarith [hWidth, hS]
  change (Nat.clog 2 (C + 1) + 2) * (Nat.clog 2 (C + 2) + 1) ≤
    ((a + b + 5) * (S + 1)) ^ 2
  have hProduct := Nat.mul_le_mul hRegSpace hWidthSpace
  simpa only [pow_two] using hProduct

/-- For a fixed finite-control machine and finite work alphabet, the abstract
register storage is quadratic in capacity under the input-length bound
`n ≤ 2^S`. -/
theorem tmConfig_register_storage_quadratic (Q Γ : Type*)
    [Fintype Q] [Fintype Γ] (k n S : ℕ) (hS : 1 ≤ S)
    (hInput : n ≤ 2 ^ S) :
    abstractRegisterStorage
      (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n S) + 1))
      (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n S) + 2)) ≤
    ((Nat.clog 2 (Fintype.card Q + 1) + 2 +
      (1 + (Nat.clog 2 (Fintype.card Γ + 1) + 1) * k) + 5) * (S + 1)) ^ 2 := by
  exact abstractRegisterStorage_quadratic
    (Fintype.card (TMConfig Q Γ k n S)) S
    (Nat.clog 2 (Fintype.card Q + 1) + 2)
    (1 + (Nat.clog 2 (Fintype.card Γ + 1) + 1) * k)
    hS (tmConfig_count_plus_one_le_pow Q Γ k n S (by omega) hInput)

/-- Abstract finite-space Savitch simulation: an accepting bounded-capacity
machine run leads to a tagged accepting ID, and the register storage proxy is
quadratic in the capacity under `n ≤ 2^S`. -/
theorem acceptsWithinCapacity_abstractly_with_space_bound
    {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (capacity : ℕ) (hCapacity : 0 < capacity) (hInput : n ≤ 2 ^ capacity)
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
          (finiteConfigCode (TMConfig Q Γ k n capacity) target).val ∧
      abstractRegisterStorage
        (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 1))
        (Nat.clog 2 (Fintype.card (TMConfig Q Γ k n capacity) + 2)) ≤
        ((Nat.clog 2 (Fintype.card Q + 1) + 2 +
          (1 + (Nat.clog 2 (Fintype.card Γ + 1) + 1) * k) + 5) *
          (capacity + 1)) ^ 2 := by
  rcases acceptsWithinCapacity_abstractly M input capacity hCapacity hAccepts with
    ⟨target, final, hAccept, hRun, hTag, hCode⟩
  have hStorage := tmConfig_register_storage_quadratic Q Γ k n capacity
    (by omega) hInput
  exact ⟨target, final, hAccept, hRun, hTag, hCode, hStorage⟩

end SavitchLemma

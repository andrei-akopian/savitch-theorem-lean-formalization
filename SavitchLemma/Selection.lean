module

public import Batteries.Data.Fin.Lemmas
public import SavitchLemma.SavitchAlgorithm

@[expose] public section

/-!
# Register-selection lemmas

This module records the least-index guarantees used by D1 and D3.  Keeping
these search facts separate from the algorithm definition makes the later
register-progress proofs easier to read.
-/

namespace SavitchLemma

/-- A successful untagged-register search returns an untagged register, and
every earlier working register is tagged. -/
theorem firstUntagged_eq_some_iff (cfg : ZDConfig r N) (j : Fin r) :
    firstUntagged cfg = some j ↔
      cfg.tag j.castSucc = false ∧ ∀ i : Fin r, i < j → cfg.tag i.castSucc = true := by
  unfold firstUntagged
  rw [← Fin.find?_eq_find?_finRange, Fin.find?_eq_some_iff]
  simp

/-- If the untagged-register search fails, all working registers are tagged. -/
theorem firstUntagged_eq_none_iff (cfg : ZDConfig r N) :
    firstUntagged cfg = none ↔ ∀ i : Fin r, cfg.tag i.castSucc = true := by
  unfold firstUntagged
  rw [← Fin.find?_eq_find?_finRange, Fin.find?_eq_none_iff]
  simp

/-- A successful D3 search returns a register below the maximum code, and all
earlier working registers already contain the maximum. -/
theorem firstBelowMax_eq_some_iff (cfg : ZDConfig r N) (j : Fin r) :
    firstBelowMax cfg = some j ↔
      (cfg.x j.castSucc).val < N ∧
        ∀ i : Fin r, i < j → ¬ (cfg.x i.castSucc).val < N := by
  unfold firstBelowMax
  rw [← Fin.find?_eq_find?_finRange, Fin.find?_eq_some_iff]
  simp

/-- If D3 finds no register below the maximum, every working register is at
the maximum. -/
theorem firstBelowMax_eq_none_iff (cfg : ZDConfig r N) :
    firstBelowMax cfg = none ↔ ∀ i : Fin r, ¬ (cfg.x i.castSucc).val < N := by
  unfold firstBelowMax
  rw [← Fin.find?_eq_find?_finRange, Fin.find?_eq_none_iff]
  simp

end SavitchLemma

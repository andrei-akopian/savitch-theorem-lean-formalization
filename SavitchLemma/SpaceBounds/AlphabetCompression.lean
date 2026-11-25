module

public import SavitchLemma.SpaceBounds.AlphabetCompressionSim
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Alphabet Compression Cleanup and Prefix Theorem

Halting, ruler/scratch tape cleanup (`rwg_halt_step`, `rwg_clear`, `rwg_backRuler`,
`rwg_backScratch`), and the top-level `rwg_prefix` theorem for `rwCompGen`,
building on the step-by-step simulation proofs in `AlphabetCompressionSim`.
-/

namespace SavitchLemma

section Proofs

variable {QD I Γ : Type} [Fintype QD] [Fintype I] [Fintype Γ]

theorem rwg_halt_step (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S + 1 < B) (hRB : S + 1 < B)
    (final : OneSidedTMConfig QD Γ 1 n) (hFinS : (final.workTapes 0).head < S)
    (hNone : D.transition final.state (readInput input final.inputHead) final.scannedWork = none)
    (m : ℕ) (hm : m ≤ S) (hm_head : (final.workTapes 0).head ≤ m) :
    RWRun (rwCompGen D) input B (rwgCfg D final m)
      ⟨.inl .goLeftRuler, final.inputHead,
        tapes5 (rulerTape (max m ((final.workTapes 0).head + 1)) ((final.workTapes 0).head + 1))
          (scratchEnc D (final.workTapes 0)
            (1 + Fintype.card Γ * (final.workTapes 0).head + (Fintype.card Γ - 1)))
          fixedTape⟩ := by
  set w := Fintype.card Γ
  have hw := card_pos_of_blank D
  have hScB1 : w * (final.workTapes 0).head + w ≤ w * S := by
    have := Nat.mul_le_mul_left w (show (final.workTapes 0).head + 1 ≤ S by omega)
    simpa [mul_add] using this
  have hRead := rwg_read_loop D input S B (Nat.lt_of_succ_lt hSB) (Nat.lt_of_succ_lt hRB)
    final.state final.inputHead (final.workTapes 0) hFinS m hm 0 hw (fun _ => .blank)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
  have hBufUpdate :
      Function.update
        (fun j : Fin w => if j.val + 1 = w then SimSym.blank
          else encodeSym D ((final.workTapes 0).cells (final.workTapes 0).head) j)
        ⟨w - 1, Nat.sub_lt hw one_pos⟩
        ((scratchEnc D (final.workTapes 0) (1 + w * (final.workTapes 0).head + (w - 1))).cells
          (1 + w * (final.workTapes 0).head + (w - 1))) =
      encodeSym D ((final.workTapes 0).cells (final.workTapes 0).head) := by
    funext j
    by_cases hj : j = ⟨w - 1, Nat.sub_lt hw one_pos⟩
    · subst hj
      have hcb := scratchEnc_cell_block D (final.workTapes 0)
        (1 + w * (final.workTapes 0).head + (w - 1))
        (final.workTapes 0).head (w - 1) (Nat.sub_lt hw one_pos)
      simpa [w] using hcb
    · have hjv : j.val + 1 ≠ w := fun h => hj (Fin.ext (by simp at h ⊢; omega))
      simp [Function.update, hj, hjv]
  have hDec : decodeBlock D (encodeSym D ((final.workTapes 0).cells (final.workTapes 0).head)) =
      (final.workTapes 0).cells (final.workTapes 0).head := decodeBlock_encodeSym D _
  have hNotLt : ¬ ((w - 1) + 1 < Fintype.card Γ) := by omega
  have hStep := rwg_step_one D input B
    (.read final.state ⟨w - 1, Nat.sub_lt hw one_pos⟩
      (fun j => if j.val + 1 = w then SimSym.blank
        else encodeSym D ((final.workTapes 0).cells (final.workTapes 0).head) j))
    final.inputHead final.inputHead
    (rulerTape m ((final.workTapes 0).head + 1))
    (scratchEnc D (final.workTapes 0) (1 + w * (final.workTapes 0).head + (w - 1))) fixedTape
    (rulerTape (max m ((final.workTapes 0).head + 1)) ((final.workTapes 0).head + 1))
    (scratchEnc D (final.workTapes 0) (1 + w * (final.workTapes 0).head + (w - 1)))
    (.inl .goLeftRuler) .stay (.bit true, .stay)
    ((scratchEnc D (final.workTapes 0) (1 + w * (final.workTapes 0).head + (w - 1))).cells
      (1 + w * (final.workTapes 0).head + (w - 1)), .stay)
    (by
      dsimp only [rwCompGen]
      simp only [hNotLt, ↓reduceDIte, tapes5_tRuler, tapes5_tScratch]
      rw [show (scratchEnc D (final.workTapes 0) (1 + w * (final.workTapes 0).head + (w - 1))).head =
          1 + w * (final.workTapes 0).head + (w - 1) from rfl, hBufUpdate, hDec]
      have hSc : final.scannedWork =
          fun _ => (final.workTapes 0).cells (final.workTapes 0).head := by
        funext t; rw [Subsingleton.elim t 0]; rfl
      rw [← hSc, hNone])
    (by simp [moveHead])
    (rulerTape_updateAndMove_bit m (final.workTapes 0).head (final.workTapes 0).head hm_head .stay
      (by simp [moveOneSidedHead]))
    (OneSidedTape.stay_same _)
    (by simp [fixedTape]; omega)
    (by simp [rulerTape]; omega)
    (by simp [scratchEnc]; omega)
    (by simp [rulerTape]; omega)
    (by simp [scratchEnc]; omega)
  exact hRead.trans hStep

theorem rwg_goLeftRuler (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (ih : Fin (n + 2)) (S B : ℕ) (hRB : S + 1 < B) (Sc : OneSidedTape SimSym) (hScB : Sc.head < B) :
    ∀ h, h ≤ S →
      RWRun (rwCompGen D) input B
        ⟨.inl .goLeftRuler, ih, tapes5 (rulerTape S h) Sc fixedTape⟩
        ⟨.inl .goLeftScratch, ih, tapes5 (rulerTape S 1) Sc fixedTape⟩ := by
  intro h
  induction h with
  | zero =>
    intro _
    refine rwg_step_one D input B .goLeftRuler ih ih (rulerTape S 0) Sc fixedTape
      (rulerTape S 1) Sc (.inl .goLeftScratch) .stay (.leftMark, .right) (Sc.cells Sc.head, .stay)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tRuler, rulerTape, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq, rulerTape]
        congr 1; funext i; by_cases hi : i = 0 <;> simp [hi])
      (OneSidedTape.stay_same _)
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) hScB
      (by simp [rulerTape]; omega) hScB
  | succ h ih_h =>
    intro hh
    have hStep := rwg_step_one D input B .goLeftRuler ih ih (rulerTape S (h + 1)) Sc fixedTape
      (rulerTape S h) Sc (.inl .goLeftRuler) .stay
      ((rulerTape S (h + 1)).cells (h + 1), .left) (Sc.cells Sc.head, .stay)
      (by
        dsimp only [rwCompGen]
        have hlt : h + 1 ≤ S := hh
        simp only [tapes5_tRuler, rulerTape, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte, hlt]
        exact mk5_congr rfl rfl (by simp) rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (write_same_move (rulerTape S (h + 1)) (mv := .left) (h' := h)
          (by simp [rulerTape, moveOneSidedHead]))
      (OneSidedTape.stay_same _)
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) hScB
      (by simp [rulerTape]; omega) hScB
    exact hStep.trans (ih_h (by omega))

theorem rwg_goLeftScratch (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (ih : Fin (n + 2)) (B : ℕ) (hB : 1 < B) (R : OneSidedTape SimSym) (hRB : R.head < B)
    (ScCells : ℕ → SimSym) (h0 : ScCells 0 = .leftMark)
    (hNonLeft : ∀ p, 1 ≤ p → ScCells p ≠ .leftMark) :
    ∀ h, h < B →
      RWRun (rwCompGen D) input B
        ⟨.inl .goLeftScratch, ih, tapes5 R ⟨ScCells, h⟩ fixedTape⟩
        ⟨.inl (.clear ⟨0, card_pos_of_blank D⟩), ih, tapes5 R ⟨ScCells, 1⟩ fixedTape⟩ := by
  intro h
  induction h with
  | zero =>
    intro _
    refine rwg_step_one D input B .goLeftScratch ih ih R ⟨ScCells, 0⟩ fixedTape
      R ⟨ScCells, 1⟩ (.inl (.clear ⟨0, card_pos_of_blank D⟩)) .stay
      (R.cells R.head, .stay) (.leftMark, .right)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tScratch, h0, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]
        congr 1; funext i; by_cases hi : i = 0 <;> simp [hi, h0])
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
  | succ h ih_h =>
    intro hh
    have hne : ScCells (h + 1) ≠ .leftMark := hNonLeft (h + 1) (by omega)
    have hStep := rwg_step_one D input B .goLeftScratch ih ih R ⟨ScCells, h + 1⟩ fixedTape
      R ⟨ScCells, h⟩ (.inl .goLeftScratch) .stay
      (R.cells R.head, .stay) (ScCells (h + 1), .left)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tScratch, hne, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, h + 1⟩ (mv := .left) (h' := h) (by simp [moveOneSidedHead]))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
    exact hStep.trans (ih_h (by omega))

theorem rwg_clear (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (ih : Fin (n + 2)) (S B : ℕ) (hRB : S + 1 < B) (hSB : 1 + Fintype.card Γ * S < B) :
    ∀ (d : ℕ) (c : ℕ) (_hd : S + 1 - c = d) (_hc0 : 1 ≤ c) (_hcS : c ≤ S + 1)
      (g : ℕ → SimSym),
      RWRun (rwCompGen D) input B
        ⟨.inl (.clear ⟨0, card_pos_of_blank D⟩), ih,
          tapes5 (rulerTape S c) ⟨g, 1 + Fintype.card Γ * (c - 1)⟩ fixedTape⟩
        ⟨.inl .backRuler, ih,
          tapes5 (rulerCap S (S + 1))
            ⟨fun i => if 1 + Fintype.card Γ * (c - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
              then .blank else g i, 1 + Fintype.card Γ * S⟩ fixedTape⟩ := by
  intro d
  induction d with
  | zero =>
    intro c hd hc0 hcS g
    have hcEq : c = S + 1 := by omega
    subst hcEq
    have hNotBit : (rulerTape S (S + 1)).cells (S + 1) ≠ .bit true := by
      simp [rulerTape]
    have hFun : (fun i => if 1 + Fintype.card Γ * (S + 1 - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
        then SimSym.blank else g i) = g := by
      simp only [Nat.add_sub_cancel]
      funext i; split_ifs with h <;> [omega; rfl]
    rw [hFun]
    refine rwg_step_one D input B (.clear ⟨0, card_pos_of_blank D⟩) ih ih
      (rulerTape S (S + 1)) ⟨g, 1 + Fintype.card Γ * S⟩ fixedTape
      (rulerCap S (S + 1)) ⟨g, 1 + Fintype.card Γ * S⟩
      (.inl .backRuler) .stay (.endMark, .stay) (g (1 + Fintype.card Γ * S), .stay)
      (by
        dsimp only [rwCompGen]
        have hNotBit' : (rulerTape S (S + 1)).cells (rulerTape S (S + 1)).head ≠ .bit true := hNotBit
        simp only [tapes5_tRuler, hNotBit', ↓reduceIte, ↓reduceDIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq, rulerTape, rulerCap]
        congr 1; funext i; by_cases hi0 : i = 0 <;> by_cases hiS : i = S + 1 <;> simp [hi0, hiS])
      (OneSidedTape.stay_same _)
      (by simp [fixedTape]; omega) (by simp [rulerTape]; omega) (by simp; omega)
      (by simp [rulerCap]; omega) (by simp; omega)
  | succ d ih_d =>
    intro c hd hc0 hcS g
    have hcLt : c ≤ S := by omega
    have hw := card_pos_of_blank D
    have hBit : (rulerTape S c).cells c = .bit true := by
      simp [rulerTape, show c ≠ 0 by omega, hcLt]
    have hMulC : Fintype.card Γ * c ≤ Fintype.card Γ * S :=
      Nat.mul_le_mul_left (Fintype.card Γ) hcLt
    have hMulCm : Fintype.card Γ * (c - 1) + Fintype.card Γ = Fintype.card Γ * c := by
      have : c = (c - 1) + 1 := by omega
      conv_rhs => rw [this, mul_add, mul_one]
    have hSub : ∀ (k : ℕ) (hk : 1 ≤ k) (hk_le : k ≤ Fintype.card Γ) (g' : ℕ → SimSym),
        RWRun (rwCompGen D) input B
          ⟨.inl (.clear ⟨k % Fintype.card Γ, Nat.mod_lt _ hw⟩), ih,
            tapes5 (rulerTape S (c + 1)) ⟨g', 1 + Fintype.card Γ * (c - 1) + k⟩ fixedTape⟩
          ⟨.inl (.clear ⟨0, hw⟩), ih,
            tapes5 (rulerTape S (c + 1))
              ⟨fun i => if 1 + Fintype.card Γ * (c - 1) + k ≤ i ∧
                  i < 1 + Fintype.card Γ * c then .blank else g' i,
                1 + Fintype.card Γ * c⟩ fixedTape⟩ := by
      intro k hk hk_le g'
      suffices h : ∀ r k (hk : 1 ≤ k) (hk_le : k ≤ Fintype.card Γ)
          (hr : Fintype.card Γ - k = r) (g' : ℕ → SimSym),
          RWRun (rwCompGen D) input B
            ⟨.inl (.clear ⟨k % Fintype.card Γ, Nat.mod_lt _ hw⟩), ih,
              tapes5 (rulerTape S (c + 1)) ⟨g', 1 + Fintype.card Γ * (c - 1) + k⟩ fixedTape⟩
            ⟨.inl (.clear ⟨0, hw⟩), ih,
              tapes5 (rulerTape S (c + 1))
                ⟨fun i => if 1 + Fintype.card Γ * (c - 1) + k ≤ i ∧
                    i < 1 + Fintype.card Γ * c then .blank else g' i,
                  1 + Fintype.card Γ * c⟩ fixedTape⟩ by
        exact h (Fintype.card Γ - k) k hk hk_le rfl g'
      intro r
      induction r with
      | zero =>
        intro k hk hk_le hr g'
        have hkEq : k = Fintype.card Γ := by omega
        subst hkEq
        simp only [Nat.mod_self]
        rw [Nat.add_assoc, hMulCm]
        have hFun : (fun i => if 1 + Fintype.card Γ * c ≤ i ∧ i < 1 + Fintype.card Γ * c
            then SimSym.blank else g' i) = g' := by
          funext i; split_ifs with h <;> [omega; rfl]
        rw [hFun]
      | succ r ih_r =>
        intro k hk hk_le hr g'
        have hkLt : k < Fintype.card Γ := by omega
        have hkMod : k % Fintype.card Γ = k := Nat.mod_eq_of_lt hkLt
        have hPos : 1 + Fintype.card Γ * (c - 1) + k < B := by omega
        have hNext : (k + 1) % Fintype.card Γ = if h1 : k + 1 < Fintype.card Γ then k + 1 else 0 := by
          split_ifs with h1
          · exact Nat.mod_eq_of_lt h1
          · have : k + 1 = Fintype.card Γ := by omega
            rw [this, Nat.mod_self]
        have hStep := rwg_step_one D input B (.clear ⟨k % Fintype.card Γ, Nat.mod_lt _ hw⟩) ih ih
          (rulerTape S (c + 1)) ⟨g', 1 + Fintype.card Γ * (c - 1) + k⟩ fixedTape
          (rulerTape S (c + 1))
          ⟨fun i => if i = 1 + Fintype.card Γ * (c - 1) + k then .blank else g' i,
            1 + Fintype.card Γ * (c - 1) + (k + 1)⟩
          (.inl (.clear ⟨(k + 1) % Fintype.card Γ, Nat.mod_lt _ hw⟩)) .stay
          ((rulerTape S (c + 1)).cells (c + 1), .stay) (.blank, .right)
          (by
            dsimp only [rwCompGen]
            simp only [tapes5_tRuler, hkMod, show ¬ k = 0 by omega, ↓reduceDIte]
            split_ifs with h1
            · exact mk5_congr (by simp [hNext, h1]) rfl rfl rfl
                (fun _ _ _ => rfl)
            · exact mk5_congr (by simp [hNext, h1]) rfl rfl rfl
                (fun _ _ _ => rfl))
          (by simp [moveHead])
          (OneSidedTape.stay_same _)
          (by simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]; rfl)
          (by simp [fixedTape]; omega)
          (by simp [rulerTape]; omega)
          (by simp; omega)
          (by simp [rulerTape]; omega)
          (by simp; omega)
        have hRest := ih_r (k + 1) (by omega) (by omega) (by omega)
          (fun i => if i = 1 + Fintype.card Γ * (c - 1) + k then .blank else g' i)
        have hFun :
            (fun i => if 1 + Fintype.card Γ * (c - 1) + (k + 1) ≤ i ∧
                i < 1 + Fintype.card Γ * c then SimSym.blank
              else if i = 1 + Fintype.card Γ * (c - 1) + k then SimSym.blank else g' i) =
            (fun i => if 1 + Fintype.card Γ * (c - 1) + k ≤ i ∧
                i < 1 + Fintype.card Γ * c then SimSym.blank else g' i) := by
          funext i
          by_cases h1 : i = 1 + Fintype.card Γ * (c - 1) + k
          · subst h1
            have : 1 + Fintype.card Γ * (c - 1) + k < 1 + Fintype.card Γ * c := by omega
            simp [this]
          · have : (1 + Fintype.card Γ * (c - 1) + (k + 1) ≤ i ∧ i < 1 + Fintype.card Γ * c) ↔
                (1 + Fintype.card Γ * (c - 1) + k ≤ i ∧ i < 1 + Fintype.card Γ * c) := by omega
            split_ifs with ha hb <;> first | rfl | (exfalso; omega)
        rw [hFun] at hRest
        exact hStep.trans hRest
    have hFirst := rwg_step_one D input B (.clear ⟨0, hw⟩) ih ih
      (rulerTape S c) ⟨g, 1 + Fintype.card Γ * (c - 1)⟩ fixedTape
      (rulerTape S (c + 1))
      ⟨fun i => if i = 1 + Fintype.card Γ * (c - 1) then .blank else g i,
        1 + Fintype.card Γ * (c - 1) + 1⟩
      (.inl (.clear ⟨1 % Fintype.card Γ, Nat.mod_lt _ hw⟩)) .stay (.bit true, .right) (.blank, .right)
      (by
        dsimp only [rwCompGen]
        have hBit' : (rulerTape S c).cells (rulerTape S c).head = .bit true := hBit
        simp only [tapes5_tRuler, hBit', ↓reduceIte, ↓reduceDIte]
        split_ifs with h1
        · exact mk5_congr (by simp [Nat.mod_eq_of_lt h1]) rfl rfl rfl
            (fun _ _ _ => rfl)
        · exact mk5_congr (by simp [show Fintype.card Γ = 1 by omega]) rfl rfl rfl
            (fun _ _ _ => rfl))
      (by simp [moveHead])
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq, rulerTape]
        congr 1; funext i
        by_cases hi0 : i = 0
        · simp [hi0, show 0 ≠ c by omega]
        · by_cases hic : i = c
          · rw [hic]; simp [hcLt, show c ≠ 0 by omega]
          · simp [hi0, hic])
      (by simp only [OneSidedTape.updateAndMove, moveOneSidedHead])
      (by simp [fixedTape]; omega)
      (by simp [rulerTape]; omega)
      (by simp; omega)
      (by simp [rulerTape]; omega)
      (by simp; omega)
    have hMid := hSub 1 le_rfl hw (fun i => if i = 1 + Fintype.card Γ * (c - 1) then .blank else g i)
    have hTail := ih_d (c + 1) (by omega) (by omega) (by omega)
      (fun i => if 1 + Fintype.card Γ * (c - 1) + 1 ≤ i ∧ i < 1 + Fintype.card Γ * c
        then .blank else if i = 1 + Fintype.card Γ * (c - 1) then .blank else g i)
    have hSubEq : c + 1 - 1 = c := by omega
    rw [hSubEq] at hTail
    have hFunFinal :
        (fun i => if 1 + Fintype.card Γ * c ≤ i ∧ i < 1 + Fintype.card Γ * S then SimSym.blank
          else if 1 + Fintype.card Γ * (c - 1) + 1 ≤ i ∧ i < 1 + Fintype.card Γ * c then SimSym.blank
          else if i = 1 + Fintype.card Γ * (c - 1) then SimSym.blank else g i) =
        (fun i => if 1 + Fintype.card Γ * (c - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
          then SimSym.blank else g i) := by
      funext i
      by_cases hi : i = 1 + Fintype.card Γ * (c - 1)
      · subst hi
        have hlt : 1 + Fintype.card Γ * (c - 1) < 1 + Fintype.card Γ * S := by omega
        simp [hlt]
      · split_ifs <;> first | rfl | (exfalso; omega)
    rw [hFunFinal] at hTail
    exact hFirst.trans (hMid.trans hTail)

theorem rwg_backRuler (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (ih : Fin (n + 2)) (S B : ℕ) (hRB : S + 1 < B) (Sc : OneSidedTape SimSym) (hScB : Sc.head < B) :
    ∀ h, h ≤ S + 1 →
      RWRun (rwCompGen D) input B
        ⟨.inl .backRuler, ih, tapes5 (rulerCap S h) Sc fixedTape⟩
        ⟨.inl .backScratch, ih, tapes5 (rulerCap S 1) Sc fixedTape⟩ := by
  intro h
  induction h with
  | zero =>
    intro _
    refine rwg_step_one D input B .backRuler ih ih (rulerCap S 0) Sc fixedTape
      (rulerCap S 1) Sc (.inl .backScratch) .stay (.leftMark, .right) (Sc.cells Sc.head, .stay)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tRuler, rulerCap, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq, rulerCap]
        congr 1; funext i; by_cases hi : i = 0 <;> simp [hi])
      (OneSidedTape.stay_same _)
      (by simp [fixedTape]; omega) (by simp [rulerCap]; omega) hScB
      (by simp [rulerCap]; omega) hScB
  | succ h ih_h =>
    intro hh
    have hStep := rwg_step_one D input B .backRuler ih ih (rulerCap S (h + 1)) Sc fixedTape
      (rulerCap S h) Sc (.inl .backRuler) .stay
      ((rulerCap S (h + 1)).cells (h + 1), .left) (Sc.cells Sc.head, .stay)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tRuler, rulerCap, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte]
        by_cases hlt : h + 1 ≤ S
        · simp only [hlt, ↓reduceIte]
          exact mk5_congr rfl rfl (by simp) rfl (fun _ _ _ => rfl)
        · have heq : h + 1 = S + 1 := by omega
          simp only [↓reduceIte, heq, show ¬ S + 1 ≤ S by omega]
          exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (write_same_move (rulerCap S (h + 1)) (mv := .left) (h' := h)
          (by simp [rulerCap, moveOneSidedHead]))
      (OneSidedTape.stay_same _)
      (by simp [fixedTape]; omega) (by simp [rulerCap]; omega) hScB
      (by simp [rulerCap]; omega) hScB
    exact hStep.trans (ih_h (by omega))

theorem rwg_backScratch (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (ih : Fin (n + 2)) (B : ℕ) (hB : 1 < B) (R : OneSidedTape SimSym) (hRB : R.head < B)
    (ScCells : ℕ → SimSym) (h0 : ScCells 0 = .leftMark)
    (hNonLeft : ∀ p, 1 ≤ p → ScCells p ≠ .leftMark) :
    ∀ h, h < B →
      RWRun (rwCompGen D) input B
        ⟨.inl .backScratch, ih, tapes5 R ⟨ScCells, h⟩ fixedTape⟩
        ⟨.inr (), ih, tapes5 R ⟨ScCells, 1⟩ fixedTape⟩ := by
  intro h
  induction h with
  | zero =>
    intro _
    refine rwg_step_one D input B .backScratch ih ih R ⟨ScCells, 0⟩ fixedTape
      R ⟨ScCells, 1⟩ (.inr ()) .stay (R.cells R.head, .stay) (.leftMark, .right)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tScratch, h0, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]
        congr 1; funext i; by_cases hi : i = 0 <;> simp [hi, h0])
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
  | succ h ih_h =>
    intro hh
    have hne : ScCells (h + 1) ≠ .leftMark := hNonLeft (h + 1) (by omega)
    have hStep := rwg_step_one D input B .backScratch ih ih R ⟨ScCells, h + 1⟩ fixedTape
      R ⟨ScCells, h⟩ (.inl .backScratch) .stay
      (R.cells R.head, .stay) (ScCells (h + 1), .left)
      (by
        dsimp only [rwCompGen]
        simp only [tapes5_tScratch, hne, ↓reduceIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, h + 1⟩ (mv := .left) (h' := h) (by simp [moveOneSidedHead]))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
    exact hStep.trans (ih_h (by omega))

theorem encodeSym_ne_leftMark (D : MultitapeDTM QD I Γ 1) (γ : Γ)
    (j : Fin (Fintype.card Γ)) : encodeSym D γ j ≠ .leftMark := by
  simp only [encodeSym]
  split_ifs <;> decide

theorem dgood_blank_gen (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I) (S : ℕ)
    {a b : OneSidedTMConfig QD Γ 1 n}
    (hab : Relation.ReflTransGen (DGoodGen D input S) a b)
    (ha : ∀ i, S ≤ i → (a.workTapes 0).cells i = D.blank) :
    ∀ i, S ≤ i → (b.workTapes 0).cells i = D.blank := by
  induction hab with
  | refl => exact ha
  | @tail b c _ hbc ih =>
    obtain ⟨hstep, hb, _⟩ := hbc
    obtain ⟨_, _, _, _, _, _, hup⟩ := hstep
    obtain ⟨h', _, hT⟩ := updateAndMove_eq_gen (hup 0)
    intro i hi
    have hb0 := hb 0
    rw [hT]
    have : i ≠ (b.workTapes 0).head := by omega
    simp [this, ih i hi]

theorem rwg_prefix (D : MultitapeDTM QD I Γ 1) {n : ℕ}
    (input : Fin n → I) (S : ℕ) (hS : 1 ≤ S) (B : ℕ)
    (hB : (Fintype.card Γ + 2) * (S + 1) ≤ B)
    (hHalt : D.HaltsScanningExactly input S) :
    ∃ (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2)),
      PrefixPrepares (rwCompGen D) input S B initTapes inHead := by
  obtain ⟨final, hRun, hNone, hReach, _hFinalWithin⟩ := hHalt
  obtain ⟨mid, hMid, hMidHead⟩ := hReach hS
  have hw := card_pos_of_blank D
  have hSB : Fintype.card Γ * S + 1 < B := by nlinarith
  have hRB : S + 1 < B := by nlinarith
  have h1B : 1 < B := by omega
  have hU : Relator.RightUnique (DGoodGen D input S) :=
    fun a b c h1 h2 => D.oneSidedStep_deterministic input h1.1 h2.1
  have hMF : Relation.ReflTransGen (DGoodGen D input S) mid final := by
    rcases Relation.ReflTransGen.total_of_right_unique hU hMid hRun with h | h
    · exact h
    · rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hs, _⟩
      · rw [h']
      · exfalso
        obtain ⟨a, ha, _⟩ := hs.1
        simp [MultitapeDTM.toNTM, hNone] at ha
  have hFinHeadLt : (final.workTapes 0).head < S := by
    rcases Relation.ReflTransGen.cases_tail hRun with h | ⟨c, _, hstep⟩
    · subst h; simp [MultitapeNTM.oneSidedInitialConfig]; exact hS
    · exact hstep.2.2 0
  have hScFin : Fintype.card Γ * (final.workTapes 0).head + Fintype.card Γ ≤ Fintype.card Γ * S := by
    have := Nat.mul_le_mul_left (Fintype.card Γ) (show (final.workTapes 0).head + 1 ≤ S by omega)
    simpa [mul_add] using this
  have hPre : RWRun (rwCompGen D) input B
      ⟨.inl .pre, ⟨0, by omega⟩, fun _ => ⟨fun _ => .blank, 0⟩⟩
      (rwgCfg D D.toNTM.oneSidedInitialConfig 0) :=
    Relation.ReflTransGen.single
      ⟨rwg_pre_step D input, fun _ => by simp; omega,
        tapes5_head_lt _ _ _ _ (by simp [rulerTape]; exact h1B)
          (by simp only [scratchEnc, MultitapeNTM.oneSidedInitialConfig, mul_zero, add_zero]; exact h1B)
          (by simp [fixedTape]; omega)⟩
  obtain ⟨m₁, _, hm1S, hR1, _, hmidS, hmid_m1⟩ := rwg_sim_run D input S B hSB hRB hMid 0 (Nat.zero_le _)
    (by simp [MultitapeNTM.oneSidedInitialConfig]; omega)
    (by simp [MultitapeNTM.oneSidedInitialConfig])
  obtain ⟨m₂, hm12, hm2S, hR2, hm2ne, hfinS, hfin_m2⟩ := rwg_sim_run D input S B hSB hRB hMF m₁ hm1S hmidS hmid_m1
  have hM := dgood_mid_le_gen D input S hMF hMidHead m₂ hm2ne hm2S
  have hHaltStep := rwg_halt_step D input S B hSB hRB final hfinS hNone m₂ hm2S hfin_m2
  rw [hM] at hHaltStep
  have hGoL := rwg_goLeftRuler D input final.inputHead S B hRB
    (scratchEnc D (final.workTapes 0)
      (1 + Fintype.card Γ * (final.workTapes 0).head + (Fintype.card Γ - 1)))
    (by simp [scratchEnc]; omega)
    ((final.workTapes 0).head + 1) (by omega)
  have hGoS := rwg_goLeftScratch D input final.inputHead B h1B (rulerTape S 1)
    (by simp [rulerTape]; omega)
    (scratchEnc D (final.workTapes 0) 0).cells
    (scratchEnc_at_zero D (final.workTapes 0) 0)
    (fun p hp => by
      simp only [scratchEnc, show p ≠ 0 by omega, ↓reduceIte]
      exact encodeSym_ne_leftMark D _ _)
    (1 + Fintype.card Γ * (final.workTapes 0).head + (Fintype.card Γ - 1))
    (by omega)
  have hClear := rwg_clear D input final.inputHead S B hRB (by omega) S 1 rfl le_rfl (by omega)
    (scratchEnc D (final.workTapes 0) 0).cells
  have hBackR := rwg_backRuler D input final.inputHead S B hRB
    ⟨fun i => if 1 + Fintype.card Γ * (1 - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
      then .blank else (scratchEnc D (final.workTapes 0) 0).cells i, 1 + Fintype.card Γ * S⟩
    (by simp; omega) (S + 1) le_rfl
  have hBackS := rwg_backScratch D input final.inputHead B h1B (rulerCap S 1)
    (by simp [rulerCap]; omega)
    (fun i => if 1 + Fintype.card Γ * (1 - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
      then .blank else (scratchEnc D (final.workTapes 0) 0).cells i)
    (by simp [scratchEnc])
    (fun p hp => by
      split_ifs
      · decide
      · simp only [scratchEnc, show p ≠ 0 by omega, ↓reduceIte]
        exact encodeSym_ne_leftMark D _ _)
    (1 + Fintype.card Γ * S) (by have := Nat.lt_of_succ_lt hSB; omega)
  have hTotal := hPre.trans (hR1.trans (hR2.trans (hHaltStep.trans
    (hGoL.trans (hGoS.trans (hClear.trans (hBackR.trans hBackS)))))))
  refine ⟨tapes5 (rulerCap S 1)
    ⟨fun i => if 1 + Fintype.card Γ * (1 - 1) ≤ i ∧ i < 1 + Fintype.card Γ * S
      then .blank else (scratchEnc D (final.workTapes 0) 0).cells i, 1⟩ fixedTape,
    final.inputHead, hTotal, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tapes5_tRuler]; exact rulerCap_matches S
  · have ht : ∀ Sc, tapes5 (rulerCap S 1) Sc fixedTape tRegs = fixedTape := fun Sc => by
      simp [tapes5, show tRegs ≠ tRuler by decide, show tRegs ≠ tScratch by decide]
    rw [ht]; exact fixedTape_matches
  · have ht : ∀ Sc, tapes5 (rulerCap S 1) Sc fixedTape tArgA = fixedTape := fun Sc => by
      simp [tapes5, show tArgA ≠ tRuler by decide, show tArgA ≠ tScratch by decide]
    rw [ht]; exact fixedTape_matches
  · have ht : ∀ Sc, tapes5 (rulerCap S 1) Sc fixedTape tArgB = fixedTape := fun Sc => by
      simp [tapes5, show tArgB ≠ tRuler by decide, show tArgB ≠ tScratch by decide]
    rw [ht]; exact fixedTape_matches
  · rw [tapes5_tScratch]
    refine ⟨rfl, fun i => ?_⟩
    by_cases hi0 : i = 0
    · simp [hi0, scratchEnc]
    · by_cases hiS : i < 1 + Fintype.card Γ * S
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp [hiS]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hFinBlank : ∀ x, S ≤ x → (final.workTapes 0).cells x = D.blank :=
          dgood_blank_gen D input S hRun (fun _ _ => rfl)
        have hDiv : S ≤ j / Fintype.card Γ := by
          have := Nat.div_add_mod j (Fintype.card Γ)
          have := Nat.mod_lt j hw
          nlinarith
        simp [scratchEnc, hFinBlank _ hDiv, encodeSym_blank]

end Proofs

end SavitchLemma

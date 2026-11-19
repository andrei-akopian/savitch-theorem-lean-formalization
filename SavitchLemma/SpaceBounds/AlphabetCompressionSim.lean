module

public import SavitchLemma.SpaceBounds.AlphabetCompressionDef
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Alphabet Compression Correctness Proofs

Simulation, cleanup, and `rwg_prefix` proofs for `rwCompGen`.
-/

namespace SavitchLemma

section Proofs

variable {QD I Γ : Type} [Fintype QD] [Fintype I] [Fintype Γ]

theorem rwg_pre_step (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I) :
    (rwCompGen D).CompStep input
      ⟨.inl .pre, ⟨0, by omega⟩, fun _ => ⟨fun _ => .blank, 0⟩⟩
      (rwgCfg (n := n) D D.toNTM.oneSidedInitialConfig 0) := by
  refine ⟨.pre, rfl, ?_⟩
  refine ⟨rfl, ⟨0, by omega⟩, rfl, rfl, ?_⟩
  intro t
  have hbl : D.toNTM.blank = D.blank := rfl
  simp [rwCompGen, mk5, OneSidedTape.updateAndMove, moveOneSidedHead, rwgCfg, tapes5,
    rulerTape, scratchEnc, fixedTape, MultitapeNTM.oneSidedInitialConfig, hbl]
  split_ifs <;> first | (congr 1; funext i; by_cases hi : i = 0 <;> simp [hi, encodeSym_blank]) | rfl

theorem rwg_read_loop (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S < B) (hRB : S < B)
    (q : QD) (ih : Fin (n + 2)) (T : OneSidedTape Γ) (hTS : T.head < S)
    (m : ℕ) (_hm : m ≤ S) :
    ∀ (k : ℕ) (hk : k < Fintype.card Γ) (buf : Fin (Fintype.card Γ) → SimSym),
      (∀ j : Fin (Fintype.card Γ), j.val < k → buf j = encodeSym D (T.cells T.head) j) →
      RWRun (rwCompGen D) input B
        ⟨.inl (.read q ⟨k, hk⟩ buf), ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchEnc D T (1 + Fintype.card Γ * T.head + k)) fixedTape⟩
        ⟨.inl (.read q ⟨Fintype.card Γ - 1, Nat.sub_lt (card_pos_of_blank D) one_pos⟩
            (fun j => if j.val + 1 = Fintype.card Γ then buf j
              else encodeSym D (T.cells T.head) j)),
          ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchEnc D T (1 + Fintype.card Γ * T.head + (Fintype.card Γ - 1))) fixedTape⟩ := by
  intro k
  have hw := card_pos_of_blank D
  -- Induct on `Fintype.card Γ - 1 - k`
  suffices h : ∀ d k (hk : k < Fintype.card Γ) (hd : Fintype.card Γ - 1 - k = d)
      (buf : Fin (Fintype.card Γ) → SimSym)
      (hbuf : ∀ j : Fin (Fintype.card Γ), j.val < k → buf j = encodeSym D (T.cells T.head) j),
      RWRun (rwCompGen D) input B
        ⟨.inl (.read q ⟨k, hk⟩ buf), ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchEnc D T (1 + Fintype.card Γ * T.head + k)) fixedTape⟩
        ⟨.inl (.read q ⟨Fintype.card Γ - 1, Nat.sub_lt hw one_pos⟩
            (fun j => if j.val + 1 = Fintype.card Γ then buf j
              else encodeSym D (T.cells T.head) j)),
          ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchEnc D T (1 + Fintype.card Γ * T.head + (Fintype.card Γ - 1))) fixedTape⟩ by
    intro hk buf hbuf
    exact h (Fintype.card Γ - 1 - k) k hk rfl buf hbuf
  intro d
  induction d with
  | zero =>
    intro k hk hd buf hbuf
    have hk_eq : k = Fintype.card Γ - 1 := by omega
    subst hk_eq
    have hbuf_eq : (fun j : Fin (Fintype.card Γ) =>
        if j.val + 1 = Fintype.card Γ then buf j else encodeSym D (T.cells T.head) j) = buf := by
      funext j
      split_ifs with hj
      · rfl
      · exact (hbuf j (by omega)).symm
    rw [hbuf_eq]
  | succ d ih_d =>
    intro k hk hd buf hbuf
    have hlt : k + 1 < Fintype.card Γ := by omega
    have hcell : (scratchEnc D T (1 + Fintype.card Γ * T.head + k)).cells
        (1 + Fintype.card Γ * T.head + k) = encodeSym D (T.cells T.head) ⟨k, hk⟩ :=
      scratchEnc_cell_block D T _ T.head k hk
    have hScB1 : Fintype.card Γ * T.head + Fintype.card Γ ≤ Fintype.card Γ * S := by
      have := Nat.mul_le_mul_left (Fintype.card Γ) (show T.head + 1 ≤ S by omega)
      simpa [mul_add] using this
    have hStep := rwg_step_one D input B (.read q ⟨k, hk⟩ buf) ih ih
      (rulerTape m (T.head + 1)) (scratchEnc D T (1 + Fintype.card Γ * T.head + k)) fixedTape
      (rulerTape m (T.head + 1)) (scratchEnc D T (1 + Fintype.card Γ * T.head + (k + 1)))
      (.inl (.read q ⟨k + 1, hlt⟩
        (Function.update buf ⟨k, hk⟩ (encodeSym D (T.cells T.head) ⟨k, hk⟩))))
      .stay
      ((rulerTape m (T.head + 1)).cells (T.head + 1), .stay)
      (encodeSym D (T.cells T.head) ⟨k, hk⟩, .right)
      (by
        have hcell' : (scratchEnc D T (1 + Fintype.card Γ * T.head + k)).cells
            (scratchEnc D T (1 + Fintype.card Γ * T.head + k)).head =
            encodeSym D (T.cells T.head) ⟨k, hk⟩ := hcell
        simp only [rwCompGen, hlt, ↓reduceDIte, tapes5_tRuler, tapes5_tScratch, hcell']
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (by
        have h1 := write_same_move (scratchEnc D T (1 + Fintype.card Γ * T.head + k))
          (mv := .right) (h' := 1 + Fintype.card Γ * T.head + (k + 1))
          (by simp [moveOneSidedHead]; rfl)
        have hcell' : (scratchEnc D T (1 + Fintype.card Γ * T.head + k)).cells
            (scratchEnc D T (1 + Fintype.card Γ * T.head + k)).head =
            encodeSym D (T.cells T.head) ⟨k, hk⟩ := hcell
        rw [hcell'] at h1
        exact h1)
      (by simp [fixedTape]; omega)
      (by simp [rulerTape]; omega)
      (by simp [scratchEnc]; omega)
      (by simp [rulerTape]; omega)
      (by simp [scratchEnc]; omega)
    have hRest := ih_d (k + 1) hlt (by omega)
      (Function.update buf ⟨k, hk⟩ (encodeSym D (T.cells T.head) ⟨k, hk⟩))
      (fun j hj => by
        by_cases hj' : j = ⟨k, hk⟩
        · subst hj'; simp
        · have hjv : j.val < k := by
            have : j.val ≠ k := fun h => hj' (Fin.ext h)
            omega
          simp [Function.update, hj', hbuf j hjv])
    have hbuf_eq :
        (fun j : Fin (Fintype.card Γ) =>
          if j.val + 1 = Fintype.card Γ then
            Function.update buf ⟨k, hk⟩ (encodeSym D (T.cells T.head) ⟨k, hk⟩) j
          else encodeSym D (T.cells T.head) j) =
        (fun j : Fin (Fintype.card Γ) =>
          if j.val + 1 = Fintype.card Γ then buf j
          else encodeSym D (T.cells T.head) j) := by
      funext j
      split_ifs with hj
      · have hne : j ≠ ⟨k, hk⟩ := fun heq => by
          subst heq
          simp only at hj
          omega
        simp [Function.update, hne]
      · rfl
    rw [hbuf_eq] at hRest
    exact hStep.trans hRest

theorem rwg_writeBack_loop (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S < B) (hRB : S < B)
    (q' : QD) (im wm : TapeMove) (γ' : Γ) (ih : Fin (n + 2)) (T : OneSidedTape Γ)
    (hTS : T.head < S) (m : ℕ) (_hm : m ≤ S) :
    ∀ (k : ℕ) (hk : k < Fintype.card Γ),
      RWRun (rwCompGen D) input B
        ⟨.inl (.writeBack q' im wm γ' ⟨k, hk⟩), ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchPartial D T T.head γ' (k + 1) (1 + Fintype.card Γ * T.head + k)) fixedTape⟩
        ⟨.inl (.writeBack q' im wm γ' ⟨0, card_pos_of_blank D⟩), ih,
          tapes5 (rulerTape m (T.head + 1))
            (scratchPartial D T T.head γ' 1 (1 + Fintype.card Γ * T.head)) fixedTape⟩ := by
  intro k
  induction k with
  | zero =>
    intro _
    exact Relation.ReflTransGen.refl
  | succ k ih_k =>
    intro hk
    have hw := card_pos_of_blank D
    have hStep := rwg_step_one D input B (.writeBack q' im wm γ' ⟨k + 1, hk⟩) ih ih
      (rulerTape m (T.head + 1))
      (scratchPartial D T T.head γ' (k + 1 + 1) (1 + Fintype.card Γ * T.head + (k + 1))) fixedTape
      (rulerTape m (T.head + 1))
      (scratchPartial D T T.head γ' (k + 1) (1 + Fintype.card Γ * T.head + k))
      (.inl (.writeBack q' im wm γ' ⟨k, by omega⟩))
      .stay
      ((rulerTape m (T.head + 1)).cells (T.head + 1), .stay)
      (encodeSym D γ' ⟨k + 1, hk⟩, .left)
      (by
        simp only [rwCompGen, dite_eq_right (fun h => absurd h (by omega : ¬ k + 1 = 0)), tapes5_tRuler]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (scratchPartial_update D T T.head γ' (k + 1) hk .left _
        (by simp [moveOneSidedHead]))
      (by simp [fixedTape]; omega)
      (by simp [rulerTape]; omega)
      (by
        have h1 : Fintype.card Γ * T.head + Fintype.card Γ ≤ Fintype.card Γ * S := by
          have := Nat.mul_le_mul_left (Fintype.card Γ) (show T.head + 1 ≤ S by omega)
          simpa [mul_add] using this
        simp [scratchPartial]; omega)
      (by simp [rulerTape]; omega)
      (by
        have h1 : Fintype.card Γ * T.head + Fintype.card Γ ≤ Fintype.card Γ * S := by
          have := Nat.mul_le_mul_left (Fintype.card Γ) (show T.head + 1 ≤ S by omega)
          simpa [mul_add] using this
        simp [scratchPartial]; omega)
    exact hStep.trans (ih_k (by omega))

theorem rwg_shiftR_loop (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (B : ℕ) (q' : QD) (ih : Fin (n + 2)) (R : OneSidedTape SimSym) (hRB : R.head < B)
    (ScCells : ℕ → SimSym) :
    ∀ (r : ℕ) (hr : r < Fintype.card Γ) (p : ℕ) (_hp : p + r + 1 < B),
      RWRun (rwCompGen D) input B
        ⟨.inl (.shiftR q' ⟨r, hr⟩), ih, tapes5 R ⟨ScCells, p⟩ fixedTape⟩
        ⟨.inl (.read q' ⟨0, card_pos_of_blank D⟩ (fun _ => .blank)), ih,
          tapes5 R ⟨ScCells, p + r + 1⟩ fixedTape⟩ := by
  intro r
  induction r with
  | zero =>
    intro hr p hp
    refine rwg_step_one D input B (.shiftR q' ⟨0, hr⟩) ih ih R ⟨ScCells, p⟩ fixedTape
      R ⟨ScCells, p + 0 + 1⟩ (.inl (.read q' ⟨0, card_pos_of_blank D⟩ (fun _ => .blank)))
      .stay (R.cells R.head, .stay) (ScCells p, .right)
      (by simp [rwCompGen, mk5])
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, p⟩ (mv := .right) (h' := p + 0 + 1)
        (by simp [moveOneSidedHead]))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
  | succ r ih_r =>
    intro hr p hp
    have hStep := rwg_step_one D input B (.shiftR q' ⟨r + 1, hr⟩) ih ih R ⟨ScCells, p⟩ fixedTape
      R ⟨ScCells, p + 1⟩ (.inl (.shiftR q' ⟨r, by omega⟩))
      .stay (R.cells R.head, .stay) (ScCells p, .right)
      (by simp [rwCompGen, mk5])
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, p⟩ (mv := .right) (h' := p + 1)
        (by simp [moveOneSidedHead]))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
    have hRest := ih_r (by omega) (p + 1) (by omega)
    have hpEq : p + 1 + r + 1 = p + (r + 1) + 1 := by omega
    rw [hpEq] at hRest
    exact hStep.trans hRest

theorem rwg_shiftL_loop (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (B : ℕ) (q' : QD) (ih : Fin (n + 2)) (R : OneSidedTape SimSym) (hRB : R.head < B)
    (ScCells : ℕ → SimSym) :
    ∀ (r : ℕ) (hr : r < Fintype.card Γ) (p : ℕ) (_hp0 : r + 1 ≤ p) (_hpB : p < B),
      RWRun (rwCompGen D) input B
        ⟨.inl (.shiftL q' ⟨r, hr⟩), ih, tapes5 R ⟨ScCells, p⟩ fixedTape⟩
        ⟨.inl (.read q' ⟨0, card_pos_of_blank D⟩ (fun _ => .blank)), ih,
          tapes5 R ⟨ScCells, p - (r + 1)⟩ fixedTape⟩ := by
  intro r
  induction r with
  | zero =>
    intro hr p hp0 hpB
    refine rwg_step_one D input B (.shiftL q' ⟨0, hr⟩) ih ih R ⟨ScCells, p⟩ fixedTape
      R ⟨ScCells, p - 1⟩ (.inl (.read q' ⟨0, card_pos_of_blank D⟩ (fun _ => .blank)))
      .stay (R.cells R.head, .stay) (ScCells p, .left)
      (by simp [rwCompGen, mk5])
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, p⟩ (mv := .left) (h' := p - 1)
        (by simp [moveOneSidedHead]; omega))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
  | succ r ih_r =>
    intro hr p hp0 hpB
    have hStep := rwg_step_one D input B (.shiftL q' ⟨r + 1, hr⟩) ih ih R ⟨ScCells, p⟩ fixedTape
      R ⟨ScCells, p - 1⟩ (.inl (.shiftL q' ⟨r, by omega⟩))
      .stay (R.cells R.head, .stay) (ScCells p, .left)
      (by simp [rwCompGen, mk5])
      (by simp [moveHead])
      (OneSidedTape.stay_same _)
      (write_same_move ⟨ScCells, p⟩ (mv := .left) (h' := p - 1)
        (by simp [moveOneSidedHead]; omega))
      (by simp [fixedTape]; omega) hRB (by simp; omega) hRB (by simp; omega)
    have hRest := ih_r (by omega) (p - 1) (by omega) (by omega)
    have hpEq : p - 1 - (r + 1) = p - (r + 1 + 1) := by omega
    rw [hpEq] at hRest
    exact hStep.trans hRest

theorem rulerTape_updateAndMove_bit (m h h' : ℕ) (hm_head : h ≤ m) (mv : TapeMove)
    (hmv : moveOneSidedHead h mv = some h') :
    (rulerTape m (h + 1)).updateAndMove (.bit true) mv =
      some (rulerTape (max m (h + 1)) (h' + 1)) := by
  simp only [OneSidedTape.updateAndMove]
  cases mv
  · cases h with
    | zero => simp [moveOneSidedHead] at hmv
    | succ h =>
      simp only [moveOneSidedHead, Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel,
        Option.some.injEq] at hmv
      have hmv1 : moveOneSidedHead (h + 1 + 1) .left = some (h' + 1) := by
        simp [moveOneSidedHead, ← hmv]
      dsimp only [rulerTape]
      rw [hmv1]
      simp only [Option.some.injEq]
      congr 1; funext p
      by_cases hp0 : p = 0
      · simp [hp0]
      · by_cases hph : p = h + 1 + 1
        · subst hph; simp
        · have hMax : (p ≤ max m (h + 1 + 1)) ↔ (p ≤ m) := by omega
          simp [hp0, hph, hMax]
  · simp only [moveOneSidedHead, Option.some.injEq] at hmv
    subst hmv; simp only [moveOneSidedHead]
    congr 1; simp only [rulerTape]; congr 1; funext p
    by_cases hp0 : p = 0
    · simp [hp0]
    · by_cases hph : p = h + 1
      · subst hph; simp
      · have hMax : (p ≤ max m (h + 1)) ↔ (p ≤ m) := by omega
        simp [hp0, hph, hMax]
  · simp only [moveOneSidedHead, Option.some.injEq] at hmv
    subst hmv; simp only [moveOneSidedHead]
    congr 1; simp only [rulerTape]; congr 1; funext p
    by_cases hp0 : p = 0
    · simp [hp0]
    · by_cases hph : p = h + 1
      · subst hph; simp
      · have hMax : (p ≤ max m (h + 1)) ↔ (p ≤ m) := by omega
        simp [hp0, hph, hMax]

theorem rwg_sim_step (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S + 1 < B) (hRB : S + 1 < B)
    (m : ℕ) (hm : m ≤ S) {a b : OneSidedTMConfig QD Γ 1 n}
    (ha_m : (a.workTapes 0).head ≤ m)
    (hStep : DGoodGen D input S a b) :
    RWRun (rwCompGen D) input B (rwgCfg D a m)
      (rwgCfg D b (max m ((a.workTapes 0).head + 1))) := by
  obtain ⟨⟨act, hActMem, hState, ih', hIn, hInEq, hUp⟩, haW, hbW⟩ := hStep
  subst hInEq
  have hTrans : D.transition a.state (readInput input a.inputHead) a.scannedWork = some act := by
    simpa [MultitapeDTM.toNTM] using hActMem
  have ha0 : (a.workTapes 0).head < S := haW 0
  have hb0 : (b.workTapes 0).head < S := hbW 0
  set w := Fintype.card Γ
  have hw := card_pos_of_blank D
  have hRead := rwg_read_loop D input S B (Nat.lt_of_succ_lt hSB) (Nat.lt_of_succ_lt hRB)
    a.state a.inputHead (a.workTapes 0) ha0 m hm 0 hw (fun _ => .blank)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
  have hSB' : w * S + 1 < B := hSB
  have hScB1 : w * (a.workTapes 0).head + w ≤ w * S := by
    have := Nat.mul_le_mul_left w (show (a.workTapes 0).head + 1 ≤ S by omega)
    simpa [mul_add] using this
  have hScB2 : w * (b.workTapes 0).head + w ≤ w * S := by
    have := Nat.mul_le_mul_left w (show (b.workTapes 0).head + 1 ≤ S by omega)
    simpa [mul_add] using this
  have hBufUpdate :
      Function.update
        (fun j : Fin w => if j.val + 1 = w then SimSym.blank
          else encodeSym D ((a.workTapes 0).cells (a.workTapes 0).head) j)
        ⟨w - 1, Nat.sub_lt hw one_pos⟩
        ((scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1))).cells
          (1 + w * (a.workTapes 0).head + (w - 1))) =
      encodeSym D ((a.workTapes 0).cells (a.workTapes 0).head) := by
    funext j
    by_cases hj : j = ⟨w - 1, Nat.sub_lt hw one_pos⟩
    · subst hj
      have hcb := scratchEnc_cell_block D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1))
        (a.workTapes 0).head (w - 1) (Nat.sub_lt hw one_pos)
      simpa [w] using hcb
    · have hjv : j.val + 1 ≠ w := fun h => hj (Fin.ext (by simp at h ⊢; omega))
      simp [Function.update, hj, hjv]
  have hDec : decodeBlock D (encodeSym D ((a.workTapes 0).cells (a.workTapes 0).head)) =
      (a.workTapes 0).cells (a.workTapes 0).head := decodeBlock_encodeSym D _
  have hNotLt : ¬ ((w - 1) + 1 < Fintype.card Γ) := by omega
  have hTransStep := rwg_step_one D input B
    (.read a.state ⟨w - 1, Nat.sub_lt hw one_pos⟩
      (fun j => if j.val + 1 = w then SimSym.blank
        else encodeSym D ((a.workTapes 0).cells (a.workTapes 0).head) j))
    a.inputHead a.inputHead
    (rulerTape m ((a.workTapes 0).head + 1))
    (scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1))) fixedTape
    (rulerTape m ((a.workTapes 0).head + 1))
    (scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1)))
    (.inl (.writeBack act.nextState act.inputMove (act.workMove 0) (act.write 0)
      ⟨w - 1, Nat.sub_lt hw one_pos⟩))
    .stay
    ((rulerTape m ((a.workTapes 0).head + 1)).cells ((a.workTapes 0).head + 1), .stay)
    ((scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1))).cells
      (1 + w * (a.workTapes 0).head + (w - 1)), .stay)
    (by
      simp only [rwCompGen, hNotLt, ↓reduceDIte, tapes5_tRuler, tapes5_tScratch]
      rw [show (scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1))).head =
          1 + w * (a.workTapes 0).head + (w - 1) from rfl, hBufUpdate, hDec]
      have hSc : a.scannedWork = fun _ => (a.workTapes 0).cells (a.workTapes 0).head := by
        funext t; rw [Subsingleton.elim t 0]; rfl
      rw [← hSc, hTrans]
      exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
    (by simp [moveHead])
    (OneSidedTape.stay_same _)
    (OneSidedTape.stay_same _)
    (by simp [fixedTape]; omega)
    (by simp [rulerTape]; omega)
    (by simp [scratchEnc]; omega)
    (by simp [rulerTape]; omega)
    (by simp [scratchEnc]; omega)
  have hWB := rwg_writeBack_loop D input S B (Nat.lt_of_succ_lt hSB) (Nat.lt_of_succ_lt hRB)
    act.nextState act.inputMove (act.workMove 0) (act.write 0) a.inputHead
    (a.workTapes 0) ha0 m hm (w - 1) (Nat.sub_lt hw one_pos)
  have hTopEq : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0)
      (w - 1 + 1) (1 + w * (a.workTapes 0).head + (w - 1)) =
      scratchEnc D (a.workTapes 0) (1 + w * (a.workTapes 0).head + (w - 1)) := by
    have hweq : w - 1 + 1 = w := by omega
    rw [hweq, scratchPartial_top]
  rw [hTopEq] at hWB
  have hUp0 := updateAndMove_eq_gen (hUp 0)
  obtain ⟨hbHead, hMvHead, hTb⟩ := hUp0
  have hbHeadEq : hbHead = (b.workTapes 0).head := by rw [hTb]
  subst hbHeadEq
  have hNewT : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 0
      (1 + w * (a.workTapes 0).head) =
      scratchEnc D (b.workTapes 0) (1 + w * (a.workTapes 0).head) := by
    rw [scratchPartial_zero, hTb]
    rfl
  have hRulerMv : (rulerTape m ((a.workTapes 0).head + 1)).updateAndMove (.bit true)
      (act.workMove 0) =
      some (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1)) :=
    rulerTape_updateAndMove_bit m (a.workTapes 0).head (b.workTapes 0).head ha_m (act.workMove 0) hMvHead
  have hWriteZero :
      RWRun (rwCompGen D) input B
        ⟨.inl (.writeBack act.nextState act.inputMove (act.workMove 0) (act.write 0) ⟨0, hw⟩),
          a.inputHead,
          tapes5 (rulerTape m ((a.workTapes 0).head + 1))
            (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
              (1 + w * (a.workTapes 0).head))
            fixedTape⟩
        (rwgCfg D b (max m ((a.workTapes 0).head + 1))) := by
    rw [rwgCfg, hState]
    cases hwm : act.workMove 0 with
    | stay =>
      have hbEq : (b.workTapes 0).head = (a.workTapes 0).head := by
        rw [hwm] at hMvHead; simp [moveOneSidedHead] at hMvHead; exact hMvHead.symm
      refine rwg_step_one D input B
        (.writeBack act.nextState act.inputMove .stay (act.write 0) ⟨0, hw⟩)
        a.inputHead b.inputHead
        (rulerTape m ((a.workTapes 0).head + 1))
        (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
          (1 + w * (a.workTapes 0).head))
        fixedTape
        (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
        (scratchEnc D (b.workTapes 0) (1 + w * (b.workTapes 0).head))
        (.inl (.read act.nextState ⟨0, hw⟩ (fun _ => .blank)))
        act.inputMove (.bit true, .stay) (encodeSym D (act.write 0) ⟨0, hw⟩, .stay)
        (by
          dsimp only [rwCompGen]
          simp only [↓reduceDIte])
        hIn (by rw [← hwm]; exact hRulerMv)
        (by
          rw [hbEq, ← hNewT]
          simpa [w] using scratchPartial_update D (a.workTapes 0) (a.workTapes 0).head
            (act.write 0) 0 hw .stay (1 + Fintype.card Γ * (a.workTapes 0).head)
            (by simp [moveOneSidedHead]))
        (by simp [fixedTape]; omega)
        (by simp [rulerTape]; omega)
        (by simp [scratchPartial]; omega)
        (by simp [rulerTape]; omega)
        (by simp [scratchEnc]; omega)
    | right =>
      have hbEq : (b.workTapes 0).head = (a.workTapes 0).head + 1 := by
        rw [hwm] at hMvHead; simp [moveOneSidedHead] at hMvHead; exact hMvHead.symm
      by_cases hw1 : 1 < Fintype.card Γ
      · have hStep0 := rwg_step_one D input B
          (.writeBack act.nextState act.inputMove .right (act.write 0) ⟨0, hw⟩)
          a.inputHead b.inputHead
          (rulerTape m ((a.workTapes 0).head + 1))
          (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
            (1 + w * (a.workTapes 0).head))
          fixedTape
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (scratchEnc D (b.workTapes 0) (1 + w * (a.workTapes 0).head + 1))
          (.inl (.shiftR act.nextState ⟨w - 2, by omega⟩))
          act.inputMove (.bit true, .right) (encodeSym D (act.write 0) ⟨0, hw⟩, .right)
          (by
            dsimp only [rwCompGen]
            simp only [↓reduceDIte, hw1]
            exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
          hIn (by rw [← hwm]; exact hRulerMv)
          (by
            have hsc := scratchPartial_update D (a.workTapes 0) (a.workTapes 0).head
              (act.write 0) 0 hw .right (1 + Fintype.card Γ * (a.workTapes 0).head + 1)
              (by simp [moveOneSidedHead])
            have hEq2 : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 0
                (1 + Fintype.card Γ * (a.workTapes 0).head + 1) =
                scratchEnc D (b.workTapes 0) (1 + w * (a.workTapes 0).head + 1) := by
              rw [scratchPartial_zero, hTb]; rfl
            simpa [hEq2, w] using hsc)
          (by simp [fixedTape]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchPartial]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchEnc]; omega)
        have hShift := rwg_shiftR_loop D input B act.nextState b.inputHead
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (by simp [rulerTape]; omega)
          (scratchEnc D (b.workTapes 0) 0).cells (w - 2) (by omega)
          (1 + w * (a.workTapes 0).head + 1) (by omega)
        have hP : 1 + w * (a.workTapes 0).head + 1 + (w - 2) + 1 = 1 + w * (b.workTapes 0).head := by
          rw [hbEq, mul_add, mul_one]; omega
        rw [hP] at hShift
        exact hStep0.trans hShift
      · have hwEq : w = 1 := by omega
        refine rwg_step_one D input B
          (.writeBack act.nextState act.inputMove .right (act.write 0) ⟨0, hw⟩)
          a.inputHead b.inputHead
          (rulerTape m ((a.workTapes 0).head + 1))
          (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
            (1 + w * (a.workTapes 0).head))
          fixedTape
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (scratchEnc D (b.workTapes 0) (1 + w * (b.workTapes 0).head))
          (.inl (.read act.nextState ⟨0, hw⟩ (fun _ => .blank)))
          act.inputMove (.bit true, .right) (encodeSym D (act.write 0) ⟨0, hw⟩, .right)
          (by
            dsimp only [rwCompGen]
            simp only [↓reduceDIte, hw1])
          hIn (by rw [← hwm]; exact hRulerMv)
          (by
            have hsc := scratchPartial_update D (a.workTapes 0) (a.workTapes 0).head
              (act.write 0) 0 hw .right (1 + w * (b.workTapes 0).head)
              (by
                dsimp only [w] at hwEq ⊢
                rw [hbEq, hwEq]
                simp [moveOneSidedHead]; omega)
            have hEq2 : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 0
                (1 + w * (b.workTapes 0).head) =
                scratchEnc D (b.workTapes 0) (1 + w * (b.workTapes 0).head) := by
              rw [scratchPartial_zero, hTb]; rfl
            simpa [hEq2] using hsc)
          (by simp [fixedTape]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchPartial]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchEnc, hwEq]; omega)
    | left =>
      have hpos : 0 < (a.workTapes 0).head := by
        rw [hwm] at hMvHead; simp only [moveOneSidedHead] at hMvHead
        split_ifs at hMvHead with h0
        exact h0
      have hbEq : (b.workTapes 0).head + 1 = (a.workTapes 0).head := by
        rw [hwm] at hMvHead; simp only [moveOneSidedHead] at hMvHead
        split_ifs at hMvHead
        simp only [Option.some.injEq] at hMvHead; omega
      by_cases hw1 : 1 < Fintype.card Γ
      · have hStep0 := rwg_step_one D input B
          (.writeBack act.nextState act.inputMove .left (act.write 0) ⟨0, hw⟩)
          a.inputHead b.inputHead
          (rulerTape m ((a.workTapes 0).head + 1))
          (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
            (1 + w * (a.workTapes 0).head))
          fixedTape
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (scratchEnc D (b.workTapes 0) (1 + w * (a.workTapes 0).head - 1))
          (.inl (.shiftL act.nextState ⟨w - 2, by omega⟩))
          act.inputMove (.bit true, .left) (encodeSym D (act.write 0) ⟨0, hw⟩, .left)
          (by
            dsimp only [rwCompGen]
            simp only [↓reduceDIte, hw1]
            exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
          hIn (by rw [← hwm]; exact hRulerMv)
          (by
            dsimp only [w]
            have hsc := scratchPartial_update D (a.workTapes 0) (a.workTapes 0).head
              (act.write 0) 0 hw .left (1 + Fintype.card Γ * (a.workTapes 0).head - 1)
              (by simp [moveOneSidedHead])
            have hEq2 : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 0
                (1 + Fintype.card Γ * (a.workTapes 0).head - 1) =
                scratchEnc D (b.workTapes 0) (1 + Fintype.card Γ * (a.workTapes 0).head - 1) := by
              rw [scratchPartial_zero, hTb]; rfl
            rw [← hEq2]
            exact hsc)
          (by simp [fixedTape]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchPartial]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchEnc]; omega)
        have hShift := rwg_shiftL_loop D input B act.nextState b.inputHead
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (by simp [rulerTape]; omega)
          (scratchEnc D (b.workTapes 0) 0).cells (w - 2) (by omega)
          (1 + w * (a.workTapes 0).head - 1)
          (by
            have : w ≤ w * (a.workTapes 0).head := Nat.le_mul_of_pos_right w hpos
            omega)
          (by omega)
        have hP : 1 + w * (a.workTapes 0).head - 1 - (w - 2 + 1) = 1 + w * (b.workTapes 0).head := by
          have : w * (a.workTapes 0).head = w * (b.workTapes 0).head + w := by rw [← hbEq, mul_add, mul_one]
          omega
        rw [hP] at hShift
        exact hStep0.trans hShift
      · have hwEq : w = 1 := by omega
        refine rwg_step_one D input B
          (.writeBack act.nextState act.inputMove .left (act.write 0) ⟨0, hw⟩)
          a.inputHead b.inputHead
          (rulerTape m ((a.workTapes 0).head + 1))
          (scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 1
            (1 + w * (a.workTapes 0).head))
          fixedTape
          (rulerTape (max m ((a.workTapes 0).head + 1)) ((b.workTapes 0).head + 1))
          (scratchEnc D (b.workTapes 0) (1 + w * (b.workTapes 0).head))
          (.inl (.read act.nextState ⟨0, hw⟩ (fun _ => .blank)))
          act.inputMove (.bit true, .left) (encodeSym D (act.write 0) ⟨0, hw⟩, .left)
          (by
            dsimp only [rwCompGen]
            simp only [↓reduceDIte, hw1])
          hIn (by rw [← hwm]; exact hRulerMv)
          (by
            have hsc := scratchPartial_update D (a.workTapes 0) (a.workTapes 0).head
              (act.write 0) 0 hw .left (1 + w * (b.workTapes 0).head)
              (by
                dsimp only [w] at hwEq ⊢
                rw [← hbEq, hwEq]
                simp [moveOneSidedHead]
                omega)
            have hEq2 : scratchPartial D (a.workTapes 0) (a.workTapes 0).head (act.write 0) 0
                (1 + w * (b.workTapes 0).head) =
                scratchEnc D (b.workTapes 0) (1 + w * (b.workTapes 0).head) := by
              rw [scratchPartial_zero, hTb]; rfl
            simpa [hEq2] using hsc)
          (by simp [fixedTape]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchPartial]; omega)
          (by simp [rulerTape]; omega)
          (by simp [scratchEnc, hwEq]; omega)
  exact hRead.trans (hTransStep.trans (hWB.trans hWriteZero))

theorem rwg_sim_run (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S + 1 < B) (hRB : S + 1 < B)
    {a b : OneSidedTMConfig QD Γ 1 n}
    (hRun : Relation.ReflTransGen (DGoodGen D input S) a b)
    (m : ℕ) (hm : m ≤ S) (ha : (a.workTapes 0).head < S) (ha_m : (a.workTapes 0).head ≤ m) :
    ∃ m' ≥ m, m' ≤ S ∧
      RWRun (rwCompGen D) input B (rwgCfg D a m) (rwgCfg D b m') ∧
      (a ≠ b → (a.workTapes 0).head + 1 ≤ m') ∧
      (b.workTapes 0).head < S ∧
      (b.workTapes 0).head ≤ m' := by
  induction hRun with
  | refl => exact ⟨m, le_rfl, hm, Relation.ReflTransGen.refl, fun h => absurd rfl h, ha, ha_m⟩
  | @tail b c _ hstep ih =>
    obtain ⟨m', hmm', hm'S, hRun', ha', hbS, hb_m'⟩ := ih
    have hc : (c.workTapes 0).head < S := hstep.2.2 0
    have hc_le : (c.workTapes 0).head ≤ (b.workTapes 0).head + 1 := by
      obtain ⟨_, _, _, _, _, _, hup⟩ := hstep.1
      exact step_head_le_gen (hup 0)
    have hS1 := rwg_sim_step D input S B hSB hRB m' hm'S hb_m' hstep
    refine ⟨max m' ((b.workTapes 0).head + 1), le_trans hmm' (le_max_left _ _),
      max_le hm'S hbS, hRun'.trans hS1, fun _ => ?_, hc, le_trans hc_le (le_max_right _ _)⟩
    by_cases hab : a = b
    · subst hab; exact le_max_right _ _
    · exact le_trans (ha' hab) (le_max_left _ _)

theorem dgood_mid_le_gen (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S : ℕ) {b c : OneSidedTMConfig QD Γ 1 n}
    (hbc : Relation.ReflTransGen (DGoodGen D input S) b c)
    (hb : (b.workTapes 0).head + 1 = S) (m₂ : ℕ)
    (hm₂ : b ≠ c → (b.workTapes 0).head + 1 ≤ m₂)
    (hm₂S : m₂ ≤ S) :
    max m₂ ((c.workTapes 0).head + 1) = S := by
  have hcS : (c.workTapes 0).head < S := by
    cases hbc using Relation.ReflTransGen.head_induction_on with
    | refl => omega
    | head hstep hrest =>
      have : ∀ x y, Relation.ReflTransGen (DGoodGen D input S) x y →
          (x.workTapes 0).head < S → (y.workTapes 0).head < S := by
        intro x y hxy hx
        induction hxy with
        | refl => exact hx
        | tail _ hs _ => exact hs.2.2 0
      exact this _ _ hrest (hstep.2.2 0)
  by_cases hbc_eq : b = c
  · rw [← hbc_eq]; omega
  · have := hm₂ hbc_eq; omega


end Proofs

end SavitchLemma

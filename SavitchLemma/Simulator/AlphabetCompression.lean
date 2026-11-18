module

public import SavitchLemma.Simulator.RulerWriter
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Alphabet Compression for Measurable Space Functions

Given a single-tape deterministic machine `D` over an arbitrary finite alphabet `Γ` that
halts after scanning exactly `S` squares, `rwCompGen D` simulates `D` on `tScratch` by
encoding each `Γ`-cell as a block of `w = Fintype.card Γ` cells over `SimSym` while
tracking the visited `Γ`-cells on `tRuler` (1 cell per `Γ`-cell). It then rewinds,
clears `tScratch`, caps `tRuler` with `endMark`, and rewinds, yielding `PrefixPrepares`
within space `(w + 2) * (S + 1)`.
-/

namespace SavitchLemma

section Encoding

variable {QD I Γ : Type} [Fintype QD] [Fintype I] [Fintype Γ]

/-- Every finite alphabet with a blank symbol has positive cardinality. -/
theorem card_pos_of_blank (D : MultitapeDTM QD I Γ 1) : 0 < Fintype.card Γ :=
  Fintype.card_pos_iff.mpr ⟨D.blank⟩

/-- Encode a `Γ`-symbol as a fixed-width block of `Fintype.card Γ` `SimSym`s,
mapping `D.blank` to all `.blank` and every other symbol to a 1-hot `.bit` block. -/
noncomputable def encodeSym (D : MultitapeDTM QD I Γ 1) (γ : Γ)
    (j : Fin (Fintype.card Γ)) : SimSym :=
  open Classical in
  if γ = D.blank then .blank
  else if j = Fintype.equivFin Γ γ then .bit true else .bit false

theorem encodeSym_blank (D : MultitapeDTM QD I Γ 1) (j : Fin (Fintype.card Γ)) :
    encodeSym D D.blank j = .blank := by
  simp [encodeSym]

theorem encodeSym_injective (D : MultitapeDTM QD I Γ 1) :
    Function.Injective (encodeSym D) := by
  classical
  intro γ₁ γ₂ hEq
  have hw := card_pos_of_blank D
  by_cases h1 : γ₁ = D.blank <;> by_cases h2 : γ₂ = D.blank
  · exact h1.trans h2.symm
  · have h0 := congrFun hEq ⟨0, hw⟩
    simp only [encodeSym, h1, ↓reduceIte, h2] at h0
    split_ifs at h0
  · have h0 := congrFun hEq ⟨0, hw⟩
    simp only [encodeSym, h1, h2, ↓reduceIte] at h0
    split_ifs at h0
  · have hj := congrFun hEq (Fintype.equivFin Γ γ₁)
    simp only [encodeSym, h1, h2, ↓reduceIte] at hj
    split_ifs at hj with heq
    · exact (Fintype.equivFin Γ).injective heq
    · cases hj

/-- Decode a `Fin (Fintype.card Γ) → SimSym` block back to `Γ`. -/
noncomputable def decodeBlock (D : MultitapeDTM QD I Γ 1)
    (f : Fin (Fintype.card Γ) → SimSym) : Γ :=
  open Classical in
  if h : ∃ γ : Γ, encodeSym D γ = f then Classical.choose h else D.blank

theorem decodeBlock_encodeSym (D : MultitapeDTM QD I Γ 1) (γ : Γ) :
    decodeBlock D (encodeSym D γ) = γ := by
  classical
  have h : ∃ γ' : Γ, encodeSym D γ' = encodeSym D γ := ⟨γ, rfl⟩
  simp only [decodeBlock, h, ↓reduceDIte]
  exact encodeSym_injective D (Classical.choose_spec h)

end Encoding

section Component

instance : Fintype TapeMove :=
  Fintype.ofEquiv (Fin 3)
    { toFun := fun
        | 0 => .left
        | 1 => .stay
        | 2 => .right
      invFun := fun
        | .left => 0
        | .stay => 1
        | .right => 2
      left_inv := by rintro ⟨x, hx⟩; match x with | 0 => rfl | 1 => rfl | 2 => rfl | n + 3 => omega
      right_inv := by rintro (_ | _ | _) <;> rfl }

/-- Control states of the alphabet-compressed ruler writer. -/
inductive RWGState (QD Γ : Type) [Fintype Γ] where
  | pre
  | read (q : QD) (idx : Fin (Fintype.card Γ)) (buf : Fin (Fintype.card Γ) → SimSym)
  | writeBack (q : QD) (im wm : TapeMove) (sym : Γ) (idx : Fin (Fintype.card Γ))
  | shiftR (q : QD) (rem : Fin (Fintype.card Γ))
  | shiftL (q : QD) (rem : Fin (Fintype.card Γ))
  | goLeftRuler
  | goLeftScratch
  | clear (rem : Fin (Fintype.card Γ))
  | backRuler
  | backScratch

instance {QD Γ : Type} [Fintype QD] [Fintype Γ] : Fintype (RWGState QD Γ) :=
  let w := Fintype.card Γ
  Fintype.ofEquiv
    (Unit ⊕
      (QD × Fin w × (Fin w → SimSym)) ⊕
      (QD × TapeMove × TapeMove × Γ × Fin w) ⊕
      (QD × Fin w) ⊕
      (QD × Fin w) ⊕
      Unit ⊕ Unit ⊕ Fin w ⊕ Unit ⊕ Unit)
    { toFun := fun x => match x with
        | .inl () => .pre
        | .inr (.inl (q, idx, buf)) => .read q idx buf
        | .inr (.inr (.inl (q, im, wm, sym, idx))) => .writeBack q im wm sym idx
        | .inr (.inr (.inr (.inl (q, rem)))) => .shiftR q rem
        | .inr (.inr (.inr (.inr (.inl (q, rem))))) => .shiftL q rem
        | .inr (.inr (.inr (.inr (.inr (.inl ()))))) => .goLeftRuler
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))) => .goLeftScratch
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rem))))))) => .clear rem
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))) => .backRuler
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))) => .backScratch
      invFun := fun x => match x with
        | .pre => .inl ()
        | .read q idx buf => .inr (.inl (q, idx, buf))
        | .writeBack q im wm sym idx => .inr (.inr (.inl (q, im, wm, sym, idx)))
        | .shiftR q rem => .inr (.inr (.inr (.inl (q, rem))))
        | .shiftL q rem => .inr (.inr (.inr (.inr (.inl (q, rem)))))
        | .goLeftRuler => .inr (.inr (.inr (.inr (.inr (.inl ())))))
        | .goLeftScratch => .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
        | .clear rem => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rem)))))))
        | .backRuler => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))
        | .backScratch => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))))
      left_inv := by rintro (_ | ⟨_, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | _ | _ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl }

/-- The alphabet-compressed ruler-writer component for an arbitrary 1-tape DTM `D`. -/
noncomputable def rwCompGen {QD I Γ : Type} [Fintype QD] [Fintype I] [Fintype Γ]
    (D : MultitapeDTM QD I Γ 1) :
    TMComponent (RWGState QD Γ) I SimSym 5 Unit where
  start := .pre
  step st inSym works :=
    let w := Fintype.card Γ
    let hw : 0 < w := card_pos_of_blank D
    let keep : Fin 5 → SimSym × TapeMove := fun t => (works t, .stay)
    let keepR : SimSym × TapeMove := (works tRuler, .stay)
    let keepS : SimSym × TapeMove := (works tScratch, .stay)
    match st with
    | .pre =>
      mk5 (.inl (.read D.startState ⟨0, hw⟩ (fun _ => .blank))) .stay
        (.leftMark, .right) (.leftMark, .right) (fun _ => (.leftMark, .right))
    | .read q idx buf =>
      let buf' : Fin w → SimSym := Function.update buf idx (works tScratch)
      if h : idx.val + 1 < w then
        mk5 (.inl (.read q ⟨idx.val + 1, h⟩ buf')) .stay
          keepR (works tScratch, .right) keep
      else
        let γ := decodeBlock D buf'
        match D.transition q inSym (fun _ => γ) with
        | some a =>
          mk5 (.inl (.writeBack a.nextState a.inputMove (a.workMove 0) (a.write 0) idx)) .stay
            keepR keepS keep
        | none =>
          mk5 (.inl .goLeftRuler) .stay (.bit true, .stay) keepS keep
    | .writeBack q' im wm sym idx =>
      let sCell := (encodeSym D sym idx, if idx.val = 0 then .stay else .left)
      if h0 : idx.val = 0 then
        let rCell := (.bit true, wm)
        match wm with
        | .stay =>
          mk5 (.inl (.read q' ⟨0, hw⟩ (fun _ => .blank))) im rCell (encodeSym D sym idx, .stay) keep
        | .right =>
          if h1 : 1 < w then
            mk5 (.inl (.shiftR q' ⟨w - 2, by omega⟩)) im rCell
              (encodeSym D sym idx, .right) keep
          else
            mk5 (.inl (.read q' ⟨0, hw⟩ (fun _ => .blank))) im rCell
              (encodeSym D sym idx, .right) keep
        | .left =>
          if h1 : 1 < w then
            mk5 (.inl (.shiftL q' ⟨w - 2, by omega⟩)) im rCell
              (encodeSym D sym idx, .left) keep
          else
            mk5 (.inl (.read q' ⟨0, hw⟩ (fun _ => .blank))) im rCell
              (encodeSym D sym idx, .left) keep
      else
        mk5 (.inl (.writeBack q' im wm sym ⟨idx.val - 1, by omega⟩)) .stay
          keepR sCell keep
    | .shiftR q' rem =>
      if h0 : rem.val = 0 then
        mk5 (.inl (.read q' ⟨0, hw⟩ (fun _ => .blank))) .stay keepR (works tScratch, .right) keep
      else
        mk5 (.inl (.shiftR q' ⟨rem.val - 1, by omega⟩)) .stay keepR (works tScratch, .right) keep
    | .shiftL q' rem =>
      if h0 : rem.val = 0 then
        mk5 (.inl (.read q' ⟨0, hw⟩ (fun _ => .blank))) .stay keepR (works tScratch, .left) keep
      else
        mk5 (.inl (.shiftL q' ⟨rem.val - 1, by omega⟩)) .stay keepR (works tScratch, .left) keep
    | .goLeftRuler =>
      if works tRuler = .leftMark then
        mk5 (.inl .goLeftScratch) .stay (.leftMark, .right) keepS keep
      else
        mk5 (.inl .goLeftRuler) .stay (works tRuler, .left) keepS keep
    | .goLeftScratch =>
      if works tScratch = .leftMark then
        mk5 (.inl (.clear ⟨0, hw⟩)) .stay keepR (.leftMark, .right) keep
      else
        mk5 (.inl .goLeftScratch) .stay keepR (works tScratch, .left) keep
    | .clear rem =>
      if h0 : rem.val = 0 then
        if works tRuler = .bit true then
          if h1 : 1 < w then
            mk5 (.inl (.clear ⟨1, h1⟩)) .stay (.bit true, .right) (.blank, .right) keep
          else
            mk5 (.inl (.clear ⟨0, hw⟩)) .stay (.bit true, .right) (.blank, .right) keep
        else
          mk5 (.inl .backRuler) .stay (.endMark, .stay) keepS keep
      else
        if hNext : rem.val + 1 < w then
          mk5 (.inl (.clear ⟨rem.val + 1, hNext⟩)) .stay keepR (.blank, .right) keep
        else
          mk5 (.inl (.clear ⟨0, hw⟩)) .stay keepR (.blank, .right) keep
    | .backRuler =>
      if works tRuler = .leftMark then
        mk5 (.inl .backScratch) .stay (.leftMark, .right) keepS keep
      else
        mk5 (.inl .backRuler) .stay (works tRuler, .left) keepS keep
    | .backScratch =>
      if works tScratch = .leftMark then
        mk5 (.inr ()) .stay keepR (.leftMark, .right) keep
      else
        mk5 (.inl .backScratch) .stay keepR (works tScratch, .left) keep

end Component

section Proofs

variable {QD I Γ : Type} [Fintype QD] [Fintype I] [Fintype Γ]

/-- Encoded scratch tape for `T : OneSidedTape Γ` with head `h`. -/
noncomputable def scratchEnc (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ)
    (h : ℕ) : OneSidedTape SimSym :=
  ⟨fun p =>
    if p = 0 then .leftMark
    else encodeSym D (T.cells ((p - 1) / Fintype.card Γ))
      ⟨(p - 1) % Fintype.card Γ, Nat.mod_lt _ (card_pos_of_blank D)⟩, h⟩

theorem scratchEnc_cell_block (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ) (h i j : ℕ)
    (hj : j < Fintype.card Γ) :
    (scratchEnc D T h).cells (1 + Fintype.card Γ * i + j) = encodeSym D (T.cells i) ⟨j, hj⟩ := by
  have hw := card_pos_of_blank D
  simp only [scratchEnc]
  have hne : 1 + Fintype.card Γ * i + j ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have hsub : 1 + Fintype.card Γ * i + j - 1 = Fintype.card Γ * i + j := by omega
  simp only [hsub, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem scratchEnc_at_zero (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ) (h : ℕ) :
    (scratchEnc D T h).cells 0 = .leftMark := by
  simp [scratchEnc]

/-- Partial block-encoded scratch tape: block `i` has `encodeSym D γ'` at indices `≥ k`
and `encodeSym D (T.cells i)` at indices `< k`. -/
noncomputable def scratchPartial (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ)
    (i : ℕ) (γ' : Γ) (k : ℕ) (h : ℕ) : OneSidedTape SimSym :=
  ⟨fun p =>
    if p = 0 then .leftMark
    else
      let w := Fintype.card Γ
      let blk := (p - 1) / w
      let off := (p - 1) % w
      if blk = i ∧ k ≤ off then encodeSym D γ' ⟨off, Nat.mod_lt _ (card_pos_of_blank D)⟩
      else encodeSym D (T.cells blk) ⟨off, Nat.mod_lt _ (card_pos_of_blank D)⟩, h⟩

theorem scratchPartial_top (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ)
    (i : ℕ) (γ' : Γ) (h : ℕ) :
    scratchPartial D T i γ' (Fintype.card Γ) h = scratchEnc D T h := by
  unfold scratchPartial scratchEnc
  congr 1; funext p
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    have hlt := Nat.mod_lt (p - 1) (card_pos_of_blank D)
    have hnot : ¬ ((p - 1) / Fintype.card Γ = i ∧ Fintype.card Γ ≤ (p - 1) % Fintype.card Γ) := by
      omega
    simp [hnot]

theorem scratchPartial_zero (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ)
    (i : ℕ) (γ' : Γ) (h : ℕ) :
    scratchPartial D T i γ' 0 h =
      scratchEnc D ⟨fun x => if x = i then γ' else T.cells x, T.head⟩ h := by
  unfold scratchPartial scratchEnc
  congr 1; funext p
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte, Nat.zero_le, and_true]
    split_ifs <;> rfl

theorem scratchPartial_update (D : MultitapeDTM QD I Γ 1) (T : OneSidedTape Γ)
    (i : ℕ) (γ' : Γ) (k : ℕ) (hk : k < Fintype.card Γ) (mv : TapeMove) (h' : ℕ)
    (hmv : moveOneSidedHead (1 + Fintype.card Γ * i + k) mv = some h') :
    (scratchPartial D T i γ' (k + 1) (1 + Fintype.card Γ * i + k)).updateAndMove
        (encodeSym D γ' ⟨k, hk⟩) mv =
      some (scratchPartial D T i γ' k h') := by
  have hw := card_pos_of_blank D
  simp only [OneSidedTape.updateAndMove]
  change (match moveOneSidedHead (1 + Fintype.card Γ * i + k) mv with
    | none => none
    | some head => some _) = some _
  rw [hmv]
  simp only [Option.some.injEq]
  unfold scratchPartial
  congr 1; funext p
  by_cases hp : p = 1 + Fintype.card Γ * i + k
  · subst hp
    have hne : 1 + Fintype.card Γ * i + k ≠ 0 := by omega
    have hsub : 1 + Fintype.card Γ * i + k - 1 = Fintype.card Γ * i + k := by omega
    simp only [↓reduceIte, hne, hsub, Nat.mul_add_div hw, Nat.div_eq_of_lt hk, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hk, le_rfl, and_self]
  · simp only [hp, ↓reduceIte]
    by_cases hp0 : p = 0
    · simp [hp0]
    · simp only [hp0, ↓reduceIte]
      have hne : ((p - 1) / Fintype.card Γ = i ∧ k ≤ (p - 1) % Fintype.card Γ) ↔
          ((p - 1) / Fintype.card Γ = i ∧ k + 1 ≤ (p - 1) % Fintype.card Γ) := by
        constructor <;> rintro ⟨hdiv, hmod⟩
        · refine ⟨hdiv, ?_⟩
          by_cases hmodk : (p - 1) % Fintype.card Γ = k
          · exfalso
            have hdm := Nat.div_add_mod (p - 1) (Fintype.card Γ)
            rw [hdiv, hmodk] at hdm
            omega
          · omega
        · exact ⟨hdiv, by omega⟩
      simp only [hne]

private theorem tRuler_ne_tScratch : tRuler ≠ tScratch := by decide
private theorem tScratch_ne_tRuler : tScratch ≠ tRuler := by decide

@[simp] theorem tapes5_tRuler (R Sc F : OneSidedTape SimSym) :
    tapes5 R Sc F tRuler = R := by simp [tapes5]

@[simp] theorem tapes5_tScratch (R Sc F : OneSidedTape SimSym) :
    tapes5 R Sc F tScratch = Sc := by simp [tapes5, tScratch_ne_tRuler]

/-- Good-step relation for an arbitrary alphabet `Γ`. -/
def DGoodGen (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I) (S : ℕ) :
    OneSidedTMConfig QD Γ 1 n → OneSidedTMConfig QD Γ 1 n → Prop :=
  fun a b => D.oneSidedStep input a b ∧ a.HeadsWithin S ∧ b.HeadsWithin S

theorem step_head_le_gen {T T' : OneSidedTape Γ} {w : Γ} {mv : TapeMove}
    (h : T.updateAndMove w mv = some T') : T'.head ≤ T.head + 1 := by
  unfold OneSidedTape.updateAndMove at h
  cases hm : moveOneSidedHead T.head mv with
  | none => rw [hm] at h; cases h
  | some h' =>
    simp only [hm, Option.some.injEq] at h
    subst h
    dsimp only
    cases mv
    · simp only [moveOneSidedHead] at hm
      by_cases h0 : T.head = 0
      · simp [h0] at hm
      · simp [h0] at hm; omega
    · simp [moveOneSidedHead] at hm; omega
    · simp [moveOneSidedHead] at hm; omega

theorem updateAndMove_eq_gen {T T' : OneSidedTape Γ} {w : Γ} {mv : TapeMove}
    (h : T.updateAndMove w mv = some T') :
    ∃ h', moveOneSidedHead T.head mv = some h' ∧
      T' = ⟨fun i => if i = T.head then w else T.cells i, h'⟩ := by
  unfold OneSidedTape.updateAndMove at h
  cases hm : moveOneSidedHead T.head mv with
  | none => rw [hm] at h; cases h
  | some h' =>
    simp only [hm, Option.some.injEq] at h
    exact ⟨h', rfl, h.symm⟩

theorem mk5_congr {St : Type*} {nx₁ nx₂ : St} {im₁ im₂ : TapeMove}
    {r₁ r₂ s₁ s₂ : SimSym × TapeMove} {o₁ o₂ : Fin 5 → SimSym × TapeMove}
    (hn : nx₁ = nx₂) (hi : im₁ = im₂) (hr : r₁ = r₂) (hs : s₁ = s₂)
    (ho : ∀ t, t ≠ tRuler → t ≠ tScratch → o₁ t = o₂ t) :
    mk5 nx₁ im₁ r₁ s₁ o₁ = mk5 nx₂ im₂ r₂ s₂ o₂ := by
  subst hn; subst hi; subst hr; subst hs
  simp only [mk5]; congr 1 <;> funext t <;> split_ifs with h1 h2
  · rfl
  · rfl
  · exact congrArg Prod.fst (ho t h1 h2)
  · rfl
  · rfl
  · exact congrArg Prod.snd (ho t h1 h2)

theorem rwg_step_one (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (B : ℕ) (st : RWGState QD Γ) (ih ih' : Fin (n + 2))
    (R Sc F R' Sc' : OneSidedTape SimSym)
    (nx : RWGState QD Γ ⊕ Unit) (im : TapeMove) (r s : SimSym × TapeMove)
    (hAct : (rwCompGen D).step st (readInput input ih)
        (fun t => (tapes5 R Sc F t).cells (tapes5 R Sc F t).head) =
      mk5 nx im r s (fun t => ((tapes5 R Sc F t).cells (tapes5 R Sc F t).head, .stay)))
    (hIn : moveHead (n + 2) ih im = some ih')
    (hR : R.updateAndMove r.1 r.2 = some R') (hS : Sc.updateAndMove s.1 s.2 = some Sc')
    (hFB : F.head < B) (hRB : R.head < B) (hSB : Sc.head < B)
    (hR'B : R'.head < B) (hS'B : Sc'.head < B) :
    RWRun (rwCompGen D) input B ⟨.inl st, ih, tapes5 R Sc F⟩ ⟨nx, ih', tapes5 R' Sc' F⟩ :=
  Relation.ReflTransGen.single
    ⟨compStep_mk5 (rwCompGen D) input st ih ih' R Sc F R' Sc' nx im r s hAct hIn hR hS,
     tapes5_head_lt R Sc F B hRB hSB hFB,
     tapes5_head_lt R' Sc' F B hR'B hS'B hFB⟩

/-- Configuration of `rwCompGen D` at the start of simulating a `D` configuration. -/
noncomputable def rwgCfg {n : ℕ} (D : MultitapeDTM QD I Γ 1)
    (c : OneSidedTMConfig QD Γ 1 n) (m : ℕ) :
    OneSidedTMConfig (RWGState QD Γ ⊕ Unit) SimSym 5 n :=
  ⟨.inl (.read c.state ⟨0, card_pos_of_blank D⟩ (fun _ => .blank)), c.inputHead,
    tapes5 (rulerTape m ((c.workTapes 0).head + 1))
      (scratchEnc D (c.workTapes 0) (1 + Fintype.card Γ * (c.workTapes 0).head)) fixedTape⟩

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
    (m : ℕ) (hm : m ≤ S) :
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
          simp only [Fin.val_mk] at hj
          omega
        simp [Function.update, hne]
      · rfl
    rw [hbuf_eq] at hRest
    exact hStep.trans hRest

theorem rwg_writeBack_loop (D : MultitapeDTM QD I Γ 1) {n : ℕ} (input : Fin n → I)
    (S B : ℕ) (hSB : Fintype.card Γ * S < B) (hRB : S < B)
    (q' : QD) (im wm : TapeMove) (γ' : Γ) (ih : Fin (n + 2)) (T : OneSidedTape Γ)
    (hTS : T.head < S) (m : ℕ) (hm : m ≤ S) :
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
        simp only [rwCompGen, dif_neg (by omega : ¬ k + 1 = 0), tapes5_tRuler]
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
    ∀ (r : ℕ) (hr : r < Fintype.card Γ) (p : ℕ) (hp : p + r + 1 < B),
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
    ∀ (r : ℕ) (hr : r < Fintype.card Γ) (p : ℕ) (hp0 : r + 1 ≤ p) (hpB : p < B),
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

private theorem rulerTape_updateAndMove_bit (m h h' : ℕ) (hm_head : h ≤ m) (mv : TapeMove)
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
        · subst hph; simp [hp0]
        · have hMax : (p ≤ max m (h + 1 + 1)) ↔ (p ≤ m) := by omega
          simp [hp0, hph, hMax]
  · simp only [moveOneSidedHead, Option.some.injEq] at hmv
    subst hmv; simp only [moveOneSidedHead]
    congr 1; simp only [rulerTape]; congr 1; funext p
    by_cases hp0 : p = 0
    · simp [hp0]
    · by_cases hph : p = h + 1
      · subst hph; simp [hp0]
      · have hMax : (p ≤ max m (h + 1)) ↔ (p ≤ m) := by omega
        simp [hp0, hph, hMax]
  · simp only [moveOneSidedHead, Option.some.injEq] at hmv
    subst hmv; simp only [moveOneSidedHead]
    congr 1; simp only [rulerTape]; congr 1; funext p
    by_cases hp0 : p = 0
    · simp [hp0]
    · by_cases hph : p = h + 1
      · subst hph; simp [hp0]
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
          simp only [Fin.val_mk, ↓reduceDIte])
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
            simp only [Fin.val_mk, ↓reduceDIte, hw1]
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
            simp only [Fin.val_mk, ↓reduceDIte, hw1])
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
            simp only [Fin.val_mk, ↓reduceDIte, hw1]
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
            simp only [Fin.val_mk, ↓reduceDIte, hw1])
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
      simp only [dif_neg hNotLt, tapes5_tRuler, tapes5_tScratch]
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
        exact mk5_congr rfl rfl (by simp [rulerTape, hlt]) rfl (fun _ _ _ => rfl))
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
    ∀ (d : ℕ) (c : ℕ) (hd : S + 1 - c = d) (hc0 : 1 ≤ c) (hcS : c ≤ S + 1)
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
        simp only [tapes5_tRuler, hNotBit', ↓reduceIte, Fin.val_mk, ↓reduceDIte]
        exact mk5_congr rfl rfl rfl rfl (fun _ _ _ => rfl))
      (by simp [moveHead])
      (by
        simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq, rulerTape, rulerCap]
        congr 1; funext i; by_cases hi0 : i = 0 <;> by_cases hiS : i = S + 1 <;> simp [hi0, hiS] <;> omega)
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
            simp only [tapes5_tRuler, hkMod, Fin.val_mk, dif_neg (show ¬ k = 0 by omega)]
            split_ifs with h1
            · exact mk5_congr (by simp [Fin.ext_iff, hNext, h1]) rfl rfl rfl
                (fun _ _ _ => rfl)
            · exact mk5_congr (by simp [Fin.ext_iff, hNext, h1]) rfl rfl rfl
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
        simp only [tapes5_tRuler, hBit', ↓reduceIte, Fin.val_mk, ↓reduceDIte]
        split_ifs with h1
        · exact mk5_congr (by simp [Fin.ext_iff, Nat.mod_eq_of_lt h1]) rfl rfl rfl
            (fun _ _ _ => rfl)
        · exact mk5_congr (by simp [Fin.ext_iff, show Fintype.card Γ = 1 by omega]) rfl rfl rfl
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
      (by simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq])
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
          exact mk5_congr rfl rfl (by simp [rulerCap, hlt]) rfl (fun _ _ _ => rfl)
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
  obtain ⟨final, hRun, hNone, hReach⟩ := hHalt
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
        simp [show j + 1 ≠ 0 by omega, show 1 + Fintype.card Γ * (1 - 1) ≤ j + 1 by omega, hiS]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hFinBlank : ∀ x, S ≤ x → (final.workTapes 0).cells x = D.blank :=
          dgood_blank_gen D input S hRun (fun _ _ => rfl)
        have hDiv : S ≤ j / Fintype.card Γ := by
          have := Nat.div_add_mod j (Fintype.card Γ)
          have := Nat.mod_lt j hw
          nlinarith
        simp [show j + 1 ≠ 0 by omega, show ¬ (1 + Fintype.card Γ * (1 - 1) ≤ j + 1 ∧
          j + 1 < 1 + Fintype.card Γ * S) by omega, scratchEnc, hFinBlank _ hDiv, encodeSym_blank]

end Proofs

end SavitchLemma

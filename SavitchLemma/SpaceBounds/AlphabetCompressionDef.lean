module

public import SavitchLemma.SpaceBounds.RulerWriter
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

omit [Fintype Γ] in
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
      · simp at hm; omega
    · simp [moveOneSidedHead] at hm; omega
    · simp [moveOneSidedHead] at hm; omega

omit [Fintype Γ] in
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


end Proofs

end SavitchLemma

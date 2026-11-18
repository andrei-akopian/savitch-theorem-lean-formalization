module

public import Mathlib.Data.Nat.Log
public import SavitchLemma.Abstract.AcceptingZD
public import SavitchLemma.Model.MachineModel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Concrete bit-field encoding of finite-capacity machine configurations

Each configuration in `TMConfig Q Γ k n S` is serialized LSB-first into a fixed
number of bits `bitWidth Q Γ k S`, terminated by the two-bit marker `[true, false]`.
This embeds `TMConfig Q Γ k n S` injectively into `ValidCode (2 ^ bitWidth - 1)`
so that `0` (all zeros) and `2 ^ bitWidth - 1` (all ones) are never valid IDs.
-/

namespace SavitchLemma

/-- Encode a natural number into `width` LSB-first bits. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | width + 1, x => decide (x % 2 = 1) :: natToBits width (x / 2)

/-- Decode an LSB-first bit list into a natural number. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- Increment an LSB-first bit list by one (wrapping on all-ones). -/
def incBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

theorem natToBits_length (width x : ℕ) : (natToBits width x).length = width := by
  induction width generalizing x with
  | zero => rfl
  | succ w ih => simp [natToBits, ih]

theorem bitsToNat_lt_pow (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

theorem bitsToNat_natToBits (width x : ℕ) :
    bitsToNat (natToBits width x) = x % 2 ^ width := by
  induction width generalizing x with
  | zero => simp [natToBits, bitsToNat, Nat.mod_one]
  | succ w ih =>
    simp only [natToBits, bitsToNat, ih, pow_succ']
    have hDivMod : x % (2 * 2 ^ w) = x % 2 + 2 * ((x / 2) % 2 ^ w) := by
      have h1 : x = 2 * (x / 2) + x % 2 := (Nat.div_add_mod x 2).symm
      have h2 : x / 2 = 2 ^ w * ((x / 2) / 2 ^ w) + (x / 2) % 2 ^ w :=
        (Nat.div_add_mod (x / 2) (2 ^ w)).symm
      have h3 : x = (2 * 2 ^ w) * ((x / 2) / 2 ^ w) + (x % 2 + 2 * ((x / 2) % 2 ^ w)) := by
        calc
          x = 2 * (2 ^ w * ((x / 2) / 2 ^ w) + (x / 2) % 2 ^ w) + x % 2 := by
            conv_lhs => rw [h1, h2]
          _ = (2 * 2 ^ w) * ((x / 2) / 2 ^ w) + (x % 2 + 2 * ((x / 2) % 2 ^ w)) := by ring
      have hBound : x % 2 + 2 * ((x / 2) % 2 ^ w) < 2 * 2 ^ w := by
        have hm₁ : x % 2 < 2 := Nat.mod_lt x (by decide)
        have hm₂ : (x / 2) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.pow_pos (by decide))
        omega
      conv_lhs => rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hBound]
    have hMod : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    rcases hMod with h0 | h1
    · simp [h0, hDivMod]
    · simp [h1, hDivMod]

theorem bitsToNat_natToBits_of_lt {width x : ℕ} (hx : x < 2 ^ width) :
    bitsToNat (natToBits width x) = x := by
  rw [bitsToNat_natToBits, Nat.mod_eq_of_lt hx]

theorem natToBits_bitsToNat (bs : List Bool) :
    natToBits bs.length (bitsToNat bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, natToBits, bitsToNat]
    cases b
    · simp [ih]
    · have hDiv : (1 + 2 * bitsToNat bs) / 2 = bitsToNat bs := by omega
      simp [hDiv, ih]

theorem bitsToNat_append (bs₁ bs₂ : List Bool) :
    bitsToNat (bs₁ ++ bs₂) = bitsToNat bs₁ + 2 ^ bs₁.length * bitsToNat bs₂ := by
  induction bs₁ with
  | nil => simp [bitsToNat]
  | cons b bs₁ ih =>
    simp only [List.cons_append, bitsToNat, ih, List.length_cons, pow_succ']
    ring

theorem bitsToNat_replicate_true (w : ℕ) :
    bitsToNat (List.replicate w true) = 2 ^ w - 1 := by
  induction w with
  | zero => simp [bitsToNat]
  | succ w ih =>
    simp only [List.replicate_succ, bitsToNat, ↓reduceIte, ih, pow_succ']
    have hPos : 1 ≤ 2 ^ w := Nat.one_le_pow w 2 (by decide)
    omega

theorem bitsToNat_firstCode (w : ℕ) (_hw : 1 ≤ w) :
    bitsToNat (true :: List.replicate (w - 1) false) = 1 := by
  have hZero : ∀ m, bitsToNat (List.replicate m false) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, bitsToNat, ih]
  simp [bitsToNat, hZero]

theorem incBits_length (bs : List Bool) : (incBits bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [incBits, ih]

theorem bitsToNat_incBits {bs : List Bool} (hHasFalse : false ∈ bs) :
    bitsToNat (incBits bs) = bitsToNat bs + 1 := by
  induction bs with
  | nil => simp at hHasFalse
  | cons b bs ih =>
    cases b
    · simp [incBits, bitsToNat]
      omega
    · rcases List.mem_cons.mp hHasFalse with hEq | hMem
      · cases hEq
      · simp [incBits, bitsToNat, ih hMem]
        omega

theorem false_mem_of_bitsToNat_lt {bs : List Bool}
    (hLt : bitsToNat bs < 2 ^ bs.length - 1) : false ∈ bs := by
  have hAllTrue : ∀ l : List Bool, false ∉ l → l = List.replicate l.length true := by
    intro l hNoFalse
    induction l with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.mem_cons, not_or] at hNoFalse
      cases b
      · exact (hNoFalse.1 rfl).elim
      · simpa [List.replicate_succ] using ih hNoFalse.2
  by_contra hNoFalse
  have hRep := hAllTrue bs hNoFalse
  rw [hRep, List.length_replicate, bitsToNat_replicate_true] at hLt
  omega

/-- Number of bits needed to represent a control state in `Q`. -/
def qBits (Q : Type*) [Fintype Q] : ℕ :=
  Nat.clog 2 (Fintype.card Q + 1)

/-- Number of bits needed to represent a tape symbol in `Γ`. -/
def gammaBits (Γ : Type*) [Fintype Γ] : ℕ :=
  Nat.clog 2 (Fintype.card Γ + 1)

/-- Bit-width of a serialized work tape of capacity `S`. -/
def tapeBitWidth (Γ : Type*) [Fintype Γ] (S : ℕ) : ℕ :=
  S + S * gammaBits Γ

/-- Total bit-width of one serialized machine configuration register. -/
def configBitWidth (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) : ℕ :=
  qBits Q + (S + 2) + k * tapeBitWidth Γ S + 2

theorem configBitWidth_ge_two (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    2 ≤ configBitWidth Q Γ k S := by
  unfold configBitWidth
  omega

theorem configBitWidth_gt_one_pow (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    1 < 2 ^ configBitWidth Q Γ k S - 1 := by
  have hW := configBitWidth_ge_two Q Γ k S
  have hPow : 4 ≤ 2 ^ configBitWidth Q Γ k S := by
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ configBitWidth Q Γ k S := Nat.pow_le_pow_right (by decide : 0 < 2) hW
  omega

/-- Total number of bits in the serialized tape fields, excluding the 2-bit
valid-ID marker. -/
def configBodyWidth (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) : ℕ :=
  qBits Q + (S + 2) + k * tapeBitWidth Γ S

theorem configBitWidth_eq_body_add_two (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    configBitWidth Q Γ k S = configBodyWidth Q Γ k S + 2 := rfl

/-- Serialize one bounded work tape: `S`-bit head position followed by `S`
symbol fields of `gammaBits Γ` bits each. -/
noncomputable def encodeTapeBits (Γ : Type*) [Fintype Γ] {S : ℕ}
    (tape : BoundedTape Γ S) : List Bool :=
  natToBits S tape.head.val ++
    (List.finRange S).flatMap (fun c => natToBits (gammaBits Γ) (Fintype.equivFin Γ (tape.cells c)).val)

theorem encodeTapeBits_length (Γ : Type*) [Fintype Γ] {S : ℕ}
    (tape : BoundedTape Γ S) : (encodeTapeBits Γ tape).length = tapeBitWidth Γ S := by
  unfold encodeTapeBits tapeBitWidth
  rw [List.length_append, natToBits_length]
  congr 1
  rw [List.length_flatMap]
  have hConst : ∀ c ∈ List.finRange S,
      (natToBits (gammaBits Γ) (Fintype.equivFin Γ (tape.cells c)).val).length = gammaBits Γ :=
    fun c _ => natToBits_length _ _
  rw [List.map_congr_left hConst, List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

/-- Serialize a full bounded configuration into `configBitWidth Q Γ k S` bits,
with `[true, false]` as the two most significant bits. -/
noncomputable def encodeConfigBits (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    {k n S : ℕ} (cfg : TMConfig Q Γ k n S) : List Bool :=
  natToBits (qBits Q) (Fintype.equivFin Q cfg.state).val ++
  natToBits (S + 2) cfg.inputHead.val ++
  (List.finRange k).flatMap (fun t => encodeTapeBits Γ (cfg.workTapes t)) ++
  [true, false]

theorem encodeConfigBits_length (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    {k n S : ℕ} (cfg : TMConfig Q Γ k n S) :
    (encodeConfigBits Q Γ cfg).length = configBitWidth Q Γ k S := by
  unfold encodeConfigBits configBitWidth
  simp only [List.length_append, natToBits_length, List.length_cons, List.length_nil]
  have hTapes :
      ((List.finRange k).flatMap (fun t => encodeTapeBits Γ (cfg.workTapes t))).length =
        k * tapeBitWidth Γ S := by
    rw [List.length_flatMap]
    have hConst : ∀ t ∈ List.finRange k,
        (encodeTapeBits Γ (cfg.workTapes t)).length = tapeBitWidth Γ S :=
      fun t _ => encodeTapeBits_length Γ (cfg.workTapes t)
    rw [List.map_congr_left hConst, List.map_const', List.sum_replicate, List.length_finRange,
      smul_eq_mul]
  rw [hTapes]

/-- Abstract code `0 < val < 2^W - 1` associated to a configuration. -/
noncomputable def bitEncodeConfig (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    {k n S : ℕ} (cfg : TMConfig Q Γ k n S) :
    ValidCode (2 ^ configBitWidth Q Γ k S - 1) := by
  let bs := encodeConfigBits Q Γ cfg
  let bodyLen := configBodyWidth Q Γ k S
  have hLen : bs.length = bodyLen + 2 := encodeConfigBits_length Q Γ cfg
  let val := bitsToNat bs
  have hValLt : val < 2 ^ configBitWidth Q Γ k S := by
    rw [configBitWidth_eq_body_add_two, ← hLen]
    exact bitsToNat_lt_pow bs
  let body :=
    natToBits (qBits Q) (Fintype.equivFin Q cfg.state).val ++
    natToBits (S + 2) cfg.inputHead.val ++
    (List.finRange k).flatMap (fun t => encodeTapeBits Γ (cfg.workTapes t))
  have hBodyLen : body.length = bodyLen := by
    simp only [body, List.length_append, natToBits_length]
    congr 1
    rw [List.length_flatMap]
    have hConst : ∀ t ∈ List.finRange k,
        (encodeTapeBits Γ (cfg.workTapes t)).length = tapeBitWidth Γ S :=
      fun t _ => encodeTapeBits_length Γ (cfg.workTapes t)
    rw [List.map_congr_left hConst, List.map_const', List.sum_replicate, List.length_finRange,
      smul_eq_mul]
  have hBs : bs = body ++ [true, false] := by
    simp [bs, encodeConfigBits, body, List.append_assoc]
  have hCalc : val = bitsToNat body + 2 ^ bodyLen * 1 := by
    dsimp [val]
    rw [hBs, bitsToNat_append, hBodyLen]
    simp [bitsToNat]
  have hMaxBody : val < 2 ^ (bodyLen + 1) := by
    have hBodyLt := bitsToNat_lt_pow body
    rw [hBodyLen] at hBodyLt
    rw [hCalc]
    simp only [mul_one, pow_succ']
    omega
  have hPos : 0 < val := by
    have hPowPos : 0 < 2 ^ bodyLen := Nat.pow_pos (by decide)
    omega
  have hLtMax : val < 2 ^ configBitWidth Q Γ k S - 1 := by
    change val < 2 ^ (bodyLen + 2) - 1
    have hPow : 2 ^ (bodyLen + 2) = 2 * 2 ^ (bodyLen + 1) := by simp [pow_succ']
    have hPowOne : 2 ≤ 2 ^ (bodyLen + 1) := by
      calc
        2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ (bodyLen + 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have hPowGeOne : 1 ≤ 2 ^ configBitWidth Q Γ k S := Nat.one_le_pow _ 2 (by decide)
  exact ⟨⟨val, by omega⟩, hPos, hLtMax⟩

/-- `encodeConfigBits` is injective on `TMConfig Q Γ k n S`. -/
theorem encodeConfigBits_injective (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    {k n S : ℕ} (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) :
    Function.Injective (encodeConfigBits Q Γ (k := k) (n := n) (S := S)) := by
  intro c₁ c₂ hEq
  have hInBound₁ : c₁.inputHead.val < 2 ^ (S + 2) := by
    have h1 : c₁.inputHead.val < n + 2 := c₁.inputHead.isLt
    have h2 : 2 ≤ 2 ^ S := by
      calc
        2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide : 0 < 2) hS
    have h3 : n + 2 ≤ 2 ^ (S + 1) := by
      calc
        n + 2 ≤ 2 ^ S + 2 := Nat.add_le_add_right hInput 2
        _ ≤ 2 ^ S + 2 ^ S := Nat.add_le_add_left h2 _
        _ = 2 ^ (S + 1) := by simp [pow_succ']; omega
    have h4 : 2 ^ (S + 1) < 2 ^ (S + 2) := by
      have hPos : 0 < 2 ^ (S + 1) := Nat.pow_pos (by decide)
      simp [pow_succ']
    omega
  have hInBound₂ : c₂.inputHead.val < 2 ^ (S + 2) := by
    have h1 : c₂.inputHead.val < n + 2 := c₂.inputHead.isLt
    have h2 : 2 ≤ 2 ^ S := by
      calc
        2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide : 0 < 2) hS
    have h3 : n + 2 ≤ 2 ^ (S + 1) := by
      calc
        n + 2 ≤ 2 ^ S + 2 := Nat.add_le_add_right hInput 2
        _ ≤ 2 ^ S + 2 ^ S := Nat.add_le_add_left h2 _
        _ = 2 ^ (S + 1) := by simp [pow_succ']; omega
    have h4 : 2 ^ (S + 1) < 2 ^ (S + 2) := by
      have hPos : 0 < 2 ^ (S + 1) := Nat.pow_pos (by decide)
      simp [pow_succ']
    omega
  have hQBound₁ : (Fintype.equivFin Q c₁.state).val < 2 ^ qBits Q := by
    have h1 := (Fintype.equivFin Q c₁.state).isLt
    have h2 : Fintype.card Q + 1 ≤ 2 ^ qBits Q := Nat.le_pow_clog (by decide : 1 < 2) _
    omega
  have hQBound₂ : (Fintype.equivFin Q c₂.state).val < 2 ^ qBits Q := by
    have h1 := (Fintype.equivFin Q c₂.state).isLt
    have h2 : Fintype.card Q + 1 ≤ 2 ^ qBits Q := Nat.le_pow_clog (by decide : 1 < 2) _
    omega
  -- Compare prefix chunks of fixed lengths
  have hStripTail :
      natToBits (qBits Q) (Fintype.equivFin Q c₁.state).val ++
        natToBits (S + 2) c₁.inputHead.val ++
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₁.workTapes t)) =
      natToBits (qBits Q) (Fintype.equivFin Q c₂.state).val ++
        natToBits (S + 2) c₂.inputHead.val ++
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₂.workTapes t)) := by
    exact List.append_cancel_right hEq
  have hQEqBits :
      natToBits (qBits Q) (Fintype.equivFin Q c₁.state).val =
      natToBits (qBits Q) (Fintype.equivFin Q c₂.state).val := by
    have hTake := congrArg (List.take (qBits Q)) hStripTail
    simpa [List.append_assoc, List.take_left', natToBits_length] using hTake
  have hRest₁ :
      natToBits (S + 2) c₁.inputHead.val ++
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₁.workTapes t)) =
      natToBits (S + 2) c₂.inputHead.val ++
        (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₂.workTapes t)) := by
    have hDrop := congrArg (List.drop (qBits Q)) hStripTail
    simpa [List.append_assoc, List.drop_left', natToBits_length] using hDrop
  have hInEqBits :
      natToBits (S + 2) c₁.inputHead.val = natToBits (S + 2) c₂.inputHead.val := by
    have hTake := congrArg (List.take (S + 2)) hRest₁
    simpa [List.take_left', natToBits_length] using hTake
  have hTapesEqBits :
      (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₁.workTapes t)) =
      (List.finRange k).flatMap (fun t => encodeTapeBits Γ (c₂.workTapes t)) := by
    have hDrop := congrArg (List.drop (S + 2)) hRest₁
    simpa [List.drop_left', natToBits_length] using hDrop
  have hStateEq : c₁.state = c₂.state := by
    have hVal := congrArg bitsToNat hQEqBits
    rw [bitsToNat_natToBits_of_lt hQBound₁, bitsToNat_natToBits_of_lt hQBound₂] at hVal
    exact (Fintype.equivFin Q).injective (Fin.ext hVal)
  have hInEq : c₁.inputHead = c₂.inputHead := by
    have hVal := congrArg bitsToNat hInEqBits
    rw [bitsToNat_natToBits_of_lt hInBound₁, bitsToNat_natToBits_of_lt hInBound₂] at hVal
    exact Fin.ext hVal
  have hWorkEq : c₁.workTapes = c₂.workTapes := by
    funext t
    have hFlat : ∀ (l : List (Fin k)) (f g : Fin k → List Bool),
        (∀ x, (f x).length = tapeBitWidth Γ S) →
        (∀ x, (g x).length = tapeBitWidth Γ S) →
        l.flatMap f = l.flatMap g →
        ∀ x ∈ l, f x = g x := by
      intro l f g hf hg hfg x hx
      induction l with
      | nil => simp at hx
      | cons y ys ih =>
        simp only [List.flatMap_cons] at hfg
        have hHead : f y = g y := by
          have hTake := congrArg (List.take (tapeBitWidth Γ S)) hfg
          simpa [List.take_left', hf y, hg y] using hTake
        have hTail : ys.flatMap f = ys.flatMap g := by
          have hDrop := congrArg (List.drop (tapeBitWidth Γ S)) hfg
          simpa [List.drop_left', hf y, hg y] using hDrop
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hHead
        · exact ih hTail hx'
    have hTapeBitsEq := hFlat (List.finRange k)
      (fun t => encodeTapeBits Γ (c₁.workTapes t))
      (fun t => encodeTapeBits Γ (c₂.workTapes t))
      (fun t => encodeTapeBits_length Γ (c₁.workTapes t))
      (fun t => encodeTapeBits_length Γ (c₂.workTapes t))
      hTapesEqBits t (List.mem_finRange t)
    unfold encodeTapeBits at hTapeBitsEq
    have hWHBits :
        natToBits S (c₁.workTapes t).head.val = natToBits S (c₂.workTapes t).head.val := by
      have hTake := congrArg (List.take S) hTapeBitsEq
      simpa [List.take_left', natToBits_length] using hTake
    have hCellsFlat :
        (List.finRange S).flatMap
          (fun c => natToBits (gammaBits Γ) (Fintype.equivFin Γ ((c₁.workTapes t).cells c)).val) =
        (List.finRange S).flatMap
          (fun c => natToBits (gammaBits Γ) (Fintype.equivFin Γ ((c₂.workTapes t).cells c)).val) := by
      have hDrop := congrArg (List.drop S) hTapeBitsEq
      simpa [List.drop_left', natToBits_length] using hDrop
    have hHeadLt₁ : (c₁.workTapes t).head.val < 2 ^ S :=
      lt_trans (c₁.workTapes t).head.isLt Nat.lt_two_pow_self
    have hHeadLt₂ : (c₂.workTapes t).head.val < 2 ^ S :=
      lt_trans (c₂.workTapes t).head.isLt Nat.lt_two_pow_self
    have hHeadEq : (c₁.workTapes t).head = (c₂.workTapes t).head := by
      have hVal := congrArg bitsToNat hWHBits
      rw [bitsToNat_natToBits_of_lt hHeadLt₁, bitsToNat_natToBits_of_lt hHeadLt₂] at hVal
      exact Fin.ext hVal
    have hCellsEq : (c₁.workTapes t).cells = (c₂.workTapes t).cells := by
      funext c
      have hFlatC : ∀ (l : List (Fin S)) (f g : Fin S → List Bool),
          (∀ x, (f x).length = gammaBits Γ) →
          (∀ x, (g x).length = gammaBits Γ) →
          l.flatMap f = l.flatMap g →
          ∀ x ∈ l, f x = g x := by
        intro l f g hf hg hfg x hx
        induction l with
        | nil => simp at hx
        | cons y ys ih =>
          simp only [List.flatMap_cons] at hfg
          have hTake := congrArg (List.take (gammaBits Γ)) hfg
          have hHead : f y = g y := by simpa [List.take_left', hf y, hg y] using hTake
          have hDrop := congrArg (List.drop (gammaBits Γ)) hfg
          have hTail : ys.flatMap f = ys.flatMap g := by
            simpa [List.drop_left', hf y, hg y] using hDrop
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hHead
          · exact ih hTail hx'
      have hCBits := hFlatC (List.finRange S)
        (fun x => natToBits (gammaBits Γ) (Fintype.equivFin Γ ((c₁.workTapes t).cells x)).val)
        (fun x => natToBits (gammaBits Γ) (Fintype.equivFin Γ ((c₂.workTapes t).cells x)).val)
        (fun _ => natToBits_length _ _) (fun _ => natToBits_length _ _)
        hCellsFlat c (List.mem_finRange c)
      have hGB₁ : (Fintype.equivFin Γ ((c₁.workTapes t).cells c)).val < 2 ^ gammaBits Γ := by
        have h1 := (Fintype.equivFin Γ ((c₁.workTapes t).cells c)).isLt
        have h2 : Fintype.card Γ + 1 ≤ 2 ^ gammaBits Γ := Nat.le_pow_clog (by decide : 1 < 2) _
        omega
      have hGB₂ : (Fintype.equivFin Γ ((c₂.workTapes t).cells c)).val < 2 ^ gammaBits Γ := by
        have h1 := (Fintype.equivFin Γ ((c₂.workTapes t).cells c)).isLt
        have h2 : Fintype.card Γ + 1 ≤ 2 ^ gammaBits Γ := Nat.le_pow_clog (by decide : 1 < 2) _
        omega
      have hVal := congrArg bitsToNat hCBits
      rw [bitsToNat_natToBits_of_lt hGB₁, bitsToNat_natToBits_of_lt hGB₂] at hVal
      exact (Fintype.equivFin Γ).injective (Fin.ext hVal)
    cases hT₁ : c₁.workTapes t
    cases hT₂ : c₂.workTapes t
    simp only [hT₁, hT₂] at hHeadEq hCellsEq
    simp [hHeadEq, hCellsEq]
  cases c₁
  cases c₂
  simp only at hStateEq hInEq hWorkEq
  subst hStateEq hInEq hWorkEq
  rfl

theorem bitEncodeConfig_injective (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    {k n S : ℕ} (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) :
    Function.Injective (bitEncodeConfig Q Γ (k := k) (n := n) (S := S)) := by
  intro c₁ c₂ hEq
  have hVal : bitsToNat (encodeConfigBits Q Γ c₁) = bitsToNat (encodeConfigBits Q Γ c₂) :=
    congrArg (fun v => v.val.val) hEq
  have hBits := congrArg (natToBits (configBitWidth Q Γ k S)) hVal
  have hLen₁ : (encodeConfigBits Q Γ c₁).length = configBitWidth Q Γ k S :=
    encodeConfigBits_length Q Γ c₁
  have hLen₂ : (encodeConfigBits Q Γ c₂).length = configBitWidth Q Γ k S :=
    encodeConfigBits_length Q Γ c₂
  have h1 := natToBits_bitsToNat (encodeConfigBits Q Γ c₁)
  have h2 := natToBits_bitsToNat (encodeConfigBits Q Γ c₂)
  rw [hLen₁] at h1
  rw [hLen₂] at h2
  rw [h1, h2] at hBits
  exact encodeConfigBits_injective Q Γ hS hInput hBits

/-- Concrete bit-field `AbstractProblem` induced by `M` at capacity `S`. -/
noncomputable def bitProblem {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S : ℕ) : AbstractProblem (2 ^ configBitWidth Q Γ k S - 1) where
  step source target :=
    ∃ before after : TMConfig Q Γ k n S,
      (bitEncodeConfig Q Γ before).val = source ∧
      (bitEncodeConfig Q Γ after).val = target ∧
      M.step input S before after
  noStepToZero := by
    intro source ⟨_, after, _, hTarget, _⟩
    have hZero : (bitEncodeConfig Q Γ after).val.val = 0 := by
      simpa using congrArg Fin.val hTarget
    have hPos := (bitEncodeConfig Q Γ after).property.1
    omega
  noStepToMax := by
    intro source ⟨_, after, _, hTarget, _⟩
    have hMax : (bitEncodeConfig Q Γ after).val.val = 2 ^ configBitWidth Q Γ k S - 1 := by
      simpa using congrArg Fin.val hTarget
    have hLt := (bitEncodeConfig Q Γ after).property.2
    omega

/-- Decidable acceptance predicate on bit-encoded configurations. -/
noncomputable def bitIsAccepting {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (n S : ℕ)
    (code : Fin ((2 ^ configBitWidth Q Γ k S - 1) + 1)) : Bool := by
  classical
  exact decide (∃ cfg : TMConfig Q Γ k n S,
    (bitEncodeConfig Q Γ cfg).val = code ∧ M.accepting cfg.state)

theorem bitProblem_step_iff {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (before after : TMConfig Q Γ k n S) :
    (bitProblem M input S).step
      (bitEncodeConfig Q Γ before).val (bitEncodeConfig Q Γ after).val ↔
      M.step input S before after := by
  constructor
  · rintro ⟨b', a', hb, ha, hStep⟩
    have hbEq : b' = before :=
      bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext hb)
    have haEq : a' = after :=
      bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext ha)
    subst hbEq haEq
    exact hStep
  · intro hStep
    exact ⟨before, after, rfl, rfl, hStep⟩

/-- Soundness of `zdAcceptingStep` on `bitProblem`: if `zdAcceptingStep` reaches
`.accept`, then `M` accepts `input` within capacity `S`. -/
theorem bitProblem_accepting_sound {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S) (r : ℕ)
    (hAcc : Relation.ReflTransGen
      (zdOutcomeStep (bitProblem M input S) (configBitWidth_gt_one_pow Q Γ k S)
        (bitIsAccepting M n S))
      (.running (zdInitial r (2 ^ configBitWidth Q Γ k S - 1)
        (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))))
      .accept) :
    M.AcceptsWithinCapacity input S (by omega) := by
  obtain ⟨target, hTargetAcc, hReach⟩ :=
    zdAcceptingStep_soundness (bitProblem M input S) r
      (configBitWidth_gt_one_pow Q Γ k S) (bitIsAccepting M n S)
      (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega))) hAcc
  classical
  simp only [bitIsAccepting, decide_eq_true_eq] at hTargetAcc
  rcases hTargetAcc with ⟨finalCfg, hCodeEq, hStateAcc⟩
  have hConcreteRun : ∀ {x y : Fin ((2 ^ configBitWidth Q Γ k S - 1) + 1)},
      Relation.ReflTransGen (bitProblem M input S).step x y →
      ∀ c₁ : TMConfig Q Γ k n S, (bitEncodeConfig Q Γ c₁).val = x →
      ∃ c₂ : TMConfig Q Γ k n S, (bitEncodeConfig Q Γ c₂).val = y ∧
        Relation.ReflTransGen (M.step input S) c₁ c₂ := by
    intro x y hR
    induction hR with
    | refl =>
      intro c₁ hx
      exact ⟨c₁, hx, Relation.ReflTransGen.refl⟩
    | @tail prev curr _ hStep ih =>
      intro c₁ hx
      rcases ih c₁ hx with ⟨cMid, hcMid, hRunMid⟩
      rcases hStep with ⟨b', a', hb', ha', hM⟩
      have hMidEq : b' = cMid :=
        bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext (hb'.trans hcMid.symm))
      subst hMidEq
      exact ⟨a', ha', Relation.ReflTransGen.tail hRunMid hM⟩
  obtain ⟨c₂, hc₂, hMRun⟩ :=
    hConcreteRun hReach (M.initialConfig (n := n) S (by omega)) rfl
  have hcEq : c₂ = finalCfg :=
    bitEncodeConfig_injective Q Γ hS hInput (Subtype.ext (hc₂.trans hCodeEq.symm))
  subst hcEq
  exact ⟨c₂, hMRun, hStateAcc⟩

/-- Completeness of `zdAcceptingStep` on `bitProblem` with `r = configBitWidth`:
if `M` accepts `input` within capacity `S`, then `zdAcceptingStep` reaches `.accept`. -/
theorem bitProblem_accepting_complete {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S : ℕ) (hS : 1 ≤ S) (hInput : n ≤ 2 ^ S)
    (hAccepts : M.AcceptsWithinCapacity input S (by omega)) :
    Relation.ReflTransGen
      (zdOutcomeStep (bitProblem M input S) (configBitWidth_gt_one_pow Q Γ k S)
        (bitIsAccepting M n S))
      (.running (zdInitial (configBitWidth Q Γ k S + 1) (2 ^ configBitWidth Q Γ k S - 1)
        (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))))
      .accept := by
  rcases hAccepts with ⟨finalCfg, hRun, hAcc⟩
  have hCodeRun : Relation.ReflTransGen (bitProblem M input S).step
      (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega))).val
      (bitEncodeConfig Q Γ finalCfg).val := by
    clear hAcc
    induction hRun with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hStep ih =>
      exact Relation.ReflTransGen.tail ih
        ((bitProblem_step_iff M input S hS hInput prev curr).2 hStep)
  have hShort := reachesWithin_of_reflTransGen (bitProblem M input S) hCodeRun
  have hPow : 2 ^ configBitWidth Q Γ k S - 1 ≤ 2 ^ configBitWidth Q Γ k S := Nat.sub_le _ _
  have hWithin := ReachesWithin.mono (bitProblem M input S) hPow hShort
  have hTargetAcc : bitIsAccepting M n S (bitEncodeConfig Q Γ finalCfg).val = true := by
    classical
    simp only [bitIsAccepting, decide_eq_true_eq]
    exact ⟨finalCfg, rfl, hAcc⟩
  exact zdAcceptingStep_completeness (bitProblem M input S)
    (configBitWidth_gt_one_pow Q Γ k S) (bitIsAccepting M n S)
    (configBitWidth Q Γ k S)
    (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))
    (bitEncodeConfig Q Γ finalCfg) hTargetAcc hWithin

theorem bitProblem_step_bits_iff {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (input : Fin n → InputAlphabet)
    (S : ℕ) (bs₁ bs₂ : List Bool)
    (hLen₁ : bs₁.length = configBitWidth Q Γ k S)
    (hLen₂ : bs₂.length = configBitWidth Q Γ k S) :
    (bitProblem M input S).step
      ⟨bitsToNat bs₁, by have := bitsToNat_lt_pow bs₁; rw [hLen₁] at this; omega⟩
      ⟨bitsToNat bs₂, by have := bitsToNat_lt_pow bs₂; rw [hLen₂] at this; omega⟩ ↔
    ∃ c₁ c₂ : TMConfig Q Γ k n S,
      encodeConfigBits Q Γ c₁ = bs₁ ∧ encodeConfigBits Q Γ c₂ = bs₂ ∧
      M.step input S c₁ c₂ := by
  constructor
  · rintro ⟨c₁, c₂, hc₁, hc₂, hStep⟩
    refine ⟨c₁, c₂, ?_, ?_, hStep⟩
    · have hVal := congrArg Fin.val hc₁
      have hBits := congrArg (natToBits (configBitWidth Q Γ k S)) hVal
      have h1 := natToBits_bitsToNat (encodeConfigBits Q Γ c₁)
      have h2 := natToBits_bitsToNat bs₁
      rw [encodeConfigBits_length] at h1
      rw [hLen₁] at h2
      exact h1.symm.trans (hBits.trans h2)
    · have hVal := congrArg Fin.val hc₂
      have hBits := congrArg (natToBits (configBitWidth Q Γ k S)) hVal
      have h1 := natToBits_bitsToNat (encodeConfigBits Q Γ c₂)
      have h2 := natToBits_bitsToNat bs₂
      rw [encodeConfigBits_length] at h1
      rw [hLen₂] at h2
      exact h1.symm.trans (hBits.trans h2)
  · rintro ⟨c₁, c₂, rfl, rfl, hStep⟩
    refine ⟨c₁, c₂, ?_, ?_, hStep⟩ <;> exact Fin.ext rfl

theorem bitIsAccepting_bits_iff {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (S : ℕ) (bs : List Bool)
    (hLen : bs.length = configBitWidth Q Γ k S) :
    bitIsAccepting M n S
      ⟨bitsToNat bs, by have := bitsToNat_lt_pow bs; rw [hLen] at this; omega⟩ = true ↔
    ∃ c : TMConfig Q Γ k n S, encodeConfigBits Q Γ c = bs ∧ M.accepting c.state := by
  classical
  simp only [bitIsAccepting, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hAcc⟩
    refine ⟨c, ?_, hAcc⟩
    have hVal := congrArg Fin.val hc
    have hBits := congrArg (natToBits (configBitWidth Q Γ k S)) hVal
    have h1 := natToBits_bitsToNat (encodeConfigBits Q Γ c)
    have h2 := natToBits_bitsToNat bs
    rw [encodeConfigBits_length] at h1
    rw [hLen] at h2
    exact h1.symm.trans (hBits.trans h2)
  · rintro ⟨c, rfl, hAcc⟩
    exact ⟨c, Fin.ext rfl, hAcc⟩

/-- Quadratic bound on the bit-encoded register storage `(W + 2) * (W + 2)`. -/
theorem bitConfig_storage_quadratic (Q Γ : Type*) [Fintype Q] [Fintype Γ]
    (k S : ℕ) (hS : 1 ≤ S) :
    (configBitWidth Q Γ k S + 2) * (configBitWidth Q Γ k S + 2) ≤
      ((qBits Q + 6 + k * (1 + gammaBits Γ)) * (S + 1)) ^ 2 := by
  have hW : configBitWidth Q Γ k S + 2 ≤
      (qBits Q + 6 + k * (1 + gammaBits Γ)) * (S + 1) := by
    unfold configBitWidth tapeBitWidth
    nlinarith [hS]
  have hMul := Nat.mul_le_mul hW hW
  simpa only [pow_two] using hMul

end SavitchLemma

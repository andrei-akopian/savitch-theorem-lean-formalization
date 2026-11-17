module

public import SavitchLemma.AcceptingZD
public import SavitchLemma.ConcreteEncoding
public import SavitchLemma.RegisterTapeOps

@[expose] public section

/-!
# Simulator core helpers

Defines shared 5-tape actions, bit-relation trackers, and tape summaries.
-/

namespace SavitchLemma

/-! ## General 5-tape action & bit helpers -/

/-- Build a stationary-input `TMAction` directly from per-tape writes and moves. -/
def mkWorkAction {Q : Type*} {k : ℕ} (next : Q)
    (writeFn : Fin k → SimSym) (moveFn : Fin k → TapeMove) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write := writeFn
  workMove := moveFn

theorem OneSidedTape.updateAndMove_stay_self (t : OneSidedTape SimSym) :
    t.updateAndMove (t.cells t.head) .stay = some t := by
  simp only [OneSidedTape.updateAndMove, moveOneSidedHead, Option.some.injEq]
  cases t
  simp only [OneSidedTape.mk.injEq, and_true]
  funext i
  split_ifs with h
  · rw [h]
  · rfl

theorem compStep_head_override {Q Exit InputAlphabet : Type*} {k n : ℕ}
    (M : TMComponent Q InputAlphabet SimSym k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes nextTapes finalTapes : Fin k → OneSidedTape SimSym)
    (inHead finalInHead : Fin (n + 2)) (e : Exit)
    (q q' : Q)
    (hHeads : ∀ j, (initTapes j).head < bound j)
    (hNextHeads : ∀ j, (nextTapes j).head < bound j)
    (hInMove : moveHead (n + 2) inHead
      (M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).inputMove = some inHead)
    (hUpd : ∀ j, (initTapes j).updateAndMove
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).write j)
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
      some (nextTapes j))
    (hNextState : (M.step q (readInput input inHead)
      (fun j => (initTapes j).cells (initTapes j).head)).nextState = .inl q')
    (hRest : Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q', inHead, nextTapes⟩ ⟨.inr e, finalInHead, finalTapes⟩) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, inHead, initTapes⟩ ⟨.inr e, finalInHead, finalTapes⟩ := by
  refine Relation.ReflTransGen.head ⟨?_, hHeads, hNextHeads⟩ hRest
  exact ⟨q, rfl, hNextState.symm, inHead, hInMove, rfl, hUpd⟩

theorem compStep_exit_override {Q Exit InputAlphabet : Type*} {k n : ℕ}
    (M : TMComponent Q InputAlphabet SimSym k Exit)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (initTapes nextTapes : Fin k → OneSidedTape SimSym)
    (inHead : Fin (n + 2)) (e : Exit) (q : Q)
    (hHeads : ∀ j, (initTapes j).head < bound j)
    (hNextHeads : ∀ j, (nextTapes j).head < bound j)
    (hInMove : moveHead (n + 2) inHead
      (M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).inputMove = some inHead)
    (hUpd : ∀ j, (initTapes j).updateAndMove
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).write j)
      ((M.step q (readInput input inHead)
        (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
      some (nextTapes j))
    (hNextState : (M.step q (readInput input inHead)
      (fun j => (initTapes j).cells (initTapes j).head)).nextState = .inr e) :
    Relation.ReflTransGen
      (fun a b => M.CompStep input a b ∧
        (∀ j, (a.workTapes j).head < bound j) ∧
        (∀ j, (b.workTapes j).head < bound j))
      ⟨.inl q, inHead, initTapes⟩ ⟨.inr e, inHead, nextTapes⟩ := by
  refine Relation.ReflTransGen.single ⟨?_, hHeads, hNextHeads⟩
  exact ⟨q, rfl, hNextState.symm, inHead, hInMove, rfl, hUpd⟩

theorem true_mem_iff_bitsToNat_pos (bs : List Bool) :
    true ∈ bs ↔ 0 < bitsToNat bs := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    cases b
    · have h1 : (true ∈ false :: bs) ↔ true ∈ bs := by simp
      rw [h1, ih]
      simp only [bitsToNat]
      cases bitsToNat bs <;> simp
    · simp [bitsToNat]

theorem true_not_mem_iff_bitsToNat_zero (bs : List Bool) :
    true ∉ bs ↔ bitsToNat bs = 0 := by
  rw [true_mem_iff_bitsToNat_pos]
  omega

/-- Decode `m` bits (LSB-first) into an element of a finite type `U`, returning
`none` when the decoded integer is at least `Fintype.card U`. -/
noncomputable def decodeBitsOpt (m : ℕ) (U : Type*) [Fintype U]
    (f : Fin m → Bool) : Option U :=
  let v := bitsToNat (List.ofFn f)
  if h : v < Fintype.card U then
    some ((Fintype.equivFin U).symm ⟨v, h⟩)
  else
    none

theorem decodeBitsOpt_eq_some_iff {m : ℕ} {U : Type*} [Fintype U]
    (hPow : Fintype.card U + 1 ≤ 2 ^ m) (f : Fin m → Bool) (u : U) :
    decodeBitsOpt m U f = some u ↔
      natToBits m (Fintype.equivFin U u).val = List.ofFn f := by
  unfold decodeBitsOpt
  dsimp only
  constructor
  · intro hDec
    split_ifs at hDec with hLt
    simp only [Option.some.injEq] at hDec
    have hVal : (Fintype.equivFin U u).val = bitsToNat (List.ofFn f) := by
      rw [← hDec, Equiv.apply_symm_apply]
    rw [hVal]
    have hId := natToBits_bitsToNat (List.ofFn f)
    simpa [List.length_ofFn] using hId
  · intro hBits
    have hValLt : (Fintype.equivFin U u).val < 2 ^ m := by
      have h1 := (Fintype.equivFin U u).isLt
      omega
    have hNat := congrArg bitsToNat hBits
    rw [bitsToNat_natToBits_of_lt hValLt] at hNat
    have hLt : bitsToNat (List.ofFn f) < Fintype.card U := by
      rw [← hNat]
      exact (Fintype.equivFin U u).isLt
    simp only [hLt, ↓reduceDIte, Option.some.injEq]
    apply (Fintype.equivFin U).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext hNat.symm

/-- Finite-state DFA tracker comparing two equal-length LSB-first bit streams
`u` (A) and `v` (B) for equality (`v = u`), increment (`v = u + 1`), and decrement
(`u = v + 1`) simultaneously in one left-to-right pass. -/
structure BitRelState where
  eqOk : Bool
  incOk : Bool
  incCarry : Bool
  decOk : Bool
  decCarry : Bool
  deriving DecidableEq

def BitRelState.equivProd : BitRelState ≃ Bool × Bool × Bool × Bool × Bool where
  toFun s := (s.eqOk, s.incOk, s.incCarry, s.decOk, s.decCarry)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨_, _, _, _, _⟩; rfl

instance : Fintype BitRelState :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool × Bool) BitRelState.equivProd.symm

def BitRelState.init : BitRelState :=
  ⟨true, true, true, true, true⟩

def BitRelState.step (st : BitRelState) (a b : Bool) : BitRelState where
  eqOk := st.eqOk && (a == b)
  incOk := st.incOk && (b == xor a st.incCarry)
  incCarry := a && st.incCarry
  decOk := st.decOk && (a == xor b st.decCarry)
  decCarry := b && st.decCarry

def BitRelState.runList (st : BitRelState) (u v : List Bool) : BitRelState :=
  (u.zip v).foldl (fun s p => s.step p.1 p.2) st

theorem BitRelState.runList_eqOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    (st.runList u v).eqOk = true ↔ (st.eqOk = true ∧ u = v) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil => simp [BitRelState.runList]
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change ((st.step a b).runList us vs).eqOk = true ↔ st.eqOk = true ∧ a :: us = b :: vs
      rw [ih (st.step a b) vs hLen]
      simp [BitRelState.step, Bool.and_eq_true, List.cons.injEq]
      tauto

theorem BitRelState.runList_incOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    ((st.runList u v).incOk && !(st.runList u v).incCarry) = true ↔
      (st.incOk = true ∧ bitsToNat v = bitsToNat u + st.incCarry.toNat) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil =>
      simp only [BitRelState.runList, List.zip_nil_right, List.foldl_nil, bitsToNat, Nat.zero_add,
        Bool.and_eq_true, Bool.not_eq_true']
      cases st.incOk <;> cases st.incCarry <;> simp
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change (((st.step a b).runList us vs).incOk &&
        !((st.step a b).runList us vs).incCarry) = true ↔
        st.incOk = true ∧ bitsToNat (b :: vs) = bitsToNat (a :: us) + st.incCarry.toNat
      rw [ih (st.step a b) vs hLen]
      simp only [BitRelState.step, Bool.and_eq_true, bitsToNat]
      cases st.incOk <;> cases a <;> cases b <;> cases st.incCarry <;> simp <;> omega

theorem BitRelState.runList_decOk (st : BitRelState) (u v : List Bool)
    (hLen : u.length = v.length) :
    ((st.runList u v).decOk && !(st.runList u v).decCarry) = true ↔
      (st.decOk = true ∧ bitsToNat u = bitsToNat v + st.decCarry.toNat) := by
  induction u generalizing st v with
  | nil =>
    cases v with
    | nil =>
      simp only [BitRelState.runList, List.zip_nil_right, List.foldl_nil, bitsToNat, Nat.zero_add,
        Bool.and_eq_true, Bool.not_eq_true']
      cases st.decOk <;> cases st.decCarry <;> simp
    | cons _ _ => simp at hLen
  | cons a us ih =>
    cases v with
    | nil => simp at hLen
    | cons b vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      change (((st.step a b).runList us vs).decOk &&
        !((st.step a b).runList us vs).decCarry) = true ↔
        st.decOk = true ∧ bitsToNat (a :: us) = bitsToNat (b :: vs) + st.decCarry.toNat
      rw [ih (st.step a b) vs hLen]
      simp only [BitRelState.step, Bool.and_eq_true, bitsToNat]
      cases st.decOk <;> cases a <;> cases b <;> cases st.decCarry <;> simp <;> omega

theorem BitRelState.init_runList (u v : List Bool) (hLen : u.length = v.length) :
    let r := BitRelState.init.runList u v
    (r.eqOk = true ↔ bitsToNat u = bitsToNat v) ∧
    ((r.incOk && !r.incCarry) = true ↔ bitsToNat v = bitsToNat u + 1) ∧
    ((r.decOk && !r.decCarry) = true ↔ bitsToNat u = bitsToNat v + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitRelState.runList_eqOk BitRelState.init u v hLen]
    simp only [BitRelState.init, true_and]
    constructor
    · intro h; subst h; rfl
    · intro h
      have h1 := natToBits_bitsToNat u
      have h2 := natToBits_bitsToNat v
      rw [hLen] at h1
      rw [h] at h1
      exact h1.symm.trans h2
  · simpa [BitRelState.init] using BitRelState.runList_incOk BitRelState.init u v hLen
  · simpa [BitRelState.init] using BitRelState.runList_decOk BitRelState.init u v hLen

/-- Finite-state predicate checking whether `rel` witnesses `moveHead (n+2) h₁ mv = some h₂`
given `inSym = readInput input h₁`. -/
def relMatchesInputMove {InputAlphabet : Type*} (inSym : InputSymbol InputAlphabet)
    (rel : BitRelState) (mv : TapeMove) : Bool :=
  match mv with
  | .left =>
    match inSym with
    | .leftEnd => false
    | _ => rel.decOk && !rel.decCarry
  | .stay => rel.eqOk
  | .right =>
    match inSym with
    | .rightEnd => false
    | _ => rel.incOk && !rel.incCarry

theorem relMatchesInputMove_iff {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (h₁ : Fin (n + 2)) (h₂val : ℕ)
    (u v : List Bool) (hLen : u.length = v.length)
    (hU : bitsToNat u = h₁.val) (hV : bitsToNat v = h₂val)
    (mv : TapeMove) :
    relMatchesInputMove (readInput input h₁) (BitRelState.init.runList u v) mv = true ↔
      ∃ h₂ : Fin (n + 2), moveHead (n + 2) h₁ mv = some h₂ ∧ h₂.val = h₂val := by
  obtain ⟨hEq, hInc, hDec⟩ := BitRelState.init_runList u v hLen
  cases mv with
  | left =>
    unfold relMatchesInputMove readInput
    split_ifs with h0 hR
    · simp [moveHead, h0]
    · simp only [moveHead, hDec, hU, hV]
      have hPos : 0 < h₁.val := by omega
      simp only [hPos, ↓reduceDIte]
      constructor
      · intro h
        refine ⟨⟨h₁.val - 1, by omega⟩, rfl, by simp; omega⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val - 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
    · simp only [moveHead, hDec, hU, hV]
      have hPos : 0 < h₁.val := by omega
      simp only [hPos, ↓reduceDIte]
      constructor
      · intro h
        refine ⟨⟨h₁.val - 1, by omega⟩, rfl, by simp; omega⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val - 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
  | stay =>
    unfold relMatchesInputMove moveHead
    simp only [hEq, hU, hV, Option.some.injEq]
    constructor
    · intro h; exact ⟨h₁, rfl, h⟩
    · rintro ⟨_, rfl, hVal⟩; exact hVal
  | right =>
    unfold relMatchesInputMove readInput
    split_ifs with h0 hR
    · have hLt : h₁.val + 1 < n + 2 := by omega
      simp only [moveHead, hLt, ↓reduceDIte, hInc, hU, hV]
      constructor
      · intro h; exact ⟨⟨h₁.val + 1, hLt⟩, rfl, by simp [h]⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val + 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega
    · simp [moveHead, hR]
    · have hLt : h₁.val + 1 < n + 2 := by omega
      simp only [moveHead, hLt, ↓reduceDIte, hInc, hU, hV]
      constructor
      · intro h; exact ⟨⟨h₁.val + 1, hLt⟩, rfl, by simp [h]⟩
      · rintro ⟨next, hM, hVal⟩
        have hValNext : next.val = h₁.val + 1 := by
          have := congrArg (Option.map Fin.val) hM
          simpa using this.symm
        omega

/-- Position relative to the current tape head during an `S`-cell sweep. -/
inductive HeadMatchState where
  | before
  | atHead
  | pastHead
  deriving DecidableEq

def HeadMatchState.equivFin : HeadMatchState ≃ Fin 3 where
  toFun | .before => 0 | .atHead => 1 | .pastHead => 2
  invFun | 0 => .before | 1 => .atHead | _ => .pastHead
  left_inv x := by cases x <;> rfl
  right_inv i := by revert i; decide

instance : Fintype HeadMatchState := Fintype.ofEquiv (Fin 3) HeadMatchState.equivFin.symm

/-- Finite summary of checking one serialized work-tape block between `tArgA` and `tArgB`. -/
structure TapeSummary (Γ : Type*) where
  ok : Bool
  scanned : Γ
  written : Γ
  leftValid : Bool
  stayValid : Bool
  rightValid : Bool

instance {Γ : Type*} [Fintype Γ] : Fintype (TapeSummary Γ) :=
  Fintype.ofEquiv (Bool × Γ × Γ × Bool × Bool × Bool)
    { toFun := fun ⟨ok, s, w, l, st, r⟩ => ⟨ok, s, w, l, st, r⟩
      invFun := fun t => (t.ok, t.scanned, t.written, t.leftValid, t.stayValid, t.rightValid)
      left_inv := fun ⟨_, _, _, _, _, _⟩ => rfl
      right_inv := fun t => by cases t; rfl }

def TapeSummary.matchesAction {Γ : Type*} [DecidableEq Γ] (ts : TapeSummary Γ)
    (w : Γ) (mv : TapeMove) : Bool :=
  ts.ok && decide (ts.written = w) &&
    match mv with
    | .left => ts.leftValid
    | .stay => ts.stayValid
    | .right => ts.rightValid

end SavitchLemma

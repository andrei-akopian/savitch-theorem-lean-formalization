module

public import SavitchLemma.AcceptingZD
public import SavitchLemma.ConcreteEncoding
public import SavitchLemma.RegisterTapeOps

@[expose] public section

/-!
# Concrete 5-tape deterministic Savitch simulator

This module implements and verifies the fixed-capacity concrete simulator
`savitchFixedCapComponent` on the 5-tape workspace (`tRuler`, `tRegs`, `tArgA`,
`tArgB`, `tScratch`) for any nondeterministic machine `M : MultitapeNTM Q InputAlphabet Γ k`,
starting from `1^S` on `tRuler` and blank-marker tapes `[.leftMark]` on `tRegs..tScratch`.
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

/-! ## D0: Initializing the Savitch register array from `tRuler = 1^S` -/

/-- Write `m` copies of `.bit true` simultaneously onto `tArgA` and `tArgB`. -/
def writeConstOnes (InputAlphabet : Type*) (m : ℕ) :
    TMComponent (Fin (m + 1)) InputAlphabet SimSym 5 Unit where
  start := ⟨0, Nat.zero_lt_succ m⟩
  step idx _ scanned :=
    if h : idx.val < m then
      mkWorkAction (.inl ⟨idx.val + 1, by omega⟩)
        (fun j => if j = tArgA ∨ j = tArgB then .bit true else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB then .right else .stay)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem writeConstOnes_reachesExit {InputAlphabet : Type*} {n : ℕ} (m : ℕ)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (prefA prefB : List SimSym)
    (hBoundA : prefA.length + m < bound tArgA)
    (hBoundB : prefB.length + m < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchA : TapeMatches (initTapes tArgA) prefA prefA.length)
    (hMatchB : TapeMatches (initTapes tArgB) prefB prefB.length) :
    ∃ ftA ftB,
      (writeConstOnes InputAlphabet m).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tArgA then ftA else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftA (prefA ++ List.replicate m (.bit true)) (prefA.length + m) ∧
      TapeMatches ftB (prefB ++ List.replicate m (.bit true)) (prefB.length + m) := by
  have hNeAB : tArgA ≠ tArgB := by decide
  have hStep : ∀ rem, ∀ done (hSum : done + rem = m) pA pB tA tB,
      TapeMatches tA pA pA.length →
      TapeMatches tB pB pB.length →
      pA.length + rem < bound tArgA →
      pB.length + rem < bound tArgB →
      ∃ ftA ftB,
        Relation.ReflTransGen
          (fun a b => (writeConstOnes InputAlphabet m).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl ⟨done, by omega⟩, inHead,
            fun j => if j = tArgA then tA else if j = tArgB then tB else initTapes j⟩
          ⟨.inr (), inHead,
            fun j => if j = tArgA then ftA else if j = tArgB then ftB else initTapes j⟩ ∧
        TapeMatches ftA (pA ++ List.replicate rem (.bit true)) (pA.length + rem) ∧
        TapeMatches ftB (pB ++ List.replicate rem (.bit true)) (pB.length + rem) := by
    intro rem
    induction rem with
    | zero =>
      intro done hSum pA pB tA tB htA htB hBA hBB
      have hDone : done = m := by omega
      have hHeads : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [htA.head_eq] using hBA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, htB.head_eq] using hBB
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ftA, hUpdA, hMA⟩ := htA.update_keep .stay rfl
      obtain ⟨ftB, hUpdB, hMB⟩ := htB.update_keep .stay rfl
      have hUpd : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).updateAndMove
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).write j)
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).workMove j) =
            some (if j = tArgA then ftA else if j = tArgB then ftB else initTapes j) := by
        intro j
        have hNotLt : ¬ done < m := by omega
        simp only [writeConstOnes, mkWorkAction, hNotLt, ↓reduceDIte]
        by_cases h1 : j = tArgA
        · subst h1; simpa using hUpdA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1] using hUpdB
          · simp only [h1, h2, ↓reduceIte]
            exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j,
          (if j = tArgA then ftA else if j = tArgB then ftB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [hMA.head_eq] using hBA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, hMB.head_eq] using hBB
          · simp [h1, h2, hOtherBounds j h1 h2]
      refine ⟨ftA, ftB, compStep_exit_override (writeConstOnes InputAlphabet m) input bound
        _ _ inHead () ⟨done, by omega⟩ hHeads hNextH
        (by
          have hNotLt : ¬ done < m := by omega
          simp [writeConstOnes, mkWorkAction, moveHead, hNotLt])
        hUpd
        (by
          have hNotLt : ¬ done < m := by omega
          simp [writeConstOnes, mkWorkAction, hNotLt]),
        by simpa using hMA, by simpa using hMB⟩
    | succ r ih =>
      intro done hSum pA pB tA tB htA htB hBA hBB
      have hLt : done < m := by omega
      have hHeads : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [htA.head_eq] using by omega
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, htB.head_eq] using by omega
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ntA, hUpdA, hMA⟩ := htA.update_append (.bit true)
      obtain ⟨ntB, hUpdB, hMB⟩ := htB.update_append (.bit true)
      have hUpd : ∀ j,
          (if j = tArgA then tA else if j = tArgB then tB else initTapes j).updateAndMove
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).write j)
            (((writeConstOnes InputAlphabet m).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = tArgA then tA else if j = tArgB then tB else initTapes j).cells
                (if j = tArgA then tA else if j = tArgB then tB else initTapes j).head)).workMove j) =
            some (if j = tArgA then ntA else if j = tArgB then ntB else initTapes j) := by
        intro j
        simp only [writeConstOnes, mkWorkAction, hLt, ↓reduceDIte]
        by_cases h1 : j = tArgA
        · subst h1; simpa using hUpdA
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1] using hUpdB
          · simp only [h1, h2, ↓reduceIte]
            exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j,
          (if j = tArgA then ntA else if j = tArgB then ntB else initTapes j).head < bound j := by
        intro j
        by_cases h1 : j = tArgA
        · subst h1; simpa [hMA.head_eq] using by omega
        · by_cases h2 : j = tArgB
          · subst h2; simpa [h1, hMB.head_eq] using by omega
          · simp [h1, h2, hOtherBounds j h1 h2]
      obtain ⟨ftA, ftB, hRest, hFA, hFB⟩ := ih (done + 1) (by omega) (pA ++ [.bit true])
        (pB ++ [.bit true]) ntA ntB (by simpa using hMA) (by simpa using hMB)
        (by simp; omega) (by simp; omega)
      refine ⟨ftA, ftB, compStep_head_override (writeConstOnes InputAlphabet m) input bound
        _ _ _ inHead inHead () ⟨done, by omega⟩ ⟨done + 1, by omega⟩ hHeads hNextH
        (by simp [writeConstOnes, mkWorkAction, moveHead, hLt]) hUpd
        (by simp [writeConstOnes, mkWorkAction, hLt]) hRest, ?_, ?_⟩
      · have : pA.length + (r + 1) = (pA ++ [SimSym.bit true]).length + r := by simp; omega
        rw [this]
        simpa [List.replicate_succ, List.append_assoc] using hFA
      · have : pB.length + (r + 1) = (pB ++ [SimSym.bit true]).length + r := by simp; omega
        rw [this]
        simpa [List.replicate_succ, List.append_assoc] using hFB
  have hTapesSelf : (fun j => if j = tArgA then initTapes tArgA
      else if j = tArgB then initTapes tArgB else initTapes j) = initTapes := by
    funext j; by_cases h1 : j = tArgA <;> by_cases h2 : j = tArgB <;> simp [h1, h2, hNeAB.symm]
  have hRes := hStep m 0 (Nat.zero_add m) prefA prefB
    (initTapes tArgA) (initTapes tArgB) hMatchA hMatchB hBoundA hBoundB
  rw [hTapesSelf] at hRes
  exact hRes

/-- One-step atom advancing a single tape `t` one cell to the right without changing its cell. -/
def stepRightAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) scanned (fun j => if j = t then .right else .stay)

theorem stepRightAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (contents : List SimSym) (pos : ℕ) (hBound : pos + 1 < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) contents pos) :
    ∃ ft,
      (stepRightAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft contents (pos + 1) := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using by omega
    · exact hOtherBounds j hj
  have hMove : moveOneSidedHead pos .right = some (pos + 1) := by simp [moveOneSidedHead]
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_keep .right hMove
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((stepRightAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [stepRightAtom, mkWorkAction] using hUpdT
    · simp only [stepRightAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (stepRightAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH rfl hUpd rfl, hFT⟩

/-- Check `tRuler`: if `.bit true`, exit `true` (staying put); else write `.endMark`
on `tArgA` and `tArgB` (`.stay`) and exit `false`. -/
def rulerCheckOrEndAB (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5) (Exit := Bool)
    (fun _ scanned =>
      match scanned tRuler with
      | .bit true => mkWorkAction true scanned (fun _ => .stay)
      | _ => mkWorkAction false
          (fun j => if j = tArgA ∨ j = tArgB then .endMark else scanned j) (fun _ => .stay))

/-- Loop body for `writeRulerScaledOnes`: on each `.bit true` of `tRuler`, append `scale`
ones to `tArgA` and `tArgB` and advance `tRuler`; on `.endMark`, write `.endMark` on
`tArgA` and `tArgB` and exit. -/
def writeRulerScaledOnesBody (InputAlphabet : Type*) (scale : ℕ) :=
  (rulerCheckOrEndAB InputAlphabet).branch
    (((writeConstOnes InputAlphabet scale).seq (stepRightAtom InputAlphabet tRuler)).mapExit
      (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit)))
    (TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5)
      (Exit := Unit ⊕ Unit)
      (fun _ scanned => mkWorkAction (.inr ()) scanned (fun _ => .stay)))

def writeRulerScaledOnes (InputAlphabet : Type*) (scale : ℕ) :=
  (writeRulerScaledOnesBody InputAlphabet scale).loop

theorem writeRulerScaledOnes_reachesExit {InputAlphabet : Type*} {n : ℕ} (scale : ℕ)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pA pB : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + S * scale < bound tArgA)
    (hBoundB : pB.length + S * scale < bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) pA pA.length)
    (hMatchB : TapeMatches (initTapes tArgB) pB pB.length) :
    ∃ ftR ftA ftB,
      (writeRulerScaledOnes InputAlphabet scale).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) (1 + S) ∧
      TapeMatches ftA (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
        (pA.length + S * scale) ∧
      TapeMatches ftB (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
        (pB.length + S * scale) := by
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    ∃ done rem curA curB,
      done + rem = S ∧
      curA = pA ++ List.replicate (done * scale) (.bit true) ∧
      curB = pB ++ List.replicate (done * scale) (.bit true) ∧
      TapeMatches (tapes tRuler) rC (1 + done) ∧
      TapeMatches (tapes tArgA) curA curA.length ∧
      TapeMatches (tapes tArgB) curB curB.length
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (writeRulerScaledOnesBody InputAlphabet scale).ReachesExit input bound tapes ih
          (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧
        (S + 1 - (tapes' tRuler).head) < (S + 1 - (tapes tRuler).head)) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (writeRulerScaledOnesBody InputAlphabet scale).ReachesExit input bound tapes ih
          (.inr e) tapes' ih' ∧
        ih' = inHead ∧
        (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes' j = initTapes j) ∧
        TapeMatches (tapes' tRuler) rC (1 + S) ∧
        TapeMatches (tapes' tArgA) (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
          (pA.length + S * scale) ∧
        TapeMatches (tapes' tArgB) (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
          (pB.length + S * scale)) := by
    intro tapes ih ⟨hIh, hOth, done, rem, curA, curB, hSum, hCurA, hCurB, htR, htA, htB⟩
    subst ih
    have hCurALen : curA.length = pA.length + done * scale := by simp [hCurA]
    have hCurBLen : curB.length = pB.length + done * scale := by simp [hCurB]
    have hMulLe : done * scale + rem * scale = S * scale := by
      rw [← Nat.add_mul, hSum]
    have hHeads : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRuler
      · subst h1; simpa [htR.head_eq] using by omega
      · by_cases h2 : j = tArgA
        · subst h2; simpa [htA.head_eq, hCurALen] using by omega
        · by_cases h3 : j = tArgB
          · subst h3; simpa [htB.head_eq, hCurBLen] using by omega
          · rw [hOth j h1 h2 h3]; exact hOtherBounds j h1 h2 h3
    cases rem with
    | zero =>
      have hDone : done = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = S + 1 := by omega
        simp [rC, hIdx]
      obtain ⟨ntA, hUpdA, hMA⟩ := htA.update_append_move rfl .endMark .stay rfl
      obtain ⟨ntB, hUpdB, hMB⟩ := htB.update_append_move rfl .endMark .stay rfl
      let nextT := fun j => if j = tArgA then ntA else if j = tArgB then ntB else tapes j
      have hChk : (rulerCheckOrEndAB InputAlphabet).ReachesExit input bound tapes inHead
          false nextT inHead := by
        refine compStep_exit_override (rulerCheckOrEndAB InputAlphabet) input bound tapes nextT
          inHead false () hHeads
          (fun j => by
            by_cases h2 : j = tArgA
            · subst h2; simpa [nextT, hMA.head_eq, hCurALen, hDone] using hBoundA
            · by_cases h3 : j = tArgB
              · subst h3; simpa [nextT, h2, hMB.head_eq, hCurBLen, hDone] using hBoundB
              · simpa [nextT, h2, h3] using hHeads j)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction,
              nextT]
            by_cases h2 : j = tArgA
            · subst h2; simpa using hUpdA
            · by_cases h3 : j = tArgB
              · subst h3; simpa [h2] using hUpdB
              · simp only [h2, h3, ↓reduceIte]
                exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hNextH : ∀ j, (nextT j).head < bound j := by
        intro j
        by_cases h2 : j = tArgA
        · subst h2; simpa [nextT, hMA.head_eq, hCurALen, hDone] using hBoundA
        · by_cases h3 : j = tArgB
          · subst h3; simpa [nextT, h2, hMB.head_eq, hCurBLen, hDone] using hBoundB
          · simpa [nextT, h2, h3] using hHeads j
      have hExit := TMComponent.atom_reachesExit
        (fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound nextT inHead hNextH inHead (by simp [mkWorkAction, moveHead]) nextT
        (fun j => by
          simp only [mkWorkAction]
          exact OneSidedTape.updateAndMove_stay_self _)
        hNextH
      refine Or.inr ⟨(), nextT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound false hChk (by simpa [mkWorkAction] using hExit),
        rfl, fun j hj1 hj2 hj3 => by simp [nextT, hj2, hj3, hOth j hj1 hj2 hj3],
        ?_, ?_, ?_⟩
      · simpa [nextT, hNeRA, hNeRB, hDone] using htR
      · simpa [nextT, hCurA, hDone, List.append_assoc] using hMA
      · simpa [nextT, hCurB, hNeAB.symm, hDone, List.append_assoc] using hMB
    | succ r =>
      have hDoneLt : done < S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : (1 + done) = done + 1 := Nat.add_comm 1 done
        simp only [rC, hIdx, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left (by simp; exact hDoneLt)]
        simp
      have hChk : (rulerCheckOrEndAB InputAlphabet).ReachesExit input bound tapes inHead
          true tapes inHead := by
        refine compStep_exit_override (rulerCheckOrEndAB InputAlphabet) input bound tapes tapes
          inHead true () hHeads hHeads
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckOrEndAB, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hScaleBoundA : curA.length + scale < bound tArgA := by
        have : 1 * scale ≤ (r + 1) * scale := Nat.mul_le_mul_right scale (by omega)
        omega
      have hScaleBoundB : curB.length + scale < bound tArgB := by
        have : 1 * scale ≤ (r + 1) * scale := Nat.mul_le_mul_right scale (by omega)
        omega
      obtain ⟨ftA, ftB, hWriteOnes, hFA, hFB⟩ := writeConstOnes_reachesExit scale input bound
        curA curB hScaleBoundA hScaleBoundB tapes inHead
        (fun j h1 h2 => hHeads j) htA htB
      let midT := fun j => if j = tArgA then ftA else if j = tArgB then ftB else tapes j
      have hMidR : TapeMatches (midT tRuler) rC (1 + done) := by
        simpa [midT, hNeRA, hNeRB] using htR
      obtain ⟨ftR, hStepR, hFR⟩ := stepRightAtom_reachesExit tRuler input bound rC (1 + done)
        (by omega) midT inHead (fun j hj => by
          by_cases h2 : j = tArgA
          · subst h2; simpa [midT, hFA.head_eq, hCurALen] using by omega
          · by_cases h3 : j = tArgB
            · subst h3; simpa [midT, h2, hFB.head_eq, hCurBLen] using by omega
            · simpa [midT, h2, h3] using hHeads j)
        hMidR
      have hSeq := TMComponent.mapExit_reachesExit _ (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit))
        input bound ((writeConstOnes InputAlphabet scale).seq_reachesExit
          (stepRightAtom InputAlphabet tRuler) input bound hWriteOnes hStepR)
      let finalT := fun j => if j = tRuler then ftR else midT j
      refine Or.inl ⟨finalT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound true hChk hSeq, ?_, ?_⟩
      · refine ⟨rfl, fun j hj1 hj2 hj3 => by simp [finalT, midT, hj1, hj2, hj3, hOth j hj1 hj2 hj3],
          done + 1, r, curA ++ List.replicate scale (.bit true), curB ++ List.replicate scale (.bit true),
          by omega, ?_, ?_, ?_,
          by simpa [finalT, midT, hNeRA.symm] using hFA,
          by simpa [finalT, midT, hNeRB.symm, hNeAB.symm] using hFB⟩
        · rw [hCurA, List.append_assoc, ← List.replicate_add]
          congr 2
          rw [Nat.succ_mul]
        · rw [hCurB, List.append_assoc, ← List.replicate_add]
          congr 2
          rw [Nat.succ_mul]
        · have : 1 + done + 1 = 1 + (done + 1) := by omega
          rw [← this]
          simpa [finalT] using hFR
      · simp [finalT, hFR.head_eq, htR.head_eq]
        omega
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun _ tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) rC (1 + S) ∧
    TapeMatches (tapes tArgA) (pA ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
      (pA.length + S * scale) ∧
    TapeMatches (tapes tArgB) (pB ++ List.replicate (S * scale) (.bit true) ++ [.endMark])
      (pB.length + S * scale)
  have hInitInv : Inv initTapes inHead :=
    ⟨rfl, fun _ _ _ _ => rfl, 0, S, pA, pB, Nat.zero_add S, by simp, by simp, hMatchR, hMatchA, hMatchB⟩
  obtain ⟨e, finalTapes, finalInHead, hLoop, hIh, hOth, hFR, hFA, hFB⟩ :=
    TMComponent.loop_reachesExit (writeRulerScaledOnesBody InputAlphabet scale) input bound
      Inv (fun tapes _ => S + 1 - (tapes tRuler).head) Post hStep initTapes inHead hInitInv
  have hEqTapes : finalTapes = fun j => if j = tRuler then finalTapes tRuler
      else if j = tArgA then finalTapes tArgA
      else if j = tArgB then finalTapes tArgB else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1; rfl
    · by_cases h2 : j = tArgA
      · subst h2; simp [h1]
      · by_cases h3 : j = tArgB
        · subst h3; simp [h1, h2]
        · simp [h1, h2, h3, hOth j h1 h2 h3]
  rw [hEqTapes, hIh] at hLoop
  exact ⟨finalTapes tRuler, finalTapes tArgA, finalTapes tArgB, hLoop, hFR, hFA, hFB⟩

/-- Build `1^W` templates on `tArgA` and `tArgB` from `tRuler = 1^S`, restoring
`tRuler`, `tArgA`, and `tArgB` to head `1`. -/
def writeWidthOnes (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ)
    (InputAlphabet : Type*) :=
  (writeConstOnes InputAlphabet (qBits Q + 4)).seq
    ((writeRulerScaledOnes InputAlphabet (1 + k * (1 + gammaBits Γ))).seq
      ((rewindTape InputAlphabet tRuler).seq
        ((rewindTape InputAlphabet tArgA).seq (rewindTape InputAlphabet tArgB))))

theorem configBitWidth_eq_linear (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k S : ℕ) :
    configBitWidth Q Γ k S = (qBits Q + 4) + S * (1 + k * (1 + gammaBits Γ)) := by
  unfold configBitWidth tapeBitWidth
  have h1 : k * (S + S * gammaBits Γ) = S * (k * (1 + gammaBits Γ)) := by
    calc
      k * (S + S * gammaBits Γ) = k * S + k * (S * gammaBits Γ) := Nat.mul_add _ _ _
      _ = S * k + S * (k * gammaBits Γ) := by rw [Nat.mul_comm k S, Nat.mul_left_comm k S]
      _ = S * (k + k * gammaBits Γ) := (Nat.mul_add _ _ _).symm
      _ = S * (k * (1 + gammaBits Γ)) := by rw [Nat.mul_add k 1 (gammaBits Γ), Nat.mul_one]
  have h2 : S + S * (k * (1 + gammaBits Γ)) = S * (1 + k * (1 + gammaBits Γ)) := by
    rw [Nat.mul_add S 1, Nat.mul_one]
  omega

theorem writeWidthOnes_reachesExit (Q Γ : Type*) [Fintype Q] [Fintype Γ] (k : ℕ)
    {InputAlphabet : Type*} {n : ℕ}
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ) (S : ℕ)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tArgA → j ≠ tArgB → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1) :
    ∃ ftR ftA ftB,
      (writeWidthOnes Q Γ k InputAlphabet).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftA
        (.leftMark :: List.replicate (configBitWidth Q Γ k S) (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftB
        (.leftMark :: List.replicate (configBitWidth Q Γ k S) (.bit true) ++ [.endMark]) 1 := by
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  let W := configBitWidth Q Γ k S
  have hW : W = (qBits Q + 4) + S * (1 + k * (1 + gammaBits Γ)) :=
    configBitWidth_eq_linear Q Γ k S
  obtain ⟨a₁, b₁, hConst, hMA₁, hMB₁⟩ := writeConstOnes_reachesExit (qBits Q + 4) input bound
    [.leftMark] [.leftMark] (by simp; omega) (by simp; omega) initTapes inHead
    (fun j h1 h2 => by
      by_cases hR : j = tRuler
      · subst hR; simpa [hMatchR.head_eq] using by omega
      · exact hOtherBounds j hR h1 h2)
    hMatchA hMatchB
  let t₁ := fun j => if j = tArgA then a₁ else if j = tArgB then b₁ else initTapes j
  have hT1R : TapeMatches (t₁ tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 := by
    simpa [t₁, hNeRA, hNeRB] using hMatchR
  obtain ⟨r₂, a₂, b₂, hScaled, hMR₂, hMA₂, hMB₂⟩ := writeRulerScaledOnes_reachesExit
    (1 + k * (1 + gammaBits Γ)) input bound S
    ([.leftMark] ++ List.replicate (qBits Q + 4) (.bit true))
    ([.leftMark] ++ List.replicate (qBits Q + 4) (.bit true))
    hBoundR (by simp; omega) (by simp; omega) t₁ inHead
    (fun j hj1 hj2 hj3 => by simp [t₁, hj2, hj3, hOtherBounds j hj1 hj2 hj3])
    hT1R
    (by
      have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length =
          1 + (qBits Q + 4) := by simp; omega
      rw [hPos]
      simpa [t₁] using hMA₁)
    (by
      have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length =
          1 + (qBits Q + 4) := by simp; omega
      rw [hPos]
      simpa [t₁, hNeAB.symm] using hMB₁)
  let cR := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  let cW := SimSym.leftMark :: List.replicate W (.bit true) ++ [SimSym.endMark]
  have hNoLeftS : ∀ (M : ℕ) i, 1 ≤ i →
      i < (SimSym.leftMark :: List.replicate M (.bit true) ++ [SimSym.endMark]).length →
      (SimSym.leftMark :: List.replicate M (.bit true) ++ [SimSym.endMark])[i]? ≠
        some SimSym.leftMark := by
    intro M i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < M
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = M := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  have hW_A : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true) ++
      List.replicate (S * (1 + k * (1 + gammaBits Γ))) (SimSym.bit true) ++ [SimSym.endMark]) = cW := by
    rw [List.append_assoc [SimSym.leftMark], ← List.replicate_add]
    simp [cW, hW]
  have hMA₂' : TapeMatches a₂ cW (1 + W) := by
    have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length +
        S * (1 + k * (1 + gammaBits Γ)) = 1 + W := by
      simp [hW]; omega
    rw [hW_A, hPos] at hMA₂
    exact hMA₂
  have hMB₂' : TapeMatches b₂ cW (1 + W) := by
    have hPos : ([SimSym.leftMark] ++ List.replicate (qBits Q + 4) (SimSym.bit true)).length +
        S * (1 + k * (1 + gammaBits Γ)) = 1 + W := by
      simp [hW]; omega
    rw [hW_A, hPos] at hMB₂
    exact hMB₂
  let t₂ := fun j => if j = tRuler then r₂ else if j = tArgA then a₂
      else if j = tArgB then b₂ else t₁ j
  obtain ⟨rewR, hRewR, hFR, hRewROth⟩ := rewindTape_reachesExit tRuler input bound cR
    (by simp [cR]) rfl (hNoLeftS S) (by simp [cR]; exact hBoundR) t₂ inHead
    (fun j hj => by
      by_cases h2 : j = tArgA
      · subst h2; simpa [t₂, hj, hMA₂'.head_eq] using by omega
      · by_cases h3 : j = tArgB
        · subst h3; simpa [t₂, hj, h2, hMB₂'.head_eq] using by omega
        · simp [t₂, t₁, hj, h2, h3, hOtherBounds j hj h2 h3])
    (1 + S) (by omega) (by simp [cR]; omega) (by simpa [t₂, cR] using hMR₂)
  obtain ⟨rewA, hRewA, hFA, hRewAOth⟩ := rewindTape_reachesExit tArgA input bound cW
    (by simp [cW]) rfl (hNoLeftS W) (by simp [cW]; exact hBoundA) rewR inHead
    (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hFR.head_eq] using by omega
      · by_cases h3 : j = tArgB
        · subst h3; rw [hRewROth tArgB hNeRB.symm]
          simpa [t₂, hNeRA.symm, hNeRB.symm, hNeAB.symm, hMB₂'.head_eq] using by omega
        · rw [hRewROth j h1]; simp [t₂, t₁, h1, hj, h3, hOtherBounds j h1 hj h3])
    (1 + W) (by omega) (by simp [cW]; omega)
    (by rw [hRewROth tArgA hNeRA.symm]; simpa [t₂, hNeRA.symm] using hMA₂')
  obtain ⟨rewB, hRewB, hFB, hRewBOth⟩ := rewindTape_reachesExit tArgB input bound cW
    (by simp [cW]) rfl (hNoLeftS W) (by simp [cW]; exact hBoundB) rewA inHead
    (fun j hj => by
      by_cases h2 : j = tArgA
      · subst h2; simpa [hFA.head_eq] using by omega
      · by_cases h1 : j = tRuler
        · subst h1; rw [hRewAOth tRuler hNeRA]; simpa [hFR.head_eq] using by omega
        · rw [hRewAOth j h2, hRewROth j h1]
          simp [t₂, t₁, h1, h2, hj, hOtherBounds j h1 h2 hj])
    (1 + W) (by omega) (by simp [cW]; omega)
    (by
      rw [hRewAOth tArgB hNeAB.symm, hRewROth tArgB hNeRB.symm]
      simpa [t₂, hNeRA, hNeRB.symm, hNeAB.symm] using hMB₂')
  have hSeqAB := (rewindTape InputAlphabet tArgA).seq_reachesExit (rewindTape InputAlphabet tArgB)
    input bound hRewA hRewB
  have hSeqRAB := (rewindTape InputAlphabet tRuler).seq_reachesExit _ input bound hRewR hSeqAB
  have hSeqScaled := (writeRulerScaledOnes InputAlphabet (1 + k * (1 + gammaBits Γ))).seq_reachesExit
    _ input bound hScaled hSeqRAB
  have hSeqFull := (writeConstOnes InputAlphabet (qBits Q + 4)).seq_reachesExit
    _ input bound hConst hSeqScaled
  have hFinalEq : rewB = fun j => if j = tRuler then rewR tRuler
      else if j = tArgA then rewA tArgA
      else if j = tArgB then rewB tArgB else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1
      rw [hRewBOth tRuler hNeRB, hRewAOth tRuler hNeRA]
      simp
    · by_cases h2 : j = tArgA
      · subst h2
        rw [hRewBOth tArgA hNeAB]
        simp [h1]
      · by_cases h3 : j = tArgB
        · subst h3; simp [h1, h2]
        · rw [hRewBOth j h3, hRewAOth j h2, hRewROth j h1]
          simp [t₂, t₁, h1, h2, h3]
  rw [hFinalEq] at hSeqFull
  exact ⟨rewR tRuler, rewA tArgA, rewB tArgB, hSeqFull, hFR, hFA, hFB⟩

/-- Append a fixed `List Bool` onto tape `t`, moving right after each bit. -/
def writeFixedBits (InputAlphabet : Type*) (t : Fin 5) (bits : List Bool) :
    TMComponent (Fin (bits.length + 1)) InputAlphabet SimSym 5 Unit where
  start := ⟨0, Nat.zero_lt_succ bits.length⟩
  step idx _ scanned :=
    if h : idx.val < bits.length then
      mkWorkAction (.inl ⟨idx.val + 1, by omega⟩)
        (fun j => if j = t then .bit bits[idx.val] else scanned j)
        (fun j => if j = t then .right else .stay)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem writeFixedBits_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5) (bits : List Bool)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref : List SimSym) (hBound : pref.length + bits.length < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) pref pref.length) :
    ∃ ft,
      (writeFixedBits InputAlphabet t bits).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ bits.map SimSym.bit) (pref.length + bits.length) := by
  have hStep : ∀ suf, ∀ (done : ℕ) (hSum : done + suf.length = bits.length)
      (hDrop : bits.drop done = suf) (p : List SimSym) (tp : OneSidedTape SimSym),
      TapeMatches tp p p.length →
      p.length + suf.length < bound t →
      ∃ ft,
        Relation.ReflTransGen
          (fun a b => (writeFixedBits InputAlphabet t bits).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl ⟨done, by omega⟩, inHead, fun j => if j = t then tp else initTapes j⟩
          ⟨.inr (), inHead, fun j => if j = t then ft else initTapes j⟩ ∧
        TapeMatches ft (p ++ suf.map SimSym.bit) (p.length + suf.length) := by
    intro suf
    induction suf with
    | nil =>
      intro done hSum _ p tp htp hB
      have hDone : done = bits.length := by simp at hSum; omega
      have hHeads : ∀ j, (if j = t then tp else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [htp.head_eq] using hB
        · simp [hj, hOtherBounds j hj]
      obtain ⟨ft, hUpdT, hFT⟩ := htp.update_keep .stay rfl
      have hNotLt : ¬ done < bits.length := by omega
      have hUpd : ∀ j,
          (if j = t then tp else initTapes j).updateAndMove
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).write j)
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).workMove j) =
            some (if j = t then ft else initTapes j) := by
        intro j
        simp only [writeFixedBits, mkWorkAction, hNotLt, ↓reduceDIte]
        by_cases hj : j = t
        · subst hj; simpa using hUpdT
        · simp only [hj, ↓reduceIte]; exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [hFT.head_eq] using hB
        · simp [hj, hOtherBounds j hj]
      refine ⟨ft, compStep_exit_override (writeFixedBits InputAlphabet t bits) input bound
        _ _ inHead () ⟨done, by omega⟩ hHeads hNextH
        (by simp [writeFixedBits, mkWorkAction, moveHead, hNotLt]) hUpd
        (by simp [writeFixedBits, mkWorkAction, hNotLt]), by simpa using hFT⟩
    | cons b bs ih =>
      intro done hSum hDrop p tp htp hB
      have hLt : done < bits.length := by simp at hSum; omega
      have hBitEq : bits[done] = b := by
        have hGet := congrArg (fun l : List Bool => l[0]?) hDrop
        rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hLt] at hGet
        exact Option.some.inj hGet
      have hDrop' : bits.drop (done + 1) = bs := by
        rw [← List.tail_drop, hDrop]
        rfl
      have hHeads : ∀ j, (if j = t then tp else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [htp.head_eq] using by simp at hB ⊢; omega
        · simp [hj, hOtherBounds j hj]
      obtain ⟨nt, hUpdT, hNT⟩ := htp.update_append (.bit b)
      have hUpd : ∀ j,
          (if j = t then tp else initTapes j).updateAndMove
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).write j)
            (((writeFixedBits InputAlphabet t bits).step ⟨done, by omega⟩
              (readInput input inHead)
              (fun j => (if j = t then tp else initTapes j).cells
                (if j = t then tp else initTapes j).head)).workMove j) =
            some (if j = t then nt else initTapes j) := by
        intro j
        simp only [writeFixedBits, mkWorkAction, hLt, ↓reduceDIte, hBitEq]
        by_cases hj : j = t
        · subst hj; simpa using hUpdT
        · simp only [hj, ↓reduceIte]; exact OneSidedTape.updateAndMove_stay_self _
      have hNextH : ∀ j, (if j = t then nt else initTapes j).head < bound j := by
        intro j; by_cases hj : j = t
        · subst hj; simpa [hNT.head_eq] using by simp at hB ⊢; omega
        · simp [hj, hOtherBounds j hj]
      obtain ⟨ft, hRest, hFT⟩ := ih (done + 1) (by simp at hSum ⊢; omega) hDrop'
        (p ++ [.bit b]) nt (by simpa using hNT) (by simp at hB ⊢; omega)
      refine ⟨ft, compStep_head_override (writeFixedBits InputAlphabet t bits) input bound
        _ _ _ inHead inHead () ⟨done, by omega⟩ ⟨done + 1, by omega⟩ hHeads hNextH
        (by simp [writeFixedBits, mkWorkAction, moveHead, hLt]) hUpd
        (by simp [writeFixedBits, mkWorkAction, hLt]) hRest, ?_⟩
      have hPos : p.length + (b :: bs).length =
          (p ++ [SimSym.bit b]).length + bs.length := by
        simp; omega
      rw [hPos]
      simpa [List.append_assoc] using hFT
  have hTapesSelf : (fun j => if j = t then initTapes t else initTapes j) = initTapes := by
    funext j; by_cases hj : j = t <;> simp [hj]
  have hRes := hStep bits 0 (Nat.zero_add bits.length) rfl pref (initTapes t) hMatch hBound
  rw [hTapesSelf] at hRes
  exact hRes

/-- Repeat a `Unit`-exiting component `m` times sequentially. -/
def repeatUnit {Q InputAlphabet : Type*} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit) :
    TMComponent (Fin (m + 1) × Q) InputAlphabet SimSym 5 Unit where
  start := (⟨0, Nat.zero_lt_succ m⟩, M.start)
  step st inSym scanned :=
    if h : st.1.val < m then
      (M.step st.2 inSym scanned).mapState fun
        | .inl q' => .inl (st.1, q')
        | .inr () => .inl (⟨st.1.val + 1, by omega⟩, M.start)
    else
      mkWorkAction (.inr ()) scanned (fun _ => .stay)

theorem repeatUnit_reachesExit {Q InputAlphabet : Type*} {n : ℕ} (m : ℕ)
    (M : TMComponent Q InputAlphabet SimSym 5 Unit)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (Inv : ℕ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop)
    (hStep : ∀ i, i < m → ∀ tapes ih, Inv i tapes ih →
      ∃ tapes' ih',
        M.ReachesExit input bound tapes ih () tapes' ih' ∧ Inv (i + 1) tapes' ih') :
    ∀ tapes ih, Inv 0 tapes ih →
      (∀ t, (tapes t).head < bound t) →
      ∃ tapes' ih',
        (repeatUnit m M).ReachesExit input bound tapes ih () tapes' ih' ∧
        Inv m tapes' ih' := by
  intro tapes ih hInv0 hH0
  have hLift : ∀ (i : ℕ) (hi : i < m), ∀ a b,
      (∃ q₀, a.state = .inl q₀) →
      Relation.ReflTransGen
        (fun x y => M.CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j)) a b →
      Relation.ReflTransGen
        (fun x y => (repeatUnit m M).CompStep input x y ∧
          (∀ j, (x.workTapes j).head < bound j) ∧
          (∀ j, (y.workTapes j).head < bound j))
        ⟨.inl (⟨i, by omega⟩, match a.state with | .inl q => q | .inr () => M.start),
          a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q => .inl (⟨i, by omega⟩, q)
         | .inr () => .inl (⟨i + 1, by omega⟩, M.start),
          b.inputHead, b.workTapes⟩ := by
    intro i hi a b ha hR
    induction hR with
    | refl =>
      rcases ha with ⟨q₀, hq₀⟩
      simp [hq₀]
      exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ihR =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail (by simpa [hState] using ihR) ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (⟨i, by omega⟩, q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig (Fin (m + 1) × Q ⊕ Unit) SimSym 5 n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(⟨i, by omega⟩, q), by simp, ?_, ihC, ?_, hInC, ?_⟩
      · simp only [repeatUnit, hi, ↓reduceDIte, TMAction.mapState, hScanned, hNext]
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hInM
      · simpa [repeatUnit, hi, TMAction.mapState, hScanned] using hTps
  have hLoop : ∀ rem i (hi : i + rem = m) tps ihC,
      Inv i tps ihC → (∀ j, (tps j).head < bound j) →
      ∃ tps' ih',
        Relation.ReflTransGen
          (fun x y => (repeatUnit m M).CompStep input x y ∧
            (∀ j, (x.workTapes j).head < bound j) ∧
            (∀ j, (y.workTapes j).head < bound j))
          ⟨.inl (⟨i, by omega⟩, M.start), ihC, tps⟩
          ⟨.inr (), ih', tps'⟩ ∧
        Inv m tps' ih' := by
    intro rem
    induction rem with
    | zero =>
      intro i hi tps ihC hInvI hHI
      have hEqM : i = m := by omega
      subst i
      refine ⟨tps, ihC, Relation.ReflTransGen.single ⟨?_, hHI, hHI⟩, hInvI⟩
      refine ⟨(⟨m, Nat.lt_succ_self m⟩, M.start), rfl, ?_, ihC, ?_, rfl, ?_⟩
      · simp [repeatUnit, mkWorkAction]
      · simp [repeatUnit, mkWorkAction, moveHead]
      · intro j
        simp only [repeatUnit, Nat.lt_irrefl, ↓reduceDIte, mkWorkAction]
        exact OneSidedTape.updateAndMove_stay_self _
    | succ r ihR =>
      intro i hi tps ihC hInvI hHI
      obtain ⟨tpsMid, ihMid, hRunM, hInvMid⟩ := hStep i (by omega) tps ihC hInvI
      have hLifted := hLift i (by omega) _ _ ⟨M.start, rfl⟩ hRunM
      have hHMid : ∀ j, (tpsMid j).head < bound j := by
        cases hRunM with
        | tail _ hLast => exact hLast.2.2
      obtain ⟨tpsEnd, ihEnd, hRest, hInvEnd⟩ := ihR (i + 1) (by omega) tpsMid ihMid hInvMid hHMid
      exact ⟨tpsEnd, ihEnd, hLifted.trans hRest, hInvEnd⟩
  exact hLoop m 0 (Nat.zero_add m) tapes ih hInv0 hH0

/-- Check whether `tRuler` currently scans `.bit true`, leaving all tapes stationary. -/
def rulerCheckRegs (InputAlphabet : Type*) :
    TMComponent Unit InputAlphabet SimSym 5 Bool :=
  TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5) (Exit := Bool)
    (fun _ scanned =>
      match scanned tRuler with
      | .bit true => mkWorkAction true scanned (fun _ => .stay)
      | _ => mkWorkAction false scanned (fun _ => .stay))

/-- Loop body appending `bits` onto `tRegs` once per `.bit true` on `tRuler`. -/
def writeRulerListRegsBody (InputAlphabet : Type*) (bits : List Bool) :=
  (rulerCheckRegs InputAlphabet).branch
    (((writeFixedBits InputAlphabet tRegs bits).seq (stepRightAtom InputAlphabet tRuler)).mapExit
      (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit)))
    (TMComponent.atom (InputAlphabet := InputAlphabet) (Γ := SimSym) (k := 5)
      (Exit := Unit ⊕ Unit)
      (fun _ scanned => mkWorkAction (.inr ()) scanned (fun _ => .stay)))

/-- Append `(List.replicate S bits).flatten` onto `tRegs` and rewind `tRuler` to cell `1`. -/
def writeRulerListRegs (InputAlphabet : Type*) (bits : List Bool) :=
  (writeRulerListRegsBody InputAlphabet bits).loop.seq (rewindTape InputAlphabet tRuler)

theorem list_flatMap_finRange_const {α : Type*} (S : ℕ) (xs : List α) :
    (List.finRange S).flatMap (fun _ => xs) = (List.replicate S xs).flatten := by
  induction S with
  | zero => simp
  | succ S ih =>
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      List.replicate_succ, List.flatten_cons]
    congr 1

theorem writeRulerListRegs_reachesExit {InputAlphabet : Type*} {n : ℕ} (bits : List Bool)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pref : List SimSym)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : pref.length + S * bits.length < bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tRegs → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs) pref pref.length) :
    ∃ ftR ftReg,
      (writeRulerListRegs InputAlphabet bits).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg (pref ++ ((List.replicate S bits).flatten).map SimSym.bit)
        (pref.length + S * bits.length) := by
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hNeRR : tRuler ≠ tRegs := by decide
  let Inv : (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    ∃ done rem cur,
      done + rem = S ∧
      cur = pref ++ ((List.replicate done bits).flatten).map SimSym.bit ∧
      TapeMatches (tapes tRuler) rC (1 + done) ∧
      TapeMatches (tapes tRegs) cur cur.length
  let Post : Unit → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun _ tapes ih =>
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) rC (1 + S) ∧
    TapeMatches (tapes tRegs) (pref ++ ((List.replicate S bits).flatten).map SimSym.bit)
      (pref.length + S * bits.length)
  have hStep : ∀ tapes ih, Inv tapes ih →
      (∃ tapes' ih',
        (writeRulerListRegsBody InputAlphabet bits).ReachesExit input bound tapes ih
          (.inl ()) tapes' ih' ∧
        Inv tapes' ih' ∧
        (S + 1 - (tapes' tRuler).head) < (S + 1 - (tapes tRuler).head)) ∨
      (∃ e : Unit, ∃ tapes' ih',
        (writeRulerListRegsBody InputAlphabet bits).ReachesExit input bound tapes ih
          (.inr e) tapes' ih' ∧
        Post e tapes' ih') := by
    intro tapes ih ⟨hIh, hOth, done, rem, cur, hSum, hCur, htR, htReg⟩
    subst ih
    have hFlattenLen : ((List.replicate done bits).flatten).length = done * bits.length := by
      induction done with
      | zero => simp
      | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
    have hCurLen : cur.length = pref.length + done * bits.length := by
      simp [hCur]
    have hMulLe : done * bits.length + rem * bits.length = S * bits.length := by
      rw [← Nat.add_mul, hSum]
    have hHeads : ∀ j, (tapes j).head < bound j := by
      intro j
      by_cases h1 : j = tRuler
      · subst h1; simpa [htR.head_eq] using by omega
      · by_cases h2 : j = tRegs
        · subst h2; simpa [htReg.head_eq, hCurLen] using by omega
        · rw [hOth j h1 h2]; exact hOtherBounds j h1 h2
    cases rem with
    | zero =>
      have hDone : done = S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = S + 1 := by omega
        simp [rC, hIdx]
      have hChk : (rulerCheckRegs InputAlphabet).ReachesExit input bound tapes inHead
          false tapes inHead := by
        refine compStep_exit_override (rulerCheckRegs InputAlphabet) input bound tapes tapes
          inHead false () hHeads hHeads
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hExit := TMComponent.atom_reachesExit
        (fun (_ : InputSymbol InputAlphabet) (scanned : Fin 5 → SimSym) =>
          mkWorkAction (Sum.inr () : Unit ⊕ Unit) scanned (fun _ => .stay))
        input bound tapes inHead hHeads inHead (by simp [mkWorkAction, moveHead]) tapes
        (fun j => by simp only [mkWorkAction]; exact OneSidedTape.updateAndMove_stay_self _)
        hHeads
      refine Or.inr ⟨(), tapes, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound false hChk (by simpa [mkWorkAction] using hExit),
        rfl, hOth, by simpa [hDone] using htR, ?_⟩
      simpa [hCur, hCurLen, hDone] using htReg
    | succ r =>
      have hDoneLt : done < S := by omega
      have hReadR : (tapes tRuler).cells (tapes tRuler).head = .bit true := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdx : 1 + done = done + 1 := Nat.add_comm 1 done
        simp only [rC, hIdx, List.cons_append, List.getElem_cons_succ]
        rw [List.getElem_append_left (by simp; exact hDoneLt)]
        simp
      have hChk : (rulerCheckRegs InputAlphabet).ReachesExit input bound tapes inHead
          true tapes inHead := by
        refine compStep_exit_override (rulerCheckRegs InputAlphabet) input bound tapes tapes
          inHead true () hHeads hHeads
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction, moveHead])
          (fun j => by
            simp only [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction]
            exact OneSidedTape.updateAndMove_stay_self _)
          (by simp [rulerCheckRegs, TMComponent.atom, TMAction.mapState, hReadR, mkWorkAction])
      have hBitsBound : cur.length + bits.length < bound tRegs := by
        have : 1 * bits.length ≤ (r + 1) * bits.length := Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨ftReg', hWrite, hFTReg'⟩ := writeFixedBits_reachesExit tRegs bits input bound cur
        hBitsBound tapes inHead (fun j hj => hHeads j) htReg
      let midT := fun j => if j = tRegs then ftReg' else tapes j
      have hMidR : TapeMatches (midT tRuler) rC (1 + done) := by
        simpa [midT, hNeRR] using htR
      obtain ⟨ftR', hStepR, hFR'⟩ := stepRightAtom_reachesExit tRuler input bound rC (1 + done)
        (by omega) midT inHead (fun j hj => by
          by_cases h2 : j = tRegs
          · subst h2; simpa [midT, hFTReg'.head_eq, hCurLen] using by omega
          · simpa [midT, h2] using hHeads j)
        hMidR
      have hSeq := TMComponent.mapExit_reachesExit _ (fun (_ : Unit) => (Sum.inl () : Unit ⊕ Unit))
        input bound ((writeFixedBits InputAlphabet tRegs bits).seq_reachesExit
          (stepRightAtom InputAlphabet tRuler) input bound hWrite hStepR)
      let finalT := fun j => if j = tRuler then ftR' else midT j
      refine Or.inl ⟨finalT, inHead,
        TMComponent.branch_reachesExit _ _ _ input bound true hChk hSeq, ?_, ?_⟩
      · refine ⟨rfl, fun j hj1 hj2 => by simp [finalT, midT, hj1, hj2, hOth j hj1 hj2],
          done + 1, r, cur ++ bits.map SimSym.bit, by omega, ?_, ?_, ?_⟩
        · rw [hCur, List.append_assoc, List.replicate_succ', List.flatten_concat, List.map_append]
        · have : 1 + done + 1 = 1 + (done + 1) := by omega
          rw [← this]; simpa [finalT] using hFR'
        · simpa [finalT, midT, hNeRR.symm] using hFTReg'
      · simp [finalT, hFR'.head_eq, htR.head_eq]
        omega
  obtain ⟨_, midTapes, midInHead, hLoop, hIh, hOth, hFR, hFReg⟩ :=
    TMComponent.loop_reachesExit (writeRulerListRegsBody InputAlphabet bits) input bound
      Inv (fun tapes _ => S + 1 - (tapes tRuler).head) Post hStep initTapes inHead
      ⟨rfl, fun _ _ _ => rfl, 0, S, pref, Nat.zero_add S, by simp, hMatchR, hMatchReg⟩
  subst midInHead
  have hNoLeft : ∀ i, 1 ≤ i → i < rC.length → rC[i]? ≠ some SimSym.leftMark := by
    intro i hi1 hiLt
    cases i with
    | zero => omega
    | succ i' =>
      simp only [rC, List.length_cons, List.length_append, List.length_replicate,
        List.length_nil] at hiLt
      rw [List.getElem?_eq_getElem (by simp [rC]; omega)]
      simp only [rC, List.cons_append, List.getElem_cons_succ]
      by_cases hi : i' < S
      · rw [List.getElem_append_left (by simp [hi])]; simp
      · have hiEq : i' = S := by omega
        rw [List.getElem_append_right (by simp [hiEq])]; simp [hiEq]
  obtain ⟨rewTapes, hRew, hFRewR, hRewOth⟩ := rewindTape_reachesExit tRuler input bound rC
    (by simp [rC]) rfl hNoLeft (by simp [rC]; exact hBoundR) midTapes inHead
    (fun j hj => by
      by_cases h2 : j = tRegs
      · subst h2; simpa [hFReg.head_eq] using by omega
      · rw [hOth j hj h2]; exact hOtherBounds j hj h2)
    (1 + S) (by omega) (by simp [rC]; omega) hFR
  have hFinalEq : rewTapes = fun j => if j = tRuler then rewTapes tRuler
      else if j = tRegs then midTapes tRegs else initTapes j := by
    funext j
    by_cases h1 : j = tRuler
    · subst h1; rfl
    · by_cases h2 : j = tRegs
      · subst h2; rw [hRewOth tRegs hNeRR.symm]; simp [h1]
      · rw [hRewOth j h1, hOth j h1 h2]; simp [h1, h2]
  have hSeq := (writeRulerListRegsBody InputAlphabet bits).loop.seq_reachesExit
    (rewindTape InputAlphabet tRuler) input bound hLoop hRew
  rw [hFinalEq] at hSeq
  exact ⟨rewTapes tRuler, midTapes tRegs, hSeq, hFRewR, hFReg⟩

/-- Append `.endMark` onto tape `t` without moving its head. -/
def writeEndMarkStayAtom (InputAlphabet : Type*) (t : Fin 5) :
    TMComponent Unit InputAlphabet SimSym 5 Unit where
  start := ()
  step _ _ scanned :=
    mkWorkAction (.inr ()) (fun j => if j = t then .endMark else scanned j) (fun _ => .stay)

theorem writeEndMarkStayAtom_reachesExit {InputAlphabet : Type*} {n : ℕ} (t : Fin 5)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (pref : List SimSym) (hBound : pref.length < bound t)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ t → (initTapes j).head < bound j)
    (hMatch : TapeMatches (initTapes t) pref pref.length) :
    ∃ ft,
      (writeEndMarkStayAtom InputAlphabet t).ReachesExit input bound initTapes inHead ()
        (fun j => if j = t then ft else initTapes j) inHead ∧
      TapeMatches ft (pref ++ [.endMark]) pref.length := by
  have hHeads : ∀ j, (initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hMatch.head_eq] using hBound
    · exact hOtherBounds j hj
  obtain ⟨ft, hUpdT, hFT⟩ := hMatch.update_append_move rfl .endMark .stay rfl
  have hUpd : ∀ j,
      (initTapes j).updateAndMove
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).write j)
        (((writeEndMarkStayAtom InputAlphabet t).step () (readInput input inHead)
          (fun j => (initTapes j).cells (initTapes j).head)).workMove j) =
        some (if j = t then ft else initTapes j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simpa [writeEndMarkStayAtom, mkWorkAction] using hUpdT
    · simp only [writeEndMarkStayAtom, mkWorkAction, hj, ↓reduceIte]
      exact OneSidedTape.updateAndMove_stay_self _
  have hNextH : ∀ j, (if j = t then ft else initTapes j).head < bound j := by
    intro j; by_cases hj : j = t
    · subst hj; simpa [hFT.head_eq] using hBound
    · simp [hj, hOtherBounds j hj]
  exact ⟨ft, compStep_exit_override (writeEndMarkStayAtom InputAlphabet t) input bound initTapes _
    inHead () () hHeads hNextH (by simp [writeEndMarkStayAtom, mkWorkAction, moveHead]) hUpd rfl, hFT⟩

/-- Write `encodeConfigBits Q Γ (M.initialConfig S hS)` and `[.endMark]` onto `tRegs`,
then rewind `tRegs` to cell `1`. -/
noncomputable def writeInitialSrcBits {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  let startQBits := natToBits (qBits Q) (Fintype.equivFin Q M.startState).val
  let blankSymBits := natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val
  let oneTapeInit :=
    (writeRulerListRegs InputAlphabet [false]).seq (writeRulerListRegs InputAlphabet blankSymBits)
  (writeFixedBits InputAlphabet tRegs startQBits).seq
    ((writeFixedBits InputAlphabet tRegs [false, false]).seq
      ((writeRulerListRegs InputAlphabet [false]).seq
        ((repeatUnit k oneTapeInit).seq
          ((writeFixedBits InputAlphabet tRegs [true, false]).seq
            ((writeEndMarkStayAtom InputAlphabet tRegs).seq (rewindTape InputAlphabet tRegs))))))

/-- Full D0 initialization component: prepares `1^W` templates on `tArgA`/`tArgB`,
builds all `W + 1` working registers initialized to `(false, 1)`, writes the encoded
initial configuration into the `source` register, and leaves `tRegs` at head `1`. -/
noncomputable def initSavitchTapes {Q InputAlphabet Γ : Type*} {k : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) :=
  (writeWidthOnes Q Γ k InputAlphabet).seq
    ((initWorkRegsFromTemplate InputAlphabet).seq (writeInitialSrcBits M))

theorem encodeConfigBits_initialConfig {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k) (S : ℕ) (hS : 0 < S) :
    encodeConfigBits Q Γ (M.initialConfig (n := n) S hS) =
      natToBits (qBits Q) (Fintype.equivFin Q M.startState).val ++
      ([false, false] ++ (List.replicate S [false]).flatten) ++
      ((List.replicate k ((List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten)).flatten) ++
      [true, false] := by
  unfold encodeConfigBits MultitapeNTM.initialConfig
  dsimp only
  have hIn : natToBits (S + 2) 0 = [false, false] ++ (List.replicate S [false]).flatten := by
    have hRepF : (List.replicate S [false]).flatten = List.replicate S false := by
      induction S with
      | zero => rfl
      | succ s _ => simp [List.replicate_succ]
    rw [natToBits_zero, hRepF, Nat.add_comm S 2, List.replicate_add]
    rfl
  have hTape : encodeTapeBits Γ
      (⟨fun _ => M.blank, ⟨0, hS⟩⟩ : BoundedTape Γ S) =
      (List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten := by
    unfold encodeTapeBits
    dsimp only
    have hRepF : (List.replicate S [false]).flatten = List.replicate S false := by
      induction S with
      | zero => rfl
      | succ s _ => simp [List.replicate_succ]
    rw [natToBits_zero, ← hRepF, list_flatMap_finRange_const]
  have hTapes : (List.finRange k).flatMap
      (fun _ : Fin k => encodeTapeBits Γ (⟨fun _ => M.blank, ⟨0, hS⟩⟩ : BoundedTape Γ S)) =
      (List.replicate k ((List.replicate S [false]).flatten ++
        (List.replicate S (natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val)).flatten)).flatten := by
    rw [list_flatMap_finRange_const]
    simp [hTape]
  rw [hIn, hTapes]

theorem writeInitialSrcBits_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (work : List (Bool × List Bool))
    (hWork : ∀ r ∈ work, r.2.length = configBitWidth Q Γ k S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : 1 + work.length * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOtherBounds : ∀ j, j ≠ tRuler → j ≠ tRegs → (initTapes j).head < bound j)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs)
      (encodeRegsPrefix work ++ [.srcSep, .tag true])
      (1 + work.length * (configBitWidth Q Γ k S + 2) + 2)) :
    ∃ ftR ftReg,
      (writeInitialSrcBits M).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg
        (encodeRegsTape work (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)))) 1 := by
  have hNeRR : tRuler ≠ tRegs := by decide
  let W := configBitWidth Q Γ k S
  let srcPref := encodeRegsPrefix work ++ [SimSym.srcSep, SimSym.tag true]
  have hPL : (encodeRegsPrefix work).length = 1 + work.length * (W + 2) :=
    encodeRegsPrefix_length W work hWork
  have hSrcPrefLen : srcPref.length = 1 + work.length * (W + 2) + 2 := by
    simp [srcPref, hPL]
  have hWVal : W = qBits Q + (S + 2) + k * (S + S * gammaBits Γ) + 2 := rfl
  have hBoundReg' :
      1 + work.length * (W + 2) + (qBits Q + (S + 2) + k * (S + S * gammaBits Γ) + 5) ≤
        bound tRegs := by
    simpa [W, configBitWidth, tapeBitWidth] using hBoundReg
  let startQBits := natToBits (qBits Q) (Fintype.equivFin Q M.startState).val
  let blankSymBits := natToBits (gammaBits Γ) (Fintype.equivFin Γ M.blank).val
  have hQBLen : startQBits.length = qBits Q := natToBits_length _ _
  have hBBLen : blankSymBits.length = gammaBits Γ := natToBits_length _ _
  have hMReg' : TapeMatches (initTapes tRegs) srcPref srcPref.length := by
    rw [hSrcPrefLen]; exact hMatchReg
  obtain ⟨rg₁, hStep1, hMG₁⟩ := writeFixedBits_reachesExit tRegs startQBits input bound srcPref
    (by rw [hSrcPrefLen, hQBLen]; omega)
    initTapes inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hMatchR.head_eq] using by omega
      · exact hOtherBounds j h1 hj)
    hMReg'
  let t₁ := fun j => if j = tRegs then rg₁ else initTapes j
  let p₁ := srcPref ++ startQBits.map SimSym.bit
  have hP1Len : p₁.length = 1 + work.length * (W + 2) + 2 + qBits Q := by
    simp [p₁, hSrcPrefLen, hQBLen]
  obtain ⟨rg₂, hStep2, hMG₂⟩ := writeFixedBits_reachesExit tRegs [false, false] input bound p₁
    (by rw [hP1Len]; simp; omega)
    t₁ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₁, hNeRR, hMatchR.head_eq] using by omega
      · simpa [t₁, hj] using hOtherBounds j h1 hj)
    (by rw [hP1Len]; simpa [t₁, p₁, hSrcPrefLen, hQBLen, Nat.add_assoc] using hMG₁)
  let t₂ := fun j => if j = tRegs then rg₂ else t₁ j
  let p₂ := p₁ ++ ([false, false] : List Bool).map SimSym.bit
  have hP2Len : p₂.length = 1 + work.length * (W + 2) + 2 + qBits Q + 2 := by
    simp [p₂, hP1Len]
  obtain ⟨ru₃, rg₃, hStep3, hMR₃, hMG₃⟩ := writeRulerListRegs_reachesExit [false] input bound S p₂
    hBoundR (by rw [hP2Len]; simp; omega)
    t₂ inHead (fun j hj1 hj2 => by
      simp [t₂, t₁, hj2, hOtherBounds j hj1 hj2])
    (by simpa [t₂, t₁, hNeRR] using hMatchR)
    (by rw [hP2Len]; simpa [t₂, p₂, hP1Len] using hMG₂)
  let t₃ := fun j => if j = tRuler then ru₃ else if j = tRegs then rg₃ else t₂ j
  let p₃ := p₂ ++ ((List.replicate S ([false] : List Bool)).flatten).map SimSym.bit
  have hRepF1 : ((List.replicate S ([false] : List Bool)).flatten).length = S := by
    induction S with
    | zero => simp
    | succ s _ => simp [List.replicate_succ]
  have hP3Len : p₃.length = 1 + work.length * (W + 2) + 2 + qBits Q + (S + 2) := by
    simp [p₃, hP2Len]
    omega
  let oneTapeInit :=
    (writeRulerListRegs InputAlphabet [false]).seq (writeRulerListRegs InputAlphabet blankSymBits)
  let oneTapeBits : List Bool :=
    (List.replicate S [false]).flatten ++ (List.replicate S blankSymBits).flatten
  have hOneLen : oneTapeBits.length = S + S * gammaBits Γ := by
    have hRepB : ((List.replicate S blankSymBits).flatten).length = S * gammaBits Γ := by
      induction S with
      | zero => simp
      | succ s _ => simp [List.replicate_succ, hBBLen, Nat.succ_mul, Nat.add_comm]
    simp only [oneTapeBits, List.length_append, hRepF1, hRepB]
  let LoopInv : ℕ → (Fin 5 → OneSidedTape SimSym) → Fin (n + 2) → Prop := fun idx tapes ih =>
    idx ≤ k ∧
    ih = inHead ∧
    (∀ j, j ≠ tRuler → j ≠ tRegs → tapes j = initTapes j) ∧
    TapeMatches (tapes tRuler) (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
    TapeMatches (tapes tRegs)
      (p₃ ++ ((List.replicate idx oneTapeBits).flatten).map SimSym.bit)
      (p₃.length + idx * oneTapeBits.length)
  have hLoopStep : ∀ i, i < k → ∀ tapes ih, LoopInv i tapes ih →
      ∃ tapes' ih',
        oneTapeInit.ReachesExit input bound tapes ih () tapes' ih' ∧ LoopInv (i + 1) tapes' ih' := by
    intro i hiK tapes ih ⟨_, hIh, hOth, htR, htReg⟩
    subst ih
    have hFlatOneLen : ((List.replicate i oneTapeBits).flatten).length = i * oneTapeBits.length := by
      induction i with
      | zero => simp
      | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
    let curP := p₃ ++ ((List.replicate i oneTapeBits).flatten).map SimSym.bit
    have hCurPLen : curP.length = p₃.length + i * oneTapeBits.length := by
      simp [curP]
    have hMulLe : (i + 1) * (S + S * gammaBits Γ) ≤ k * (S + S * gammaBits Γ) :=
      Nat.mul_le_mul_right _ hiK
    have hBoundA : curP.length + S * ([false] : List Bool).length < bound tRegs := by
      rw [hCurPLen, hP3Len, hOneLen]
      simp only [List.length_singleton, Nat.mul_one]
      have hSub : i * (S + S * gammaBits Γ) + S ≤ k * (S + S * gammaBits Γ) := by
        rw [Nat.succ_mul] at hMulLe
        omega
      omega
    obtain ⟨ruA, rgA, hRunA, hMR_A, hMG_A⟩ := writeRulerListRegs_reachesExit [false] input bound S
      curP hBoundR hBoundA tapes inHead (fun j h1 h2 => by
        rw [hOth j h1 h2]; exact hOtherBounds j h1 h2)
      htR (by rw [hCurPLen]; exact htReg)
    let mTapes := fun j => if j = tRuler then ruA else if j = tRegs then rgA else tapes j
    let curP2 := curP ++ ((List.replicate S ([false] : List Bool)).flatten).map SimSym.bit
    have hCurP2Len : curP2.length = curP.length + S := by
      simp [curP2]
    have hBoundB : curP2.length + S * blankSymBits.length < bound tRegs := by
      rw [hCurP2Len, hCurPLen, hP3Len, hOneLen, hBBLen]
      have hSub : i * (S + S * gammaBits Γ) + (S + S * gammaBits Γ) ≤ k * (S + S * gammaBits Γ) := by
        rw [← Nat.succ_mul]; exact hMulLe
      omega
    obtain ⟨ruB, rgB, hRunB, hMR_B, hMG_B⟩ := writeRulerListRegs_reachesExit blankSymBits input bound S
      curP2 hBoundR hBoundB mTapes inHead (fun j h1 h2 => by
        simp [mTapes, h1, h2, hOth j h1 h2, hOtherBounds j h1 h2])
      (by simpa [mTapes] using hMR_A)
      (by
        rw [hCurP2Len]
        simpa [mTapes, hNeRR.symm, curP2] using hMG_A)
    let fTapes := fun j => if j = tRuler then ruB else if j = tRegs then rgB else mTapes j
    refine ⟨fTapes, inHead,
      (writeRulerListRegs InputAlphabet [false]).seq_reachesExit
        (writeRulerListRegs InputAlphabet blankSymBits) input bound hRunA hRunB,
      hiK, rfl, fun j h1 h2 => by simp [fTapes, mTapes, h1, h2, hOth j h1 h2],
      by simpa [fTapes] using hMR_B, ?_⟩
    have hLenFinal : p₃.length + (i + 1) * oneTapeBits.length = curP2.length + S * blankSymBits.length := by
      rw [hCurP2Len, hCurPLen, Nat.succ_mul, hOneLen, hBBLen]; omega
    have hTapeFinal :
        curP2 ++ ((List.replicate S blankSymBits).flatten).map SimSym.bit =
          p₃ ++ ((List.replicate (i + 1) oneTapeBits).flatten).map SimSym.bit := by
      simp only [curP2, curP, oneTapeBits, List.replicate_succ', List.flatten_concat,
        List.map_append, List.append_assoc]
    rw [hLenFinal, ← hTapeFinal]
    simpa [fTapes, mTapes, hNeRR.symm] using hMG_B
  have hInitLoop : LoopInv 0 t₃ inHead := by
    refine ⟨Nat.zero_le k, rfl, fun j h1 h2 => by simp [t₃, t₂, t₁, h1, h2],
      by simpa [t₃] using hMR₃, ?_⟩
    have hEqPos : 1 + work.length * (W + 2) + 2 + qBits Q + 2 + S = p₃.length := by
      rw [hP3Len]; omega
    rw [← hEqPos]
    simpa [t₃, hNeRR.symm, p₃, hP2Len, hRepF1] using hMG₃
  obtain ⟨t₄, ih₄, hLoopRun, _, hIh4, hOth4, hMR4, hMG4⟩ :=
    repeatUnit_reachesExit k oneTapeInit input bound LoopInv hLoopStep t₃ inHead hInitLoop
      (fun j => by
        by_cases h1 : j = tRuler
        · subst h1; simpa [t₃, hMR₃.head_eq] using by omega
        · by_cases h2 : j = tRegs
          · subst h2
            simp only [t₃, h1, ↓reduceIte]
            rw [hMG₃.head_eq, hP2Len]
            simp; omega
          · simp [t₃, t₂, t₁, h1, h2, hOtherBounds j h1 h2])
  subst ih₄
  let p₄ := p₃ ++ ((List.replicate k oneTapeBits).flatten).map SimSym.bit
  have hFlatKLen : ((List.replicate k oneTapeBits).flatten).length = k * oneTapeBits.length := by
    induction k with
    | zero => simp
    | succ d _ => simp [List.replicate_succ, Nat.succ_mul, Nat.add_comm]
  have hP4Len : p₄.length = 1 + work.length * (W + 2) + 2 + qBits Q + (S + 2) + k * oneTapeBits.length := by
    simp [p₄, hP3Len]
  obtain ⟨rg₅, hStep5, hMG₅⟩ := writeFixedBits_reachesExit tRegs [true, false] input bound p₄
    (by rw [hP4Len, hOneLen]; simp; omega)
    t₄ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [hMR4.head_eq] using by omega
      · rw [hOth4 j h1 hj]; exact hOtherBounds j h1 hj)
    (by rw [hP4Len]; simpa [p₄, hP3Len] using hMG4)
  let t₅ := fun j => if j = tRegs then rg₅ else t₄ j
  let p₅ := p₄ ++ ([true, false] : List Bool).map SimSym.bit
  have hP5Len : p₅.length = 1 + work.length * (W + 2) + (W + 2) := by
    simp [p₅, hP4Len, hOneLen, hWVal]; omega
  have hP4Add2 : p₄.length + 2 = 1 + work.length * (W + 2) + (W + 2) := by
    rw [hP4Len, hOneLen, hWVal]; omega
  obtain ⟨rg₆, hStep6, hMG₆⟩ := writeEndMarkStayAtom_reachesExit tRegs input bound p₅
    (by rw [hP5Len]; omega) t₅ inHead (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₅, hNeRR, hMR4.head_eq] using by omega
      · simp [t₅, hj, hOth4 j h1 hj, hOtherBounds j h1 hj])
    (by rw [hP5Len, ← hP4Add2]; simpa [t₅, p₅, hP4Len] using hMG₅)
  let t₆ := fun j => if j = tRegs then rg₆ else t₅ j
  let cfgBits := encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega))
  have hFullTape : p₅ ++ [.endMark] = encodeRegsTape work cfgBits := by
    have hCfgMap : List.map SimSym.bit cfgBits =
        List.map SimSym.bit startQBits ++ List.map SimSym.bit [false, false] ++
        List.map SimSym.bit (List.replicate S [false]).flatten ++
        List.map SimSym.bit (List.replicate k oneTapeBits).flatten ++
        List.map SimSym.bit [true, false] := by
      simp only [cfgBits, encodeConfigBits_initialConfig M S (by omega), startQBits,
        blankSymBits, oneTapeBits, List.map_append, List.append_assoc]
    simp only [p₅, p₄, p₃, p₂, p₁, srcPref, encodeRegsTape, encodeSrcEntry, hCfgMap,
      List.append_assoc, List.cons_append, List.nil_append]
  have hMG₆' : TapeMatches (t₆ tRegs) (encodeRegsTape work cfgBits)
      (1 + work.length * (W + 2) + (W + 2)) := by
    simpa [t₆, hFullTape, hP5Len] using hMG₆
  have hCfgLen : cfgBits.length = W := encodeConfigBits_length Q Γ _
  have hFullLen : (encodeRegsTape work cfgBits).length = 1 + work.length * (W + 2) + (W + 3) :=
    encodeRegsTape_length W work cfgBits hWork hCfgLen
  obtain ⟨rewTapes, hStep7, hMG₇, hRewOth⟩ := rewindTape_reachesExit tRegs input bound
    (encodeRegsTape work cfgBits) (by rw [hFullLen]; omega)
    (encodeRegsTape_head_leftMark work cfgBits)
    (encodeRegsTape_no_other_leftMark work cfgBits)
    (by rw [hFullLen]; exact hBoundReg) t₆ inHead
    (fun j hj => by
      by_cases h1 : j = tRuler
      · subst h1; simpa [t₆, t₅, hNeRR, hMR4.head_eq] using by omega
      · simp [t₆, t₅, hj, hOth4 j h1 hj, hOtherBounds j h1 hj])
    (1 + work.length * (W + 2) + (W + 2)) (by omega) (by rw [hFullLen]; omega) hMG₆'
  have hSeq67 := (writeEndMarkStayAtom InputAlphabet tRegs).seq_reachesExit (rewindTape InputAlphabet tRegs)
    input bound hStep6 hStep7
  have hSeq5 := (writeFixedBits InputAlphabet tRegs [true, false]).seq_reachesExit _ input bound hStep5 hSeq67
  have hSeq4 := (repeatUnit k oneTapeInit).seq_reachesExit _ input bound hLoopRun hSeq5
  have hSeq3 := (writeRulerListRegs InputAlphabet [false]).seq_reachesExit _ input bound hStep3 hSeq4
  have hSeq2 := (writeFixedBits InputAlphabet tRegs [false, false]).seq_reachesExit _ input bound hStep2 hSeq3
  have hSeq1 := (writeFixedBits InputAlphabet tRegs startQBits).seq_reachesExit _ input bound hStep1 hSeq2
  have hFinalEq : rewTapes = fun j => if j = tRuler then t₄ tRuler
      else if j = tRegs then rewTapes tRegs else initTapes j := by
    funext j
    by_cases h2 : j = tRegs
    · subst h2; simp [hNeRR.symm]
    · rw [hRewOth j h2]
      by_cases h1 : j = tRuler
      · subst h1; simp [t₆, t₅, h2]
      · simp [t₆, t₅, h1, h2, hOth4 j h1 h2]
  rw [hFinalEq] at hSeq1
  exact ⟨t₄ tRuler, rewTapes tRegs, hSeq1, hMR4, hMG₇⟩

theorem initSavitchTapes_reachesExit {Q InputAlphabet Γ : Type*} {k n : ℕ}
    [Fintype Q] [Fintype InputAlphabet] [Fintype Γ]
    (M : MultitapeNTM Q InputAlphabet Γ k)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (hS : 1 ≤ S)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundReg : 1 + (configBitWidth Q Γ k S + 1) * (configBitWidth Q Γ k S + 2) +
      (configBitWidth Q Γ k S + 3) ≤ bound tRegs)
    (hBoundA : configBitWidth Q Γ k S + 2 ≤ bound tArgA)
    (hBoundB : configBitWidth Q Γ k S + 2 ≤ bound tArgB)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hBoundS : (initTapes tScratch).head < bound tScratch)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchReg : TapeMatches (initTapes tRegs) [.leftMark] 1)
    (hMatchA : TapeMatches (initTapes tArgA) [.leftMark] 1)
    (hMatchB : TapeMatches (initTapes tArgB) [.leftMark] 1) :
    ∃ ftR ftReg ftA ftB,
      (initSavitchTapes M).ReachesExit input bound initTapes inHead ()
        (fun j => if j = tRuler then ftR else if j = tRegs then ftReg
                  else if j = tArgA then ftA else if j = tArgB then ftB
                  else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1 ∧
      TapeMatches ftReg
        (zdRegsContents (configBitWidth Q Γ k S)
          (zdInitial (configBitWidth Q Γ k S + 1) (2 ^ configBitWidth Q Γ k S - 1)
            (configBitWidth_gt_one_pow Q Γ k S)
            (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega))))) 1 ∧
      TapeMatches ftA [.leftMark] 1 ∧
      TapeMatches ftB [.leftMark] 1 := by
  have hNeRR : tRuler ≠ tRegs := by decide
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeRS : tRuler ≠ tScratch := by decide
  have hNeRegA : tRegs ≠ tArgA := by decide
  have hNeRegB : tRegs ≠ tArgB := by decide
  have hNeRegS : tRegs ≠ tScratch := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  have hNeAS : tArgA ≠ tScratch := by decide
  have hNeBS : tArgB ≠ tScratch := by decide
  let W := configBitWidth Q Γ k S
  obtain ⟨r₁, a₁, b₁, hWOnes, hMR₁, hMA₁, hMB₁⟩ := writeWidthOnes_reachesExit Q Γ k input bound S
    hBoundR hBoundA hBoundB initTapes inHead (fun j hj1 hj2 hj3 => by
      by_cases hReg : j = tRegs
      · subst hReg; simpa [hMatchReg.head_eq] using by omega
      · have hjS : j = tScratch := by
          match j with
          | ⟨0, _⟩ => exact (hj1 rfl).elim
          | ⟨1, _⟩ => exact (hReg rfl).elim
          | ⟨2, _⟩ => exact (hj2 rfl).elim
          | ⟨3, _⟩ => exact (hj3 rfl).elim
          | ⟨4, _⟩ => rfl
        subst hjS; exact hBoundS)
    hMatchR hMatchA hMatchB
  let t₁ := fun j => if j = tRuler then r₁ else if j = tArgA then a₁
      else if j = tArgB then b₁ else initTapes j
  have hWGe1 : 1 ≤ W := by
    have := configBitWidth_ge_two Q Γ k S; omega
  obtain ⟨reg₂, a₂, b₂, hInitWork, hMReg₂, hMA₂, hMB₂⟩ := initWorkRegsFromTemplate_reachesExit
    input bound W hWGe1 t₁ inHead (by unfold W; omega) hBoundA hBoundB
    (fun j h1 h2 h3 => by
      by_cases hR : j = tRuler
      · subst hR; simpa [t₁, hMR₁.head_eq] using by omega
      · have hjS : j = tScratch := by
          match j with
          | ⟨0, _⟩ => exact (hR rfl).elim
          | ⟨1, _⟩ => exact (h1 rfl).elim
          | ⟨2, _⟩ => exact (h2 rfl).elim
          | ⟨3, _⟩ => exact (h3 rfl).elim
          | ⟨4, _⟩ => rfl
        subst hjS; simpa [t₁, hNeRS.symm, hNeAS.symm, hNeBS.symm] using hBoundS)
    (by simpa [t₁, hNeRR.symm, hNeRegA, hNeRegB] using hMatchReg)
    (by simpa [t₁, hNeRA.symm] using hMA₁)
    (by simpa [t₁, hNeRB.symm, hNeAB.symm] using hMB₁)
  let t₂ := fun j => if j = tRegs then reg₂ else if j = tArgA then a₂
      else if j = tArgB then b₂ else t₁ j
  let workInit := List.replicate (W + 1) (false, natToBits W 1)
  have hWorkInitLen : ∀ r ∈ workInit, r.2.length = W := by
    intro r hr; rcases List.mem_replicate.mp hr with ⟨_, rfl⟩; simp [natToBits_length]
  have hPLInit : (encodeRegsPrefix workInit).length = 1 + (W + 1) * (W + 2) := by
    simpa [workInit] using encodeRegsPrefix_length W workInit hWorkInitLen
  have hMReg₂' : TapeMatches (t₂ tRegs) (encodeRegsPrefix workInit ++ [.srcSep, .tag true])
      (1 + workInit.length * (W + 2) + 2) := by
    simpa [t₂, workInit, List.length_replicate, hPLInit] using hMReg₂
  obtain ⟨r₃, reg₃, hInitSrc, hMR₃, hMReg₃⟩ := writeInitialSrcBits_reachesExit M input bound S hS
    workInit hWorkInitLen hBoundR (by simpa [workInit] using hBoundReg) t₂ inHead
    (fun j h1 h2 => by
      by_cases hA : j = tArgA
      · subst hA; simpa [t₂, hNeRegA.symm, hMA₂.head_eq] using by omega
      · by_cases hB : j = tArgB
        · subst hB; simpa [t₂, hNeRegB.symm, hNeAB.symm, hMB₂.head_eq] using by omega
        · have hjS : j = tScratch := by
            match j with
            | ⟨0, _⟩ => exact (h1 rfl).elim
            | ⟨1, _⟩ => exact (h2 rfl).elim
            | ⟨2, _⟩ => exact (hA rfl).elim
            | ⟨3, _⟩ => exact (hB rfl).elim
            | ⟨4, _⟩ => rfl
          subst hjS
          simpa [t₂, t₁, hNeRegS.symm, hNeAS.symm, hNeBS.symm, hNeRS.symm] using hBoundS)
    (by simpa [t₂, t₁, hNeRR, hNeRA, hNeRB] using hMR₁)
    hMReg₂'
  have hSeq23 := (initWorkRegsFromTemplate InputAlphabet).seq_reachesExit
    (writeInitialSrcBits M) input bound hInitWork hInitSrc
  have hSeq123 := (writeWidthOnes Q Γ k InputAlphabet).seq_reachesExit _ input bound hWOnes hSeq23
  have hZDInitEq : encodeZDRegs W
      (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) = workInit := by
    apply List.ext_getElem
    · simp [encodeZDRegs, workInit]
    · intro i hi1 hi2
      simp only [encodeZDRegs, List.getElem_ofFn, zdInitial, firstCode, workInit,
        List.getElem_replicate]
      have hNe : i ≠ W + 1 := by simp [workInit] at hi2; omega
      simp [hNe]
  have hZDSrcEq : encodeZDSrc W
      (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) =
      encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)) := by
    simp only [encodeZDSrc, zdInitial, Fin.val_last, ↓reduceIte, bitEncodeConfig]
    have hId := natToBits_bitsToNat (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega)))
    rwa [encodeConfigBits_length] at hId
  have hFullZD : encodeRegsTape workInit (encodeConfigBits Q Γ (M.initialConfig (n := n) S (by omega))) =
      zdRegsContents W (zdInitial (W + 1) (2 ^ W - 1) (configBitWidth_gt_one_pow Q Γ k S)
        (bitEncodeConfig Q Γ (M.initialConfig (n := n) S (by omega)))) := by
    unfold zdRegsContents
    rw [hZDInitEq, hZDSrcEq]
  rw [hFullZD] at hMReg₃
  have hFinalEq : (fun j => if j = tRuler then r₃ else if j = tRegs then reg₃ else t₂ j) =
      fun j => if j = tRuler then r₃ else if j = tRegs then reg₃
        else if j = tArgA then a₂ else if j = tArgB then b₂ else initTapes j := by
    funext j
    match j with
    | ⟨0, _⟩ => simp [tRuler]
    | ⟨1, _⟩ => simp [tRuler, tRegs]
    | ⟨2, _⟩ => simp [tRuler, tRegs, tArgA, t₂, t₁]
    | ⟨3, _⟩ => simp [tRuler, tRegs, tArgA, tArgB, t₂, t₁]
    | ⟨4, _⟩ => simp [tRuler, tRegs, tArgA, tArgB, t₂, t₁]
  rw [hFinalEq] at hSeq123
  exact ⟨r₃, reg₃, a₂, b₂, hSeq123, hMR₃, hMReg₃, hMA₂, hMB₂⟩

/-! ## General monadic bind & stateful loop combinators -/

/-- Bind a component returning `E₁` into a continuation returning `E₂` with fixed
internal state `Q₂`. -/
def bindComponent {Q₁ Q₂ InputAlphabet Γ : Type*} {k : ℕ} {E₁ E₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k E₁)
    (M₂ : E₁ → TMComponent Q₂ InputAlphabet Γ k E₂) :
    TMComponent (Q₁ ⊕ (E₁ × Q₂)) InputAlphabet Γ k E₂ where
  start := .inl M₁.start
  step s inSym workSyms :=
    match s with
    | .inl q₁ =>
      (M₁.step q₁ inSym workSyms).mapState fun
        | .inl q₁' => .inl (.inl q₁')
        | .inr e₁ => .inl (.inr (e₁, (M₂ e₁).start))
    | .inr (e₁, q₂) =>
      ((M₂ e₁).step q₂ inSym workSyms).mapState fun
        | .inl q₂' => .inl (.inr (e₁, q₂'))
        | .inr e₂ => .inr e₂

theorem bindComponent_reachesExit {Q₁ Q₂ InputAlphabet Γ : Type*} {k n : ℕ} {E₁ E₂ : Type*}
    (M₁ : TMComponent Q₁ InputAlphabet Γ k E₁)
    (M₂ : E₁ → TMComponent Q₂ InputAlphabet Γ k E₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    {tapes₀ tapes₁ tapes₂ : Fin k → OneSidedTape Γ} {in₀ in₁ in₂ : Fin (n + 2)}
    {e₁ : E₁} {e₂ : E₂}
    (h₁ : M₁.ReachesExit input bound tapes₀ in₀ e₁ tapes₁ in₁)
    (h₂ : (M₂ e₁).ReachesExit input bound tapes₁ in₁ e₂ tapes₂ in₂) :
    (bindComponent M₁ M₂).ReachesExit input bound tapes₀ in₀ e₂ tapes₂ in₂ := by
  have hLift₁ : ∀ a b : OneSidedTMConfig (Q₁ ⊕ E₁) Γ k n,
      Relation.ReflTransGen
        (fun x y => M₁.CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (bindComponent M₁ M₂).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q₁ => .inl (.inl q₁)
         | .inr e => .inl (.inr (e, (M₂ e).start)), a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q₁ => .inl (.inl q₁)
         | .inr e => .inl (.inr (e, (M₂ e).start)), b.inputHead, b.workTapes⟩ := by
    intro a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (Sum.inl q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inl q, by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, TMAction.mapState, hScanned, hNext]
        cases (M₁.step q (readInput input prev.inputHead) prev.scannedWork).nextState <;> rfl
      · simpa [bindComponent, TMAction.mapState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hScanned] using hTps
  have hLift₂ : ∀ a b : OneSidedTMConfig (Q₂ ⊕ E₂) Γ k n,
      Relation.ReflTransGen
        (fun x y => (M₂ e₁).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (bindComponent M₁ M₂).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q₂ => .inl (.inr (e₁, q₂))
         | .inr e => .inr e, a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q₂ => .inl (.inr (e₁, q₂))
         | .inr e => .inr e, b.inputHead, b.workTapes⟩ := by
    intro a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (Sum.inr (e₁, q)), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((Q₁ ⊕ (E₁ × Q₂)) ⊕ E₂) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨.inr (e₁, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [bindComponent, TMAction.mapState, hScanned, hNext]
        cases ((M₂ e₁).step q (readInput input prev.inputHead) prev.scannedWork).nextState <;> rfl
      · simpa [bindComponent, TMAction.mapState, hScanned] using hInM
      · simpa [bindComponent, TMAction.mapState, hScanned] using hTps
  exact (hLift₁ _ _ h₁).trans (hLift₂ _ _ h₂)

/-- Loop carrying a finite state `State` between iterations. -/
def loopWithState {State Q InputAlphabet Γ : Type*} {k : ℕ} {Exit : Type*}
    (init : State) (body : State → TMComponent Q InputAlphabet Γ k (State ⊕ Exit)) :
    TMComponent (State × Q) InputAlphabet Γ k Exit where
  start := (init, (body init).start)
  step st inSym workSyms :=
    ((body st.1).step st.2 inSym workSyms).mapState fun
      | .inl q' => .inl (st.1, q')
      | .inr (.inl st') => .inl (st', (body st').start)
      | .inr (.inr e) => .inr e

theorem loopWithState_reachesExit {State Q InputAlphabet Γ : Type*} {k n : ℕ} {Exit : Type*}
    (init : State) (body : State → TMComponent Q InputAlphabet Γ k (State ⊕ Exit))
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (Inv : State → (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (measure : State → (Fin k → OneSidedTape Γ) → Fin (n + 2) → ℕ)
    (Post : Exit → (Fin k → OneSidedTape Γ) → Fin (n + 2) → Prop)
    (hStep : ∀ st tapes inHead, Inv st tapes inHead →
      (∃ st' tapes' inHead',
        (body st).ReachesExit input bound tapes inHead (.inl st') tapes' inHead' ∧
        Inv st' tapes' inHead' ∧
        measure st' tapes' inHead' < measure st tapes inHead) ∨
      (∃ e tapes' inHead',
        (body st).ReachesExit input bound tapes inHead (.inr e) tapes' inHead' ∧
        Post e tapes' inHead')) :
    ∀ tapes inHead, Inv init tapes inHead →
      ∃ e tapes' inHead',
        (loopWithState init body).ReachesExit input bound tapes inHead e tapes' inHead' ∧
        Post e tapes' inHead' := by
  have hLift : ∀ st, ∀ a b : OneSidedTMConfig (Q ⊕ (State ⊕ Exit)) Γ k n,
      Relation.ReflTransGen
        (fun x y => (body st).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t)) a b →
      Relation.ReflTransGen
        (fun x y => (loopWithState init body).CompStep input x y ∧
          (∀ t, (x.workTapes t).head < bound t) ∧
          (∀ t, (y.workTapes t).head < bound t))
        ⟨match a.state with
         | .inl q => .inl (st, q)
         | .inr (.inl st') => .inl (st', (body st').start)
         | .inr (.inr e) => .inr e, a.inputHead, a.workTapes⟩
        ⟨match b.state with
         | .inl q => .inl (st, q)
         | .inr (.inl st') => .inl (st', (body st').start)
         | .inr (.inr e) => .inr e, b.inputHead, b.workTapes⟩ := by
    intro st a b hR
    induction hR with
    | refl => exact Relation.ReflTransGen.refl
    | @tail prev curr _ hS ih =>
      rcases hS.1 with ⟨q, hState, hNext, ihC, hInM, hInC, hTps⟩
      refine Relation.ReflTransGen.tail ih ⟨?_, hS.2.1, hS.2.2⟩
      have hScanned :
          ({ state := Sum.inl (st, q), inputHead := prev.inputHead,
             workTapes := prev.workTapes } :
            OneSidedTMConfig ((State × Q) ⊕ Exit) Γ k n).scannedWork =
          prev.scannedWork := rfl
      refine ⟨(st, q), by simp [hState], ?_, ihC, ?_, hInC, ?_⟩
      · simp only [loopWithState, TMAction.mapState, hScanned, hNext]
        cases ((body st).step q (readInput input prev.inputHead) prev.scannedWork).nextState with
        | inl q' => rfl
        | inr e => cases e <;> rfl
      · simpa [loopWithState, TMAction.mapState, hScanned] using hInM
      · simpa [loopWithState, TMAction.mapState, hScanned] using hTps
  intro tapes inHead hInitInv
  have hWF : ∀ m st tapes inHead, measure st tapes inHead = m → Inv st tapes inHead →
      ∃ e tapes' inHead',
        Relation.ReflTransGen
          (fun x y => (loopWithState init body).CompStep input x y ∧
            (∀ t, (x.workTapes t).head < bound t) ∧
            (∀ t, (y.workTapes t).head < bound t))
          ⟨.inl (st, (body st).start), inHead, tapes⟩
          ⟨.inr e, inHead', tapes'⟩ ∧
        Post e tapes' inHead' := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro st tapes inHead hm hInvCur
      rcases hStep st tapes inHead hInvCur with
        ⟨stMid, tapesMid, inMid, hCont, hInvMid, hDec⟩ | ⟨e, tapesEnd, inEnd, hDone, hPost⟩
      · have hLifted := hLift st _ _ hCont
        have hm' : measure stMid tapesMid inMid < m := hm ▸ hDec
        obtain ⟨e, tapesEnd, inEnd, hRest, hPost⟩ :=
          ih (measure stMid tapesMid inMid) hm' stMid tapesMid inMid rfl hInvMid
        exact ⟨e, tapesEnd, inEnd, hLifted.trans hRest, hPost⟩
      · exact ⟨e, tapesEnd, inEnd, hLift st _ _ hDone, hPost⟩
  exact hWF (measure init tapes inHead) init tapes inHead rfl hInitInv

/-! ## Step checker (`checkStep`): comparing `tArgA` and `tArgB` against `bitProblem` -/

def simBitVal : SimSym → Bool
  | .bit b => b
  | _ => false

/-- Copy `2 + S` (when `startIdx = 0`) or `S` (when `startIdx = 2`) bit pairs from
`tArgA`/`tArgB`, writing `tArgA`'s bits + `.endMark` onto `tScratch`, advancing
`tRuler`/`tArgA`/`tArgB`, and computing `BitRelState`. -/
def copyHeadBitsRel (InputAlphabet : Type*) (startIdx : Fin 3) :
    TMComponent (Fin 3 × BitRelState) InputAlphabet SimSym 5 BitRelState where
  start := (startIdx, BitRelState.init)
  step st _ scanned :=
    let bA := simBitVal (scanned tArgA)
    let bB := simBitVal (scanned tArgB)
    let st' := st.2.step bA bB
    match st.1.val with
    | 0 =>
      mkWorkAction (.inl (⟨1, by decide⟩, st'))
        (fun j => if j = tScratch then .bit bA else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
    | 1 =>
      mkWorkAction (.inl (⟨2, by decide⟩, st'))
        (fun j => if j = tScratch then .bit bA else scanned j)
        (fun j => if j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
    | _ =>
      match scanned tRuler with
      | .bit true =>
        mkWorkAction (.inl (⟨2, by decide⟩, st'))
          (fun j => if j = tScratch then .bit bA else scanned j)
          (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay)
      | _ =>
        mkWorkAction (.inr st.2)
          (fun j => if j = tScratch then .endMark else scanned j)
          (fun _ => .stay)

/-- Read `2 + S` (or `S`) head bits into `tScratch` + `BitRelState`, and rewind
`tRuler` and `tScratch` to cell `1`. -/
def readHeadBlock (InputAlphabet : Type*) (startIdx : Fin 3) :=
  bindComponent (copyHeadBitsRel InputAlphabet startIdx) fun rel =>
    ((rewindTape InputAlphabet tRuler).seq (rewindTape InputAlphabet tScratch)).mapExit
      (fun _ => rel)

theorem copyHeadBitsRel_reachesExit {InputAlphabet : Type*} {n : ℕ} (startIdx : Fin 3)
    (hIdx : startIdx.val = 0 ∨ startIdx.val = 2)
    (input : Fin n → InputAlphabet) (bound : Fin 5 → ℕ)
    (S : ℕ) (pA uA sA pB uB sB : List SimSym) (ua ub : List Bool)
    (hUA : ua.length = (if startIdx.val = 0 then 2 else 0) + S)
    (hUB : ub.length = (if startIdx.val = 0 then 2 else 0) + S)
    (hUA_syms : uA = ua.map SimSym.bit) (hUB_syms : uB = ub.map SimSym.bit)
    (hBoundR : S + 2 ≤ bound tRuler)
    (hBoundA : pA.length + ua.length < bound tArgA)
    (hBoundB : pB.length + ub.length < bound tArgB)
    (hBoundS : ua.length + 2 ≤ bound tScratch)
    (initTapes : Fin 5 → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hOther : (initTapes tRegs).head < bound tRegs)
    (hMatchR : TapeMatches (initTapes tRuler)
      (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) 1)
    (hMatchA : TapeMatches (initTapes tArgA) (pA ++ uA ++ sA) pA.length)
    (hMatchB : TapeMatches (initTapes tArgB) (pB ++ uB ++ sB) pB.length)
    (hMatchS : TapeMatches (initTapes tScratch) [.leftMark] 1) :
    ∃ ftR ftA ftB ftS,
      (copyHeadBitsRel InputAlphabet startIdx).ReachesExit input bound initTapes inHead
        (BitRelState.init.runList ua ub)
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS
                  else initTapes j) inHead ∧
      TapeMatches ftR (.leftMark :: List.replicate S (.bit true) ++ [.endMark]) (1 + S) ∧
      TapeMatches ftA (pA ++ uA ++ sA) (pA.length + ua.length) ∧
      TapeMatches ftB (pB ++ uB ++ sB) (pB.length + ub.length) ∧
      TapeMatches ftS (.leftMark :: uA ++ [.endMark]) (1 + ua.length) := by
  have hNeRR : tRuler ≠ tRegs := by decide
  have hNeRA : tRuler ≠ tArgA := by decide
  have hNeRB : tRuler ≠ tArgB := by decide
  have hNeRS : tRuler ≠ tScratch := by decide
  have hNeRegA : tRegs ≠ tArgA := by decide
  have hNeRegB : tRegs ≠ tArgB := by decide
  have hNeRegS : tRegs ≠ tScratch := by decide
  have hNeAB : tArgA ≠ tArgB := by decide
  have hNeAS : tArgA ≠ tScratch := by decide
  have hNeBS : tArgB ≠ tScratch := by decide
  let rC := SimSym.leftMark :: List.replicate S (.bit true) ++ [SimSym.endMark]
  have hRC_len : rC.length = S + 2 := by simp [rC]
  have hScanRuler : ∀ rem done pA' pB' pS' uA' uB' st tR tA tB tS,
      done + rem = S →
      uA'.length = rem → uB'.length = rem →
      pA'.length + rem < bound tArgA →
      pB'.length + rem < bound tArgB →
      pS'.length + rem + 1 < bound tScratch →
      TapeMatches tR rC (1 + done) →
      TapeMatches tA (pA' ++ uA'.map SimSym.bit ++ sA) pA'.length →
      TapeMatches tB (pB' ++ uB'.map SimSym.bit ++ sB) pB'.length →
      TapeMatches tS pS' pS'.length →
      ∃ ftR ftA ftB ftS,
        Relation.ReflTransGen
          (fun a b => (copyHeadBitsRel InputAlphabet startIdx).CompStep input a b ∧
            (∀ j, (a.workTapes j).head < bound j) ∧
            (∀ j, (b.workTapes j).head < bound j))
          ⟨.inl (⟨2, by decide⟩, st), inHead,
            fun j => if j = tRuler then tR else if j = tArgA then tA
                      else if j = tArgB then tB else if j = tScratch then tS
                      else initTapes j⟩
          ⟨.inr (st.runList uA' uB'), inHead,
            fun j => if j = tRuler then ftR else if j = tArgA then ftA
                      else if j = tArgB then ftB else if j = tScratch then ftS
                      else initTapes j⟩ ∧
        TapeMatches ftR rC (1 + S) ∧
        TapeMatches ftA (pA' ++ uA'.map SimSym.bit ++ sA) (pA'.length + rem) ∧
        TapeMatches ftB (pB' ++ uB'.map SimSym.bit ++ sB) (pB'.length + rem) ∧
        TapeMatches ftS (pS' ++ uA'.map SimSym.bit ++ [.endMark]) (pS'.length + rem) := by
    intro rem
    induction rem with
    | zero =>
      intro done pA' pB' pS' uA' uB' st tR tA tB tS hSum hLA hLB hBA hBB hBS htR htA htB htS
      have hDone : done = S := by omega
      have hUA0 : uA' = [] := List.eq_nil_of_length_eq_zero hLA
      have hUB0 : uB' = [] := List.eq_nil_of_length_eq_zero hLB
      subst hUA0 hUB0
      have hReadR : tR.cells tR.head = .endMark := by
        rw [htR.read_lt (by rw [hRC_len]; omega)]
        have hIdxD : 1 + done = S + 1 := by omega
        simp [rC, hIdxD]
      have hHeads : ∀ j,
          (if j = tRuler then tR else if j = tArgA then tA
            else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
            bound j := by
        intro j
        match j with
        | ⟨0, _⟩ => simpa [tRuler, htR.head_eq] using by omega
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using hBA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using hBB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
      obtain ⟨ftS, hUpdS, hFS⟩ := htS.update_append_move rfl .endMark .stay rfl
      let nextT := fun j => if j = tRuler then tR else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then ftS else initTapes j
      have hNextH : ∀ j, (nextT j).head < bound j := by
        intro j
        match j with
        | ⟨0, _⟩ => simpa [nextT, tRuler, htR.head_eq] using by omega
        | ⟨1, _⟩ => simpa [nextT, tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
        | ⟨2, _⟩ => simpa [nextT, tRuler, tArgA, htA.head_eq] using hBA
        | ⟨3, _⟩ => simpa [nextT, tArgA, tArgB, htB.head_eq] using hBB
        | ⟨4, _⟩ => simpa [nextT, tRuler, tArgA, tArgB, tScratch, hFS.head_eq] using by omega
      have hStep1 := compStep_exit_override (copyHeadBitsRel InputAlphabet startIdx) input bound
        (fun j => if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j)
        nextT inHead (st.runList [] []) (⟨2, by decide⟩, st) hHeads hNextH
        (by simp [copyHeadBitsRel, mkWorkAction, moveHead, hReadR])
        (fun j => by
          simp only [copyHeadBitsRel, mkWorkAction, hReadR, nextT]
          match j with
          | ⟨0, _⟩ => simpa [tRuler, tScratch] using OneSidedTape.updateAndMove_stay_self tR
          | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
              OneSidedTape.updateAndMove_stay_self (initTapes 1)
          | ⟨2, _⟩ => simpa [tRuler, tArgA, tScratch] using OneSidedTape.updateAndMove_stay_self tA
          | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using OneSidedTape.updateAndMove_stay_self tB
          | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
        (by simp [copyHeadBitsRel, mkWorkAction, hReadR, BitRelState.runList])
      refine ⟨tR, tA, tB, ftS, by simpa [BitRelState.runList] using hStep1,
        by simpa [hDone] using htR, by simpa using htA, by simpa using htB, by simpa using hFS⟩
    | succ r ih =>
      intro done pA' pB' pS' uA' uB' st tR tA tB tS hSum hLA hLB hBA hBB hBS htR htA htB htS
      cases uA' with
      | nil => simp at hLA
      | cons a usA =>
        cases uB' with
        | nil => simp at hLB
        | cons b usB =>
          simp only [List.length_cons, Nat.succ.injEq] at hLA hLB
          have hDoneLt : done < S := by omega
          have hReadR : tR.cells tR.head = .bit true := by
            rw [htR.read_lt (by rw [hRC_len]; omega)]
            have hIdxD : 1 + done = done + 1 := Nat.add_comm 1 done
            simp only [rC, hIdxD, List.cons_append, List.getElem_cons_succ]
            rw [List.getElem_append_left (by simp; exact hDoneLt)]
            simp
          have hReadA : tA.cells tA.head = .bit a := by
            rw [htA.read_lt (by simp; omega)]
            simp [List.getElem_append_left (by simp : pA'.length < (pA' ++ SimSym.bit a :: (usA.map SimSym.bit ++ sA)).length)]
          have hReadB : tB.cells tB.head = .bit b := by
            rw [htB.read_lt (by simp; omega)]
            simp
          have hHeads : ∀ j,
              (if j = tRuler then tR else if j = tArgA then tA
                else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ => simpa [tRuler, htR.head_eq] using by omega
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using by omega
            | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using by omega
            | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
          obtain ⟨ntR, hUpdR, hNR⟩ := htR.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right (by simp [moveOneSidedHead])
          obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (.bit a)
          have hNextH : ∀ j,
              (if j = tRuler then ntR else if j = tArgA then ntA
                else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
                bound j := by
            intro j
            match j with
            | ⟨0, _⟩ => simpa [tRuler, hNR.head_eq] using by omega
            | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
            | ⟨2, _⟩ => simpa [tRuler, tArgA, hNA.head_eq] using by omega
            | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, hNB.head_eq] using by omega
            | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using by omega
          have hNA' : TapeMatches ntA ((pA' ++ [.bit a]) ++ usA.map SimSym.bit ++ sA) (pA' ++ [.bit a]).length := by
            simpa [List.append_assoc] using hNA
          have hNB' : TapeMatches ntB ((pB' ++ [.bit b]) ++ usB.map SimSym.bit ++ sB) (pB' ++ [.bit b]).length := by
            simpa [List.append_assoc] using hNB
          obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ :=
            ih (done + 1) (pA' ++ [.bit a]) (pB' ++ [.bit b]) (pS' ++ [.bit a]) usA usB
              (st.step a b) ntR ntA ntB ntS (by omega) hLA hLB
              (by simp; omega) (by simp; omega) (by simp; omega) hNR hNA' hNB' (by simpa using hNS)
          have hStepEq :
              (copyHeadBitsRel InputAlphabet startIdx).step (⟨2, by decide⟩, st) (readInput input inHead)
                (fun j => (if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j).cells
                  (if j = tRuler then tR else if j = tArgA then tA
                  else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head) =
              mkWorkAction (.inl (⟨2, by decide⟩, st.step a b))
                (fun j => if j = tScratch then .bit a else
                  (if j = tRuler then tR else if j = tArgA then tA
                    else if j = tArgB then tB else if j = tScratch then tS else initTapes j).cells
                  (if j = tRuler then tR else if j = tArgA then tA
                    else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head)
                (fun j => if j = tRuler ∨ j = tArgA ∨ j = tArgB ∨ j = tScratch then .right else .stay) := by
            simp [copyHeadBitsRel, hReadR, hReadA, hReadB, simBitVal]
          refine ⟨ftR, ftA, ftB, ftS,
            compStep_head_override (copyHeadBitsRel InputAlphabet startIdx) input bound
              _ _ _ inHead inHead (st.runList (a :: usA) (b :: usB))
              (⟨2, by decide⟩, st) (⟨2, by decide⟩, st.step a b) hHeads hNextH
              (by rw [hStepEq]; simp [mkWorkAction, moveHead])
              (fun j => by
                rw [hStepEq]
                simp only [mkWorkAction]
                match j with
                | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdR
                | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
                    OneSidedTape.updateAndMove_stay_self (initTapes 1)
                | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
                | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
                | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS)
              (by rw [hStepEq]; rfl)
              (by simpa [BitRelState.runList] using hRest),
            hFR,
            by simpa [List.append_assoc, Nat.add_assoc] using hFA,
            by simpa [List.append_assoc, Nat.add_assoc] using hFB,
            by simpa [List.append_assoc, Nat.add_assoc] using hFS⟩
  have hStepOne : ∀ (kIdx : ℕ) (hk : kIdx = 0 ∨ kIdx = 1),
      ∀ a b uA' uB' pA' pB' pS' tA tB tS st,
        pA'.length + 1 + uA'.length < bound tArgA →
        pB'.length + 1 + uB'.length < bound tArgB →
        pS'.length + 1 + uA'.length + 1 < bound tScratch →
        TapeMatches tA (pA' ++ (.bit a :: uA'.map SimSym.bit) ++ sA) pA'.length →
        TapeMatches tB (pB' ++ (.bit b :: uB'.map SimSym.bit) ++ sB) pB'.length →
        TapeMatches tS pS' pS'.length →
        (initTapes tRuler).head < bound tRuler →
        ∃ ntA ntB ntS,
          Relation.ReflTransGen
            (fun x y => (copyHeadBitsRel InputAlphabet startIdx).CompStep input x y ∧
              (∀ j, (x.workTapes j).head < bound j) ∧
              (∀ j, (y.workTapes j).head < bound j))
            ⟨.inl (⟨kIdx, by omega⟩, st), inHead,
              fun j => if j = tRuler then initTapes tRuler else if j = tArgA then tA
                        else if j = tArgB then tB else if j = tScratch then tS else initTapes j⟩
            ⟨.inl (⟨kIdx + 1, by omega⟩, st.step a b), inHead,
              fun j => if j = tRuler then initTapes tRuler else if j = tArgA then ntA
                        else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j⟩ ∧
          TapeMatches ntA ((pA' ++ [.bit a]) ++ uA'.map SimSym.bit ++ sA) (pA' ++ [.bit a]).length ∧
          TapeMatches ntB ((pB' ++ [.bit b]) ++ uB'.map SimSym.bit ++ sB) (pB' ++ [.bit b]).length ∧
          TapeMatches ntS (pS' ++ [.bit a]) (pS' ++ [.bit a]).length := by
    intro kIdx hk a b uA' uB' pA' pB' pS' tA tB tS st hBA hBB hBS htA htB htS hTRB
    have hReadA : tA.cells tA.head = .bit a := by
      rw [htA.read_lt (by simp; omega)]
      simp [List.getElem_append_left]
    have hReadB : tB.cells tB.head = .bit b := by
      rw [htB.read_lt (by simp; omega)]
      simp [List.getElem_append_left]
    have hHeads : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then tA
          else if j = tArgB then tB else if j = tScratch then tS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ => simpa [tRuler, tArgA, htA.head_eq] using by omega
      | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, htB.head_eq] using by omega
      | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, htS.head_eq] using by omega
    obtain ⟨ntA, hUpdA, hNA⟩ := htA.update_keep .right (by simp [moveOneSidedHead])
    obtain ⟨ntB, hUpdB, hNB⟩ := htB.update_keep .right (by simp [moveOneSidedHead])
    obtain ⟨ntS, hUpdS, hNS⟩ := htS.update_append (.bit a)
    have hNextH : ∀ j,
        (if j = tRuler then initTapes tRuler else if j = tArgA then ntA
          else if j = tArgB then ntB else if j = tScratch then ntS else initTapes j).head <
          bound j := by
      intro j
      match j with
      | ⟨0, _⟩ => simpa [tRuler] using hTRB
      | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, tRegs] using hOther
      | ⟨2, _⟩ => simpa [tRuler, tArgA, hNA.head_eq] using by omega
      | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, hNB.head_eq] using by omega
      | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch, hNS.head_eq] using by omega
    have hNextFin : (⟨kIdx + 1, by omega⟩ : Fin 3) =
        if kIdx = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩ := by
      rcases hk with rfl | rfl <;> rfl
    refine ⟨ntA, ntB, ntS, Relation.ReflTransGen.single ⟨?_, hHeads, hNextH⟩,
      by simpa [List.append_assoc] using hNA,
      by simpa [List.append_assoc] using hNB,
      by simpa using hNS⟩
    refine ⟨(⟨kIdx, by omega⟩, st), rfl, ?_, inHead, ?_, rfl, ?_⟩
    · rcases hk with rfl | rfl <;>
        simp [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
    · rcases hk with rfl | rfl <;>
        simp [copyHeadBitsRel, mkWorkAction, moveHead]
    · intro j
      rcases hk with rfl | rfl
      · simp only [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
        match j with
        | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes tRuler)
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes 1)
        | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS
      · simp only [copyHeadBitsRel, mkWorkAction, hReadA, hReadB, simBitVal]
        match j with
        | ⟨0, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes tRuler)
        | ⟨1, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using
            OneSidedTape.updateAndMove_stay_self (initTapes 1)
        | ⟨2, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdA
        | ⟨3, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdB
        | ⟨4, _⟩ => simpa [tRuler, tArgA, tArgB, tScratch] using hUpdS
  have hTapesSelf :
      (fun j => if j = tRuler then initTapes tRuler else if j = tArgA then initTapes tArgA
        else if j = tArgB then initTapes tArgB else if j = tScratch then initTapes tScratch
        else initTapes j) = initTapes := by
    funext j; match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
  rcases hIdx with h0 | h2
  · have hStartFin : startIdx = ⟨0, by decide⟩ := Fin.ext h0
    subst startIdx
    simp only [↓reduceIte] at hUA hUB
    rcases ua with _ | ⟨a₀, _ | ⟨a₁, usA⟩⟩ <;> try (simp at hUA; omega)
    rcases ub with _ | ⟨b₀, _ | ⟨b₁, usB⟩⟩ <;> try (simp at hUB; omega)
    simp only [List.length_cons, Nat.succ.injEq] at hUA hUB
    have hTRB : (initTapes tRuler).head < bound tRuler := by simpa [hMatchR.head_eq] using by omega
    obtain ⟨a₂, b₂, s₂, hS0, hMA2, hMB2, hMS2⟩ := hStepOne 0 (Or.inl rfl) a₀ b₀ (a₁ :: usA) (b₁ :: usB)
      pA pB [.leftMark] (initTapes tArgA) (initTapes tArgB) (initTapes tScratch) BitRelState.init
      (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega) (by simp at hBoundS ⊢; omega)
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS hTRB
    obtain ⟨a₃, b₃, s₃, hS1, hMA3, hMB3, hMS3⟩ := hStepOne 1 (Or.inr rfl) a₁ b₁ usA usB
      (pA ++ [.bit a₀]) (pB ++ [.bit b₀]) [.leftMark, .bit a₀] a₂ b₂ s₂ (BitRelState.init.step a₀ b₀)
      (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega) (by simp at hBoundS ⊢; omega)
      hMA2 hMB2 hMS2 hTRB
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0
      (pA ++ [.bit a₀, .bit a₁]) (pB ++ [.bit b₀, .bit b₁]) [.leftMark, .bit a₀, .bit a₁]
      usA usB ((BitRelState.init.step a₀ b₀).step a₁ b₁) (initTapes tRuler) a₃ b₃ s₃
      (Nat.zero_add S) hUA hUB (by simp at hBoundA ⊢; omega) (by simp at hBoundB ⊢; omega)
      (by simp at hBoundS ⊢; omega) hMatchR (by simpa [List.append_assoc] using hMA3)
      (by simpa [List.append_assoc] using hMB3) hMS3
    have hRun : (copyHeadBitsRel InputAlphabet ⟨0, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList (a₀ :: a₁ :: usA) (b₀ :: b₁ :: usB))
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      change Relation.ReflTransGen _ ⟨.inl (⟨0, by decide⟩, BitRelState.init), inHead, initTapes⟩ _
      rw [← hTapesSelf]
      simpa [BitRelState.runList] using hS0.trans (hS1.trans hRest)
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · simpa [hUA_syms, List.append_assoc, Nat.add_assoc] using hFA
    · simpa [hUB_syms, List.append_assoc, Nat.add_assoc] using hFB
    · simpa [hUA_syms, List.append_assoc, Nat.add_assoc] using hFS
  · have hStartFin : startIdx = ⟨2, by decide⟩ := Fin.ext h2
    subst startIdx
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.zero_add] at hUA hUB
    obtain ⟨ftR, ftA, ftB, ftS, hRest, hFR, hFA, hFB, hFS⟩ := hScanRuler S 0 pA pB [.leftMark]
      ua ub BitRelState.init (initTapes tRuler) (initTapes tArgA) (initTapes tArgB) (initTapes tScratch)
      (Nat.zero_add S) hUA hUB hBoundA hBoundB (by simp at hBoundS ⊢; omega) hMatchR
      (by simpa [hUA_syms] using hMatchA) (by simpa [hUB_syms] using hMatchB) hMatchS
    have hRun : (copyHeadBitsRel InputAlphabet ⟨2, by decide⟩).ReachesExit input bound
        initTapes inHead (BitRelState.init.runList ua ub)
        (fun j => if j = tRuler then ftR else if j = tArgA then ftA
                  else if j = tArgB then ftB else if j = tScratch then ftS else initTapes j) inHead := by
      change Relation.ReflTransGen _ ⟨.inl (⟨2, by decide⟩, BitRelState.init), inHead, initTapes⟩ _
      rw [← hTapesSelf]
      exact hRest
    refine ⟨ftR, ftA, ftB, ftS, hRun, hFR, ?_, ?_, ?_⟩
    · simpa [hUA_syms] using hFA
    · simpa [hUB_syms] using hFB
    · simpa [hUA_syms] using hFS

end SavitchLemma

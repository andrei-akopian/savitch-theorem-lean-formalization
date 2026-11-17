module

public import SavitchLemma.AcceptingZD
public import SavitchLemma.TapePrimitives

@[expose] public section

/-!
# Register-tape layout

Defines tape roles and the finite-list encoding of working and source registers.
-/

namespace SavitchLemma

/-- Tape 0 holds the space ruler `[.leftMark, .bit true (× S), .endMark]`. -/
def tRuler : Fin 5 := 0

/-- Tape 1 holds the Savitch register array. -/
def tRegs : Fin 5 := 1

/-- Tape 2 holds argument A (`1^W` during D0, or `x` during step checking). -/
def tArgA : Fin 5 := 2

/-- Tape 3 holds argument B (`1^W` during D0, or `y` during step checking). -/
def tArgB : Fin 5 := 3

/-- Tape 4 serves as a unary/binary decrement scratch tape. -/
def tScratch : Fin 5 := 4

/-- Encode one working register `(tag, bits)` as `[.tag tag] ++ bits ++ [.sep]`. -/
def encodeRegEntry (b : Bool) (bs : List Bool) : List SimSym :=
  SimSym.tag b :: bs.map SimSym.bit ++ [SimSym.sep]

/-- Encode a prefix of working registers starting with `.leftMark`. -/
def encodeRegsPrefix (work : List (Bool × List Bool)) : List SimSym :=
  SimSym.leftMark :: work.flatMap (fun r => encodeRegEntry r.1 r.2)

/-- Encode the distinguished source register at the right end of Tape 1. -/
def encodeSrcEntry (src : List Bool) : List SimSym :=
  SimSym.srcSep :: SimSym.tag true :: src.map SimSym.bit ++ [SimSym.endMark]

/-- Full contents of Tape 1 for working registers `work` and source bits `src`. -/
def encodeRegsTape (work : List (Bool × List Bool)) (src : List Bool) : List SimSym :=
  encodeRegsPrefix work ++ encodeSrcEntry src

/-- Extract the `r` working registers of `cfg : ZDConfig r N` as `W`-bit lists. -/
def encodeZDRegs {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List (Bool × List Bool) :=
  List.ofFn fun j : Fin r => (cfg.tag j.castSucc, natToBits W (cfg.x j.castSucc).val)

/-- Extract the source register `Fin.last r` of `cfg : ZDConfig r N` as a `W`-bit list. -/
def encodeZDSrc {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List Bool :=
  natToBits W (cfg.x (Fin.last r)).val

/-- Complete Tape 1 representation of `cfg : ZDConfig r N`. -/
def zdRegsContents {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) : List SimSym :=
  encodeRegsTape (encodeZDRegs W cfg) (encodeZDSrc W cfg)

@[simp]
theorem encodeRegEntry_length (b : Bool) (bs : List Bool) :
    (encodeRegEntry b bs).length = bs.length + 2 := by
  simp [encodeRegEntry]

@[simp]
theorem encodeSrcEntry_length (src : List Bool) :
    (encodeSrcEntry src).length = src.length + 3 := by
  simp [encodeSrcEntry]

theorem encodeRegsPrefix_nil : encodeRegsPrefix [] = [SimSym.leftMark] := rfl

theorem encodeRegsPrefix_snoc (work : List (Bool × List Bool)) (r : Bool × List Bool) :
    encodeRegsPrefix (work ++ [r]) = encodeRegsPrefix work ++ encodeRegEntry r.1 r.2 := by
  simp [encodeRegsPrefix, List.flatMap_append]

theorem encodeRegsPrefix_append (pref suf : List (Bool × List Bool)) :
    encodeRegsPrefix (pref ++ suf) =
      encodeRegsPrefix pref ++ suf.flatMap (fun r => encodeRegEntry r.1 r.2) := by
  simp [encodeRegsPrefix, List.flatMap_append]

theorem encodeRegsTape_split (pref suf : List (Bool × List Bool))
    (b : Bool) (bs src : List Bool) :
    encodeRegsTape (pref ++ (b, bs) :: suf) src =
      encodeRegsPrefix pref ++
        SimSym.tag b :: bs.map SimSym.bit ++
          [SimSym.sep] ++
          suf.flatMap (fun r => encodeRegEntry r.1 r.2) ++
          encodeSrcEntry src := by
  simp [encodeRegsTape, encodeRegsPrefix, encodeRegEntry, List.flatMap_append, List.append_assoc]

theorem encodeRegsPrefix_length (W : ℕ) (work : List (Bool × List Bool))
    (hLen : ∀ r ∈ work, r.2.length = W) :
    (encodeRegsPrefix work).length = 1 + work.length * (W + 2) := by
  induction work with
  | nil => simp [encodeRegsPrefix]
  | cons r rs ih =>
    have hHead : r.2.length = W := hLen r (by simp)
    have hTail : ∀ x ∈ rs, x.2.length = W := fun x hx => hLen x (by simp [hx])
    simp only [encodeRegsPrefix, List.flatMap_cons, List.length_cons, List.length_append,
      encodeRegEntry_length, hHead]
    have ih' := ih hTail
    simp only [encodeRegsPrefix, List.length_cons] at ih'
    rw [Nat.succ_mul]
    omega

theorem encodeRegsTape_length (W : ℕ) (work : List (Bool × List Bool)) (src : List Bool)
    (hWork : ∀ r ∈ work, r.2.length = W) (hSrc : src.length = W) :
    (encodeRegsTape work src).length = 1 + work.length * (W + 2) + (W + 3) := by
  simp [encodeRegsTape, encodeRegsPrefix_length W work hWork, hSrc]

theorem encodeZDRegs_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    (encodeZDRegs W cfg).length = r := by
  simp [encodeZDRegs]

theorem encodeZDRegs_bit_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    ∀ e ∈ encodeZDRegs W cfg, e.2.length = W := by
  intro e he
  simp only [encodeZDRegs, List.mem_ofFn] at he
  rcases he with ⟨j, rfl⟩
  simp [natToBits_length]

theorem encodeZDSrc_length {r N : ℕ} (W : ℕ) (cfg : ZDConfig r N) :
    (encodeZDSrc W cfg).length = W := by
  simp [encodeZDSrc, natToBits_length]

theorem encodeRegEntry_no_leftMark (b : Bool) (bs : List Bool) :
    SimSym.leftMark ∉ encodeRegEntry b bs := by
  simp [encodeRegEntry]

theorem encodeSrcEntry_no_leftMark (src : List Bool) :
    SimSym.leftMark ∉ encodeSrcEntry src := by
  simp [encodeSrcEntry]

theorem encodeRegsTape_no_other_leftMark (work : List (Bool × List Bool)) (src : List Bool) :
    ∀ i, 1 ≤ i → i < (encodeRegsTape work src).length →
      (encodeRegsTape work src)[i]? ≠ some SimSym.leftMark := by
  intro i hi1 hiLt
  cases i with
  | zero => omega
  | succ i' =>
    rw [List.getElem?_eq_getElem hiLt]
    intro hEq
    have hEq' : (encodeRegsTape work src)[i' + 1] = SimSym.leftMark := Option.some.inj hEq
    simp only [encodeRegsTape, encodeRegsPrefix, List.cons_append, List.getElem_cons_succ] at hEq'
    have hInTail : SimSym.leftMark ∈
        work.flatMap (fun r => encodeRegEntry r.1 r.2) ++ encodeSrcEntry src :=
      hEq' ▸ List.getElem_mem _
    simp only [List.mem_append, List.mem_flatMap] at hInTail
    rcases hInTail with ⟨r, _, hMemR⟩ | hMemSrc
    · exact encodeRegEntry_no_leftMark r.1 r.2 hMemR
    · exact encodeSrcEntry_no_leftMark src hMemSrc

theorem encodeRegsTape_head_leftMark (work : List (Bool × List Bool)) (src : List Bool) :
    (encodeRegsTape work src)[0]'(by simp [encodeRegsTape, encodeRegsPrefix]) = SimSym.leftMark :=
  rfl

end SavitchLemma

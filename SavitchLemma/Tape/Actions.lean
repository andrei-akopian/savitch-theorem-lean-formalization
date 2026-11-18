module

public import SavitchLemma.Tape.Alphabet
public import SavitchLemma.Model.TMCombinators

@[expose] public section

/-!
# Tape actions

Provides single- and two-tape actions and their one-step correctness lemmas.
-/

namespace SavitchLemma

/-- Helper to construct a `TMAction` that modifies only one work tape `t`
(leaving the input head and all other work tapes stationary and unchanged). -/
def singleTapeAction {Q : Type*} {k : ℕ} (next : Q) (t : Fin k)
    (writeSym : SimSym) (mv : TapeMove) (scanned : Fin k → SimSym) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write i := if i = t then writeSym else scanned i
  workMove i := if i = t then mv else .stay

/-- Helper to construct a `TMAction` that modifies two distinct work tapes `t₁, t₂`. -/
def twoTapeAction {Q : Type*} {k : ℕ} (next : Q) (t₁ t₂ : Fin k)
    (w₁ w₂ : SimSym) (m₁ m₂ : TapeMove) (scanned : Fin k → SimSym) :
    TMAction Q SimSym k where
  nextState := next
  inputMove := .stay
  write i := if i = t₁ then w₁ else if i = t₂ then w₂ else scanned i
  workMove i := if i = t₁ then m₁ else if i = t₂ then m₂ else .stay

theorem singleTapeAction_apply {Q : Type*} {k : ℕ} (next : Q) (t : Fin k)
    (writeSym : SimSym) (mv : TapeMove)
    (tapes : Fin k → OneSidedTape SimSym)
    {nextTape : OneSidedTape SimSym}
    (hUpd : (tapes t).updateAndMove writeSym mv = some nextTape) :
    ∀ i : Fin k,
      (tapes i).updateAndMove
        ((singleTapeAction next t writeSym mv (fun j => (tapes j).cells (tapes j).head)).write i)
        ((singleTapeAction next t writeSym mv (fun j => (tapes j).cells (tapes j).head)).workMove i) =
      some (if i = t then nextTape else tapes i) := by
  intro i
  by_cases hi : i = t
  · subst hi
    simpa [singleTapeAction] using hUpd
  · simp only [singleTapeAction]
    simp only [hi, ↓reduceIte]
    cases hT : tapes i with
    | mk cells head =>
      simp [OneSidedTape.updateAndMove, moveOneSidedHead]
      funext j
      by_cases hj : j = head <;> simp [hj]

theorem twoTapeAction_apply {Q : Type*} {k : ℕ} (next : Q) (t₁ t₂ : Fin k)
    (hNe : t₁ ≠ t₂) (w₁ w₂ : SimSym) (m₁ m₂ : TapeMove)
    (tapes : Fin k → OneSidedTape SimSym)
    {nt₁ nt₂ : OneSidedTape SimSym}
    (hUpd₁ : (tapes t₁).updateAndMove w₁ m₁ = some nt₁)
    (hUpd₂ : (tapes t₂).updateAndMove w₂ m₂ = some nt₂) :
    ∀ i : Fin k,
      (tapes i).updateAndMove
        ((twoTapeAction next t₁ t₂ w₁ w₂ m₁ m₂ (fun j => (tapes j).cells (tapes j).head)).write i)
        ((twoTapeAction next t₁ t₂ w₁ w₂ m₁ m₂ (fun j => (tapes j).cells (tapes j).head)).workMove i) =
      some (if i = t₁ then nt₁ else if i = t₂ then nt₂ else tapes i) := by
  intro i
  by_cases h1 : i = t₁
  · subst h1
    simpa [twoTapeAction] using hUpd₁
  · by_cases h2 : i = t₂
    · subst h2
      simpa [twoTapeAction, hNe.symm] using hUpd₂
    · simp only [twoTapeAction, h1, h2, ↓reduceIte]
      cases hT : tapes i with
      | mk cells head =>
        simp [OneSidedTape.updateAndMove, moveOneSidedHead]
        funext j
        by_cases hj : j = head <;> simp [hj]

theorem singleTape_atom_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → SimSym → (Exit × SimSym × TapeMove))
    (t : Fin k) (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hHeads : ∀ j, (tapes j).head < bound j)
    {nextTape : OneSidedTape SimSym}
    (hUpd : (tapes t).updateAndMove
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).2.1
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).2.2 = some nextTape)
    (hNextHead : nextTape.head < bound t) :
    (TMComponent.atom fun inSym scanned =>
      let res := f inSym (scanned t)
      singleTapeAction res.1 t res.2.1 res.2.2 scanned).ReachesExit input bound tapes inHead
      (f (readInput input inHead) ((tapes t).cells (tapes t).head)).1
      (fun j => if j = t then nextTape else tapes j) inHead := by
  let res := f (readInput input inHead) ((tapes t).cells (tapes t).head)
  have hAtom := TMComponent.atom_reachesExit
    (fun inSym scanned =>
      let res := f inSym (scanned t)
      singleTapeAction res.1 t res.2.1 res.2.2 scanned)
    input bound tapes inHead hHeads inHead
    (by simp [singleTapeAction, moveHead])
    (fun j => if j = t then nextTape else tapes j)
    (fun j => singleTapeAction_apply res.1 t res.2.1 res.2.2 tapes hUpd j)
    (fun j => by
      by_cases hj : j = t
      · subst hj; simpa using hNextHead
      · simp only [hj, ↓reduceIte]; exact hHeads j)
  exact hAtom

theorem twoTape_atom_reachesExit {InputAlphabet : Type*} {k n : ℕ} {Exit : Type*}
    (f : InputSymbol InputAlphabet → SimSym → SimSym →
      (Exit × SimSym × SimSym × TapeMove × TapeMove))
    (t₁ t₂ : Fin k) (hNe : t₁ ≠ t₂)
    (input : Fin n → InputAlphabet) (bound : Fin k → ℕ)
    (tapes : Fin k → OneSidedTape SimSym) (inHead : Fin (n + 2))
    (hHeads : ∀ j, (tapes j).head < bound j)
    {nt₁ nt₂ : OneSidedTape SimSym}
    (hUpd₁ : (tapes t₁).updateAndMove
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.1
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.2.1 = some nt₁)
    (hUpd₂ : (tapes t₂).updateAndMove
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.1
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).2.2.2.2 = some nt₂)
    (hHead₁ : nt₁.head < bound t₁) (hHead₂ : nt₂.head < bound t₂) :
    (TMComponent.atom fun inSym scanned =>
      let res := f inSym (scanned t₁) (scanned t₂)
      twoTapeAction res.1 t₁ t₂ res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 scanned).ReachesExit
      input bound tapes inHead
      (f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
        ((tapes t₂).cells (tapes t₂).head)).1
      (fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else tapes j) inHead := by
  let res := f (readInput input inHead) ((tapes t₁).cells (tapes t₁).head)
    ((tapes t₂).cells (tapes t₂).head)
  have hAtom := TMComponent.atom_reachesExit
    (fun inSym scanned =>
      let res := f inSym (scanned t₁) (scanned t₂)
      twoTapeAction res.1 t₁ t₂ res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 scanned)
    input bound tapes inHead hHeads inHead
    (by simp [twoTapeAction, moveHead])
    (fun j => if j = t₁ then nt₁ else if j = t₂ then nt₂ else tapes j)
    (fun j => twoTapeAction_apply res.1 t₁ t₂ hNe
      res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2 tapes hUpd₁ hUpd₂ j)
    (fun j => by
      by_cases h1 : j = t₁
      · subst h1; simpa using hHead₁
      · by_cases h2 : j = t₂
        · subst h2; simpa [h1] using hHead₂
        · simp only [h1, h2, ↓reduceIte]; exact hHeads j)
  exact hAtom

end SavitchLemma

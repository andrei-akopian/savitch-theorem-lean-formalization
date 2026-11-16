module

public import Mathlib.Logic.Relation
public import Mathlib.Tactic
public import SavitchLemma.SavitchAlgorithm

@[expose] public section

/-!
# Bounded reachability in the abstract transition graph

`AbstractPath P n a b` records a path of exactly `n` edges.  `ReachesWithin`
then gives the at-most bound used in Savitch's midpoint argument.
-/

namespace SavitchLemma

/-- An exactly-`n`-edge path in the abstract transition graph. -/
inductive AbstractPath (P : AbstractProblem N) :
    ℕ → Fin (N + 1) → Fin (N + 1) → Prop where
  | nil (a : Fin (N + 1)) : AbstractPath P 0 a a
  | cons {n : ℕ} {a b c : Fin (N + 1)}
      (edge : P.step a b) (tail : AbstractPath P n b c) :
      AbstractPath P (n + 1) a c

/-- Concatenating paths adds their exact lengths. -/
theorem AbstractPath.append (P : AbstractProblem N) {m n : ℕ}
    {a b c : Fin (N + 1)} (p : AbstractPath P m a b) (q : AbstractPath P n b c) :
    AbstractPath P (m + n) a c := by
  induction p with
  | nil => simpa using q
  | @cons m a mid b edge p ih =>
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using AbstractPath.cons edge (ih q)

/-- At-most-`bound`-edge reachability. -/
def ReachesWithin (P : AbstractProblem N) (bound : ℕ)
    (a b : Fin (N + 1)) : Prop :=
  ∃ length, length ≤ bound ∧ AbstractPath P length a b

/-- Reflexive reachability uses zero edges. -/
theorem ReachesWithin.refl (P : AbstractProblem N) (bound : ℕ)
    (a : Fin (N + 1)) : ReachesWithin P bound a a :=
  ⟨0, Nat.zero_le _, AbstractPath.nil a⟩

/-- Every one-edge transition is reachable within one step. -/
theorem ReachesWithin.single (P : AbstractProblem N) {a b : Fin (N + 1)}
    (h : P.step a b) : ReachesWithin P 1 a b :=
  ⟨1, le_rfl, AbstractPath.cons h (AbstractPath.nil b)⟩

/-- Increasing the step bound preserves reachability. -/
theorem ReachesWithin.mono (P : AbstractProblem N) {m n : ℕ} {a b : Fin (N + 1)}
    (hBound : m ≤ n) (hReach : ReachesWithin P m a b) : ReachesWithin P n a b := by
  rcases hReach with ⟨length, hLength, hPath⟩
  exact ⟨length, le_trans hLength hBound, hPath⟩

/-- Concatenating two bounded paths adds their bounds. -/
theorem ReachesWithin.trans (P : AbstractProblem N) {m n : ℕ}
    {a b c : Fin (N + 1)} (h₁ : ReachesWithin P m a b)
    (h₂ : ReachesWithin P n b c) : ReachesWithin P (m + n) a c := by
  rcases h₁ with ⟨m', hm', p⟩
  rcases h₂ with ⟨n', hn', q⟩
  refine ⟨m' + n', ?_, AbstractPath.append P p q⟩
  exact Nat.add_le_add hm' hn'

/-- Split an exact path after its first `m` edges. -/
theorem AbstractPath.splitExact (P : AbstractProblem N) (m : ℕ) :
    ∀ {n : ℕ} {a b : Fin (N + 1)},
      AbstractPath P (m + n) a b →
      ∃ c, AbstractPath P m a c ∧ AbstractPath P n c b := by
  induction m with
  | zero =>
    intro n a b h
    exact ⟨a, AbstractPath.nil a, by simpa using h⟩
  | succ m ih =>
    intro n a b h
    rw [Nat.succ_add] at h
    cases h with
    | cons edge tail =>
      obtain ⟨c, hPrefix, hSuffix⟩ := ih tail
      exact ⟨c, AbstractPath.cons edge hPrefix, hSuffix⟩

/-- An at-most path of length `m + n` splits into an at-most-`m` prefix and
an at-most-`n` suffix. -/
theorem ReachesWithin.splitAdd (P : AbstractProblem N) (m n : ℕ)
    {a b : Fin (N + 1)} (hReach : ReachesWithin P (m + n) a b) :
    ∃ c, ReachesWithin P m a c ∧ ReachesWithin P n c b := by
  rcases hReach with ⟨length, hLength, hPath⟩
  by_cases hShort : length ≤ m
  · exact ⟨b, ⟨length, hShort, hPath⟩, ReachesWithin.refl P n b⟩
  · have hm : m ≤ length := Nat.le_of_not_ge hShort
    let suffixLength := length - m
    have hDecomp : length = m + suffixLength := by
      dsimp [suffixLength]
      omega
    have hSuffix : suffixLength ≤ n := by omega
    rw [hDecomp] at hPath
    obtain ⟨c, hPrefix, hSuffixPath⟩ := AbstractPath.splitExact P m hPath
    exact ⟨c, ⟨m, le_rfl, hPrefix⟩, ⟨suffixLength, hSuffix, hSuffixPath⟩⟩

/-- Exact bounded paths imply ordinary reflexive-transitive reachability. -/
theorem AbstractPath.toReflTransGen (P : AbstractProblem N)
    {length : ℕ} {a b : Fin (N + 1)} (h : AbstractPath P length a b) :
    Relation.ReflTransGen P.step a b := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons edge _ ih => exact (Relation.ReflTransGen.single edge).trans ih

/-- Reflexive-transitive reachability has a finite exact-length path witness. -/
theorem reflTransGen_iff_exists_path (P : AbstractProblem N)
    {a b : Fin (N + 1)} :
    Relation.ReflTransGen P.step a b ↔ ∃ length, AbstractPath P length a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, AbstractPath.nil _⟩
    | @tail mid dest hPath hEdge ih =>
      rcases ih with ⟨length, p⟩
      exact ⟨length + 1, AbstractPath.append P p (AbstractPath.cons hEdge (AbstractPath.nil dest))⟩
  · rintro ⟨_, h⟩
    exact AbstractPath.toReflTransGen P h

/-- A path of at most `2^(k+1)` edges splits into two paths of at most `2^k` edges. -/
theorem ReachesWithin.splitPowTwo (P : AbstractProblem N) (k : ℕ)
    {a b : Fin (N + 1)} (hReach : ReachesWithin P (2 ^ (k + 1)) a b) :
    ∃ midpoint, ReachesWithin P (2 ^ k) a midpoint ∧
      ReachesWithin P (2 ^ k) midpoint b := by
  have hPow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    simp [pow_succ, Nat.mul_two]
  rw [hPow] at hReach
  exact ReachesWithin.splitAdd P (2 ^ k) (2 ^ k) hReach

end SavitchLemma

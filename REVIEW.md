# Formalization Review and Recommendations: Savitch's Theorem in Lean 4

## 1. Executive Summary

The progress on the abstract register-machine layer of Savitch's Theorem (`SavitchLemma/*.lean`) is **exceptionally strong**. All 9 implemented modules are clean, modular, well-documented, and completely free of `sorry` or `admit`.

More importantly, the formalization has already achieved one of the highest-value outcomes of interactive theorem proving: **discovering and mechanically certifying a genuine subtle bug in Savitch's 1970 paper (`LemmaTwoCounterexample.lean`)**.

Below is a detailed review of the existing codebase, an analysis of *why* Savitch's printed Lemma 2 fails at $j = 1$ (and how to resolve the "Source-consistency gate" in `PLAN.md`), and concrete recommendations for the next phases of the formalization.

---

## 2. Review of Completed Modules

### Strengths of the Current Implementation
1. **Clean Separation of Concerns:**
   Splitting the abstract machine into small, focused files ([SavitchAlgorithm.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/SavitchAlgorithm.lean), [Selection.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Selection.lean), [ConfigUpdates.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/ConfigUpdates.lean), [Reachability.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Reachability.lean), [StepBehavior.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/StepBehavior.lean)) keeps proof terms short and readable.
2. **Colexicographic Termination Measure ([Termination.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Termination.lean)):**
   Using `zdDigit cfg i = 2 * x_i + tag_i` and `Colex (Fin r → ℕ)` on the remaining capacity `2 * N + 1 - zdDigit cfg i` is an elegant solution. Because `D2` sets `tag_j := true` while resetting `i < j` and `D3` increments `x_j` (increasing `2 * x_j` by 2, which strictly outweighs `tag_j` dropping from `1` to `0`) while resetting `i < j`, *every* step strictly decreases the colexicographic measure.
3. **Proof of `lemma_one` via Termination + Invariant ([LemmaOne.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/LemmaOne.lean)):**
   Instead of a brittle nested induction on `(i, x)` that manually tracks intermediate configurations, `lemma_one` uses a safety invariant (`LemmaOneSafe`) along any finite execution together with `zdStep_reaches_stuck` and `zdStep_none_forces_max`. Since a stuck state forces all registers to `N`, and `target.val ≤ N`, the machine *must* exit `LemmaOneSafe` via either `LemmaOneOutcomeA` or `LemmaOneOutcomeB` before getting stuck. This is a textbook example of how to structure state-machine proofs in Lean.
4. **Certified Counterexample to Printed Lemma 2 ([LemmaTwoCounterexample.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/LemmaTwoCounterexample.lean)):**
   Rather than guessing or silently changing definitions when the base case of Lemma 2 resisted proof, you constructed a minimal counterexample ($N = 5, r = 2$, edges $1 \to 2 \to 3$, starting configuration $\langle 3, 4, 1 \rangle, \langle 0, 0, 1 \rangle$ reachable from `D0`) and proved in Lean (`printed_lemma2_counterexample`) that the machine fails to ever tag $3$ in register 1.

### Minor Code Quality & Style Suggestions
- **Import minimization in umbrella & leaf files:**
  - [SavitchLemma.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma.lean#L3) currently has `import Mathlib`. Removing `import Mathlib` from `SavitchLemma.lean` (so it only re-exports `SavitchLemma.*`) will drastically reduce compilation and startup time when building the root target.
  - Similarly, [BoundedReachability.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/BoundedReachability.lean#L4) and [Termination.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/Termination.lean#L5) have `public import Mathlib.Tactic`. Replacing that with targeted tactic imports (e.g., `Mathlib.Tactic.Omega`, `Mathlib.Tactic.Simpa`, `Mathlib.Tactic.FinCases`) will keep the dependency graph lightweight.

---

## 3. Resolving the "Source-Consistency Gate" (Why Printed Lemma 2 Fails and How to Fix It)

In [PLAN.md](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/PLAN.md#L131-L144), progress is paused at the **Source-consistency gate** because Savitch's printed Lemma 2 is false as written. Let's analyze **why** it is false in the paper and compare the two cleanest ways to resolve it.

### Diagnosis of Savitch's Off-By-One Error
Look at Savitch's informal explanation vs. his formal lemma on pages 180–184 of the paper:
- **Page 180 (Informal description):**
  > *"reduce the length of the computations it need check until it need only check, for appropriate ID's $I_1$ and $I_2$, whether, with input $w$, $Z_N$ can in **one step** go from $I_1$ to $I_2$."*
- **Page 181 (`D1` Test):**
  `D1` tests whether $x_h \vdash x_j$ (which is **at most $1 = 2^0$ step**, not $2^1 = 2$ steps).
- **Page 183–184 (Lemmas 2 & 3):**
  In Lemma 2, configuration (4) has $j - 1$ registers to the left of $x_j$:
  $$\langle \underbrace{1, \dots, 1}_{j-1}, x, x_{j+1}, \dots, x_r, I_0 \rangle, \quad \langle \underbrace{0, \dots, 0}_{j-1}, T_j, T_{j+1}, \dots, T_r, 1 \rangle$$
  In the inductive step (p. 184), Savitch writes:
  > *"Decomposing this computation from $x_q$ to $x$, we get that there is a $y$ such that there are computations of at most $2^{j-1}$ steps from $x_q$ to $y$ and from $y$ to $x$. By Lemma 1, it follows that, at some later time, either the configuration of $Z_D$ is $\langle \underbrace{1, \dots, 1}_{j-2}, y, x, x_{j+1}, \dots \rangle$..."*
  
  **Here is Savitch's slip:**
  The inductive step uses register $j - 1$ to hold the midpoint $y$. That requires $j - 1 \ge 1$, i.e., $j \ge 2$!
  When $j = 1$ (1-based), there are $j - 1 = 0$ registers to the left of register $1$. Register $1$ has **no scratch registers to its left** to store a midpoint $y$! Therefore, when `D1` inspects register $1$, it can only test direct 1-step reachability $x_q \vdash x_1$ ($2^0 = 1$ step), **not** 2-step reachability ($2^1 = 2$ steps).
  - With $0$ scratch registers to its left ($j = 1$ in 1-based, or `j = 0` in 0-based `Fin r`), register $j$ can check at most **$2^0 = 1$ step**.
  - With $1$ scratch register to its left ($j = 2$ in 1-based, or `j = 1` in 0-based `Fin r`), register $j$ uses register $1$ (`0` in 0-based) for the midpoint $y$, so it can check at most **$2^1 = 2$ steps**.
  - In general, the $j$-th 1-based register has $j - 1$ scratch registers to its left, so it checks computations of at most **$2^{j-1}$ steps** (which in 0-based indexing `j : Fin r` is simply **`2 ^ j.val` steps**!).

Savitch wrote $2^j$ instead of $2^{j-1}$ in Lemmas 2 and 3 (or equivalently, allocated $r$ registers instead of $r + 1$ work registers for $2^r$ steps), because in the base case $j = 1$ he conflated "1 step" ($2^0$) with "$j = 1 \implies 2^1$".

### Three Options to Resolve the Gate (and Recommendation)

| Option | Description | Pros | Cons |
| :--- | :--- | :--- | :--- |
| **Option A (Recommended): Use `2 ^ j.val` in Lemmas 2 & 3 (i.e. $2^{j-1}$ for 1-based $j$)** | Keep `zdStep` (D0–D3) 100% identical to the paper. State Lemmas 2 & 3 for `j : Fin r` with step bound `2 ^ j.val` ($= 2^{j-1}$ in 1-based). To check $2^r$ steps in Theorem 1, instantiate `ZDConfig (r + 1) N` (which still uses $O(L(n))$ registers). | - Zero changes to `SavitchAlgorithm.lean` or `LemmaTwoCounterexample.lean`.<br>- Base case `j.val = 0` ($2^0 = 1$ step) is literally 1 step of `D1`/`D2`!<br>- Inductive step `j.val = k + 1` ($2^{k+1}$ steps) matches Savitch's proof on p. 184 word-for-word. | Exponent is $2^{j-1}$ (1-based) = $2^{j\text{.val}}$ (0-based) rather than $2^j$ (1-based), documented by `LemmaTwoCounterexample.lean`. |
| **Option B: Add Outcome B ("or an untagged suffix register is tagged first") to Lemmas 2 & 3** | Even with $2^{j-1}$, wait: what if $q > j$ in Lemma 2, and there is an untagged register $k$ with $j < k < q$ that gets tagged by Lemma 1's Outcome B before $x_j$ gets tagged? | Essential! See the critical finding in Section 3.1 below. | Must be combined with Option A. |
| **Option C: Modify `D1` to test 2-step reachability** | Change `zdStep` so `D1` tests $\le 2$ steps instead of $\le 1$ step. | Makes $2^{j.val + 1}$ true. | Deviates from Savitch's `D1` algorithm and invalidates the 1-step elegance of the machine. |

---

### 3.1 CRITICAL FINDING #2: A Second Subtlety in Savitch's Proof of Lemma 2!

Before you write `LemmasTwoThree.lean`, there is **a second crucial detail** in Savitch's proof on page 184 that you must account for so you don't hit another roadblock!

Look at Savitch's proof of Lemma 2 on page 184:
> *"By Lemma 1, it follows that, at some later time, either the configuration of $Z_D$ is $\langle 1, \dots, 1, y, x, x_{j+1}, \dots \rangle$ with $T_{j-1} = 0$ **or the configuration is (4) with $T_j = 1$**."*

**Wait: is that what Lemma 1's Outcome B actually says?!**
Look at `LemmaOneOutcomeB` in [LemmaOne.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/SavitchLemma/LemmaOne.lean#L42-L51):
When we apply `lemma_one` to register `j - 1` (to place $y$ into register `j - 1`), `LemmaOneOutcomeB` says that the **least initially untagged register strictly to the right of `j - 1`** is tagged.
In Lemma 2, register `j` has `tag j = false`, so the least untagged register to the right of `j - 1` is indeed `j`! **Wait:** when `D2` tags register `j` during `lemma_one`, what does `D2` do to the registers to the left of `j`?
`D2` resets all registers $< j$ to `(firstCode, false)` and sets `tag j = true`, which **is** configuration (4) with $T_j = 1$!
*So in Lemma 1 applied at `j - 1`, Outcome B really does give configuration (4) with $T_j = 1$!*

**However, what about after `tag (j - 1)` becomes `true` (via IH Lemma 2), when we apply IH Lemma 3($j - 1$)?**
And what about **inside the proof of Lemma 3($j$)** when we apply `lemma_one` at `j - 1`?
In Lemma 3($j$), the configuration (5) is:
$$\langle \underbrace{1, \dots, 1}_{j-1}, x_j, \dots, x_{j+p}, x, x_{j+p+2}, \dots \rangle, \quad \langle \underbrace{0, \dots, 0}_{j-1}, \underbrace{1, \dots, 1}_{p+1}, 0, T_{j+p+2}, \dots \rangle$$
Here, registers $j, \dots, j+p$ all have tag $1$, and register $j+p+1$ (which holds $x$) is the **first** register to the right of $j - 1$ with tag $0$!
So when we apply `lemma_one` at `j - 1` inside the proof of Lemma 3($j$):
- **Outcome A** places $y$ into register $j - 1$ with tag $0$.
- **Outcome B** tags the least untagged register $> j - 1$, which is **register $j + p + 1$** (the register holding $x$), and resets all registers $< j + p + 1$ to `(1, 0)`—which is **exact configuration (6), the desired conclusion of Lemma 3($j$)**!

**Wait—what if $x_q$ (the already-tagged source of the $2^j$-step path to $x$) is to the LEFT of $x$ or gets overwritten?**
Look at the quantifier on $q$ in Lemmas 2 and 3 (p. 183):
> *"If for some index $q$, $T_q = 1$ and there is a computation of $Z_N$ of at most $2^j$ steps from $x_q$ to $x$..."*
- In **Lemma 2** (configuration 4), all registers $< j$ have $T_i = 0$, and $T_j = 0$. So any $q$ with $T_q = 1$ **automatically satisfies $q > j$**! Because $q > j$, operations on registers $\le j$ (in Lemma 1, IH Lemma 2($j-1$), and IH Lemma 3($j-1$) with $p = 0$) **never touch register $q$**! Thus $x_q$ and $T_q = 1$ remain intact throughout the entire inductive step of Lemma 2!
- Now look at **Lemma 3** (configuration 5):
  $$\langle \underbrace{1, \dots, 1}_{j-1}, x_j, \dots, x_{j+p}, x, x_{j+p+2}, \dots \rangle, \quad \langle \underbrace{0, \dots, 0}_{j-1}, \underbrace{1, \dots, 1}_{p+1}, 0, T_{j+p+2}, \dots \rangle$$
  Here, $T_q = 1$ could hold for $q \in \{j, \dots, j+p\}$ OR for $q > j+p+1$!
  Does `lemma_one` at $j - 1$ or IH Lemma 2($j - 1$) touch registers $\ge j$?
  **No!** Both `lemma_one` at $j - 1$ (unless Outcome B already finishes Lemma 3!) and IH Lemma 2($j - 1$) only modify registers $\le j - 1$!
  So every register $\ge j$—including $x_j, \dots, x_{j+p}$ and everything above $j+p+1$—is completely preserved until $T_{j-1}$ becomes $1$! And once $T_{j-1} = 1$ (with $x_{j-1} = y$), the second half of the path ($y \to^{\le 2^{j-1}} x$) only needs $q' = j - 1$ (since $x_{j-1} = y$ and $T_{j-1} = 1$)!

**Conclusion on Lemmas 2 & 3:**
Once the step bound for 0-based register `j : Fin r` is set to **`2 ^ j.val`** (i.e. $2^{j-1}$ in 1-based indexing), **both Lemma 2 and Lemma 3 hold without any additional side conditions!**
Even better: notice that **Lemma 2 is literally the $p = 0$ (empty middle block) case of Lemma 3**!
Specifically, if in Lemma 3 we allow the block of $1$-tags between the $0$-prefix and the target register to have length $m \ge 0$ (where $m = 0$ is Lemma 2 and $m = p + 1$ is Lemma 3):
- Prefix `0 ..< j`: `x = firstCode`, `tag = false`
- Middle `j ..< j + m`: `tag = true` (when $m = 0$, this range is empty!)
- Target register `j + m`: `x = target`, `tag = false`
- Suffix `> j + m`: untouched

Then **Lemma 2 and Lemma 3 collapse into a single theorem (`lemma_two_three`)** parameterized by `(j : ℕ)` and `(m : ℕ)` with `j + m < r`!
Let's verify this:
- When $m = 0$: Prefix is `0 ..< j`, Middle is empty, Target is at index `j` with `tag j = false`. If `ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x j)` for some `q` with `cfg.tag q = true`, then `Z_D` reaches the configuration where `0 ..< j` is reset, `x j` is unchanged, `tag j = true`, and `> j` is untouched. (**This is Lemma 2!**)
- When $m = p + 1$: Prefix is `0 ..< j`, Middle `j ..< j + p + 1` has `tag = true`, Target is at `j + p + 1` with `tag = false`. If `ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x (j + p + 1))` for some `q` with `cfg.tag q = true`, then `Z_D` reaches the configuration where `0 ..< j + p + 1` is reset, `x (j + p + 1)` is unchanged, `tag (j + p + 1) = true`, and `> j + p + 1` is untouched. (**This is Lemma 3!**)

Unifying Lemma 2 and Lemma 3 into a single theorem parameterized by `m : ℕ` (with `Lemma 2` as the corollary for `m = 0` and `Lemma 3` as the corollary for `m = p + 1`) will cut the proof length of `LemmasTwoThree.lean` in half!

---

## 4. Concrete Recommendations for Remaining Modules

### Recommendation 1: Finishing `BoundedReachability.lean` (Finite Path Shortening)
To prove path shortening in `BoundedReachability.lean` (if a valid code reaches another valid code, it does so in at most `N - 2` steps, or $< 2^r$ steps):
- **Avoid manual list surgical loop-removal if possible:**
  Since you already have `reflTransGen_iff_exists_path`, you can take the **minimum-length path** using `Nat.find` on `∃ length, AbstractPath P length a b`!
- Extract the list of vertices `(p.vertices : List (Fin (N + 1)))` of length `length + 1`.
- Prove that for a minimal-length path (`Nat.find_min`), `p.vertices.Nodup` holds: if `p.vertices` had a duplicate, `AbstractPath.splitExact` at the two indices would let you splice out the cycle and obtain a strictly shorter `AbstractPath`, contradicting `Nat.find_min`!
- From `p.vertices.Nodup`, if all vertices on the path are `ValidCode N` (of which there are `N - 1` codes, `1 .. N - 1`), `List.Nodup.length_le_card` immediately bounds `length + 1 ≤ N - 1` (or `length ≤ N`)!
- Note: Add `noStepFromZero` / `noStepFromMax` or assume the start code is a `ValidCode N` so that `noStepToZero` and `noStepToMax` guarantee every vertex along the path is in `ValidCode N`.

### Recommendation 2: Implementing `LemmasTwoThree.lean`
1. State the unified lemma `lemma_two_three` for `j : ℕ` and `m : ℕ` (with `hjm : j + m < r`):
   - Hypothesis:
     - `∀ k < j, cfg.x k = firstCode ∧ cfg.tag k = false`
     - `∀ k, j ≤ k → k < j + m → cfg.tag k = true`
     - `cfg.tag (j + m) = false`
     - `∃ q, cfg.tag q = true ∧ ReachesWithin P (2 ^ j) (cfg.x q) (cfg.x (j + m))`
     - `0 < (cfg.x (j + m)).val` (or `TagsSound P source.val cfg` so that `0 < (cfg.x q).val` and `cfg.x (j + m) < N`)
   - Conclusion:
     - Reaches `final` where `∀ k < j + m, final.x k = firstCode ∧ final.tag k = false`, `final.x (j + m) = cfg.x (j + m)`, `final.tag (j + m) = true`, and `∀ i > j + m, final.x i = cfg.x i ∧ final.tag i = cfg.tag i`.
2. **Base Case (`j = 0`):**
   - Since `2 ^ 0 = 1`, `ReachesWithin P 1 (cfg.x q) (cfg.x m)` means `cfg.x q = cfg.x m ∨ P.step (cfg.x q) (cfg.x m)`.
   - Since `∀ k < m, cfg.tag k = true` and `cfg.tag m = false`, `firstUntagged cfg = some ⟨m, hm⟩`.
   - `D1` tests `⟨m, hm⟩`, finds `q`, and `zdStep_of_successful_test` transitions in **one single step** to the desired configuration!
3. **Inductive Step (`j = j' + 1`):**
   - Split `ReachesWithin P (2 ^ (j' + 1))` via `ReachesWithin.splitPowTwo` into ` midpoint` with `ReachesWithin P (2 ^ j') (cfg.x q) midpoint` and `ReachesWithin P (2 ^ j') midpoint (cfg.x (j' + 1 + m))`.
   - Apply `lemma_one` at index `j'` with target `midpoint`.
     - If `LemmaOneOutcomeB` occurs, the least untagged register `> j'` is `j' + 1 + m`, so we are immediately done!
     - If `LemmaOneOutcomeA` occurs, `midpoint` is in register `j'` with `tag j' = false`.
   - Apply IH (`j'`) with `m' = 0` at register `j'` to tag `midpoint` (`tag j' = true`) and reset `< j'`.
   - Apply IH (`j'`) with `m' = m + 1` (since now `j'` and `j' + 1 ..< j' + 1 + m` all have `tag = true`!) and witness `q' = j'` to tag `j' + 1 + m` and reset `< j' + 1 + m`.
4. Derive `lemma_two` (`m = 0`) and `lemma_three` (`m = p + 1`) as 3-line corollaries of `lemma_two_three`.

### Recommendation 3: Designing `MachineModel.lean` and `InstantaneousDesc.lean`
When moving from the abstract layer to the Turing machine model:
- **Keep the deterministic simulator abstract until the very last step:**
  Notice that in `MainTheorem.lean`, there are two ways to state Theorem 1:
  1. **Relational / Space-Bounded Simulation:** A deterministic multitape TM $Z_D$ whose work tape stores `ZDConfig (r + 1) N` (encoded as a string of `r + 1` blocks of length `c * L(n)` plus `r + 1` tag bits) and simulates `zdStep`.
  2. **Modularity Tip:** Factor the proof of Theorem 1 through an intermediate theorem `savitch_abstract_completeness`:
     - For any `P : AbstractProblem N`, source `I₀ : ValidCode N`, and accepting predicate `IsAccepting : Fin (N + 1) → Bool`, if `∃ x_acc, IsAccepting x_acc ∧ ReachesWithin P (2 ^ r) I₀ x_acc` (and `r ≥ 1`), then starting from `zdInitial (r + 1) N hN I₀`, the machine reaches a configuration where some register `j` has `tag j = true` and `IsAccepting (cfg.x j) = true`.
     - Prove this theorem purely in the abstract layer first! That completely finishes the algorithmic core of Savitch's paper before a single line of `MachineModel.lean` is written.
- **Work-Tape Representation in `MachineModel.lean`:**
  - Use a structure `WorkTape (Γ : Type) := (leftRev : List Γ) (head : Γ) (right : List Γ)` or `(u v : List Γ)` together with an explicit integer/natural head position or explicit nonblank length `size : ℕ`.
  - Rather than dealing with dynamic blank-trimming during space measurement, you can parameterize space-bounded execution by a capacity `S : ℕ`: a configuration of an $S$-space-bounded execution has work tapes modeled directly as `Vector Γ S × Fin S` (a tape segment of length `S` and a head position in `Fin S`)!
  - **Why `Vector Γ S × Fin S` for space-bounded configurations is a huge win in Lean:**
    - A computation uses at most $S$ squares on each work tape iff it can be executed on a tape of length $S$.
    - `Vector Γ S × Fin S` (or `(Fin S → Γ) × Fin S`) is **automatically a `Fintype`** when `Γ` is a `Fintype`!
    - You get `Fintype (Config Z n S)` and its exact cardinality `|Q| * (n + 2) * (|Γ|^S * S)^k` in 5 lines of Lean using Mathlib's `Fintype.card_prod` and `Fintype.card_fun`, completely bypassing manual $m$-adic string parsing and list-length induction!
    - And `Fintype.equivFin` (shifted by $+1$ into `Fin (N + 1)` with $0$ and $N$ reserved) gives you the exact bijection into `ValidCode N` for free!

---

## 5. Proposed Action Plan (Next Steps)

1. **Clean up imports:** Remove `import Mathlib` from `SavitchLemma.lean` and `import Mathlib.Tactic` from leaf files.
2. **Finish `BoundedReachability.lean`:** Prove `reachesWithin_of_reflTransGen` (finite-state path shortening via `Nat.find` minimal path + `List.Nodup`).
3. **Create `LemmasTwoThree.lean`:**
   - Prove the unified `lemma_two_three` with step bound `2 ^ j.val` (resolving the source-consistency gate via Option A).
   - Deduce `lemma_two`, `lemma_three`, and `savitch_abstract_completeness` (that `zdInitial` reaches a tagged accepting ID whenever one is reachable in $\le 2^r$ steps).
4. **Create `MachineModel.lean` & `InstantaneousDesc.lean`:**
   - Define `MultitapeTM` and space-$S$ configurations using finite-domain functions `(Fin S → Γ) × Fin S` so `Fintype` and `Fintype.equivFin` provide the ID encoding and $2^{c' L(n)}$ bound automatically.
5. **Create `MainTheorem.lean`:**
   - Combine `InstantaneousDesc` with `savitch_abstract_completeness` to conclude Theorem 1.

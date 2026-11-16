# Plan for Formalizing Savitch's Theorem in Lean 4

Based on Walter J. Savitch's 1970 paper, *"Relationships Between Nondeterministic and Deterministic Tape Complexities"* ([savitch-paper-original.pdf](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/savitch-paper-original.pdf)).

---

## 1. Environment & Package Requirements

### Current Setup & Required Packages
The project ([lakefile.lean](file:///Users/andrei/Documents/Coding/Projects/savitch-lemma/lakefile.lean)) is configured with **Lean `v4.35.0`** and **Mathlib `v4.35.0`**. **No external third-party packages beyond Mathlib are needed.**

However, it is important to distinguish what Mathlib provides versus what must be defined for Savitch's paper:
- **What Mathlib has (`Mathlib.Computability.*`):**
  - `Mathlib.Computability.TuringMachine.Tape`: `Turing.Tape Γ` (bidirectional infinite tape with a head and finite non-blank support via `Turing.ListBlank Γ`) and `Turing.Dir` (`left`, `right`).
  - `Mathlib.Computability.TuringMachine.PostTuringMachine` & `StackTuringMachine`: Deterministic single-tape (`TM0`, `TM1`) and multi-stack (`TM2`) machines.
  - `Mathlib.Computability.StateTransition`: Deterministic state transition systems (`σ → Option σ`) and `Reaches` (`Relation.ReflTransGen`).
  - `Mathlib.Computability.Language` & `Encoding`: Formal languages (`Language α := Set (List α)`) and finite encodings.
- **What Mathlib lacks (and must be formalized):**
  - **Sublinear space-bounded Turing machines:** `TM0`/`TM1` place the input directly on the work tape, making sublinear space ($L(n) = \log_2 n$) impossible to measure. Savitch's model requires a **separate read-only input tape with end-markers** plus $k$ read/write work tapes.
  - **Nondeterministic Turing machines (NTMs):** Mathlib's `StateTransition` and `TM0`/`TM1`/`TM2` are strictly deterministic (`Cfg → Option Cfg`).

### Key Mathlib Imports to Use
Avoid `import Mathlib` in individual files to keep build times and memory low. Use targeted imports:
- `Mathlib.Computability.TuringMachine.Tape` (or `Mathlib.Data.List.Basic` if using list-pair tapes)
- `Mathlib.Computability.Language` (`Language Σ`)
- `Mathlib.Logic.Relation` (`Relation.ReflTransGen`, `Relation.Comp`)
- `Mathlib.Data.Nat.Log` (`Nat.log2`, `Nat.clog` for $\lceil \log_2 n \rceil$)
- `Mathlib.Data.Nat.Digits.Defs` (`Nat.digits` / `Nat.ofDigits` for $m$-adic and dyadic encodings)
- `Mathlib.Data.Fintype.Card` & `Mathlib.Data.Fintype.Pi` (for bounding the number of configurations by $2^{c' L(n)}$)

---

## 2. Proposed Module Architecture

Organize the project under `SavitchLemma/` with the following file hierarchy:

```text
SavitchLemma/
├── MachineModel.lean      -- Multitape TM/NTM with read-only input tape & space bounds
├── InstantaneousDesc.lean -- IDs, m-adic numbering, and 2^(c' L(n)) configuration bounds
├── SavitchAlgorithm.lean  -- The register/tag state machine (D0-D3) and Lemmas 1, 2, 3
├── MainTheorem.lean       -- Theorem 1 (Savitch's Theorem), Theorem 2, and Theorem 3
└── Mazes.lean             -- Threadable mazes, log-space NTM (Thm 4), and completeness (Thm 5)
```

---

## 3. Core Definitions to Formalize Before the Proof

### Phase 1: The Multitape Machine Model (`SavitchLemma/MachineModel.lean`)
Savitch (pp. 178–179) defines a machine with a read-only input tape (with left/right end-markers $\vdash, \dashv \notin \Sigma$) and $k$ two-way infinite read/write storage tapes over alphabet $\Gamma$ (with blank symbol $b \in \Gamma$).

1. **Head Movement (`Move`):**
   ```lean
   inductive Move | left | stay | right deriving DecidableEq, Fintype
   ```
2. **Bounded Work Tape (`WorkTape Γ`):**
   Rather than using Mathlib's infinite quotient `Turing.Tape Γ` and separately tracking visited cells, follow Savitch's ID representation (p. 180) directly: represent a work tape as a pair of lists `(u, v : List Γ)` representing the non-blank contiguous region $u v$ where the head scans `v.headD default`.
   - Define `WorkTape.size (t : WorkTape Γ) : ℕ := t.u.length + t.v.length`.
   - This makes the storage bound $L(n)$ an immediate syntactic property of the configuration (`∀ i, (cfg.tapes i).size ≤ L w.length`), avoiding the overhead of tracking historical head extrema over infinite tapes.
3. **Machine Structure (`MultitapeTM`):**
   Parameterize by input alphabet `Σ`, tape alphabet `Γ` (`[Inhabited Γ]`), state set `Q` (`[Fintype Q]`), and number of work tapes `k : ℕ`:
   - `q₀ : Q` (initial state)
   - `accept : Finset Q` (accepting states)
   - `step : Q → (Σ ⊕ EndMarker) → (Fin k → Γ) → Set (Q × Move × (Fin k → Γ × Move))`
   - A machine `Z` is **deterministic** (`IsDeterministic Z`) if `∀ q a s, (Z.step q a s).Subsingleton`.
4. **Configurations and Space-Bounded Steps:**
   - `Config Z n`: consists of `state : Q`, `inputPos : Fin (n + 2)` (enforcing by type that the input head never leaves $w$ and its two end-markers, p. 178), and `tapes : Fin k → WorkTape Γ`.
   - `StepWithin Z w S (c₁ c₂ : Config Z w.length) : Prop`: `c₂` is a valid one-step successor of `c₁` on input `w`, and both `c₁` and `c₂` use at most `S` squares on every work tape.
   - `ReachesInSteps Z w S (m : ℕ) (c₁ c₂ : Config Z w.length) : Prop`: defined inductively (or via `Relation.ReflTransGen`) as reachability in $\le m$ steps within storage $S$ (matching Savitch's $I \vdash^* I'$ where $I \vdash I'$ includes $I = I'$, p. 181).
5. **Acceptance Within Storage $L(n)$ & Measurability (p. 179):**
   - `AcceptsWithinStorage Z (L : ℕ → ℕ) (A : Language Σ) : Prop`:
     1. $\forall w \in A$, $\exists c_{acc}$, `c_acc.state ∈ Z.accept ∧ ∃ m, ReachesInSteps Z w (L w.length) m (initConfig w) c_acc`.
     2. $\forall w \notin A$, no accepting configuration is reachable (in any space).
   - `IsMeasurable (L : ℕ → ℕ) : Prop`: Existence of a deterministic 1-tape machine that halts on any input of length $n$ having scanned exactly $L(n)$ squares.

---

### Phase 2: Instantaneous Descriptions & $m$-adic Numbering (`SavitchLemma/InstantaneousDesc.lean`)
Savitch's algorithm (pp. 179–181) treats configurations (IDs) as strings over $\Delta = Q \cup \Gamma \cup \{1, 2, *, \uparrow\}$ of the form:
$$p q * u_1 \uparrow v_1 * u_2 \uparrow v_2 * \dots * u_k \uparrow v_k$$
and identifies them with integers $1 \le x \le N$ in $m$-adic notation ($m = |\Delta|$).

1. **Combinatorial Bound First:**
   Prove that the type of valid configurations `ValidID Z n S` (where each tape has size $\le S$ and $S \ge \log_2 n$) is finite and embeds into `Fin N` where $N = m^{\lfloor c \cdot S \rfloor}$ and $\log_2 N \le c' S$:
   - `card_validID_le : Fintype.card (ValidID Z n (L n)) ≤ 2 ^ (c' * L n)`
   - **Pigeonhole Principle Lemma (`reaches_short_of_reaches`):** If `c₁` reaches `c₂` within storage $L(n)$ in *any* number of steps, it reaches `c₂` in at most $2^{r}$ steps, where $r = \lceil c' L(n) \rceil$ (using Mathlib's `Relation.ReflTransGen` path-shortening / loop-removal).
2. **Encoding into $\{1, \dots, N\}$:**
   - Define an explicit bijection/injection between `List Δ` of length $\le \lfloor c L(n) \rfloor$ and $\{1, \dots, N\}$ via `Nat.ofDigits`.
   - Crucially, follow Savitch's trick on p. 182: ensure the maximum integer $N$ (the string of all maximal digits $a_m a_m \dots a_m$) **is never a valid ID** (`¬ IsValidID N`), so that `x ⊢ N` is always `False` for every `x`. Savitch relies on this explicitly in the proof of Lemma 1.

---

## 4. How to Perform the Actual Proof

Savitch's proof of Theorem 1 splits cleanly into two layers:
1. **The Abstract Register-Tag State Machine ($Z_D$)** and its correctness (Lemmas 1, 2, and 3 on pp. 181–184).
2. **The Tape Realization & Non-Measurable Space Trick** (pp. 180, 184–185).

Separating these two layers in Lean is essential: proving Lemmas 1, 2, and 3 directly on raw character tapes would require thousands of lines of tedious head-index arithmetic, whereas proving them on the register-tag configuration `<x₁, ..., x_{r+1}>, <T₁, ..., T_{r+1}>` is clean, purely inductive, and faithful to Savitch's paper.

### Step 1: Formalize the Register-Tag Machine $Z_D$ (`SavitchLemma/SavitchAlgorithm.lean`)
Fix input $w$, $r = \lceil c' L(|w|) \rceil$, and upper bound $N$.
Define the state of Savitch's algorithm right before executing `D1 (Test)` (p. 182):
```lean
structure ZDConfig (r N : ℕ) where
  x : Fin (r + 1) → ℕ          -- Register contents (1 ≤ x_i ≤ N, with x_{r+1} = I₀)
  T : Fin (r + 1) → Bool       -- Tag bits (0 or 1, with T_{r+1} = true)
```
Define the one-step transition function `zdStepModified (cfg : ZDConfig r N) : Option (ZDConfig r N)` combining one pass of **D1 (Test)** followed by either **D2 (Clear Storage, modified to not halt on accept)** or **D3 (Back Track)** (p. 181):
- **D1:** Find the smallest $j \le r$ with $T_j = \text{false}$.
  - If all $T_i = \text{true}$, execute **D3**.
  - Otherwise, test if $\exists h$, $T_h = \text{true} \land x_h \vdash_w x_j$ (where $x \vdash_w y$ means $x = y$ or $Z_N$ steps from $x$ to $y$ in 1 step on $w$ within space $L(|w|)$).
    - If **Yes (Modified D2):** Set $T_j \leftarrow \text{true}$, and for all $i < j$, set $x_i \leftarrow 1, T_i \leftarrow \text{false}$.
    - If **No (D3):** Find the smallest $k \le r$ with $x_k \ne N$. (If all $x_i = N$, return `none` / `REJECT`). Set $x_k \leftarrow x_k + 1$, $T_k \leftarrow \text{false}$, and for all $i < k$, set $x_i \leftarrow 1, T_i \leftarrow \text{false}$.

### Step 2: Prove Soundness (p. 182)
Prove by straightforward induction on the number of `zdStepModified` steps:
- **Soundness Invariant (`zd_soundness`):** At any point in the computation starting from `D0` (`x_i = 1, T_i = false` for $i \le r$, `x_{r+1} = I_0, T_{r+1} = true`), for every index $i$, if $T_i = \text{true}$, then `ReachesWithin Z_N w (L w.length) I₀ (cfg.x i)`.
- Why it is simple: `D0` only sets $T_{r+1} = \text{true}$ for $I_0$; `D2` only sets $T_j = \text{true}$ when $\exists h, T_h = \text{true} \land x_h \vdash x_j$; and `D3` only resets tags to `false`.

### Step 3: Prove Lemma 1 (Incrementing Registers, pp. 182–183)
**Statement (`lemma_1`):** For any $1 \le i \le r$ and $1 \le x \le N$, if $Z_D$ is in configuration (1):
$$\langle \underbrace{1, \dots, 1}_{i}, x_{i+1}, \dots, x_r, I_0 \rangle, \quad \langle \underbrace{0, \dots, 0}_{i}, T_{i+1}, \dots, T_r, 1 \rangle$$
then at some later time (`StateTransition.Reaches zdStepModified`), $Z_D$ reaches either:
- **Configuration (2):** $\langle \underbrace{1, \dots, 1}_{i-1}, x, x_{i+1}, \dots, x_r, I_0 \rangle, \langle \underbrace{0, \dots, 0}_{i}, T_{i+1}, \dots, T_r, 1 \rangle$, OR
- **Configuration (3):** $\langle \underbrace{1, \dots, 1}_{j-1}, x_j, x_{j+1}, \dots, x_r, I_0 \rangle, \langle \underbrace{0, \dots, 0}_{j-1}, 1, T_{j+1}, \dots, T_r, 1 \rangle$, where $j > i$ is the least index with $T_j = 0$.

**How to prove it in Lean:**
- Induct on $i$ from $1$ to $r$, and within $i$, induct on $x$ from $1$ to $N$.
- Base case $x = 1$: 0 steps (already in configuration (2)).
- Inductive step $x - 1 \to x$: Assume $Z_D$ does not hit (3). By IH on $x - 1$, $Z_D$ reaches $\langle 1, \dots, 1, x-1, x_{i+1}, \dots \rangle$. Next, apply the outer IH on $i - 1$ with target $N$ repeatedly (or induct on the prefix of $N$'s) to reach $\langle N, \dots, N, x-1, x_{i+1}, \dots \rangle$ with tags $\langle 0, \dots, 0, T_i, T_{i+1}, \dots \rangle$ (where $T_i$ may have become $0$ or $1$).
- Because $N$ is not a valid ID (`¬ IsValidID N`), $x_h \vdash N$ fails for all $h$, so all $i-1$ registers holding $N$ have tag $0$. Thus `D1` picks $j = 1$ (or the first $0$ tag), fails the test, and goes to `D3`.
- In `D3`, since $x_1 = \dots = x_{i-1} = N$ and $x_i = x - 1 < N$, the smallest index with $x_k \ne N$ is $k = i$. `D3` increments $x_i$ to $x$, sets $T_i \leftarrow 0$, and resets $x_1, \dots, x_{i-1} \leftarrow 1$ and $T_1, \dots, T_{i-1} \leftarrow 0$, landing in Configuration (2).

### Step 4: Prove Lemmas 2 and 3 Simultaneously (Divide-and-Conquer Reachability, pp. 183–184)
Savitch proves Lemmas 2 and 3 by simultaneous induction on $j$:
- **Lemma 2(j):** From $\langle \underbrace{1, \dots, 1}_{j-1}, x, x_{j+1}, \dots, x_r, I_0 \rangle, \langle \underbrace{0, \dots, 0}_{j-1}, 0, T_{j+1}, \dots, T_r, 1 \rangle$, if $\exists q > j$ with $T_q = 1$ and $Z_N$ reaches $x$ from $x_q$ in $\le 2^j$ steps, then $Z_D$ later reaches the same configuration with $T_j = 1$.
- **Lemma 3(j):** From $\langle \underbrace{1, \dots, 1}_{j-1}, x_j, \dots, x_{j+p}, x, x_{j+p+2}, \dots, I_0 \rangle, \langle \underbrace{0, \dots, 0}_{j-1}, \underbrace{1, \dots, 1}_{p+1}, 0, T_{j+p+2}, \dots, 1 \rangle$, if $\exists q$ with $T_q = 1$ and $Z_N$ reaches $x$ from $x_q$ in $\le 2^j$ steps, then $Z_D$ later reaches $\langle \underbrace{1, \dots, 1}_{j+p}, x, x_{j+p+2}, \dots, I_0 \rangle, \langle \underbrace{0, \dots, 0}_{j+p}, 1, T_{j+p+2}, \dots, 1 \rangle$.

**How to prove them in Lean:**
- Combine both statements into a single conjunction `∀ j, Lemma2 j ∧ Lemma3 j` and apply induction on $j$.
- **Indexing Simplification (0-based registers):** Index registers by `0 .. r` in Lean (`Fin (r + 1)`), so index $j$ has $j$ registers `0 .. j-1` to its left and checks $2^j$ steps. Then $j = 0$ is the base case ($2^0 = 1$ step, $0$ registers to the left: `D1` immediately sees $x_q \vdash x_0$ and `D2` sets $T_0 \leftarrow 1$). Every $j \ge 1$ then uses the uniform inductive step.
- **Inductive step ($j - 1 \to j$):**
  1. Given a path from $x_q$ to $x$ of length $\le 2^j$, split it at the midpoint (`reachesInSteps_mul_two`) to obtain $y$ such that $x_q \to^{\le 2^{j-1}} y$ and $y \to^{\le 2^{j-1}} x$.
  2. Apply **Lemma 1** with $i = j - 1$ and target $y$. Either $T_j$ becomes $1$ early (done), or $Z_D$ reaches configuration (7) with $x_{j-1} = y$ and $T_{j-1} = 0$.
  3. Apply **IH Lemma 2($j-1$)** (since $x_q \to^{\le 2^{j-1}} y$ and $T_q = 1$) to conclude $Z_D$ reaches configuration (7) with $T_{j-1} = 1$.
  4. Apply **IH Lemma 3($j-1$)** (with $p = 0$, since $y = x_{j-1}$ now has $T_{j-1} = 1$ and $y \to^{\le 2^{j-1}} x$) to conclude $Z_D$ reaches configuration (4) with $T_j = 1$ and all registers $< j$ cleared to $1$.
  5. Prove Lemma 3($j$) identically (applying Lemma 1 to place $y$ in register $j-1$, IH Lemma 2($j-1$) to set $T_{j-1} = 1$, and IH Lemma 3($j-1$) with $p' = p + 1$ to set $T_{j+p+1} = 1$ and clear registers).

### Step 5: Complete Theorem 1 (`SavitchLemma/MainTheorem.lean`)
1. **Measurable Case:**
   - Suppose $Z_N$ accepts $w$ within space $L(|w|)$. By `reaches_short_of_reaches`, there is an accepting ID $x_{acc}$ reachable from $I_0$ in $\le 2^r$ steps.
   - Starting from `D0`, apply **Lemma 1** ($i = r$, $x = x_{acc}$) to reach configuration (8): $\langle 1, \dots, 1, x_{acc}, I_0 \rangle, \langle 0, \dots, 0, 0, 1 \rangle$.
   - Apply **Lemma 2($r$)** (with $q = r + 1$, so $x_q = I_0, T_q = 1$) to reach configuration (8) with $T_r = 1$.
   - In the unmodified `D2`, at the moment $T_r$ (or any $T_j$ with $x_j$ accepting) would be set to $1$, $Z_D$ accepts $w$.
   - Space analysis: $r + 1 = \lceil c' L(n) \rceil + 1$ registers of size $\lfloor c L(n) \rfloor$ plus $r + 1$ tag bits uses $O(L(n)^2)$ cells, which reduces to $L(n)^2$ by alphabet compression (`TapeReduction`).
2. **Non-Measurable Iterative Deepening Case (pp. 184–185):**
   - If $L(n)$ is not measurable, $Z_D$ loops over $s = 1, 2, 3, \dots$, running the measurable algorithm assuming $L(n) = s$.
   - For each $s$, the algorithm is terminating (since `D3` strictly increments the $(r+1)$-digit base-$N$ counter on every backtrack and `D2` can only fire $N$ times per increment).
   - If $w \in A$, let $s_0 \le L(|w|)$ be the minimum storage used by an accepting computation of $Z_N$ on $w$. Then $Z_D$ rejects for $1 \le s < s_0$ and accepts at $s = s_0$, never scanning more than $s_0^2 \le L(|w|)^2$ squares.
   - If $w \notin A$, $Z_D$ rejects for every $s$ and diverges, hence never accepts $w$ (satisfying Savitch's definition of acceptance on p. 179).

### Step 6: Extensions in the Paper (Optional / Modular Milestones)
- **Theorem 2 & Corollary 2 (p. 185):** Replace $r = \lceil c' L(n) \rceil$ with $r = \lceil \log_2 T(n) \rceil$ in the exact same `ZDConfig` proof to get deterministic space $L(n) \log_2 T(n)$.
- **Theorem 3 & Corollary 3 (Padding / Upward Translation, pp. 186–187):** Formalize the padded language $A = \{w \beta^h \mid w \in B \land |w| + h \ge k(|w|)\}$ to prove that $\text{NSPACE}(L(n)) = \text{DSPACE}(L(n))$ translates upward to $H(n) \ge L(n)$.
- **Section 3: Mazes and Theorems 4 & 5 (`SavitchLemma/Mazes.lean`, pp. 187–191):**
  - Define `Maze Σ` (`X : Finset (List Σ)`, `R : List Σ → List Σ → Prop`, `s : List Σ`, `G : Finset (List Σ)`) and `Maze.IsThreadable := ∃ g ∈ G, Relation.ReflTransGen R s g`.
  - Savitch's core algorithm in Theorem 1 is a deterministic solver for `Maze.IsThreadable` on a maze of size $N \le 2^r$ using $r$ registers.

---

## 5. Recommended Execution Order & Engineering Tips

1. **Prove Lemmas 1–3 on an abstract Maze / Transition Relation first:**
   Notice that `ZDConfig` and steps `D0`–`D3` only depend on `N : ℕ`, `I₀ : ℕ`, `IsAccepting : ℕ → Bool`, and a decidable relation `Step : ℕ → ℕ → Bool` (with `¬ Step x N`). Formalizing `SavitchAlgorithm.lean` for an arbitrary finite relation first lets you complete the hardest part of the proof (Lemmas 1, 2, 3) without Turing-machine tape overhead.
2. **Use 0-based indexing (`Fin (r + 1)`) for registers:**
   Having register $j \in \{0, \dots, r-1\}$ verify paths of length $\le 2^j$ using registers $\{0, \dots, j-1\}$ makes the base case $j = 0$ ($2^0 = 1$ step, 0 auxiliary registers) immediate and avoids off-by-one arithmetic in Lean.
3. **Define a lexicographic termination measure for `zdStepModified`:**
   Even though Lemmas 1–3 only assert reachability (`∃ t, step^[t] cfg = cfg'`), proving that `zdStepModified` always terminates (needed for the non-measurable $L(n)$ loop in Theorem 1) is straightforward by exhibiting the potential function witnessing that each step either sets a tag bit from `0` to `1` or lexicographically increments `(x_r, x_{r-1}, ..., x_1)`.

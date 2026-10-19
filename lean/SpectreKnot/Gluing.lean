/-
A patch glued from children (paper §4.1 and §5): the general setting of Lemma 4.2 and Prop 5.4.

Child `c` has `E c` rim vertices `0 … E c - 1`, numbered in its orientation (all children in the same rotational
sense); edge `k` runs from vertex `k` to vertex `k+1`. Each child carries the signature's pairing at its crossover
corners `A c`, `B c` (Def 4.3, `tau`). `mate c k = some (c', k')` says that edge `k` of child `c` is edge `k'` of child
`c'`, traversed the other way; `none` says that it lies on the parent's rim. Nothing here refers to the tables: Prop 5.4
is proved for every gluing that is well formed (`WF`). `WF` asks only that each child's corners be distinct, not that
they be adjacent, and nothing about the children's interiors, so Prop 5.4 is proved a little more generally than the
paper states it.
-/
import SpectreKnot.Basic
import SpectreKnot.Box

namespace SpectreKnot

-- `nxt` and `prv`, the cyclic successor and predecessor on `0 … E-1`, are in `Basic.lean`.

/-- The successor of a vertex is a vertex. -/
theorem nxt_lt {E x : Nat} (x_lt : x < E) : nxt E x < E := by unfold nxt; split <;> omega

/-- The predecessor of a vertex is a vertex. -/
theorem prv_lt {E x : Nat} (x_lt : x < E) : prv E x < E := by unfold prv; split <;> omega

/-- The predecessor undoes the successor. -/
theorem prv_nxt {E x : Nat} (_x_lt : x < E) : prv E (nxt E x) = x := by
  unfold nxt prv; split <;> split <;> omega

/-- The successor undoes the predecessor. -/
theorem nxt_prv {E x : Nat} (x_lt : x < E) : nxt E (prv E x) = x := by
  unfold nxt prv; split <;> split <;> omega

/-- Any number of steps forwards round the rim from a vertex lands on a vertex. -/
theorem iter_nxt_lt {E u : Nat} (u_lt : u < E) (k : Nat) : iter (nxt E) k u < E := by
  induction k with
  | zero => exact u_lt
  | succ k ih => exact nxt_lt ih

/-- Any number of steps backwards round the rim from a vertex lands on a vertex. -/
theorem iter_prv_lt {E u : Nat} (u_lt : u < E) (k : Nat) : iter (prv E) k u < E := by
  induction k with
  | zero => exact u_lt
  | succ k ih => exact prv_lt ih

/-- Going round the rim: `k ≤ E` steps from `u` land at `u + k`, reduced once. -/
theorem iter_nxt_eq {E u : Nat} (u_lt : u < E) (k : Nat) (k_le : k ≤ E) :
    iter (nxt E) k u = if u + k < E then u + k else u + k - E := by
  induction k with
  | zero => simp [u_lt]
  | succ k ih =>
    rw [iter_succ, ih (by omega)]
    unfold nxt
    split <;> split <;> split <;> omega

/-- Every vertex is reached within `1 … E` steps. -/
theorem iter_nxt_cover {E u v : Nat} (u_lt : u < E) (v_lt : v < E) :
    ∃ j, 1 ≤ j ∧ j ≤ E ∧ iter (nxt E) j u = v := by
  by_cases u_lt_v : u < v
  · exact ⟨v - u, by omega, by omega, by rw [iter_nxt_eq u_lt _ (by omega)]; split <;> omega⟩
  · -- go round past vertex 0
    exact ⟨v + E - u, by omega, by omega, by rw [iter_nxt_eq u_lt _ (by omega)]; split <;> omega⟩

/-- Rim ports are `(c, u, s)`: `R_c(u)` if `s = true`, `L_c(u)` if `false`. -/
abbrev GPort := Nat × Nat × Bool

/-- The data of a patch glued from children. -/
structure Gluing where
  n : Nat
  E : Nat → Nat
  A : Nat → Nat
  B : Nat → Nat
  mate : Nat → Nat → Option (Nat × Nat)

namespace Gluing

variable (G : Gluing)

/-- A port of an actual child, at an actual rim vertex. -/
def Valid (p : GPort) : Prop := p.1 < G.n ∧ p.2.1 < G.E p.1

/-- Well-formed: every child has a rim with its corners on it, and gluing pairs edges of children with each other. -/
structure WF : Prop where
  E_pos : ∀ c, c < G.n → 0 < G.E c
  A_lt : ∀ c, c < G.n → G.A c < G.E c
  B_lt : ∀ c, c < G.n → G.B c < G.E c
  A_ne_B : ∀ c, c < G.n → G.A c ≠ G.B c
  mate_valid : ∀ c k c' k', c < G.n → k < G.E c → G.mate c k = some (c', k') →
    c' < G.n ∧ k' < G.E c' ∧ G.mate c' k' = some (c, k)

/-- `WF` as a computation, for concrete gluings. -/
def wfCheck : Bool :=
  (List.range G.n).all fun c =>
    decide (0 < G.E c) && decide (G.A c < G.E c) && decide (G.B c < G.E c) && G.A c != G.B c &&
    (List.range (G.E c)).all fun k =>
      match G.mate c k with
      | none => true
      | some (c', k') => decide (c' < G.n) && decide (k' < G.E c') && G.mate c' k' == some (c, k)

/-- If `wfCheck` returns `true`, the gluing is well formed. -/
theorem wfCheck_sound (checked : G.wfCheck = true) : G.WF := by
  simp only [wfCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at checked
  refine ⟨fun c c_lt => (checked c c_lt).1.1.1.1, fun c c_lt => (checked c c_lt).1.1.1.2,
    fun c c_lt => (checked c c_lt).1.1.2, fun c c_lt => (checked c c_lt).1.2, fun c k c' k' c_lt k_lt glued => ?_⟩
  -- what the check says about edge `k` of child `c`, which is glued to edge `k'` of `c'`
  have edge_ok := (checked c c_lt).2 k k_lt
  rw [glued] at edge_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at edge_ok
  exact ⟨edge_ok.1.1, edge_ok.1.2, edge_ok.2⟩

/-! ### The full walk (Lemma 4.2) -/

/-- `u` is a crossover corner of child `c`. -/
def corner (c u : Nat) : Bool := u == G.A c || u == G.B c

/-- `τ`: inside a child, by its signature (Def 4.3): a hook at every rim vertex but the corners, where
`R(A) ↔ R(B)` and `L(A) ↔ L(B)`. -/
def tau : GPort → GPort
  | (c, u, s) => if u = G.A c then (c, G.B c, s) else if u = G.B c then (c, G.A c, s) else (c, u, !s)

/-- `σ`: the straight-through rule (Def 3.2). `R_c(u)` lies on edge `u` near `u`; if that edge is edge `k'` of `c'`,
it is joined to the port of `c'` on it near the other end, `R_{c'}(k')`. `L_c(u)` lies on edge `u-1` near `u`, and is
joined to `L_{c'}(k'+1)`. `none` on the parent's rim. -/
def sigma : GPort → Option GPort
  | (c, u, true) => (G.mate c u).map fun (c', k') => (c', k', true)
  | (c, u, false) => (G.mate c (prv (G.E c) u)).map fun (c', k') => (c', nxt (G.E c') k', false)

/-- Lemma 4.2, as a relation: from port `x`, `FReach k x r` says that alternately applying `τ` and `σ`, with `k`
crossings, ends at the rim port `r` of the parent. -/
inductive FReach (G : Gluing) : Nat → GPort → GPort → Prop
  | stop {x : GPort} : G.sigma (G.tau x) = none → FReach G 0 x (G.tau x)
  | step {k : Nat} {x y r : GPort} : G.sigma (G.tau x) = some y → FReach G k y r → FReach G (k + 1) x r

/-- The full walk from `x` ends at `r`. For a rim port `x` of the parent, `r` is `π_P(x)` (Lemma 4.2). -/
def FullReach (x r : GPort) : Prop := ∃ k, G.FReach k x r

/-! ### Marks, runs and the reduced walk (Def 5.2, Prop 5.4) -/

/-- Vertex `x` of child `c` is *smooth* if a run passes straight through it: it is not a crossover corner of `c`,
and either both rim edges of `c` at `x` lie on the parent's rim, or both are glued to the same sibling `c'`, along
consecutive edges of `c'`, at a vertex of `c'` that is not a crossover corner of `c'`. A vertex that is not smooth is
a *mark* (Def 5.2: a junction or a crossover corner of either side). -/
def smooth (c x : Nat) : Bool :=
  !G.corner c x &&
  match G.mate c x, G.mate c (prv (G.E c) x) with
  | none, none => true
  | some (c', k'), some (c'', k'') => c'' == c' && k'' == nxt (G.E c') k' && !G.corner c' (nxt (G.E c') k')
  | _, _ => false

/-- Search for the next mark: `firstMark c x k f` checks the vertices `x, nxt x, …` (numbered `k, k+1, …`), at most
`f` of them, and returns the number of the first mark, or `k + f` if there is none. -/
def firstMark (c : Nat) : Nat → Nat → Nat → Nat
  | _, k, 0 => k
  | x, k, f + 1 => if G.smooth c x then firstMark c (nxt (G.E c) x) (k + 1) f else k

/-- The length of the run of child `c` that starts at vertex `u`: the distance to the next mark (at most `E c`). -/
def runLen (c u : Nat) : Nat := G.firstMark c (nxt (G.E c) u) 1 (G.E c - 1)

/-- The reduced `σ` of Prop 5.4: across a whole run at once, by the zigzag lemma. From `R_c(u)` the run of `c` from
`u` has length `n`; from `L_c(u)` the run is that of the sibling `c'`, from the vertex `k` of `c'` at `u`. Even `n`:
back to the same child at the far end; odd `n`: to the sibling. -/
def sigmaRed : GPort → Option GPort
  | (c, u, true) =>
    match G.mate c u with
    | none => none
    | some (c', k') =>
      let n := G.runLen c u
      some (if n % 2 = 0 then (c, iter (nxt (G.E c)) n u, false)
        else (c', iter (prv (G.E c')) n (nxt (G.E c') k'), true))
  | (c, u, false) =>
    match G.mate c (prv (G.E c) u) with
    | none => none
    | some (c', k) =>
      let n := G.runLen c' k
      some (if n % 2 = 0 then (c, iter (prv (G.E c)) n u, true)
        else (c', iter (nxt (G.E c')) n k, false))

/-- The reduced walk: alternately `τ` and `σ_red`. -/
inductive RedReach (G : Gluing) : GPort → GPort → Prop
  | stop {x : GPort} : G.sigmaRed (G.tau x) = none → RedReach G x (G.tau x)
  | step {x y r : GPort} : G.sigmaRed (G.tau x) = some y → RedReach G y r → RedReach G x r

/-! ### Computable walks -/

/-- The full walk as a computation with fuel: `none` if the fuel runs out. -/
def fullWalk : Nat → GPort → Option GPort
  | 0, _ => none
  | f + 1, x =>
    match G.sigma (G.tau x) with
    | none => some (G.tau x)
    | some y => fullWalk f y

/-- The reduced walk as a computation with fuel: `none` if the fuel runs out. -/
def redWalk : Nat → GPort → Option GPort
  | 0, _ => none
  | f + 1, x =>
    match G.sigmaRed (G.tau x) with
    | none => some (G.tau x)
    | some y => redWalk f y

/-- If the computed full walk from `x` ends at `r`, then `FullReach x r`. -/
theorem fullWalk_sound {f : Nat} {x r : GPort} (walk_eq : G.fullWalk f x = some r) : G.FullReach x r := by
  induction f generalizing x with
  | zero => simp [fullWalk] at walk_eq
  | succ f ih =>
    simp only [fullWalk] at walk_eq
    split at walk_eq
    · -- on the parent's rim: the walk stops here
      rename_i on_rim; cases walk_eq; exact ⟨0, .stop on_rim⟩
    · -- across to `y`, and on from there
      rename_i y crosses; obtain ⟨k, rest⟩ := ih walk_eq; exact ⟨k + 1, .step crosses rest⟩

/-- If the computed reduced walk from `x` ends at `r`, then `RedReach x r`. -/
theorem redWalk_sound {f : Nat} {x r : GPort} (walk_eq : G.redWalk f x = some r) : G.RedReach x r := by
  induction f generalizing x with
  | zero => simp [redWalk] at walk_eq
  | succ f ih =>
    simp only [redWalk] at walk_eq
    split at walk_eq
    · -- on the parent's rim: the walk stops here
      rename_i on_rim; cases walk_eq; exact .stop on_rim
    · -- across the run to `y`, and on from there
      rename_i y crosses; exact .step crosses (ih walk_eq)

end Gluing

end SpectreKnot

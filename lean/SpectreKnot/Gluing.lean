/-
A patch glued from children (the paper's §4 and §7.1): the setting of Lemma 4.2, for compositions.

Child `c` has `E c` rim vertices `0 … E c - 1`, numbered in its orientation (all children in the same rotational
sense); edge `k` runs from vertex `k` to vertex `k+1`. Each child carries the signature's pairing at its crossover
corners `A c`, `B c` (Def 4.3, `tau`). `mate c k = some (c', k')` says that edge `k` of child `c` is edge `k'` of child
`c'`, traversed the other way; `none` says that it lies on the parent's rim. Nothing here refers to the tables. Results
about gluings assume at most that they are well formed (`WF`), which asks only that each child's corners be distinct,
not that they be adjacent, and nothing about the children's interiors.
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

/-- Rim ports are `(c, u, s)`: `R_c(u)` if `s = true`, `L_c(u)` if `false`. -/
abbrev GPort := Nat × Nat × Bool

/-- `R` as `true`, `L` as `false`, as in `GPort`. -/
def Hand.isR : Hand → Bool
  | .R => true
  | .L => false

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

section

variable {G}

/-- A vertex that is not a crossover corner is neither `A` nor `B`. -/
theorem corner_false {c u : Nat} (not_corner : G.corner c u = false) : u ≠ G.A c ∧ u ≠ G.B c := by
  simp [corner] at not_corner; exact not_corner

/-- Away from the crossover corners, `τ` is the hook: it swaps `L` and `R` at the same vertex. -/
theorem tau_of_not_corner {c u : Nat} {s : Bool} (not_corner : G.corner c u = false) :
    G.tau (c, u, s) = (c, u, !s) := by
  obtain ⟨ne_A, ne_B⟩ := corner_false not_corner
  simp [tau, ne_A, ne_B]

/-- In a well-formed gluing, `τ` sends a port of an actual child to a port of the same child. -/
theorem tau_valid (wf : G.WF) {x : GPort} (x_valid : G.Valid x) : G.Valid (G.tau x) := by
  obtain ⟨c, u, s⟩ := x
  obtain ⟨c_lt, u_lt⟩ := x_valid
  simp only [tau]
  split
  · exact ⟨c_lt, wf.B_lt c c_lt⟩
  · split
    · exact ⟨c_lt, wf.A_lt c c_lt⟩
    · exact ⟨c_lt, u_lt⟩

end

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

/-! ### Computable walks -/

/-- The full walk as a computation with fuel: `none` if the fuel runs out. -/
def fullWalk : Nat → GPort → Option GPort
  | 0, _ => none
  | f + 1, x =>
    match G.sigma (G.tau x) with
    | none => some (G.tau x)
    | some y => fullWalk f y

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

end Gluing

end SpectreKnot

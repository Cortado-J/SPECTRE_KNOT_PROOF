/-
The abstract composition of paper §7.1, built in Lean from the tables, and its box computed by gluing (Lemma 4.2),
port by port, with no reduction.

`Comp.ofPattern T λ d ω` is the composition `P = ⋃ X_c` of §7.1: child `c` is a hexagon of kind `K_c` (Table 1)
whose side `j` has `λ(letter)` edges (Table 4); its crossover corners are `A_c` (vertex 0, or for Σ the point of side 5
at distance `d` from vertex 5) and `B_c = A_c + ω`; sides are glued in pairs by Table 2, reversing direction; the
parent's rim is listed by Table 3. Every child is given the signature box (Def 4.3). `Comp.toGluing` makes it a
`Gluing`, whose full walk computes the parent's box exactly as Lemma 4.2 says.

`Comp.check` tests the conclusion of the induction step, and `check_sound` says what a `true` means: the parent has no
closed strand and has the signature at the Γ child's corners. Run at `(ℓ₁, d₁, ±1)` for the nine kinds, this is
Computation 7.3, from the tables alone and without the reduced walk or the exported skeletons.
-/
import SpectreKnot.Lengths
import SpectreKnot.Gluing

namespace SpectreKnot.Compose

open Pattern

/-- `prefixSums [l₀, …, l₅] 0 = [0, l₀, l₀+l₁, …, E]`. -/
def prefixSums : List Nat → Nat → List Nat
  | [], a => [a]
  | x :: xs, a => a :: prefixSums xs (a + x)

/-- A child of the composition. Rim vertices and rim edges are numbered `0 … E-1` in the child's own order; edge `k`
runs from vertex `k` to vertex `k+1`. -/
structure Kid where
  kind : Kind
  len : List Nat
  U : List Nat
  E : Nat
  A : Nat
  B : Nat
  deriving Repr

/-- A child of kind `K` whose sides `0 … 5` have the lengths `len`, with Σ offset `d` and sign `ω` (`true` for
`+1`): its crossover corner `A` is vertex 0, or for Σ the point of side 5 at distance `d` from vertex 5, and
`B = A + ω`. -/
def mkKidL (K : Kind) (len : List Nat) (d : Nat) (ω : Bool) : Kid :=
  let U := prefixSums len 0
  let E := U.getD 6 0
  let A := if K = .Sigma then U.getD 5 0 + d else 0
  let B := if ω then nxt E A else prv E A
  ⟨K, len, U, E, A, B⟩

/-- A composition: the parent's kind and its children. -/
structure Comp where
  T : Kind
  kids : List Kid

/-- The composition of kind `T` in which side `j` of child `c` has `L c j` edges. (Used for the parity lemma, where
sides are lengthened one pair at a time.) -/
def Comp.ofLens (T : Kind) (L : Nat → Nat → Nat) (d : Nat) (ω : Bool) : Comp :=
  ⟨T, (List.range (Pattern.kids T).length).map fun c => mkKidL (kidAt T c) ((List.range 6).map (L c)) d ω⟩

/-- The composition of §7.1: every side with letter `x` has `lam x` edges. -/
def Comp.ofPattern (T : Kind) (lam : Letter → Nat) (d : Nat) (ω : Bool) : Comp :=
  Comp.ofLens T (fun c j => lam (letterOf (kidAt T c) j)) d ω

namespace Comp

variable (C : Comp)

/-- Child `c` (a dummy one-vertex child if there is none). -/
def kid (c : Nat) : Kid := C.kids.getD c ⟨.Gamma, [], [], 1, 0, 0⟩

/-- `sideIdx U k i`: the last `j ≤ i` with `U[j] ≤ k`, or 0. -/
def sideIdx (U : List Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => if U.getD (i + 1) 0 ≤ k then i + 1 else sideIdx U k i

/-- The side of child `c` containing edge `k`, and the offset of `k` in it. -/
def sideOf (c k : Nat) : Nat × Nat :=
  let U := (C.kid c).U
  let j := sideIdx U k 5
  (j, k - U.getD j 0)

/-- Table 2 with direction reversed: edge `k` of child `c` is edge `mate c k` of a sibling, or on the parent's rim. -/
def mate (c k : Nat) : Option (Nat × Nat) :=
  let (j, o) := C.sideOf c k
  match ((adj C.T).getD c []).getD j none with
  | none => none
  | some (c', j') =>
    let k' := C.kid c'
    some (c', k'.U.getD j' 0 + k'.len.getD j' 0 - 1 - o)

/-- The composition as a gluing of children with the signature. -/
def toGluing : Gluing :=
  ⟨C.kids.length, fun c => (C.kid c).E, fun c => (C.kid c).A, fun c => (C.kid c).B, C.mate⟩

/-- All ports of all children. -/
def ports : List GPort :=
  (List.range C.kids.length).flatMap fun c =>
    (List.range (C.kid c).E).flatMap fun u => [(c, u, true), (c, u, false)]

/-- Every port of an actual child is in the list `ports`. -/
theorem mem_ports {x : GPort} (x_valid : C.toGluing.Valid x) : x ∈ C.ports := by
  obtain ⟨c, u, s⟩ := x
  obtain ⟨c_lt, u_lt⟩ := x_valid
  simp only [ports, List.mem_flatMap, List.mem_range]
  exact ⟨c, c_lt, u, u_lt, by cases s <;> simp⟩

/-- Enough fuel for any walk: a walk never repeats a port. -/
def fuel : Nat := C.ports.length + 1

/-- The parent's rim edges `(c, k)` in the children's rotational sense, from Table 3 (which lists the parent's sides in
the parent's own order, the opposite sense). -/
def rimEdges : List (Nat × Nat) :=
  let own := ((pside C.T).flatMap id).flatMap fun (c, j) =>
    let k := C.kid c
    (List.range (k.len.getD j 0)).map fun i => (c, k.U.getD j 0 + k.len.getD j 0 - 1 - i)
  own.reverse

/-- The parent's rim ports at the vertex between consecutive rim edges `e₁ = (c₁, k₁)` and `e₂ = (c₂, k₂)`:
`L` on `e₁` and `R` on `e₂`. -/
def rimVertexPorts : List (GPort × GPort) :=
  let es := C.rimEdges
  let n := es.length
  (List.range n).map fun t =>
    let (c₁, k₁) := es.getD t (0, 0)
    let (c₂, k₂) := es.getD ((t + 1) % n) (0, 0)
    ((c₁, nxt (C.kid c₁).E k₁, false), (c₂, k₂, true))

/-- Rim vertex number `t` of the parent, as its pair of ports. -/
def vtx (t : Nat) : GPort × GPort := C.rimVertexPorts.getD t ((0, 0, false), (0, 0, false))

/-- The rim indices of the Γ child's crossover corners `A` and `B` (the Γ child is the last). -/
def tA : Nat :=
  let g := C.kids.length - 1
  (C.rimVertexPorts.findIdx? fun (_, pR) => pR == (g, (C.kid g).A, true)).getD C.rimVertexPorts.length

/-- The rim index of the Γ child's crossover corner `B` (see `tA`). -/
def tB : Nat :=
  let g := C.kids.length - 1
  (C.rimVertexPorts.findIdx? fun (_, pR) => pR == (g, (C.kid g).B, true)).getD C.rimVertexPorts.length

/-- The conclusion of the induction step for this composition (see `check_sound` for what `true` means):
(1) the gluing is well formed;
(2) no closed strand: the walk from every port ends on the parent's rim;
(3) a hook at every parent rim vertex except the Γ child's corners `A` and `B`;
(4) `A` and `B` are rim vertices of the parent and adjacent, `B` after `A` in the children's sense if `ω = +1` and
before it if `ω = -1` (so `B = A + ω_{m+1}` in the parent's own order, the opposite sense);
(5) the crossover `R(A) ↔ R(B)`, `L(A) ↔ L(B)`. -/
def check (ω : Bool) : Bool :=
  let G := C.toGluing
  let n := C.rimVertexPorts.length
  G.wfCheck &&
  (C.ports.all fun x => (G.fullWalk C.fuel x).isSome) &&
  ((List.range n).all fun t => t == C.tA || t == C.tB || G.fullWalk C.fuel (C.vtx t).1 == some (C.vtx t).2) &&
  decide (C.tA < n) && decide (C.tB < n) &&
  C.tB == (if ω then (C.tA + 1) % n else (C.tA + n - 1) % n) &&
  G.fullWalk C.fuel (C.vtx C.tA).2 == some (C.vtx C.tB).2 &&
  G.fullWalk C.fuel (C.vtx C.tA).1 == some (C.vtx C.tB).1

/-- What `check` establishes, as theorems about the gluing (`FullReach x r`: the parent's arcs join `x` to `r`). -/
theorem check_sound {ω : Bool} (checked : C.check ω = true) :
    let G := C.toGluing
    let n := C.rimVertexPorts.length
    G.WF ∧
    (∀ x, G.Valid x → ∃ r, G.FullReach x r) ∧
    (∀ t, t < n → t ≠ C.tA → t ≠ C.tB → G.FullReach (C.vtx t).1 (C.vtx t).2) ∧
    C.tA < n ∧ C.tB < n ∧ C.tB = (if ω then (C.tA + 1) % n else (C.tA + n - 1) % n) ∧
    G.FullReach (C.vtx C.tA).2 (C.vtx C.tB).2 ∧ G.FullReach (C.vtx C.tA).1 (C.vtx C.tB).1 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨wf_checked, all_end⟩, hooks⟩, A_lt⟩, B_lt⟩, adjacent⟩, cross_R⟩, cross_L⟩ := checked
  refine ⟨Gluing.wfCheck_sound _ wf_checked, fun x x_valid => ?_, fun t t_lt ne_A ne_B => ?_, A_lt, B_lt, adjacent,
    Gluing.fullWalk_sound _ cross_R, Gluing.fullWalk_sound _ cross_L⟩
  · have ends := all_end x (C.mem_ports x_valid)  -- the computed walk from `x` ends within the fuel
    cases walk_eq : C.toGluing.fullWalk C.fuel x with
    | none => rw [walk_eq] at ends; contradiction
    | some r => exact ⟨r, Gluing.fullWalk_sound _ walk_eq⟩
  · rcases hooks t t_lt with (is_A | is_B) | hook
    · exact absurd is_A ne_A
    · exact absurd is_B ne_B
    · exact Gluing.fullWalk_sound _ hook

end Comp

end SpectreKnot.Compose

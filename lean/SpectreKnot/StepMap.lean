/-
**The junction map of the nest** (the paper's Computation 9.2 and Lemma 9.3), one level at a time. In the Δ composition, child 1 is the previous block of
the nest. Every arc of child 1 lies on a parent hook at a *junction*, the vertex where piece `q` of Table 3 starts, and
`q` depends only on where the arc is on child 1's rim and on the sign `ω` (`tgt`); the arcs on child 1's side 2,
which lies on the parent's rim, are parent hooks themselves. `StepOK` states this; it is checked by the kernel at the
level-1 lengths (`step_base`) and carried to every admissible `(L, d)` by moves (`StepOK.move`, `adm_step`), as the
signature was in `Parity.lean`.
-/
import SpectreKnot.ProofA
import SpectreKnot.NewWalk

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### The map -/

/-- Piece `q` of the Δ-supertile's rim (Table 3, flattened). -/
abbrev pieceD (q : Nat) : Nat × Nat := (pcs .Delta).getD q (0, 0)

/-- The port `R` of the parent hook at the start of piece `q`, as a port of the composition: the child vertex where
piece `q`'s side ends, in the children's sense (port `L` there). -/
def jR (L : Nat → Nat → Nat) (q : Nat) : GPort :=
  ((pieceD q).1, pos (L (pieceD q).1) (((pieceD q).2 + 1) % 6), false)

/-- The port `L` of the same parent hook: the child vertex where piece `q - 1`'s side begins (port `R` there). -/
def jL (L : Nat → Nat → Nat) (q : Nat) : GPort :=
  ((pieceD (q - 1)).1, pos (L (pieceD (q - 1)).1) (pieceD (q - 1)).2, true)

/-- Where an arc of child 1 goes: the junction (a piece number) of the parent hook it lies on, for the port `s` at
rim vertex `u` of child 1 (side lengths `f`); `none` for a vertex inside side 2 (a parent hook itself). Child 1's
corners are `A = 0` and `B = 1` (`ω`) or `B = E - 1` (not `ω`); their arcs are the crossover arcs. -/
def tgt (ω : Bool) (f : Nat → Nat) (u : Nat) (s : Bool) : Option Nat :=
  if ω then
    if u = 0 ∨ u = 1 then some (if s then 17 else 9)
    else if u ≤ pos f 2 then some 17 else if u < pos f 3 then none else if u < pos f 4 then some 16
    else if u < pos f 5 then some 12 else some 9
  else
    if u = 0 ∨ u = pos f 6 - 1 then some (if s then 21 else 16)
    else if u ≤ pos f 1 then some 21 else if u ≤ pos f 2 then some 17 else if u < pos f 3 then none else some 16

/-- The junction for a vertex well inside side `j` of child 1. -/
def sideTgt (ω : Bool) (j : Nat) : Option Nat :=
  if ω then (if j ≤ 1 then some 17 else if j = 2 then none else if j = 3 then some 16 else if j = 4 then some 12
    else some 9)
  else (if j = 0 then some 21 else if j = 1 then some 17 else if j = 2 then none else some 16)

/-- **The junction map holds**: the walk from every port of child 1 (outside side 2) ends at a port of the parent hook
at the junction `tgt` names. -/
def StepOK (L : Nat → Nat → Nat) (d : Nat) (ω : Bool) : Prop :=
  ∀ u, u < pos (L 1) 6 → ∀ s q, tgt ω (L 1) u s = some q →
    ∃ r, (Comp.ofLens .Delta L d ω).toGluing.FullReach (1, u, s) r ∧ (r = jR L q ∨ r = jL L q)

/-- Well inside side `j`, the map depends only on `j`: at a vertex `u` at least two edges from both ends of side `j`
of child 1 (side lengths `f`), `tgt` is `sideTgt ω j`, for either port `s`. -/
theorem tgt_side {ω : Bool} {f : Nat → Nat} {j u : Nat} (s : Bool) (hj : j < 6) (after_start : pos f j + 2 ≤ u)
    (before_end : u + 2 ≤ pos f (j + 1)) : tgt ω f u s = sideTgt ω j := by
  -- the sides start in order round the rim
  have mono : ∀ a b, a ≤ b → pos f a ≤ pos f b := fun a b a_le_b => pos_mono f a_le_b
  -- side 0 starts at vertex 0
  have p0 : pos f 0 = 0 := rfl
  -- side `j` ends before the rim does
  have end_le := mono (j + 1) 6 (by omega)
  -- the starts of sides 1 to 5, in order
  have order : pos f 1 ≤ pos f 2 ∧ pos f 2 ≤ pos f 3 ∧ pos f 3 ≤ pos f 4 ∧ pos f 4 ≤ pos f 5 :=
    ⟨mono 1 2 (by omega), mono 2 3 (by omega), mono 3 4 (by omega), mono 4 5 (by omega)⟩
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · have before_end : u + 2 ≤ pos f 1 := before_end -- side 0 ends where side 1 starts
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true] <;>
      rw [ite_eq_right (by omega), ite_eq_left (by omega)] <;> simp
  · have before_end : u + 2 ≤ pos f 2 := before_end -- side 1 ends where side 2 starts
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; simp
  · have before_end : u + 2 ≤ pos f 3 := before_end -- side 2 ends where side 3 starts
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp
  · have before_end : u + 2 ≤ pos f 4 := before_end -- side 3 ends where side 4 starts
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp
  · have before_end : u + 2 ≤ pos f 5 := before_end -- side 4 ends where side 5 starts
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)]; simp
  · have before_end : u + 2 ≤ pos f 6 := before_end -- side 5 ends where the rim ends
    cases ω <;> simp only [tgt, sideTgt, Bool.false_eq_true, ite_false, ite_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]; simp

/-! ### The base case: the kernel's check at the level-1 lengths -/

/-- The checks of `StepOK` at `(ℓ₁, d₁)`. -/
def stepCheck (ω : Bool) : Bool :=
  let C := Comp.ofLens .Delta (L₁ .Delta) (dOff 1) ω
  (List.range (pos (L₁ .Delta 1) 6)).all fun u => [true, false].all fun s =>
    match tgt ω (L₁ .Delta 1) u s with
    | none => true
    | some q =>
      C.toGluing.fullWalk C.fuel (1, u, s) == some (jR (L₁ .Delta) q) ||
        C.toGluing.fullWalk C.fuel (1, u, s) == some (jL (L₁ .Delta) q)

/-- The kernel's check passes at the level-1 lengths for `ω = true`. -/
theorem stepCheck_true : stepCheck true = true := by decide +kernel
/-- The kernel's check passes at the level-1 lengths for `ω = false`. -/
theorem stepCheck_false : stepCheck false = true := by decide +kernel

/-- The check is sound: if it passes, the junction map holds at `(ℓ₁, d₁)`. -/
theorem stepCheck_sound {ω : Bool} (check : stepCheck ω = true) : StepOK (L₁ .Delta) (dOff 1) ω := by
  intro u hu s q tgt_eq
  simp only [stepCheck, List.all_eq_true, List.mem_range] at check
  -- the check at vertex `u` and port `s`
  have at_port := check u hu s (by cases s <;> simp)
  rw [tgt_eq] at at_port
  simp only [Bool.or_eq_true, beq_iff_eq] at at_port
  rcases at_port with walk_R | walk_L
  · exact ⟨_, fullWalk_sound _ walk_R, Or.inl rfl⟩
  · exact ⟨_, fullWalk_sound _ walk_L, Or.inr rfl⟩

/-- **The base case**: the junction map holds at the level-1 lengths `(ℓ₁, d₁)`, for both signs. -/
theorem step_base (ω : Bool) : StepOK (L₁ .Delta) (dOff 1) ω := by
  cases ω
  · exact stepCheck_sound stepCheck_false
  · exact stepCheck_sound stepCheck_true

end SpectreKnot.Statement

/-! ### Positions under a move -/

namespace SpectreKnot.Gluing.Cut.OK

-- `ok`: the cut `κ` can be made in `G`
variable {G : Gluing} {κ : Cut} (ok : κ.OK G)

include ok

/-- A cut keeps the order of positions on a child's rim. -/
theorem sh_lt_sh {c u v : Nat} (u_lt_v : u < v) : κ.sh c u < κ.sh c v := by
  rcases ok.sh_cases c u with ⟨u_stays, u_before₀, u_before₁⟩ | ⟨u_moves, u_after⟩ <;>
  rcases ok.sh_cases c v with ⟨v_stays, v_before₀, v_before₁⟩ | ⟨v_moves, v_after⟩
  · omega
  · omega
  · -- `u` moves on, so it lies after the cut; then so does `v`, which cannot stay
    rcases u_after with ⟨on_c₀, past_e₀⟩ | ⟨shared, on_c₁, past_e₁⟩
    · have := v_before₀ on_c₀ -- `v` stays, so it is not past the cut on `c₀`
      omega
    · have := v_before₁ ⟨shared, on_c₁⟩ -- `v` stays, so it is not past the cut on `c₁`
      omega
  · omega

/-- A cut keeps strict order both ways. -/
theorem sh_lt_iff {c u v : Nat} : κ.sh c u < κ.sh c v ↔ u < v := by
  constructor
  · intro sh_lt
    rcases Nat.lt_or_ge u v with u_lt_v | v_le_u
    · exact u_lt_v
    · rcases Nat.eq_or_lt_of_le v_le_u with same | v_lt_u
      · subst same; omega
      · have := ok.sh_lt_sh (c := c) v_lt_u -- `v < u` would put the moved positions the other way round
        omega
  · exact ok.sh_lt_sh

end SpectreKnot.Gluing.Cut.OK

namespace SpectreKnot.Compose.Move.OK

open Gluing Pattern

set_option linter.unusedSectionVars false

-- `ok`: the move `μ` can be made at `(L, d)`
variable {T : Kind} {μ : Move} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} (ok : μ.OK T L d ω)

include ok

/-- The vertices of the children stay put under a move: the cut takes the start of side `v` of child `c` to the
start of side `v` with the new lengths. -/
theorem shpos {c v : Nat} (hc : c < nk T) (hv : v ≤ 6) :
    (μ.cut T L).sh c (pos (L c) v) = pos (μ.lens T L c) v := by
  -- the cut edge is not the last edge of side `j₀`
  have cut_before_end := ok.r₀'
  -- nor its first
  have cut_after_start := ok.r₀
  -- `j₀` is a side
  have j₀_lt := ok.j₀
  by_cases on_c₀ : c = μ.c₀
  · subst on_c₀
    rw [ok.pos_c₀]
    by_cases after_j₀ : μ.j₀ < v
    · -- side `v` starts after the cut:
      -- side `j₀` ends no later than side `v` starts
      have j₀_end_le := pos_mono (L μ.c₀) (show μ.j₀ + 1 ≤ v by omega)
      rw [pos_succ] at j₀_end_le
      rw [ite_eq_left after_j₀, ok.sh₀_gt (by omega)]
    · -- side `v` starts before the cut:
      -- side `v` starts no later than side `j₀`
      have := pos_mono (L μ.c₀) (show v ≤ μ.j₀ by omega)
      rw [ite_eq_right after_j₀, ok.sh₀_le (by omega), Nat.add_zero]
  · by_cases on_c₁ : μ.two T = true ∧ c = μ.c₁ T
    · obtain ⟨shared, rfl⟩ := on_c₁
      -- the sibling's side `j₁` is as long as side `j₀`
      have same_len := ok.L₁ shared
      -- and `j₁` is a side
      have j₁_lt := (ok.sib shared).2.1
      rw [ok.pos_c₁ shared]
      by_cases after_j₁ : μ.j₁ T < v
      · -- side `v` starts after the cut:
        -- side `j₁` ends no later than side `v` starts
        have j₁_end_le := pos_mono (L (μ.c₁ T)) (show μ.j₁ T + 1 ≤ v by omega)
        rw [pos_succ] at j₁_end_le
        rw [ite_eq_left after_j₁, ok.sh₁_gt shared (by simp only [Move.r₁]; omega)]
      · -- side `v` starts before the cut:
        -- side `v` starts no later than side `j₁`
        have := pos_mono (L (μ.c₁ T)) (show v ≤ μ.j₁ T by omega)
        rw [ite_eq_right after_j₁, ok.sh₁_le shared (by simp only [Move.r₁]; omega), Nat.add_zero]
    · rw [ok.sh_oth on_c₀ on_c₁, ok.pos_other on_c₀ on_c₁]

/-- Vertex 1 stays put (the cut edge is never the first edge of a child). -/
theorem sh_one (c : Nat) : (μ.cut T L).sh c 1 = 1 := by
  -- the cut edge is not the first edge of its side
  have cut_after_start := ok.r₀
  -- nor its last
  have cut_before_end := ok.r₀'
  unfold Cut.sh
  rw [ite_eq_right (by simp only [Move.cut]; omega), ite_eq_right (by simp only [Move.cut, Move.r₁]; omega)]

/-- The last vertex of a child moves with the end of its rim. -/
theorem sh_last {c : Nat} (hc : c < nk T) :
    (μ.cut T L).sh c (pos (L c) 6 - 1) = pos (μ.lens T L c) 6 - 1 := by
  -- the last side has an edge, after the move
  have last_pos := ok.lens_pos_len c hc 5 (by omega)
  -- and before
  have last_pos' := ok.pos_len c hc 5 (by omega)
  -- so the rim has an edge
  have rim_pos : 1 ≤ pos (L c) 6 := by rw [pos_succ]; omega
  -- the end of the rim moves to the new end
  have rim_end := ok.shpos hc (show 6 ≤ 6 by omega)
  rcases ok.cutOK.sh_cases c (pos (L c) 6 - 1) with ⟨last_stays, last_before₀, last_before₁⟩ | ⟨last_moves, last_after⟩
  · rcases ok.cutOK.sh_cases c (pos (L c) 6) with ⟨end_stays, _, _⟩ | ⟨end_moves, end_after⟩
    · rw [last_stays]; rw [end_stays] at rim_end; omega
    · -- the end moves on but the last vertex does not: then the cut edge would be the last edge
      rcases end_after with ⟨on_c₀, past_e₀⟩ | ⟨shared, on_c₁, past_e₁⟩
      · have last_le := last_before₀ on_c₀ -- the last vertex is not past the cut
        -- the cut edge is not the last edge of `c₀`
        have cut_lt := ok.cutOK.e₀
        rw [← on_c₀, ofLens_E hc] at cut_lt
        omega
      · have last_le := last_before₁ ⟨shared, on_c₁⟩ -- the last vertex is not past the cut
        -- the cut edge is not the last edge of `c₁`
        have cut_lt := ok.cutOK.e₁ shared
        rw [← on_c₁, ofLens_E hc] at cut_lt
        omega
  · rcases ok.cutOK.sh_cases c (pos (L c) 6) with ⟨end_stays, end_before₀, end_before₁⟩ | ⟨end_moves, _⟩
    · -- the last vertex moves on but the end does not: impossible, the end comes after it
      rcases last_after with ⟨on_c₀, past_e₀⟩ | ⟨shared, on_c₁, past_e₁⟩
      · have := end_before₀ on_c₀ -- the end is not past the cut on `c₀`
        omega
      · have := end_before₁ ⟨shared, on_c₁⟩ -- the end is not past the cut on `c₁`
        omega
    · rw [last_moves]; rw [end_moves] at rim_end; omega

end SpectreKnot.Compose.Move.OK

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### The map under a move -/

/-- The junctions the map names are pieces `1 … 21`. -/
theorem tgt_lt {ω : Bool} {f : Nat → Nat} {u : Nat} {s : Bool} {q : Nat} (tgt_eq : tgt ω f u s = some q) :
    1 ≤ q ∧ q < 22 := by
  unfold tgt at tgt_eq
  revert tgt_eq
  cases ω <;> cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> (repeat' split) <;> intro tgt_eq <;>
    simp only [Option.some.injEq, reduceCtorEq] at tgt_eq <;> omega

/-- Each of the Δ supertile's 22 rim pieces is a side of an actual child. -/
theorem piece_ok : ∀ q, q < 22 → (pieceD q).1 < nk .Delta ∧ (pieceD q).2 < 6 := by decide

/-- Child 1 of Δ has only one side on the parent's rim: side 2. -/
theorem adj_one_none : ∀ j, j < 6 → adjAt .Delta 1 j = none → j = 2 := by decide

/-- Child 1's corners are `0` and `1` or `E - 1`: a vertex `x` with `2 ≤ x ≤ E - 2` is not a corner. -/
theorem corner_one {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} {x : Nat} (two_le_x : 2 ≤ x)
    (x_le : x + 2 ≤ pos (L 1) 6) : (Comp.ofLens .Delta L d ω).toGluing.corner 1 x = false := by
  -- child 1 is an actual child
  have one_lt : 1 < nk .Delta := by decide
  simp only [Gluing.corner, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  rw [ofLens_B one_lt, ofLens_A one_lt, ite_eq_right (by decide)]
  cases ω <;> simp only [ite_true, ite_false, Bool.false_eq_true, nxt, prv] <;> constructor <;> (try split) <;> omega

/-- The map, read through a renumbering `φ` of child 1's rim that keeps the order, the first two vertices, the last
vertex and the six corners (from side lengths `f` to `f'`). -/
theorem tgt_map {ω : Bool} {f f' φ : Nat → Nat} (keeps_lt : ∀ a b, φ a < φ b ↔ a < b) (fixes_zero : φ 0 = 0)
    (fixes_one : φ 1 = 1) (maps_last : φ (pos f 6 - 1) = pos f' 6 - 1)
    (maps_corners : ∀ k, k ≤ 6 → φ (pos f k) = pos f' k) (u : Nat) (s : Bool) :
    tgt ω f' (φ u) s = tgt ω f u s := by
  -- `φ` is one to one
  have keeps_eq : ∀ a b, φ a = φ b ↔ a = b := fun a b => by
    constructor
    · intro same
      rcases Nat.lt_trichotomy a b with a_lt_b | a_eq_b | b_lt_a
      · have := (keeps_lt a b).mpr a_lt_b -- `φ` keeps the strict order
        omega
      · exact a_eq_b
      · have := (keeps_lt b a).mpr b_lt_a -- `φ` keeps the strict order
        omega
    · intro same; rw [same]
  -- `φ` keeps `≤`
  have keeps_le : ∀ a b, φ a ≤ φ b ↔ a ≤ b := fun a b => by
    rw [← Nat.not_lt, ← Nat.not_lt, keeps_lt]
  -- each test in `tgt` gives the same answer after the renumbering: the test `u = 0`
  have is_zero : (φ u = 0) = (u = 0) := propext (by
    -- `φ u = φ 0` exactly when `u = 0`
    have at_zero := keeps_eq u 0
    rwa [fixes_zero] at at_zero)
  -- the test `u = 1`
  have is_one : (φ u = 1) = (u = 1) := propext (by
    -- `φ u = φ 1` exactly when `u = 1`
    have at_one := keeps_eq u 1
    rwa [fixes_one] at at_one)
  -- the test for the last vertex
  have is_last : (φ u = pos f' 6 - 1) = (u = pos f 6 - 1) := propext (by
    -- `φ u` is the last vertex exactly when `u` is
    have at_last := keeps_eq u (pos f 6 - 1)
    rwa [maps_last] at at_last)
  -- the tests `u ≤` a corner
  have le_corner : ∀ k, k ≤ 6 → (φ u ≤ pos f' k) = (u ≤ pos f k) := fun k hk =>
    propext (by
      -- `φ u` is at most corner `k` exactly when `u` is
      have at_corner := keeps_le u (pos f k)
      rwa [maps_corners k hk] at at_corner)
  -- the tests `u <` a corner
  have lt_corner : ∀ k, k ≤ 6 → (φ u < pos f' k) = (u < pos f k) := fun k hk =>
    propext (by
      -- `φ u` is before corner `k` exactly when `u` is
      have at_corner := keeps_lt u (pos f k)
      rwa [maps_corners k hk] at at_corner)
  simp only [tgt, is_zero, is_one, is_last, le_corner 1 (by omega), le_corner 2 (by omega), lt_corner 3 (by omega),
    lt_corner 4 (by omega), lt_corner 5 (by omega)]

section
-- `ok`: the move `μ` can be made in the Δ composition at `(L, d)`
variable {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} {μ : Move} (ok : μ.OK .Delta L d ω)
include ok

set_option quotPrecheck false
local notation "G₀" => (Comp.ofLens .Delta L d ω).toGluing
local notation "G₁" => (Comp.ofLens .Delta (μ.lens .Delta L) (μ.d' .Delta L d) ω).toGluing
local notation "Gs" => subdiv (Comp.ofLens .Delta L d ω).toGluing (μ.cut .Delta L)
local notation "κ" => μ.cut .Delta L


/-- A move takes port `R` of the hook at junction `q` (as `jR` reads it) to the same port with the new lengths. -/
theorem port_jR {q : Nat} (hq : q < 22) : (κ).port (jR L q) = jR (μ.lens .Delta L) q := by
  -- piece `q` is a side of an actual child
  obtain ⟨child_lt, _⟩ := piece_ok q hq
  show ((pieceD q).1, (κ).sh (pieceD q).1 (pos (L (pieceD q).1) (((pieceD q).2 + 1) % 6)), false) = _
  rw [ok.shpos child_lt (by omega)]; rfl

/-- A move takes port `L` of the hook at junction `q` (as `jL` reads it) to the same port with the new lengths. -/
theorem port_jL {q : Nat} (q_pos : 1 ≤ q) (hq : q < 22) : (κ).port (jL L q) = jL (μ.lens .Delta L) q := by
  -- piece `q - 1` is a side of an actual child
  obtain ⟨child_lt, side_lt⟩ := piece_ok (q - 1) (by omega)
  show ((pieceD (q - 1)).1, (κ).sh (pieceD (q - 1)).1 (pos (L (pieceD (q - 1)).1) (pieceD (q - 1)).2), true) = _
  rw [ok.shpos child_lt (by omega)]; rfl

/-- Vertex 0 of child 1 stays put under a move. -/
theorem sh_zero : (κ).sh 1 0 = 0 := by
  rcases ok.cutOK.sh_cases 1 0 with ⟨stays, _⟩ | ⟨_, after_cut⟩
  · exact stays
  · rcases after_cut with ⟨_, past_cut⟩ | ⟨_, _, past_cut⟩ <;> omega

/-- **The map survives a move** whose cut, if on child 1, is at least two edges from either end of its side. -/
theorem StepOK.move (clear₀ : μ.c₀ = 1 → 2 ≤ μ.r₀ ∧ μ.r₀ + 3 ≤ L 1 μ.j₀)
    (clear₁ : μ.two .Delta = true → μ.c₁ .Delta = 1 → 2 ≤ μ.r₁ L ∧ μ.r₁ L + 3 ≤ L 1 (μ.j₁ .Delta))
    (old_map : StepOK L d ω) : StepOK (μ.lens .Delta L) (μ.d' .Delta L d) ω := by
  intro u' hu' s q tgt_eq
  -- the cut can be made
  have cut_ok := ok.cutOK
  -- and the cut gluing is well formed
  have wf_cut := cut_ok.wf_subdiv
  -- child 1 is an actual child
  have one_lt : 1 < nk .Delta := by decide
  -- child 1's rim, before the move
  have rim_old : (G₀).E 1 = pos (L 1) 6 := ofLens_E one_lt
  -- and after the cut
  have rim_cut : (Gs).E 1 = pos (μ.lens .Delta L 1) 6 := by rw [← ok.E_eq one_lt, ofLens_E one_lt]
  -- the junction is one of the pieces `1 … 21`
  obtain ⟨q_pos, q_lt⟩ := tgt_lt tgt_eq
  -- the end: from the subdivided gluing to the new composition
  have to_new : ∀ r, (Gs).FullReach (1, u', s) ((κ).port r) → (r = jR L q ∨ r = jL L q) →
      ∃ r', (G₁).FullReach (1, u', s) r' ∧ (r' = jR (μ.lens .Delta L) q ∨ r' = jL (μ.lens .Delta L) q) := by
    intro r cut_walk at_junction
    refine ⟨_, ok.equiv.symm.fullReach wf_cut ⟨?_, ?_⟩ cut_walk, ?_⟩
    · show 1 < (G₀).n
      rw [ofLens_n]; exact one_lt
    · show u' < (Gs).E 1
      rw [rim_cut]; exact hu'
    · rcases at_junction with rfl | rfl
      · exact Or.inl (port_jR ok q_lt)
      · exact Or.inr (port_jL ok q_pos q_lt)
  by_cases new₀ : 1 = (κ).c₀ ∧ (κ).e₀ < u' ∧ u' ≤ (κ).e₀ + 2
  · -- a new vertex of child `c₀ = 1`
    obtain ⟨is_c₀, after_cut, within_cut⟩ := new₀
    -- the move is on child 1
    have μ_c₀ : μ.c₀ = 1 := is_c₀.symm
    -- and so is the cut
    have κ_c₀ : (κ).c₀ = 1 := is_c₀.symm
    -- the cut is two edges clear of both ends of side `j₀`
    obtain ⟨clear_start, clear_end⟩ := clear₀ μ_c₀
    -- `j₀` is a side
    have j₀_lt := ok.j₀
    -- side `j₀` starts where it did
    have start_j₀ := ok.pos_c₀ μ.j₀
    -- and ends two edges later
    have end_j₀ := ok.pos_c₀ (μ.j₀ + 1)
    rw [μ_c₀] at start_j₀ end_j₀
    rw [ite_eq_right (by omega)] at start_j₀
    rw [ite_eq_left (by omega)] at end_j₀
    -- side `j₀` has `L 1 j₀` edges
    have side_len := pos_succ (L 1) μ.j₀
    -- and lies within the rim
    have side_in_rim := pos_mono (L 1) (show μ.j₀ + 1 ≤ 6 by omega)
    -- where the cut edge is
    have cut_at : (κ).e₀ = pos (L 1) μ.j₀ + μ.r₀ := by show pos (L μ.c₀) μ.j₀ + μ.r₀ = _; rw [μ_c₀]
    -- the new vertex is well inside side `j₀`
    rw [tgt_side s j₀_lt (by omega) (by omega)] at tgt_eq
    cases glued : μ.two .Delta
    · -- a rim side: it is side 2, where the map is not defined
      -- the only rim side of child 1 is side 2
      have side_two : μ.j₀ = 2 := by
        apply adj_one_none _ j₀_lt
        -- side `j₀` of child 1 has no sibling
        have no_sib : (adjAt .Delta μ.c₀ μ.j₀).isSome = false := glued
        rw [μ_c₀] at no_sib
        cases adj : adjAt .Delta 1 μ.j₀ with
        | none => rfl
        | some _ => rw [adj] at no_sib; contradiction
      rw [side_two] at tgt_eq; simp [sideTgt] at tgt_eq
    · have cut_shared : (κ).two = true := glued -- the cut edge is shared with a sibling
      -- the old vertices next to the cut lie well inside side `j₀` too, with the same junction
      have old_tgt : ∀ x, x = (κ).e₀ ∨ x = (κ).e₀ + 1 → tgt ω (L 1) x s = some q := by
        intro x next_to_cut
        rw [tgt_side s j₀_lt (by omega) (by omega)]; exact tgt_eq
      rcases (show u' = (κ).e₀ + 1 ∨ u' = (κ).e₀ + 2 by omega) with rfl | rfl
      · -- new vertex `e₀ + 1` follows the old `e₀ + 1`
        obtain ⟨r, old_walk, at_junction⟩ := old_map _ (by omega) s q (old_tgt _ (Or.inr rfl))
        refine to_new r ?_ at_junction
        cases s
        · -- port `L`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw0_1F cut_shared (r := r) (by rw [κ_c₀]; exact old_walk)
          rw [κ_c₀] at new_walk; exact new_walk
        · -- port `R`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw0_1T cut_shared (by rw [κ_c₀]; exact corner_one (by omega) (by omega)) (r := r)
            (by rw [κ_c₀]; exact old_walk)
          rw [κ_c₀] at new_walk; exact new_walk
      · -- new vertex `e₀ + 2` follows the old `e₀`
        obtain ⟨r, old_walk, at_junction⟩ := old_map _ (by omega) s q (old_tgt _ (Or.inl rfl))
        refine to_new r ?_ at_junction
        cases s
        · -- port `L`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw0_2F cut_shared (by rw [κ_c₀]; exact corner_one (by omega) (by omega)) (r := r)
            (by rw [κ_c₀]; exact old_walk)
          rw [κ_c₀] at new_walk; exact new_walk
        · -- port `R`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw0_2T cut_shared (r := r) (by rw [κ_c₀]; exact old_walk)
          rw [κ_c₀] at new_walk; exact new_walk
  · by_cases new₁ : (κ).two = true ∧ 1 = (κ).c₁ ∧ (κ).e₁ < u' ∧ u' ≤ (κ).e₁ + 2
    · -- a new vertex of child `c₁ = 1`
      obtain ⟨cut_shared, is_c₁, after_cut, within_cut⟩ := new₁
      -- the side cut is glued to a sibling
      have shared : μ.two .Delta = true := cut_shared
      -- the sibling is child 1
      have μ_c₁ : μ.c₁ .Delta = 1 := is_c₁.symm
      -- and so is the cut's second child
      have κ_c₁ : (κ).c₁ = 1 := is_c₁.symm
      -- the cut is two edges clear of both ends of side `j₁`
      obtain ⟨clear_start, clear_end⟩ := clear₁ shared μ_c₁
      -- `j₁` is a side
      have j₁_lt := (ok.sib shared).2.1
      -- side `j₁` is as long as side `j₀`
      have same_len := ok.L₁ shared
      -- the cut edge is not the last edge of side `j₁`
      have r₁_le := ok.r₁_le
      -- side `j₁` starts where it did
      have start_j₁ := ok.pos_c₁ shared (μ.j₁ .Delta)
      -- and ends two edges later
      have end_j₁ := ok.pos_c₁ shared (μ.j₁ .Delta + 1)
      rw [μ_c₁] at start_j₁ end_j₁ same_len
      rw [ite_eq_right (by omega)] at start_j₁
      rw [ite_eq_left (by omega)] at end_j₁
      -- side `j₁` has `L 1 j₁` edges
      have side_len := pos_succ (L 1) (μ.j₁ .Delta)
      -- and lies within the rim
      have side_in_rim := pos_mono (L 1) (show μ.j₁ .Delta + 1 ≤ 6 by omega)
      -- where the cut edge is
      have cut_at : (κ).e₁ = pos (L 1) (μ.j₁ .Delta) + μ.r₁ L := by
        show pos (L (μ.c₁ .Delta)) (μ.j₁ .Delta) + μ.r₁ L = _; rw [μ_c₁]
      -- the new vertex is well inside side `j₁`
      rw [tgt_side s j₁_lt (by omega) (by omega)] at tgt_eq
      -- the old vertices next to the cut lie well inside side `j₁` too, with the same junction
      have old_tgt : ∀ x, x = (κ).e₁ ∨ x = (κ).e₁ + 1 → tgt ω (L 1) x s = some q := by
        intro x next_to_cut
        rw [tgt_side s j₁_lt (by omega) (by omega)]; exact tgt_eq
      rcases (show u' = (κ).e₁ + 1 ∨ u' = (κ).e₁ + 2 by omega) with rfl | rfl
      · -- new vertex `e₁ + 1` follows the old `e₁ + 1`
        obtain ⟨r, old_walk, at_junction⟩ := old_map _ (by omega) s q (old_tgt _ (Or.inr rfl))
        refine to_new r ?_ at_junction
        cases s
        · -- port `L`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw1_1F cut_shared (r := r) (by rw [κ_c₁]; exact old_walk)
          rw [κ_c₁] at new_walk; exact new_walk
        · -- port `R`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw1_1T cut_shared (by rw [κ_c₁]; exact corner_one (by omega) (by omega)) (r := r)
            (by rw [κ_c₁]; exact old_walk)
          rw [κ_c₁] at new_walk; exact new_walk
      · -- new vertex `e₁ + 2` follows the old `e₁`
        obtain ⟨r, old_walk, at_junction⟩ := old_map _ (by omega) s q (old_tgt _ (Or.inl rfl))
        refine to_new r ?_ at_junction
        cases s
        · -- port `L`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw1_2F cut_shared (by rw [κ_c₁]; exact corner_one (by omega) (by omega)) (r := r)
            (by rw [κ_c₁]; exact old_walk)
          rw [κ_c₁] at new_walk; exact new_walk
        · -- port `R`
          -- in the cut gluing, the walk from the new vertex ends where the old walk did
          have new_walk := cut_ok.nw1_2T cut_shared (r := r) (by rw [κ_c₁]; exact old_walk)
          rw [κ_c₁] at new_walk; exact new_walk
    · -- an old vertex
      obtain ⟨u, hu, rfl⟩ := cut_ok.preimage (c := 1) (by rw [rim_cut]; exact hu') new₀ new₁
      rw [tgt_map (fun a b => cut_ok.sh_lt_iff) (sh_zero ok) (ok.sh_one 1) (ok.sh_last one_lt)
        (fun k hk => ok.shpos one_lt hk)] at tgt_eq
      obtain ⟨r, old_walk, at_junction⟩ := old_map u (by rw [← rim_old]; exact hu) s q tgt_eq
      exact to_new r (cut_ok.port_reach ⟨by rw [ofLens_n]; exact one_lt, hu⟩ old_walk) at_junction

end

end SpectreKnot.Statement

/-! ### Every level -/

namespace SpectreKnot.Compose

open Gluing Pattern

namespace Move

/-- The conditions of a move from the shortened lengths: a move cutting side `j₀` of child `c₀` at offset `r₀`, at
least one edge from its start and three from its end (with the lengths after the move), can be made at admissible
shortened lengths whose composition is well formed, if it is clear of the Σ corner. -/
theorem mkOK {T : Kind} {μ : Move} {L : Nat → Nat → Nat} {ω : Bool} (hc₀ : μ.c₀ < nk T) (hj₀ : μ.j₀ < 6)
    (r₀_pos : 1 ≤ μ.r₀) (r₀_room : μ.r₀ + 4 ≤ L μ.c₀ μ.j₀) {d₀ : Nat} (adm₀ : Adm T (μ.shorten T L) d₀)
    (cut₀ : kidAt T μ.c₀ = .Sigma → μ.j₀ = 5 → d₀ + 1 ≤ μ.r₀ ∨ μ.r₀ + 2 ≤ d₀)
    (cut₁ : μ.two T = true → kidAt T (μ.c₁ T) ≠ .Sigma ∨ μ.j₁ T ≠ 5)
    (wf₀ : (Comp.ofLens T (μ.shorten T L) d₀ ω).toGluing.WF) : μ.OK T (μ.shorten T L) d₀ ω :=
  { wf := wf₀
    pos_len := fun c hc j hj => by
      -- each side is at least as long as at level 1
      have := (adm₀.len c hc j hj).1
      -- where it has at least 5 edges
      have := L₁_ge T c j
      omega
    pair := adm₀.pair
    c₀ := hc₀
    j₀ := hj₀
    r₀ := r₀_pos
    r₀' := by simp only [shorten]; rw [ite_eq_left (show μ.Hit T μ.c₀ μ.j₀ from Or.inl ⟨rfl, rfl⟩)]; omega
    sig := fun c hc is_sigma => by
      -- room for the Σ corner on side 5, as at level 1
      have := adm₀.sig c hc is_sigma
      -- and `d₀ ≥ d₁`
      have := adm₀.d_ge
      rw [L₁_sig is_sigma, dOff_one] at *
      omega
    sig1 := fun c c' hc hc' is_sigma is_sigma' => sigma_unique T c hc c' hc' is_sigma is_sigma'
    cut₀ := cut₀
    cut₁ := fun shared is_sigma side_five => by
      rcases cut₁ shared with not_sigma | not_five <;> contradiction }

end Move

/-- **Induction over admissible lengths** (the induction of `adm_sig`, for any property). A property of `(L, d)` that
holds at `(ℓ₁, d₁)`, depends only on the lengths of actual sides (and on `d` only through the Σ child), and survives
every move whose cut is two edges clear of both ends of its side or lies on the Σ child's side 5, holds for every
admissible `(L, d)`. -/
theorem adm_induct (T : Kind) (ω : Bool) (P : (Nat → Nat → Nat) → Nat → Prop)
    (congr : ∀ L L' d d', (∀ c, c < nk T → ∀ j, j < 6 → L c j = L' c j) →
      (∀ c, c < nk T → kidAt T c = .Sigma → d = d') → P L' d' → P L d)
    (base : P (L₁ T) (dOff 1))
    (step : ∀ (μ : Move) (L : Nat → Nat → Nat) (d : Nat), μ.OK T L d ω →
      ((2 ≤ μ.r₀ ∧ μ.r₀ + 3 ≤ L μ.c₀ μ.j₀) ∨ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5)) → P L d →
      P (μ.lens T L) (μ.d' T L d)) :
    ∀ N L d, excess T L < N → Adm T L d → P L d := by
  intro N
  induction N with
  | zero => intro L d below_zero; omega
  | succ N ih =>
    intro L d excess_lt adm
    -- the Σ child is an actual child, of kind Σ
    obtain ⟨sig_lt, sig_kind⟩ := sigIdx_spec T
    -- `d₁ = 6`
    have d₁_eq := dOff_one
    by_cases at_base : excess T L = 0
    · -- the base case: `(L, d) = (ℓ₁, d₁)`
      -- every side is as long as at level 1
      have is_L₁ : ∀ c, c < nk T → ∀ j, j < 6 → L c j = L₁ T c j := fun c hc j hj => by
        -- no excess on side `j` of child `c`
        have := tot_eq_zero (tot_eq_zero at_base c hc) j hj
        -- and the side is at least as long as at level 1
        have := (adm.len c hc j hj).1
        omega
      -- and the Σ offset is `d₁`
      have is_d₁ : d = dOff 1 := by
        -- room for the Σ corner on side 5
        have := adm.sig _ sig_lt sig_kind
        -- which is as long as at level 1
        have := is_L₁ _ sig_lt 5 (by omega)
        -- and `d ≥ d₁`
        have := adm.d_ge
        omega
      exact congr L (L₁ T) d (dOff 1) is_L₁ (fun _ _ _ => is_d₁) base
    · -- a side longer than at level 1
      obtain ⟨c, hc, child_excess⟩ := tot_ne_zero at_base
      obtain ⟨j, hj, side_excess⟩ := tot_ne_zero child_excess
      -- side `j` of child `c` is at least two edges longer than at level 1
      have longer : L₁ T c j + 2 ≤ L c j := by
        -- it is at least as long, with the same parity
        have := adm.len c hc j hj
        omega
      -- one step back
      have back : ∀ μ : Move, μ.c₀ < nk T → μ.j₀ < 6 → L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ → 1 ≤ μ.r₀ →
          μ.r₀ + 4 ≤ L μ.c₀ μ.j₀ → ∀ d₀, Adm T (μ.shorten T L) d₀ →
          (kidAt T μ.c₀ = .Sigma → μ.j₀ = 5 → d₀ + 1 ≤ μ.r₀ ∨ μ.r₀ + 2 ≤ d₀) →
          (μ.two T = true → kidAt T (μ.c₁ T) ≠ .Sigma ∨ μ.j₁ T ≠ 5) → μ.d' T (μ.shorten T L) d₀ = d →
          ((2 ≤ μ.r₀ ∧ μ.r₀ + 5 ≤ L μ.c₀ μ.j₀) ∨ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5)) → P L d := by
        intro μ hc₀ hj₀ big r₀_pos r₀_room d₀ adm₀ cut₀ cut₁ d_after clear
        -- the move can be made from the shortened lengths, whose composition has the signature
        have move_ok : μ.OK T (μ.shorten T L) d₀ ω :=
          Move.mkOK hc₀ hj₀ r₀_pos r₀_room adm₀ cut₀ cut₁ (adm_sig T ω _ _ _ (Nat.lt_succ_self _) adm₀).wf
        -- the induction hypothesis: the property holds at the shortened lengths, which have less excess
        have holds₀ := ih _ _ (by
          -- shortening lowers the excess
          have := Move.excess_shorten adm hc₀ hj₀ big
          omega) adm₀
        -- side `j₀` of `c₀` is two edges shorter before the move
        have shortened : μ.shorten T L μ.c₀ μ.j₀ = L μ.c₀ μ.j₀ - 2 := by
          simp only [Move.shorten]; rw [ite_eq_left (show μ.Hit T μ.c₀ μ.j₀ from Or.inl ⟨rfl, rfl⟩)]
        -- the property survives the move
        have after := step μ _ _ move_ok (by
          rw [shortened]
          rcases clear with clear_ends | on_sigma_five
          · exact Or.inl ⟨clear_ends.1, by omega⟩
          · exact Or.inr on_sigma_five) holds₀
        rwa [Move.lens_shorten adm hc₀ hj₀ big, d_after] at after
      -- the sibling glued to side 5 of the Σ child is not the Σ child
      have sib_not_sig : ∀ μ : Move, μ.c₀ = sigIdx T → μ.j₀ = 5 → μ.two T = true → kidAt T (μ.c₁ T) ≠ .Sigma := by
        intro μ on_sigma side_five shared sib_sigma
        -- Table 2 glues side `j₀` of `c₀` to side `j₁` of `c₁`
        have sib := Move.adj₀ (T := T) (μ := μ)
        rw [ite_eq_left shared] at sib
        -- the sibling is an actual child, other than `c₀`
        have sib_valid := adj_valid (on_sigma ▸ sig_lt) (by omega) sib
        exact sib_valid.2.2.1 (sigma_unique T _ sib_valid.1 _ (on_sigma ▸ sig_lt) sib_sigma (on_sigma ▸ sig_kind))
      by_cases on_sig_five : (c = sigIdx T ∧ j = 5) ∨ adjAt T c j = some (sigIdx T, 5)
      · -- a move on the Σ child's side 5
        -- that side is at least two edges longer than at level 1
        have big : L₁ T (sigIdx T) 5 + 2 ≤ L (sigIdx T) 5 := by
          rcases on_sig_five with ⟨rfl, rfl⟩ | glued_to
          · exact longer
          · rw [adm.pair c hc j hj _ _ glued_to]
            show letterLen 1 (letterOf (kidAt T (sigIdx T)) 5) + 2 ≤ _
            rw [pair_letter hc hj glued_to]; exact longer
        -- side 5 of the Σ child has 10 edges at level 1
        have sig_five := L₁_sig sig_kind
        -- room for the Σ corner on side 5
        have corner_room := adm.sig _ sig_lt sig_kind
        -- `d ≥ d₁`
        have d_ge := adm.d_ge
        -- and `d` has the parity of `d₁`
        have d_par := adm.d_par
        by_cases d_big : dOff 1 + 2 ≤ d
        · -- cut the edge at offset 1, before the Σ corner, which moves back by 2
          obtain ⟨μ, μ_c₀, μ_j₀, μ_r₀⟩ : ∃ μ : Move, μ.c₀ = sigIdx T ∧ μ.j₀ = 5 ∧ μ.r₀ = 1 :=
            ⟨⟨_, 5, 1⟩, rfl, rfl, rfl⟩
          have hc₀ : μ.c₀ < nk T := μ_c₀ ▸ sig_lt -- the Σ child is an actual child
          have hj₀ : μ.j₀ < 6 := by omega -- and side 5 is a side
          -- the side cut is at least two edges longer than at level 1
          have big' : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ := by rw [μ_c₀, μ_j₀]; exact big
          -- before the move it is two edges shorter
          have shortened : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 - 2 := by
            simp only [Move.shorten]; rw [ite_eq_left (show μ.Hit T (sigIdx T) 5 from Or.inl ⟨μ_c₀.symm, μ_j₀.symm⟩)]
          -- the shortened lengths, with `d - 2`, are admissible
          have adm₀ : Adm T (μ.shorten T L) (d - 2) :=
            Move.adm_shorten adm hc₀ hj₀ big' (by omega) (by omega) (fun c' hc' is_sigma => by
              rw [sigma_unique T _ hc' _ sig_lt is_sigma sig_kind, shortened, sig_five]; omega)
          refine back μ hc₀ hj₀ big' (by omega) (by rw [μ_c₀, μ_j₀, μ_r₀]; omega) _ adm₀
            (fun _ _ => Or.inr (by omega)) (fun shared => Or.inl (sib_not_sig μ μ_c₀ μ_j₀ shared)) ?_
            (Or.inr ⟨by rw [μ_c₀]; exact sig_kind, μ_j₀⟩)
          -- the move puts the Σ corner back at `d`
          have new_d := Move.d'_c₀ (L := μ.shorten T L) (d := d - 2) (by rw [μ_c₀]; exact sig_kind) μ_j₀
            (fun ⟨shared, is_sigma, _⟩ => sib_not_sig μ μ_c₀ μ_j₀ shared is_sigma)
          rw [ite_eq_left (by omega)] at new_d; omega
        · -- `d = d₁`: cut the edge just after the Σ corner, which stays put
          have is_d₁ : d = dOff 1 := by omega -- `d` has the parity of `d₁`
          obtain ⟨μ, μ_c₀, μ_j₀, μ_r₀⟩ : ∃ μ : Move, μ.c₀ = sigIdx T ∧ μ.j₀ = 5 ∧ μ.r₀ = d + 1 :=
            ⟨⟨_, 5, d + 1⟩, rfl, rfl, rfl⟩
          have hc₀ : μ.c₀ < nk T := μ_c₀ ▸ sig_lt -- the Σ child is an actual child
          have hj₀ : μ.j₀ < 6 := by omega -- and side 5 is a side
          -- the side cut is at least two edges longer than at level 1
          have big' : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ := by rw [μ_c₀, μ_j₀]; exact big
          -- before the move it is two edges shorter
          have shortened : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 - 2 := by
            simp only [Move.shorten]; rw [ite_eq_left (show μ.Hit T (sigIdx T) 5 from Or.inl ⟨μ_c₀.symm, μ_j₀.symm⟩)]
          -- the shortened lengths, with the same `d`, are admissible
          have adm₀ : Adm T (μ.shorten T L) d :=
            Move.adm_shorten adm hc₀ hj₀ big' d_ge d_par (fun c' hc' is_sigma => by
              rw [sigma_unique T _ hc' _ sig_lt is_sigma sig_kind, shortened, sig_five]; omega)
          refine back μ hc₀ hj₀ big' (by omega) (by rw [μ_c₀, μ_j₀, μ_r₀]; omega) _ adm₀
            (fun _ _ => Or.inl (by omega)) (fun shared => Or.inl (sib_not_sig μ μ_c₀ μ_j₀ shared)) ?_
            (Or.inr ⟨by rw [μ_c₀]; exact sig_kind, μ_j₀⟩)
          -- the move leaves the Σ corner at `d`
          have new_d := Move.d'_c₀ (L := μ.shorten T L) (d := d) (by rw [μ_c₀]; exact sig_kind) μ_j₀
            (fun ⟨shared, is_sigma, _⟩ => sib_not_sig μ μ_c₀ μ_j₀ shared is_sigma)
          rw [ite_eq_right (by omega)] at new_d; omega
      · -- a move elsewhere, cutting the third edge of the side
        obtain ⟨μ, μ_c₀, μ_j₀, μ_r₀⟩ : ∃ μ : Move, μ.c₀ = c ∧ μ.j₀ = j ∧ μ.r₀ = 2 := ⟨⟨c, j, 2⟩, rfl, rfl, rfl⟩
        subst μ_c₀ μ_j₀
        -- every side has at least 5 edges at level 1
        have L₁_five := L₁_ge T μ.c₀ μ.j₀
        -- the side cut is not the Σ child's side 5
        have not_sig_five₀ : ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5) := fun ⟨is_sigma, side_five⟩ =>
          on_sig_five (Or.inl ⟨sigma_unique T _ hc _ sig_lt is_sigma sig_kind, side_five⟩)
        -- nor is the sibling's side glued to it
        have not_sig_five₁ : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5) := by
          rintro ⟨shared, is_sigma, side_five⟩
          -- Table 2 glues side `j₀` of `c₀` to side `j₁` of `c₁`
          have sib := Move.adj₀ (T := T) (μ := μ)
          rw [ite_eq_left shared] at sib
          -- the sibling is an actual child
          have sib_valid := adj_valid hc hj sib
          rw [sigma_unique T _ sib_valid.1 _ sig_lt is_sigma sig_kind, side_five] at sib
          exact on_sig_five (Or.inr sib)
        -- so the move leaves the Σ child's side 5 alone
        have sig_not_hit : ¬ μ.Hit T (sigIdx T) 5 := by
          rintro (⟨is_c₀, is_j₀⟩ | ⟨shared, is_c₁, is_j₁⟩)
          · exact not_sig_five₀ ⟨is_c₀ ▸ sig_kind, is_j₀.symm⟩
          · exact not_sig_five₁ ⟨shared, is_c₁ ▸ sig_kind, is_j₁.symm⟩
        -- the Σ child's side 5 is as long before the move as after
        have unchanged : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 := by
          simp only [Move.shorten]; rw [ite_eq_right sig_not_hit]; omega
        -- the shortened lengths, with the same `d`, are admissible
        have adm₀ : Adm T (μ.shorten T L) d :=
          Move.adm_shorten adm hc hj longer adm.d_ge adm.d_par (fun c' hc' is_sigma => by
            rw [sigma_unique T _ hc' _ sig_lt is_sigma sig_kind, unchanged]; exact adm.sig _ sig_lt sig_kind)
        refine back μ hc hj longer (by omega) (by omega) _ adm₀
          (fun is_sigma side_five => absurd ⟨is_sigma, side_five⟩ not_sig_five₀) (fun shared => ?_)
          (Move.d'_eq not_sig_five₀ not_sig_five₁) (Or.inl ⟨by omega, by omega⟩)
        by_cases is_sigma : kidAt T (μ.c₁ T) = .Sigma
        · exact Or.inr (fun side_five => not_sig_five₁ ⟨shared, is_sigma, side_five⟩)
        · exact Or.inl is_sigma

end SpectreKnot.Compose

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- The map depends on the side lengths only through the positions of the corners. -/
theorem tgt_congr {ω : Bool} {f f' : Nat → Nat} (same_pos : ∀ k, k ≤ 6 → pos f k = pos f' k) (u : Nat) (s : Bool) :
    tgt ω f' u s = tgt ω f u s :=
  tgt_map (φ := fun x => x) (fun _ _ => Iff.rfl) rfl rfl (by rw [same_pos 6 (by omega)]) same_pos u s

/-- The junction map depends only on the lengths of actual sides (and on `d` only through the Σ child). -/
theorem StepOK.congr {L L' : Nat → Nat → Nat} {d d' : Nat} {ω : Bool}
    (same_len : ∀ c, c < nk .Delta → ∀ j, j < 6 → L c j = L' c j)
    (same_d : ∀ c, c < nk .Delta → kidAt .Delta c = .Sigma → d = d') (holds' : StepOK L' d' ω) : StepOK L d ω := by
  -- the corners are in the same places
  have same_pos : ∀ c, c < nk .Delta → ∀ v, v ≤ 6 → pos (L c) v = pos (L' c) v :=
    fun c hc v _ => pos_congr v (fun i hi => same_len c hc i (by omega))
  -- child 1 is an actual child
  have one_lt : 1 < nk .Delta := by decide
  intro u hu s q tgt_eq
  -- the junction is one of the pieces `1 … 21`
  obtain ⟨q_pos, q_lt⟩ := tgt_lt tgt_eq
  rw [tgt_congr (f := L' 1) (fun k hk => (same_pos 1 one_lt k hk).symm)] at tgt_eq
  obtain ⟨r, walk, at_junction⟩ := holds' u (by rw [← same_pos 1 one_lt 6 (by omega)]; exact hu) s q tgt_eq
  refine ⟨r, by rw [ofLens_congr same_len same_d]; exact walk, ?_⟩
  -- pieces `q` and `q - 1` are sides of actual children
  obtain ⟨child_lt, side_lt⟩ := piece_ok q q_lt
  obtain ⟨child_lt', side_lt'⟩ := piece_ok (q - 1) (by omega)
  -- so the junction's port `R` is the same with either lengths
  have same_jR : jR L q = jR L' q := by
    simp only [jR, same_pos _ child_lt _ (show ((pieceD q).2 + 1) % 6 ≤ 6 by omega)]
  -- and so is its port `L`
  have same_jL : jL L q = jL L' q := by
    simp only [jL, same_pos _ child_lt' _ (show (pieceD (q - 1)).2 ≤ 6 by omega)]
  rw [same_jR, same_jL]; exact at_junction

/-- Child 1 of Δ is not a Σ. -/
theorem kid_one : kidAt .Delta 1 ≠ .Sigma := by decide

/-- The sibling glued to side 5 of Δ's Σ child is not child 1. -/
theorem sig_partner : ∀ c, c < nk .Delta → kidAt .Delta c = .Sigma → ((adjAt .Delta c 5).getD (0, 0)).1 ≠ 1 := by
  decide

/-- **The junction map at every level** `m ≥ 1`. -/
theorem step_level (m : Nat) (m_pos : 1 ≤ m) (ω : Bool) : StepOK (Lk m .Delta) (dOff m) ω := by
  refine adm_induct .Delta ω (fun L d => StepOK L d ω)
    (fun L L' d d' same_len same_d holds' => StepOK.congr same_len same_d holds')
    (step_base ω) ?_ _ _ _ (Nat.lt_succ_self _) (adm_level .Delta m m_pos)
  intro μ L d move_ok clear old_map
  refine StepOK.move move_ok ?_ ?_ old_map
  · -- a cut on child 1 is two edges clear of the ends of its side (child 1 is not a Σ)
    intro on_child_one
    rcases clear with ⟨clear_start, clear_end⟩ | ⟨is_sigma, _⟩
    · rw [on_child_one] at clear_end; exact ⟨clear_start, clear_end⟩
    · rw [on_child_one] at is_sigma; exact absurd is_sigma kid_one
  · -- and so is the same cut seen from the sibling, if that is child 1
    intro shared sib_child_one
    rcases clear with ⟨clear_start, clear_end⟩ | ⟨is_sigma, side_five⟩
    · have same_len := move_ok.L₁ shared -- the sibling's side is as long as side `j₀`
      rw [sib_child_one] at same_len
      simp only [Move.r₁]
      omega
    · exfalso
      -- the sibling glued to the Σ child's side 5 is not child 1
      have not_one := sig_partner _ move_ok.c₀ is_sigma
      rw [← side_five] at not_one
      exact not_one sib_child_one

end SpectreKnot.Statement

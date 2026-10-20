/-
Walks through the two new vertices of a cut edge (paper Lemma 7.1: a cut creates no closed strand; Lemma 9.3: the new
vertices). When an edge shared by two children is cut into three, each child gets two new vertices on it. The ribbon
from a port at a new vertex follows one of the two connections of the zigzag lemma along the new path, for one or two
crossings, to a port at an old vertex next to the cut, and runs on from there (`step0_2F`, …). So a cut creates no
closed strand (`noLoops`). And the strand through a new vertex's hook is the strand that, before the cut, ran through
the hook at the old vertex next to it, the port of the same hand: `e₀ + 2` follows the old `e₀`, and `e₀ + 1` the old
`e₀ + 1` (and the same on the other side; `nw0_2F`, …). That carries the junction map (`StepMap.lean`) through moves.
-/
import SpectreKnot.Subdivide

namespace SpectreKnot.Gluing

/-- The first step of a walk, then the rest: if from `x` the piece and then the crossing lead to `y`, and the walk
from `y` ends at `r`, then the walk from `x` ends at `r`. -/
theorem fullReach_step {G : Gluing} {x y r : GPort} (first_step : G.sigma (G.tau x) = some y)
    (rest : G.FullReach y r) : G.FullReach x r := by
  obtain ⟨k, rest_walk⟩ := rest
  exact ⟨k + 1, .step first_step rest_walk⟩

/-- A walk whose first step lands on `y` goes on from `y`: if the walk from `x` ends at `r`, so does the walk from
`y`. -/
theorem fullReach_first {G : Gluing} {x y r : GPort} (first_step : G.sigma (G.tau x) = some y)
    (walk : G.FullReach x r) : G.FullReach y r := by
  obtain ⟨k, walk_k⟩ := walk
  cases walk_k with
  | stop at_rim =>
    -- the walk cannot stop at once: its first crossing exists
    rw [first_step] at at_rim; contradiction
  | step step_to rest_walk =>
    -- the walk's first step is the same step, to `y`
    rw [first_step] at step_to
    simp only [Option.some.injEq] at step_to
    subst step_to
    exact ⟨_, rest_walk⟩

namespace Cut.OK

set_option linter.unusedSectionVars false

-- `ok`: the cut `κ` can be made in `G`
variable {G : Gluing} {κ : Cut} (ok : κ.OK G)

include ok

/-- A walk of `G` from an actual port, carried into the cut gluing: it starts and ends at the same ports, with
positions after the cut moved on by 2. -/
theorem port_reach {x r : GPort} (x_valid : G.Valid x) (walk : G.FullReach x r) :
    (subdiv G κ).FullReach (κ.port x) (κ.port r) := by
  obtain ⟨k, walk_k⟩ := walk
  exact Sim.reach ok.wf ok.sim k x r x_valid walk_k

section
-- `shared`: the cut edge is shared by two children, `c₀` and `c₁`
variable (shared : κ.two = true)
include shared

/-! ### From a new port to an old one -/

/-- New vertex `e₀ + 2` of `c₀`, port `L`: through the new hook and across new edge `e₀ + 2`, the ribbon reaches
`R_{c₁}` at the old vertex `e₁`, and runs on from there. -/
theorem step0_2F {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₁, κ.e₁, true)) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 2, false) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  simp only [Cut.port, ok.sh_c₁_le shared (Nat.le_refl _)] at walk
  refine fullReach_step ?_ walk
  rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), ite_eq_left shared]
  simp

/-- New vertex `e₀ + 2` of `c₀`, port `R`: across new edges `e₀ + 1` and `e₁ + 2`, through the new hook of `c₁` at
`e₁ + 2`, the ribbon reaches `R_{c₀}` at the old vertex `e₀`, and runs on from there. -/
theorem step0_2T {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₀, κ.e₀, true)) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 2, true) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₀_le (Nat.le_refl _)] at walk
  refine fullReach_step (y := (κ.c₁, κ.e₁ + 2, false)) ?_ (fullReach_step ?_ walk)
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, ok.E_c₀, show κ.e₀ + 2 = (κ.e₀ + 1) + 1 from rfl,
      prv_succ', ok.mate_new₀ (by omega), ite_eq_left shared]
    simp only [Option.map_some, show κ.e₁ + 2 - 1 = κ.e₁ + 1 by omega, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 1 + 1 <
      (G.E κ.c₁ + 2) by omega)]
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
    simp

/-- New vertex `e₀ + 1` of `c₀`, port `R`: through the new hook and across new edge `e₀`, the ribbon reaches `L_{c₁}`
at the old vertex `e₁ + 1`, and runs on from there. -/
theorem step0_1T {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₁, κ.e₁ + 1, false)) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 1, true) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₁_gt shared (show κ.e₁ < κ.e₁ + 1 by omega)] at walk
  refine fullReach_step ?_ walk
  rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₀, ite_eq_left shared]
  simp only [Option.map_some, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 2 + 1 < G.E κ.c₁ + 2 by omega)]

/-- New vertex `e₀ + 1` of `c₀`, port `L`: across new edges `e₀ + 1` and `e₁`, through the new hook of `c₁` at
`e₁ + 1`, the ribbon reaches `L_{c₀}` at the old vertex `e₀ + 1`, and runs on from there. -/
theorem step0_1F {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₀, κ.e₀ + 1, false)) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 1, false) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₀_gt (show κ.e₀ < κ.e₀ + 1 by omega)] at walk
  refine fullReach_step (y := (κ.c₁, κ.e₁ + 1, true)) ?_ (fullReach_step ?_ walk)
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), ite_eq_left shared]
    simp only [Option.map_some, show κ.e₁ + 2 - 1 = κ.e₁ + 1 by omega]
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₁ shared]
    simp only [Option.map_some, ok.E_c₀, nxt_of_lt' (show κ.e₀ + 2 + 1 < G.E κ.c₀ + 2 by omega)]

/-- New vertex `e₁ + 2` of `c₁`, port `L`: through the new hook and across new edge `e₁ + 2`, the ribbon reaches
`R_{c₀}` at the old vertex `e₀`, and runs on from there. -/
theorem step1_2F {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₀, κ.e₀, true)) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 2, false) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  simp only [Cut.port, ok.sh_c₀_le (Nat.le_refl _)] at walk
  refine fullReach_step ?_ walk
  rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
  simp

/-- New vertex `e₁ + 2` of `c₁`, port `R`: across new edges `e₁ + 1` and `e₀ + 2`, through the new hook of `c₀` at
`e₀ + 2`, the ribbon reaches `R_{c₁}` at the old vertex `e₁`, and runs on from there. -/
theorem step1_2T {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₁, κ.e₁, true)) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 2, true) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₁_le shared (Nat.le_refl _)] at walk
  refine fullReach_step (y := (κ.c₀, κ.e₀ + 2, false)) ?_ (fullReach_step ?_ walk)
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, ok.E_c₁ shared,
      show κ.e₁ + 2 = (κ.e₁ + 1) + 1 from rfl, prv_succ', ok.mate_new₁ shared (by omega)]
    simp only [Option.map_some, show κ.e₀ + 2 - 1 = κ.e₀ + 1 by omega, ok.E_c₀,
      nxt_of_lt' (show κ.e₀ + 1 + 1 < G.E κ.c₀ + 2 by omega)]
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), ite_eq_left shared]
    simp

/-- New vertex `e₁ + 1` of `c₁`, port `R`: through the new hook and across new edge `e₁`, the ribbon reaches `L_{c₀}`
at the old vertex `e₀ + 1`, and runs on from there. -/
theorem step1_1T {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₀, κ.e₀ + 1, false)) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, true) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₀_gt (show κ.e₀ < κ.e₀ + 1 by omega)] at walk
  refine fullReach_step ?_ walk
  rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₁ shared]
  simp only [Option.map_some, ok.E_c₀, nxt_of_lt' (show κ.e₀ + 2 + 1 < G.E κ.c₀ + 2 by omega)]

/-- New vertex `e₁ + 1` of `c₁`, port `L`: across new edges `e₁ + 1` and `e₀`, through the new hook of `c₀` at
`e₀ + 1`, the ribbon reaches `L_{c₁}` at the old vertex `e₁ + 1`, and runs on from there. -/
theorem step1_1F {r : GPort} (walk : (subdiv G κ).FullReach (κ.port (κ.c₁, κ.e₁ + 1, false)) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, false) r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  simp only [Cut.port, ok.sh_c₁_gt shared (show κ.e₁ < κ.e₁ + 1 by omega)] at walk
  refine fullReach_step (y := (κ.c₀, κ.e₀ + 1, true)) ?_ (fullReach_step ?_ walk)
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
    simp only [Option.map_some, show κ.e₀ + 2 - 1 = κ.e₀ + 1 by omega]
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₀, ite_eq_left shared]
    simp only [Option.map_some, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 2 + 1 < G.E κ.c₁ + 2 by omega)]

/-! ### The same strand as before the cut (Lemma 9.3) -/

/-- New vertex `e₀ + 2` of `c₀`, port `L`: the walk from `L(e₀ + 2)` in the cut gluing ends where the walk from the
old `L(e₀)` ended in `G` (when `e₀` is not a corner of `c₀`). -/
theorem nw0_2F (not_corner : G.corner κ.c₀ κ.e₀ = false) {r : GPort} (old_walk : G.FullReach (κ.c₀, κ.e₀, false) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 2, false) (κ.port r) := by
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
  -- in `G`: through the hook at `e₀` to `R_{c₀}(e₀)`, then across the cut edge to `R_{c₁}(e₁)`
  have first_step : G.sigma (G.tau (κ.c₀, κ.e₀, false)) = some (κ.c₁, κ.e₁, true) := by
    rw [tau_of_not_corner not_corner, Bool.not_false, sigmaR]
    -- the cut edge is edge `e₁` of `c₁`
    have cut_mate := ok.mate
    rw [ite_eq_left shared] at cut_mate
    rw [cut_mate]; rfl
  -- in the cut gluing, one step from `L(e₀ + 2)` reaches `R_{c₁}(e₁)` too; from there, the rest of the old walk
  exact ok.step0_2F shared (ok.port_reach ⟨c₁_lt, e₁_lt⟩ (fullReach_first first_step old_walk))

/-- New vertex `e₀ + 2` of `c₀`, port `R`: the walk from `R(e₀ + 2)` in the cut gluing ends where the walk from the
old `R(e₀)` ended in `G`. -/
theorem nw0_2T {r : GPort} (old_walk : G.FullReach (κ.c₀, κ.e₀, true) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 2, true) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- two steps from `R(e₀ + 2)` reach `R_{c₀}(e₀)`; from there, the old walk
  exact ok.step0_2T shared (ok.port_reach ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩ old_walk)

/-- New vertex `e₀ + 1` of `c₀`, port `R`: the walk from `R(e₀ + 1)` in the cut gluing ends where the walk from the
old `R(e₀ + 1)` ended in `G` (when the old `e₀ + 1` is not a corner of `c₀`). -/
theorem nw0_1T (not_corner : G.corner κ.c₀ (κ.e₀ + 1) = false) {r : GPort}
    (old_walk : G.FullReach (κ.c₀, κ.e₀ + 1, true) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 1, true) (κ.port r) := by
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
  -- and not its last edge
  have e₁_succ_lt := ok.e₁ shared
  -- in `G`: through the hook at the old `e₀ + 1` to `L`, then across the cut edge to `L_{c₁}(e₁ + 1)`
  have first_step : G.sigma (G.tau (κ.c₀, κ.e₀ + 1, true)) = some (κ.c₁, κ.e₁ + 1, false) := by
    rw [tau_of_not_corner not_corner, Bool.not_true, sigmaL, prv_succ']
    -- the cut edge is edge `e₁` of `c₁`
    have cut_mate := ok.mate
    rw [ite_eq_left shared] at cut_mate
    rw [cut_mate]
    simp only [Option.map_some, nxt_of_lt' e₁_succ_lt]
  -- in the cut gluing, one step from `R(e₀ + 1)` reaches `L_{c₁}` at the old `e₁ + 1` too; then the rest of the old
  -- walk
  exact ok.step0_1T shared
    (ok.port_reach ⟨c₁_lt, show κ.e₁ + 1 < G.E κ.c₁ by omega⟩ (fullReach_first first_step old_walk))

/-- New vertex `e₀ + 1` of `c₀`, port `L`: the walk from `L(e₀ + 1)` in the cut gluing ends where the walk from the
old `L(e₀ + 1)` ended in `G`. -/
theorem nw0_1F {r : GPort} (old_walk : G.FullReach (κ.c₀, κ.e₀ + 1, false) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 1, false) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- two steps from `L(e₀ + 1)` reach `L_{c₀}` at the old `e₀ + 1`; from there, the old walk
  exact ok.step0_1F shared (ok.port_reach ⟨ok.c₀, show κ.e₀ + 1 < G.E κ.c₀ by omega⟩ old_walk)

/-- New vertex `e₁ + 2` of `c₁`, port `L`: the walk from `L(e₁ + 2)` in the cut gluing ends where the walk from the
old `L(e₁)` ended in `G` (when `e₁` is not a corner of `c₁`). -/
theorem nw1_2F (not_corner : G.corner κ.c₁ κ.e₁ = false) {r : GPort} (old_walk : G.FullReach (κ.c₁, κ.e₁, false) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 2, false) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- the cut edge's mate is glued back to it
  obtain ⟨_, _, mate_back⟩ := ok.two_mate shared
  -- in `G`: through the hook at `e₁` to `R_{c₁}(e₁)`, then across the cut edge to `R_{c₀}(e₀)`
  have first_step : G.sigma (G.tau (κ.c₁, κ.e₁, false)) = some (κ.c₀, κ.e₀, true) := by
    rw [tau_of_not_corner not_corner, Bool.not_false, sigmaR, mate_back]; rfl
  -- in the cut gluing, one step from `L(e₁ + 2)` reaches `R_{c₀}(e₀)` too; from there, the rest of the old walk
  exact ok.step1_2F shared
    (ok.port_reach ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩ (fullReach_first first_step old_walk))

/-- New vertex `e₁ + 2` of `c₁`, port `R`: the walk from `R(e₁ + 2)` in the cut gluing ends where the walk from the
old `R(e₁)` ended in `G`. -/
theorem nw1_2T {r : GPort} (old_walk : G.FullReach (κ.c₁, κ.e₁, true) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 2, true) (κ.port r) := by
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
  -- two steps from `R(e₁ + 2)` reach `R_{c₁}(e₁)`; from there, the old walk
  exact ok.step1_2T shared (ok.port_reach ⟨c₁_lt, e₁_lt⟩ old_walk)

/-- New vertex `e₁ + 1` of `c₁`, port `R`: the walk from `R(e₁ + 1)` in the cut gluing ends where the walk from the
old `R(e₁ + 1)` ended in `G` (when the old `e₁ + 1` is not a corner of `c₁`). -/
theorem nw1_1T (not_corner : G.corner κ.c₁ (κ.e₁ + 1) = false) {r : GPort}
    (old_walk : G.FullReach (κ.c₁, κ.e₁ + 1, true) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, true) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- the cut edge's mate is glued back to it
  obtain ⟨_, _, mate_back⟩ := ok.two_mate shared
  -- in `G`: through the hook at the old `e₁ + 1` to `L`, then across the cut edge to `L_{c₀}(e₀ + 1)`
  have first_step : G.sigma (G.tau (κ.c₁, κ.e₁ + 1, true)) = some (κ.c₀, κ.e₀ + 1, false) := by
    rw [tau_of_not_corner not_corner, Bool.not_true, sigmaL, prv_succ', mate_back]
    simp only [Option.map_some, nxt_of_lt' e₀_succ_lt]
  -- in the cut gluing, one step from `R(e₁ + 1)` reaches `L_{c₀}` at the old `e₀ + 1` too; then the rest of the old
  -- walk
  exact ok.step1_1T shared
    (ok.port_reach ⟨ok.c₀, show κ.e₀ + 1 < G.E κ.c₀ by omega⟩ (fullReach_first first_step old_walk))

/-- New vertex `e₁ + 1` of `c₁`, port `L`: the walk from `L(e₁ + 1)` in the cut gluing ends where the walk from the
old `L(e₁ + 1)` ended in `G`. -/
theorem nw1_1F {r : GPort} (old_walk : G.FullReach (κ.c₁, κ.e₁ + 1, false) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, false) (κ.port r) := by
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, _, _⟩ := ok.two_mate shared
  -- and not its last edge
  have e₁_succ_lt := ok.e₁ shared
  -- two steps from `L(e₁ + 1)` reach `L_{c₁}` at the old `e₁ + 1`; from there, the old walk
  exact ok.step1_1F shared (ok.port_reach ⟨c₁_lt, show κ.e₁ + 1 < G.E κ.c₁ by omega⟩ old_walk)

end

/-! ### A cut creates no closed strand (Lemma 7.1) -/

/-- **A cut creates no closed strand** (the end of the proof of Lemma 7.1). If the walk of `G` from every port reaches
the rim, so does the walk of the cut gluing from every port. From a port at an old vertex it is the image of a walk of
`G` (`Sim.reach`). From a port at a new vertex it follows one of the two connections along the new path, for one or
two crossings, to a port at an old vertex (`step0_2F`, …); or, if the cut edge lies on the rim, it leaves at once,
through the new hook. -/
theorem noLoops (no_loops : ∀ x, G.Valid x → ∃ r, G.FullReach x r) :
    ∀ x, (subdiv G κ).Valid x → ∃ r, (subdiv G κ).FullReach x r := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := ok.e₀
  -- from the image of a port of `G`: the image of its walk
  have old : ∀ y, G.Valid y → ∃ r, (subdiv G κ).FullReach (κ.port y) r := fun y y_valid => by
    obtain ⟨r, walk⟩ := no_loops y y_valid
    exact ⟨κ.port r, ok.port_reach y_valid walk⟩
  rintro ⟨c, v, s⟩ ⟨c_lt, v_lt⟩
  by_cases new₀ : c = κ.c₀ ∧ κ.e₀ < v ∧ v ≤ κ.e₀ + 2
  · obtain ⟨rfl, v_gt, v_le⟩ := new₀
    obtain ⟨i, i_ge, i_le, rfl⟩ : ∃ i, 1 ≤ i ∧ i ≤ 2 ∧ v = κ.e₀ + i := ⟨v - κ.e₀, by omega, by omega, by omega⟩
    by_cases shared : κ.two = true
    · -- the mate of the cut edge is an actual edge of an actual child
      obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
      -- and not its last edge
      have e₁_succ_lt := ok.e₁ shared
      obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
      · cases s
        · -- `L(e₀ + 1)`: to `L_{c₀}` at the old `e₀ + 1`
          obtain ⟨r, walk⟩ := old (κ.c₀, κ.e₀ + 1, false) ⟨ok.c₀, e₀_lt⟩
          exact ⟨r, ok.step0_1F shared walk⟩
        · -- `R(e₀ + 1)`: to `L_{c₁}` at the old `e₁ + 1`
          obtain ⟨r, walk⟩ := old (κ.c₁, κ.e₁ + 1, false) ⟨c₁_lt, e₁_succ_lt⟩
          exact ⟨r, ok.step0_1T shared walk⟩
      · cases s
        · -- `L(e₀ + 2)`: to `R_{c₁}(e₁)`
          obtain ⟨r, walk⟩ := old (κ.c₁, κ.e₁, true) ⟨c₁_lt, e₁_lt⟩
          exact ⟨r, ok.step0_2F shared walk⟩
        · -- `R(e₀ + 2)`: to `R_{c₀}(e₀)`
          obtain ⟨r, walk⟩ := old (κ.c₀, κ.e₀, true) ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩
          exact ⟨r, ok.step0_2T shared walk⟩
    · -- the cut edge lies on the rim: through the new hook, onto a new rim edge
      refine ⟨(subdiv G κ).tau (κ.c₀, κ.e₀ + i, s), 0, .stop ?_⟩
      rw [ok.tau_new₀ i_ge i_le]
      cases s
      · -- from `L` to `R`, on the new edge `e₀ + i`
        rw [Bool.not_false, sigmaR, ok.mate_new₀ i_le, ite_eq_right shared]; rfl
      · -- from `R` to `L`, on the new edge `e₀ + i - 1`
        rw [Bool.not_true, sigmaL, show κ.e₀ + i = (κ.e₀ + (i - 1)) + 1 by omega, prv_succ',
          ok.mate_new₀ (by omega), ite_eq_right shared]; rfl
  · by_cases new₁ : κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ < v ∧ v ≤ κ.e₁ + 2
    · obtain ⟨shared, rfl, v_gt, v_le⟩ := new₁
      -- the mate of the cut edge is an actual edge of an actual child
      obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
      -- and not its last edge
      have e₁_succ_lt := ok.e₁ shared
      obtain rfl | rfl : v = κ.e₁ + 1 ∨ v = κ.e₁ + 2 := by omega
      · cases s
        · -- `L(e₁ + 1)`: to `L_{c₁}` at the old `e₁ + 1`
          obtain ⟨r, walk⟩ := old (κ.c₁, κ.e₁ + 1, false) ⟨c₁_lt, e₁_succ_lt⟩
          exact ⟨r, ok.step1_1F shared walk⟩
        · -- `R(e₁ + 1)`: to `L_{c₀}` at the old `e₀ + 1`
          obtain ⟨r, walk⟩ := old (κ.c₀, κ.e₀ + 1, false) ⟨ok.c₀, e₀_lt⟩
          exact ⟨r, ok.step1_1T shared walk⟩
      · cases s
        · -- `L(e₁ + 2)`: to `R_{c₀}(e₀)`
          obtain ⟨r, walk⟩ := old (κ.c₀, κ.e₀, true) ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩
          exact ⟨r, ok.step1_2F shared walk⟩
        · -- `R(e₁ + 2)`: to `R_{c₁}(e₁)`
          obtain ⟨r, walk⟩ := old (κ.c₁, κ.e₁, true) ⟨c₁_lt, e₁_lt⟩
          exact ⟨r, ok.step1_2T shared walk⟩
    · -- an old vertex: the image of a port of `G`
      obtain ⟨u, u_lt, shifted⟩ := ok.preimage v_lt new₀ new₁
      obtain ⟨r, walk⟩ := old (c, u, s) ⟨c_lt, u_lt⟩
      simp only [Cut.port, shifted] at walk
      exact ⟨r, walk⟩

end Cut.OK

end SpectreKnot.Gluing

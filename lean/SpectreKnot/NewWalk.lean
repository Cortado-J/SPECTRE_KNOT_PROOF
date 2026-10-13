/-
Walks through the two new vertices of a cut edge. When an edge shared by two children is cut into three, each child
gets two new vertices on it. The strand through a new vertex's hook is the strand that, before the cut, ran through
the hook at an old vertex next to the cut: `e₀ + 2` follows the old `e₀`, and `e₀ + 1` the old `e₀ + 1` (and the same
on the other side). Used to carry the junction map (`StepMap.lean`) through moves.
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
    rw [if_pos shared] at cut_mate
    rw [cut_mate]; rfl
  -- the rest of the old walk, from `R_{c₁}(e₁)`, carried into the cut gluing
  have new_walk := ok.port_reach ⟨c₁_lt, e₁_lt⟩ (fullReach_first first_step old_walk)
  simp only [Cut.port, ok.sh_c₁_le shared (Nat.le_refl _)] at new_walk
  -- in the cut gluing: through the new hook, then across new edge `e₀ + 2` to `R_{c₁}(e₁)`
  refine fullReach_step ?_ new_walk
  rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), if_pos shared]
  simp

/-- New vertex `e₀ + 2` of `c₀`, port `R`: the walk from `R(e₀ + 2)` in the cut gluing ends where the walk from the
old `R(e₀)` ended in `G`. -/
theorem nw0_2T {r : GPort} (old_walk : G.FullReach (κ.c₀, κ.e₀, true) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 2, true) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  -- the old walk from `R_{c₀}(e₀)`, carried into the cut gluing (where `e₀` does not move)
  have new_walk := ok.port_reach ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩ old_walk
  simp only [Cut.port, ok.sh_c₀_le (Nat.le_refl _)] at new_walk
  -- two steps: across new edge `e₀ + 1` to `L_{c₁}(e₁ + 2)`, then across new edge `e₁ + 2` back to `R_{c₀}(e₀)`
  refine fullReach_step (y := (κ.c₁, κ.e₁ + 2, false)) ?_ (fullReach_step ?_ new_walk)
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, ok.E_c₀, show κ.e₀ + 2 = (κ.e₀ + 1) + 1 from rfl,
      prv_succ', ok.mate_new₀ (by omega), if_pos shared]
    simp only [Option.map_some, show κ.e₁ + 2 - 1 = κ.e₁ + 1 by omega, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 1 + 1 <
      (G.E κ.c₁ + 2) by omega)]
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
    simp

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
    rw [if_pos shared] at cut_mate
    rw [cut_mate]
    simp only [Option.map_some, nxt_of_lt' e₁_succ_lt]
  -- the rest of the old walk, from `L_{c₁}(e₁ + 1)`, carried into the cut gluing (where it is `e₁ + 3`)
  have new_walk := ok.port_reach ⟨c₁_lt, show κ.e₁ + 1 < G.E κ.c₁ by omega⟩ (fullReach_first first_step old_walk)
  simp only [Cut.port, ok.sh_c₁_gt shared (show κ.e₁ < κ.e₁ + 1 by omega)] at new_walk
  -- in the cut gluing: through the new hook, then across new edge `e₀` to `L_{c₁}(e₁ + 3)`
  refine fullReach_step ?_ new_walk
  rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₀, if_pos shared]
  simp only [Option.map_some, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 2 + 1 < G.E κ.c₁ + 2 by omega)]

/-- New vertex `e₀ + 1` of `c₀`, port `L`: the walk from `L(e₀ + 1)` in the cut gluing ends where the walk from the
old `L(e₀ + 1)` ended in `G`. -/
theorem nw0_1F {r : GPort} (old_walk : G.FullReach (κ.c₀, κ.e₀ + 1, false) r) :
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + 1, false) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  -- the old walk from `L_{c₀}(e₀ + 1)`, carried into the cut gluing (where it is `e₀ + 3`)
  have new_walk := ok.port_reach ⟨ok.c₀, show κ.e₀ + 1 < G.E κ.c₀ by omega⟩ old_walk
  simp only [Cut.port, ok.sh_c₀_gt (show κ.e₀ < κ.e₀ + 1 by omega)] at new_walk
  -- two steps: across new edge `e₀ + 1` to `R_{c₁}(e₁ + 1)`, then across new edge `e₁` to `L_{c₀}(e₀ + 3)`
  refine fullReach_step (y := (κ.c₁, κ.e₁ + 1, true)) ?_ (fullReach_step ?_ new_walk)
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), if_pos shared]
    simp only [Option.map_some, show κ.e₁ + 2 - 1 = κ.e₁ + 1 by omega]
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₁ shared]
    simp only [Option.map_some, ok.E_c₀, nxt_of_lt' (show κ.e₀ + 2 + 1 < G.E κ.c₀ + 2 by omega)]

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
  -- the rest of the old walk, from `R_{c₀}(e₀)`, carried into the cut gluing
  have new_walk := ok.port_reach ⟨ok.c₀, show κ.e₀ < G.E κ.c₀ by omega⟩ (fullReach_first first_step old_walk)
  simp only [Cut.port, ok.sh_c₀_le (Nat.le_refl _)] at new_walk
  -- in the cut gluing: through the new hook, then across new edge `e₁ + 2` to `R_{c₀}(e₀)`
  refine fullReach_step ?_ new_walk
  rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
  simp

/-- New vertex `e₁ + 2` of `c₁`, port `R`: the walk from `R(e₁ + 2)` in the cut gluing ends where the walk from the
old `R(e₁)` ended in `G`. -/
theorem nw1_2T {r : GPort} (old_walk : G.FullReach (κ.c₁, κ.e₁, true) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 2, true) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
  -- and not its last edge
  have e₁_succ_lt := ok.e₁ shared
  -- the old walk from `R_{c₁}(e₁)`, carried into the cut gluing (where `e₁` does not move)
  have new_walk := ok.port_reach ⟨c₁_lt, e₁_lt⟩ old_walk
  simp only [Cut.port, ok.sh_c₁_le shared (Nat.le_refl _)] at new_walk
  -- two steps: across new edge `e₁ + 1` to `L_{c₀}(e₀ + 2)`, then across new edge `e₀ + 2` back to `R_{c₁}(e₁)`
  refine fullReach_step (y := (κ.c₀, κ.e₀ + 2, false)) ?_ (fullReach_step ?_ new_walk)
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, ok.E_c₁ shared,
      show κ.e₁ + 2 = (κ.e₁ + 1) + 1 from rfl, prv_succ', ok.mate_new₁ shared (by omega)]
    simp only [Option.map_some, show κ.e₀ + 2 - 1 = κ.e₀ + 1 by omega, ok.E_c₀,
      nxt_of_lt' (show κ.e₀ + 1 + 1 < G.E κ.c₀ + 2 by omega)]
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₀ (by omega), if_pos shared]
    simp

/-- New vertex `e₁ + 1` of `c₁`, port `R`: the walk from `R(e₁ + 1)` in the cut gluing ends where the walk from the
old `R(e₁ + 1)` ended in `G` (when the old `e₁ + 1` is not a corner of `c₁`). -/
theorem nw1_1T (not_corner : G.corner κ.c₁ (κ.e₁ + 1) = false) {r : GPort}
    (old_walk : G.FullReach (κ.c₁, κ.e₁ + 1, true) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, true) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- nor is its mate the last edge of `c₁`
  have e₁_succ_lt := ok.e₁ shared
  -- the cut edge's mate is glued back to it
  obtain ⟨_, _, mate_back⟩ := ok.two_mate shared
  -- in `G`: through the hook at the old `e₁ + 1` to `L`, then across the cut edge to `L_{c₀}(e₀ + 1)`
  have first_step : G.sigma (G.tau (κ.c₁, κ.e₁ + 1, true)) = some (κ.c₀, κ.e₀ + 1, false) := by
    rw [tau_of_not_corner not_corner, Bool.not_true, sigmaL, prv_succ', mate_back]
    simp only [Option.map_some, nxt_of_lt' e₀_succ_lt]
  -- the rest of the old walk, from `L_{c₀}(e₀ + 1)`, carried into the cut gluing (where it is `e₀ + 3`)
  have new_walk := ok.port_reach ⟨ok.c₀, show κ.e₀ + 1 < G.E κ.c₀ by omega⟩ (fullReach_first first_step old_walk)
  simp only [Cut.port, ok.sh_c₀_gt (show κ.e₀ < κ.e₀ + 1 by omega)] at new_walk
  -- in the cut gluing: through the new hook, then across new edge `e₁` to `L_{c₀}(e₀ + 3)`
  refine fullReach_step ?_ new_walk
  rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₁ shared]
  simp only [Option.map_some, ok.E_c₀, nxt_of_lt' (show κ.e₀ + 2 + 1 < G.E κ.c₀ + 2 by omega)]

/-- New vertex `e₁ + 1` of `c₁`, port `L`: the walk from `L(e₁ + 1)` in the cut gluing ends where the walk from the
old `L(e₁ + 1)` ended in `G`. -/
theorem nw1_1F {r : GPort} (old_walk : G.FullReach (κ.c₁, κ.e₁ + 1, false) r) :
    (subdiv G κ).FullReach (κ.c₁, κ.e₁ + 1, false) (κ.port r) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_succ_lt := ok.e₀
  -- the mate of the cut edge is an actual edge of an actual child
  obtain ⟨c₁_lt, e₁_lt, _⟩ := ok.two_mate shared
  -- and not its last edge
  have e₁_succ_lt := ok.e₁ shared
  -- the old walk from `L_{c₁}(e₁ + 1)`, carried into the cut gluing (where it is `e₁ + 3`)
  have new_walk := ok.port_reach ⟨c₁_lt, show κ.e₁ + 1 < G.E κ.c₁ by omega⟩ old_walk
  simp only [Cut.port, ok.sh_c₁_gt shared (show κ.e₁ < κ.e₁ + 1 by omega)] at new_walk
  -- two steps: across new edge `e₁ + 1` to `R_{c₀}(e₀ + 1)`, then across new edge `e₀` to `L_{c₁}(e₁ + 3)`
  refine fullReach_step (y := (κ.c₀, κ.e₀ + 1, true)) ?_ (fullReach_step ?_ new_walk)
  · rw [ok.tau_new₁ shared (by omega) (by omega), Bool.not_false, sigmaR, ok.mate_new₁ shared (by omega)]
    simp only [Option.map_some, show κ.e₀ + 2 - 1 = κ.e₀ + 1 by omega]
  · rw [ok.tau_new₀ (by omega) (by omega), Bool.not_true, sigmaL, prv_succ', ok.mate_cut₀, if_pos shared]
    simp only [Option.map_some, ok.E_c₁ shared, nxt_of_lt' (show κ.e₁ + 2 + 1 < G.E κ.c₁ + 2 by omega)]

end

end Cut.OK

end SpectreKnot.Gluing

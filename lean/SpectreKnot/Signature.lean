/-
The signature of a composition (the conclusion of the induction step), stated without lists: a parent rim vertex is
found by turning about a vertex of a child (`Rot`). The signature survives cutting an edge (`Cut.OK.sig`) and passing
to an equivalent gluing (`Sig.congr`); that is what the parity lemma needs.
-/
import SpectreKnot.Subdivide

namespace SpectreKnot.Gluing

variable {G G' : Gluing}

/-! ### Turning about a vertex -/

/-- Turning about a vertex inside the parent. Vertex `u` of child `c` is where its edge `u` starts. If that edge is
glued to edge `k'` of child `c'`, the same point is where edge `k'` ends, so the next edge about it is edge `k' + 1` of
`c'`. `Rot G (c, u) r`: turning from vertex `u` of `c` reaches the vertex `r`, whose edge is on the parent's rim. -/
inductive Rot (G : Gluing) : Nat × Nat → Nat × Nat → Prop
  | stop {c u : Nat} : G.mate c u = none → Rot G (c, u) (c, u)
  | step {c u c' k' : Nat} {r : Nat × Nat} :
      G.mate c u = some (c', k') → Rot G (c', nxt (G.E c') k') r → Rot G (c, u) r

/-- Turning about a vertex has one result. -/
theorem Rot.unique {x r r' : Nat × Nat} (turn : G.Rot x r) (turn' : G.Rot x r') : r = r' := by
  induction turn generalizing r' with
  | stop on_rim =>
    cases turn' with
    | stop _ => rfl
    | step glued _ => rw [on_rim] at glued; contradiction
  | step glued _ ih =>
    cases turn' with
    | stop on_rim => rw [glued] at on_rim; contradiction
    | step glued' rest' =>
      rw [glued] at glued'
      simp only [Option.some.injEq, Prod.mk.injEq] at glued'
      obtain ⟨rfl, rfl⟩ := glued'
      exact ih rest'

/-- Vertex `u` of child `c` is a parent rim vertex, reached along the parent's rim: the edge before it, `u - 1`, is on
the parent's rim. (Its port `L` is then a port of the parent.) -/
def RimL (G : Gluing) (c u : Nat) : Prop := c < G.n ∧ u < G.E c ∧ G.mate c (prv (G.E c) u) = none

/-! ### The signature -/

/-- **The signature** of the parent, for a gluing whose crossover child is `g` (Def 4.3 at the parent's level):
* the gluing is well formed, and the walk from every port ends on the parent's rim (no closed strand);
* at every parent rim vertex, reached along the rim at vertex `u` of child `c` and left along the rim at vertex `u₂`
  of child `c₂` (`Rot`), the strand from the port `L` there leaves at the port `R` there (a hook), except at the
  crossover child's corners `A` and `B`;
* those corners are parent rim vertices (their edges lie on the parent's rim), and carry the crossover:
  `R(A) ↔ R(B)` and `L(A) ↔ L(B)`. -/
structure Sig (G : Gluing) (g : Nat) : Prop where
  wf : G.WF
  noLoops : ∀ x, G.Valid x → ∃ r, G.FullReach x r
  hooks : ∀ c u, G.RimL c u → ∃ c₂ u₂, G.Rot (c, u) (c₂, u₂) ∧
    ((c₂ = g ∧ (u₂ = G.A g ∨ u₂ = G.B g)) ∨ G.FullReach (c, u, false) (c₂, u₂, true))
  g_lt : g < G.n
  rimA : G.mate g (G.A g) = none
  rimB : G.mate g (G.B g) = none
  crossR : G.FullReach (g, G.A g, true) (g, G.B g, true)
  crossL : ∃ cA uA cB uB, G.RimL cA uA ∧ G.Rot (cA, uA) (g, G.A g) ∧ G.RimL cB uB ∧ G.Rot (cB, uB) (g, G.B g) ∧
    G.FullReach (cA, uA, false) (cB, uB, false)

/-! ### Equivalent gluings -/

namespace Equiv

variable (equiv : Equiv G G')

include equiv

/-- Turning about a vertex of a child gives the same result in an equivalent gluing. -/
theorem rot (G_wf : G.WF) {x r : Nat × Nat} (turn : G.Rot x r) : x.1 < G.n → x.2 < G.E x.1 → G'.Rot x r := by
  induction turn with
  | @stop c u on_rim => intro c_lt u_lt; exact .stop (by rw [← equiv.mate c u c_lt u_lt]; exact on_rim)
  | @step c u c' k' r glued _ ih =>
    intro c_lt u_lt
    obtain ⟨c'_lt, k'_lt, _⟩ := G_wf.mate_valid _ _ _ _ c_lt u_lt glued
    exact .step (by rw [← equiv.mate c u c_lt u_lt]; exact glued)
      (by rw [← equiv.E c' c'_lt]; exact ih c'_lt (nxt_lt k'_lt))

/-- A parent rim vertex of `G` is one of an equivalent gluing `G'`. -/
theorem rimL {c u : Nat} (rim_vertex : G.RimL c u) : G'.RimL c u := by
  obtain ⟨c_lt, u_lt, prev_on_rim⟩ := rim_vertex
  refine ⟨equiv.n ▸ c_lt, (equiv.E c c_lt) ▸ u_lt, ?_⟩
  rw [← equiv.E c c_lt, ← equiv.mate c _ c_lt (prv_lt u_lt)]; exact prev_on_rim

/-- A gluing equivalent to one with the signature has the signature, with the same crossover child. -/
theorem sig {g : Nat} (has_sig : Sig G g) : Sig G' g where
  wf := equiv.wf has_sig.wf
  noLoops x x_valid := by
    obtain ⟨r, reach⟩ := has_sig.noLoops x (equiv.valid' x_valid)
    exact ⟨r, equiv.fullReach has_sig.wf (equiv.valid' x_valid) reach⟩
  hooks c u rim_vertex := by
    -- the vertex is a parent rim vertex of `G`
    have rim_vertex_G : G.RimL c u := equiv.symm.rimL rim_vertex
    obtain ⟨c₂, u₂, turn, hook⟩ := has_sig.hooks c u rim_vertex_G
    refine ⟨c₂, u₂, equiv.rot has_sig.wf turn rim_vertex_G.1 rim_vertex_G.2.1, ?_⟩
    rw [← equiv.A g has_sig.g_lt, ← equiv.B g has_sig.g_lt]
    rcases hook with at_corner | joins
    · exact Or.inl at_corner
    · exact Or.inr (equiv.fullReach has_sig.wf ⟨rim_vertex_G.1, rim_vertex_G.2.1⟩ joins)
  g_lt := equiv.n ▸ has_sig.g_lt
  rimA := by
    rw [← equiv.A g has_sig.g_lt, ← equiv.mate g _ has_sig.g_lt (has_sig.wf.A_lt g has_sig.g_lt)]
    exact has_sig.rimA
  rimB := by
    rw [← equiv.B g has_sig.g_lt, ← equiv.mate g _ has_sig.g_lt (has_sig.wf.B_lt g has_sig.g_lt)]
    exact has_sig.rimB
  crossR := by
    rw [← equiv.A g has_sig.g_lt, ← equiv.B g has_sig.g_lt]
    exact equiv.fullReach has_sig.wf ⟨has_sig.g_lt, has_sig.wf.A_lt g has_sig.g_lt⟩ has_sig.crossR
  crossL := by
    obtain ⟨cA, uA, cB, uB, rim_A, turn_A, rim_B, turn_B, joins⟩ := has_sig.crossL
    rw [← equiv.A g has_sig.g_lt, ← equiv.B g has_sig.g_lt]
    exact ⟨cA, uA, cB, uB, equiv.rimL rim_A, equiv.rot has_sig.wf turn_A rim_A.1 rim_A.2.1, equiv.rimL rim_B,
      equiv.rot has_sig.wf turn_B rim_B.1 rim_B.2.1, equiv.fullReach has_sig.wf ⟨rim_A.1, rim_A.2.1⟩ joins⟩

end Equiv

/-! ### Cutting an edge -/

namespace Cut.OK

set_option linter.unusedSectionVars false

variable {κ : Cut} (cut_ok : κ.OK G)

include cut_ok

/-- A rim edge stays a rim edge. -/
theorem mate_none {c k : Nat} (on_rim : G.mate c k = none) : (subdiv G κ).mate c (κ.sh c k) = none := by
  by_cases is_cut₀ : c = κ.c₀ ∧ k = κ.e₀
  · obtain ⟨rfl, rfl⟩ := is_cut₀
    rw [cut_ok.sh_c₀_le (Nat.le_refl _), cut_ok.mate_cut₀, cut_ok.two_false on_rim]; rfl
  · by_cases is_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ k = κ.e₁
    · obtain ⟨cut_glued, rfl, rfl⟩ := is_cut₁
      rw [(cut_ok.two_mate cut_glued).2.2] at on_rim; contradiction
    · rw [cut_ok.mate_old is_cut₀ is_cut₁, on_rim]; rfl

/-- The vertex after a rim edge stays the vertex after a rim edge. -/
theorem rimL_port {c u : Nat} (rim_vertex : G.RimL c u) : (subdiv G κ).RimL c (κ.sh c u) := by
  obtain ⟨c_lt, u_lt, prev_on_rim⟩ := rim_vertex
  refine ⟨c_lt, cut_ok.sh_lt u_lt, ?_⟩
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  by_cases after_cut₀ : c = κ.c₀ ∧ u = κ.e₀ + 1
  · obtain ⟨rfl, rfl⟩ := after_cut₀
    rw [prv_succ'] at prev_on_rim
    -- the cut edge is on the rim, so only it is cut
    have cut_on_rim := cut_ok.two_false prev_on_rim
    rw [cut_ok.sh_c₀_gt (by omega), cut_ok.E_c₀, show κ.e₀ + 1 + 2 = (κ.e₀ + 2) + 1 by omega, prv_succ',
      cut_ok.mate_new₀ (by omega), cut_on_rim]; rfl
  · by_cases after_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ u = κ.e₁ + 1
    · obtain ⟨cut_glued, rfl, rfl⟩ := after_cut₁
      rw [prv_succ', (cut_ok.two_mate cut_glued).2.2] at prev_on_rim; contradiction
    · rw [cut_ok.prv_sh u_lt after_cut₀ after_cut₁]
      exact cut_ok.mate_none prev_on_rim

/-- Every vertex after a rim edge of the subdivided gluing is an old one, or one of the two new vertices of a cut rim
edge. -/
theorem rimL_pre {c u' : Nat} (rim_vertex : (subdiv G κ).RimL c u') :
    (∃ u, G.RimL c u ∧ κ.sh c u = u') ∨ (κ.two = false ∧ c = κ.c₀ ∧ (u' = κ.e₀ + 1 ∨ u' = κ.e₀ + 2)) := by
  obtain ⟨c_lt, u'_lt, prev_on_rim⟩ := rim_vertex
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  by_cases new₀ : c = κ.c₀ ∧ κ.e₀ < u' ∧ u' ≤ κ.e₀ + 2
  · obtain ⟨rfl, u'_gt, u'_le⟩ := new₀
    right
    -- the edge before a new vertex is a new edge
    have prev_edge : prv ((subdiv G κ).E κ.c₀) u' = κ.e₀ + (u' - 1 - κ.e₀) := by unfold prv; split <;> omega
    rw [prev_edge, cut_ok.mate_new₀ (by omega)] at prev_on_rim
    cases cut_glued : κ.two
    · exact ⟨rfl, rfl, by omega⟩
    · rw [cut_glued] at prev_on_rim; simp at prev_on_rim
  · by_cases new₁ : κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ < u' ∧ u' ≤ κ.e₁ + 2
    · exfalso
      obtain ⟨cut_glued, rfl, u'_gt, u'_le⟩ := new₁
      -- the edge before a new vertex is a new edge, which is glued
      have prev_edge : prv ((subdiv G κ).E κ.c₁) u' = κ.e₁ + (u' - 1 - κ.e₁) := by unfold prv; split <;> omega
      rw [prev_edge, cut_ok.mate_new₁ cut_glued (by omega)] at prev_on_rim; contradiction
    · left
      obtain ⟨u, u_lt, rfl⟩ := cut_ok.preimage u'_lt new₀ new₁
      refine ⟨u, ⟨c_lt, u_lt, ?_⟩, rfl⟩
      by_cases after_cut₀ : c = κ.c₀ ∧ u = κ.e₀ + 1
      · obtain ⟨rfl, rfl⟩ := after_cut₀
        rw [cut_ok.sh_c₀_gt (by omega), cut_ok.E_c₀, show κ.e₀ + 1 + 2 = (κ.e₀ + 2) + 1 by omega, prv_succ',
          cut_ok.mate_new₀ (by omega)] at prev_on_rim
        rw [prv_succ']
        cases cut_glued : κ.two
        · have cut_mate := cut_ok.mate  -- the cut edge lies on the rim
          rw [cut_glued] at cut_mate; rw [cut_mate]; rfl
        · rw [cut_glued] at prev_on_rim; simp at prev_on_rim
      · by_cases after_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ u = κ.e₁ + 1
        · exfalso
          obtain ⟨cut_glued, rfl, rfl⟩ := after_cut₁
          -- the partner edge is not the last edge of `c₁`
          have e₁_lt := cut_ok.e₁ cut_glued
          rw [cut_ok.sh_c₁_gt cut_glued (by omega), cut_ok.E_c₁ cut_glued,
            show κ.e₁ + 1 + 2 = (κ.e₁ + 2) + 1 by omega, prv_succ',
            cut_ok.mate_new₁ cut_glued (by omega)] at prev_on_rim
          contradiction
        · rw [cut_ok.prv_sh u_lt after_cut₀ after_cut₁] at prev_on_rim
          -- the edge before `u` is not the cut edge
          have not_cut₀ : ¬ (c = κ.c₀ ∧ prv (G.E c) u = κ.e₀) :=
            fun prev_cut => after_cut₀ ⟨prev_cut.1, cut_ok.prv_cut u_lt prev_cut⟩
          -- nor the partner edge
          have not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ prv (G.E c) u = κ.e₁) := fun ⟨cut_glued, is_c₁, prev_eq⟩ =>
            after_cut₁ ⟨cut_glued, is_c₁, cut_ok.prv_cut₁ cut_glued u_lt ⟨is_c₁, prev_eq⟩⟩
          rw [cut_ok.mate_old not_cut₀ not_cut₁, Option.map_eq_none_iff] at prev_on_rim
          exact prev_on_rim

/-- Turning about an old vertex gives the same result, renumbered. -/
theorem rot_port {x r : Nat × Nat} (turn : G.Rot x r) :
    x.1 < G.n → x.2 < G.E x.1 → (subdiv G κ).Rot (x.1, κ.sh x.1 x.2) (r.1, κ.sh r.1 r.2) := by
  induction turn with
  | @stop c u on_rim => intro _ _; exact .stop (cut_ok.mate_none on_rim)
  | @step c u c' k' r glued _ ih =>
    intro c_lt u_lt
    obtain ⟨c'_lt, k'_lt, _⟩ := cut_ok.wf.mate_valid _ _ _ _ c_lt u_lt glued
    -- the rest of the turn, renumbered
    have rest := ih c'_lt (nxt_lt k'_lt)
    dsimp only at rest ⊢
    by_cases is_cut₀ : c = κ.c₀ ∧ u = κ.e₀
    · obtain ⟨rfl, rfl⟩ := is_cut₀
      obtain ⟨cut_glued, partner⟩ := cut_ok.two_true glued
      simp only [Prod.mk.injEq] at partner
      obtain ⟨rfl, rfl⟩ := partner
      -- the partner edge is not the last edge of `c₁`
      have e₁_lt := cut_ok.e₁ cut_glued
      refine .step (c' := κ.c₁) (k' := κ.e₁ + 2) ?_ ?_
      · rw [cut_ok.sh_c₀_le (Nat.le_refl _), cut_ok.mate_cut₀, if_pos cut_glued]
      · rw [cut_ok.E_c₁ cut_glued, nxt_of_lt' (by omega)]
        rw [nxt_of_lt' e₁_lt, cut_ok.sh_c₁_gt cut_glued (by omega)] at rest
        exact rest
    · by_cases is_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ u = κ.e₁
      · obtain ⟨cut_glued, rfl, rfl⟩ := is_cut₁
        rw [(cut_ok.two_mate cut_glued).2.2] at glued
        simp only [Option.some.injEq, Prod.mk.injEq] at glued
        obtain ⟨rfl, rfl⟩ := glued
        -- the cut edge is not the last edge of `c₀`
        have e₀_lt := cut_ok.e₀
        refine .step (c' := κ.c₀) (k' := κ.e₀ + 2) ?_ ?_
        · rw [cut_ok.sh_c₁_le cut_glued (Nat.le_refl _), cut_ok.mate_cut₁ cut_glued]
        · rw [cut_ok.E_c₀, nxt_of_lt' (by omega)]
          rw [nxt_of_lt' e₀_lt, cut_ok.sh_c₀_gt (by omega)] at rest
          exact rest
      · refine .step (c' := c') (k' := κ.sh c' k') ?_ ?_
        · rw [cut_ok.mate_old is_cut₀ is_cut₁, glued]; rfl
        · obtain ⟨mate_not_cut₀, mate_not_cut₁⟩ := cut_ok.target_not_cut c_lt u_lt glued is_cut₀ is_cut₁
          rw [cut_ok.nxt_sh k'_lt mate_not_cut₀ mate_not_cut₁]; exact rest

/-- The two new vertices of a cut rim edge are parent rim vertices with a hook. -/
theorem new_hook (cut_on_rim : κ.two = false) {i : Nat} (i_ge : 1 ≤ i) (i_le : i ≤ 2) :
    (subdiv G κ).Rot (κ.c₀, κ.e₀ + i) (κ.c₀, κ.e₀ + i) ∧
    (subdiv G κ).FullReach (κ.c₀, κ.e₀ + i, false) (κ.c₀, κ.e₀ + i, true) := by
  -- the new edge starting at the vertex lies on the rim
  have on_rim : (subdiv G κ).mate κ.c₀ (κ.e₀ + i) = none := by rw [cut_ok.mate_new₀ (by omega), cut_on_rim]; rfl
  refine ⟨.stop on_rim, 0, ?_⟩
  -- the piece at the vertex joins its two ports, and the walk stops at port `R` there
  have stops := FReach.stop (G := subdiv G κ) (x := (κ.c₀, κ.e₀ + i, false))
    (by rw [cut_ok.tau_new₀ i_ge i_le, Bool.not_false, sigmaR, on_rim]; rfl)
  rw [cut_ok.tau_new₀ i_ge i_le, Bool.not_false] at stops
  exact stops

/-- **The signature survives cutting an edge.** -/
theorem sig {g : Nat} (has_sig : Sig G g) : Sig (subdiv G κ) g where
  wf := cut_ok.wf_subdiv
  noLoops := cut_ok.noLoops has_sig.noLoops
  hooks c u' rim_vertex := by
    rcases cut_ok.rimL_pre rim_vertex with ⟨u, old_rim_vertex, rfl⟩ | ⟨cut_on_rim, rfl, new_vertex⟩
    · obtain ⟨c₂, u₂, turn, hook⟩ := has_sig.hooks c u old_rim_vertex
      refine ⟨c₂, κ.sh c₂ u₂, cut_ok.rot_port turn old_rim_vertex.1 old_rim_vertex.2.1, ?_⟩
      rcases hook with ⟨rfl, at_A | at_B⟩ | joins
      · exact Or.inl ⟨rfl, Or.inl (by rw [at_A]; rfl)⟩
      · exact Or.inl ⟨rfl, Or.inr (by rw [at_B]; rfl)⟩
      · obtain ⟨k, walk⟩ := joins
        exact Or.inr (Sim.reach cut_ok.wf cut_ok.sim k _ _ ⟨old_rim_vertex.1, old_rim_vertex.2.1⟩ walk)
    · obtain ⟨i, i_ge, i_le, rfl⟩ : ∃ i, 1 ≤ i ∧ i ≤ 2 ∧ u' = κ.e₀ + i := by
        rcases new_vertex with rfl | rfl
        · exact ⟨1, by omega, by omega, rfl⟩
        · exact ⟨2, by omega, by omega, rfl⟩
      obtain ⟨turn, joins⟩ := cut_ok.new_hook cut_on_rim i_ge i_le
      exact ⟨κ.c₀, κ.e₀ + i, turn, Or.inr joins⟩
  g_lt := has_sig.g_lt
  rimA := cut_ok.mate_none has_sig.rimA
  rimB := cut_ok.mate_none has_sig.rimB
  crossR := by
    obtain ⟨k, walk⟩ := has_sig.crossR
    exact Sim.reach cut_ok.wf cut_ok.sim k _ _ ⟨has_sig.g_lt, has_sig.wf.A_lt g has_sig.g_lt⟩ walk
  crossL := by
    obtain ⟨cA, uA, cB, uB, rim_A, turn_A, rim_B, turn_B, ⟨k, walk⟩⟩ := has_sig.crossL
    exact ⟨cA, κ.sh cA uA, cB, κ.sh cB uB, cut_ok.rimL_port rim_A, cut_ok.rot_port turn_A rim_A.1 rim_A.2.1,
      cut_ok.rimL_port rim_B, cut_ok.rot_port turn_B rim_B.1 rim_B.2.1,
      Sim.reach cut_ok.wf cut_ok.sim k _ _ ⟨rim_A.1, rim_A.2.1⟩ walk⟩

end Cut.OK

end SpectreKnot.Gluing

/-
Simulations between gluings, and subdivision of an edge (paper Lemma 7.1, lengthening: the engine of the parity lemma).

A *simulation* `Sim G G' φ` maps the ports of `G` into those of `G'` so that `τ` commutes with `φ`, rim ports go to
rim ports, and each crossing `σ x = y` of `G` becomes a forced chain of crossings `Cross (φ x) (φ y)` in `G'` (one
crossing, or several joined by `τ`). Then every walk of `G` maps to a walk of `G'` (`Sim.reach`).

*Subdividing* an edge into three (`subdiv`) is a simulation: by the zigzag lemma with `n = 3` (`cross_three`), crossing
the three short edges ends where crossing the long one did. Lengthening a side of a composition by 2 is such a
subdivision, so the parity lemma follows by repeated subdivision from the level-1 lengths. That a cut creates no closed
strand is `Cut.OK.noLoops`, in `NewWalk.lean`.
-/
import SpectreKnot.Gluing
import SpectreKnot.Zigzag

namespace SpectreKnot.Gluing

variable {G G' : Gluing}

/-! ### Forced chains of crossings -/

/-- `Cross p q`: from port `p`, crossing an edge (`σ`) and then, while not yet at `q`, going through a piece (`τ`) and
crossing again, leads to `q`: a connection of the zigzag lemma (`Zigzag.Chain`) in the gluing. -/
abbrev Cross (G : Gluing) : GPort → GPort → Prop := Zigzag.Chain G.sigma G.tau

/-- A forced chain of crossings from `p` to `q` extends walks backwards: if the piece at `x` leads to `p`, and the walk
from `q` ends at the rim port `r`, then so does the walk from `x`. -/
theorem Cross.reach {p q : GPort} (cross : G.Cross p q) :
    ∀ x r, G.tau x = p → G.FullReach q r → G.FullReach x r := by
  induction cross with
  | one crosses =>
    intro x r tau_x reach_q
    obtain ⟨k, walk⟩ := reach_q
    exact ⟨k + 1, .step (by rw [tau_x]; exact crosses) walk⟩
  | more crosses _ ih =>
    intro x r tau_x reach_q
    obtain ⟨k, walk⟩ := ih _ r rfl reach_q
    exact ⟨k + 1, .step (by rw [tau_x]; exact crosses) walk⟩

/-- In a well-formed gluing, crossing an edge from a valid port lands on a valid port. -/
theorem sigma_valid (G_wf : G.WF) {x y : GPort} (x_valid : G.Valid x) (crosses : G.sigma x = some y) : G.Valid y := by
  obtain ⟨c, u, s⟩ := x
  obtain ⟨c_lt, u_lt⟩ := x_valid
  cases s with
  | true =>
    simp only [sigma, Option.map_eq_some_iff] at crosses
    obtain ⟨⟨c', k'⟩, glued, rfl⟩ := crosses
    -- port `R`: across edge `u` itself, to edge `k'` of `c'`
    obtain ⟨c'_lt, k'_lt, _⟩ := G_wf.mate_valid c u c' k' c_lt u_lt glued
    exact ⟨c'_lt, k'_lt⟩
  | false =>
    simp only [sigma, Option.map_eq_some_iff] at crosses
    obtain ⟨⟨c', k'⟩, glued, rfl⟩ := crosses
    -- port `L`: across the edge before vertex `u`, to the vertex after edge `k'` of `c'`
    obtain ⟨c'_lt, k'_lt, _⟩ := G_wf.mate_valid c _ c' k' c_lt (prv_lt u_lt) glued
    exact ⟨c'_lt, nxt_lt k'_lt⟩

/-! ### Simulations -/

/-- `φ` simulates `G` in `G'`. -/
structure Sim (G G' : Gluing) (φ : GPort → GPort) : Prop where
  valid : ∀ x, G.Valid x → G'.Valid (φ x)
  tau : ∀ x, G.Valid x → G'.tau (φ x) = φ (G.tau x)
  rim : ∀ x, G.Valid x → G.sigma x = none → G'.sigma (φ x) = none
  cross : ∀ x y, G.Valid x → G.sigma x = some y → G'.Cross (φ x) (φ y)

/-- Along a simulation, every walk of `G` from a valid port maps to a walk of `G'` between the images of its ends. -/
theorem Sim.reach (G_wf : G.WF) {φ : GPort → GPort} (sim : Sim G G' φ) :
    ∀ k x r, G.Valid x → G.FReach k x r → G'.FullReach (φ x) (φ r) := by
  intro k x r x_valid walk
  induction walk with
  | @stop x on_rim =>
    -- the piece at `x` commutes with `φ`
    have tau_comm := sim.tau x x_valid
    refine ⟨0, ?_⟩
    -- the image of the piece's other end is a rim port of `G'`, so the walk of `G'` stops there too
    have stops := FReach.stop (G := G') (x := φ x)
      (by rw [tau_comm]; exact sim.rim _ (tau_valid G_wf x_valid) on_rim)
    rwa [tau_comm] at stops
  | @step k x y r crosses _ ih =>
    -- the port crossed to is valid, so the rest of the walk maps too
    have y_valid := sigma_valid G_wf (tau_valid G_wf x_valid) crosses
    exact Cross.reach (sim.cross _ _ (tau_valid G_wf x_valid) crosses) (φ x) (φ r) (sim.tau x x_valid) (ih y_valid)

/-! ### Equivalent gluings -/

/-- Two gluings that agree on their actual children: the same number of children, rim lengths, corners, and gluing
of actual edges. (They may differ outside, where nothing is ever looked up.) -/
structure Equiv (G G' : Gluing) : Prop where
  n : G.n = G'.n
  E : ∀ c, c < G.n → G.E c = G'.E c
  A : ∀ c, c < G.n → G.A c = G'.A c
  B : ∀ c, c < G.n → G.B c = G'.B c
  mate : ∀ c k, c < G.n → k < G.E c → G.mate c k = G'.mate c k

namespace Equiv

variable (equiv : Equiv G G')

include equiv

/-- A valid port of `G'` is a valid port of an equivalent gluing `G`. -/
theorem valid' {x : GPort} (x_valid : G'.Valid x) : G.Valid x := by
  -- the port's child is a child of `G`
  have c_lt : x.1 < G.n := equiv.n ▸ x_valid.1
  exact ⟨c_lt, (equiv.E _ c_lt).symm ▸ x_valid.2⟩

/-- Equivalent gluings have the same pieces at valid ports. -/
theorem tau {x : GPort} (x_valid : G.Valid x) : G'.tau x = G.tau x := by
  obtain ⟨c, u, s⟩ := x
  simp only [Gluing.tau, equiv.A c x_valid.1, equiv.B c x_valid.1]

/-- Equivalent gluings cross edges in the same way at valid ports. -/
theorem sigma (G_wf : G.WF) {x : GPort} (x_valid : G.Valid x) : G'.sigma x = G.sigma x := by
  obtain ⟨c, u, s⟩ := x
  obtain ⟨c_lt, u_lt⟩ := x_valid
  cases s with
  | true => simp only [Gluing.sigma, equiv.mate c u c_lt u_lt]
  | false =>
    simp only [Gluing.sigma, ← equiv.E c c_lt, ← equiv.mate c _ c_lt (prv_lt u_lt)]
    cases glued : G.mate c (prv (G.E c) u) with
    | none => rfl
    | some p =>
      obtain ⟨c', k'⟩ := p
      -- the child glued to is a child of `G`, so its rim length is the same in `G'`
      obtain ⟨c'_lt, _, _⟩ := G_wf.mate_valid c _ c' k' c_lt (prv_lt u_lt) glued
      simp [equiv.E c' c'_lt]

/-- A gluing equivalent to a well-formed one is well formed. -/
theorem wf (G_wf : G.WF) : G'.WF where
  E_pos c c_lt := by rw [← equiv.E c (equiv.n ▸ c_lt)]; exact G_wf.E_pos c (equiv.n ▸ c_lt)
  A_lt c c_lt := by
    rw [← equiv.E c (equiv.n ▸ c_lt), ← equiv.A c (equiv.n ▸ c_lt)]; exact G_wf.A_lt c (equiv.n ▸ c_lt)
  B_lt c c_lt := by
    rw [← equiv.E c (equiv.n ▸ c_lt), ← equiv.B c (equiv.n ▸ c_lt)]; exact G_wf.B_lt c (equiv.n ▸ c_lt)
  A_ne_B c c_lt := by
    rw [← equiv.A c (equiv.n ▸ c_lt), ← equiv.B c (equiv.n ▸ c_lt)]; exact G_wf.A_ne_B c (equiv.n ▸ c_lt)
  mate_valid c k c' k' c_lt k_lt glued := by
    -- the child is a child of `G`
    have c_lt_G : c < G.n := equiv.n ▸ c_lt
    -- the edge is an edge of the child in `G`
    have k_lt_G : k < G.E c := (equiv.E c c_lt_G) ▸ k_lt
    rw [← equiv.mate c k c_lt_G k_lt_G] at glued
    obtain ⟨c'_lt, k'_lt, glued_back⟩ := G_wf.mate_valid c k c' k' c_lt_G k_lt_G glued
    exact ⟨equiv.n ▸ c'_lt, (equiv.E c' c'_lt) ▸ k'_lt, by rw [← equiv.mate c' k' c'_lt k'_lt]; exact glued_back⟩

/-- Every walk of `G` from a valid port is a walk of an equivalent gluing `G'`. -/
theorem freach (G_wf : G.WF) : ∀ k x r, G.Valid x → G.FReach k x r → G'.FReach k x r := by
  intro k x r x_valid walk
  induction walk with
  | @stop x on_rim =>
    -- the walk of `G'` stops at the same rim port
    have stops := FReach.stop (G := G') (x := x)
      (by rw [equiv.tau x_valid, equiv.sigma G_wf (tau_valid G_wf x_valid)]; exact on_rim)
    rwa [equiv.tau x_valid] at stops
  | @step k x y r crosses _ ih =>
    exact .step (by rw [equiv.tau x_valid, equiv.sigma G_wf (tau_valid G_wf x_valid)]; exact crosses)
      (ih (sigma_valid G_wf (tau_valid G_wf x_valid) crosses))

/-- A walk of `G` from a valid port reaches the same rim port in an equivalent gluing `G'`. -/
theorem fullReach (G_wf : G.WF) {x r : GPort} (x_valid : G.Valid x) (reach : G.FullReach x r) : G'.FullReach x r := by
  obtain ⟨k, walk⟩ := reach
  exact ⟨k, equiv.freach G_wf k x r x_valid walk⟩

end Equiv

/-- Equivalence of gluings is symmetric. -/
theorem Equiv.symm (equiv : Equiv G G') : Equiv G' G where
  n := equiv.n.symm
  E c c_lt := (equiv.E c (equiv.n ▸ c_lt)).symm
  A c c_lt := (equiv.A c (equiv.n ▸ c_lt)).symm
  B c c_lt := (equiv.B c (equiv.n ▸ c_lt)).symm
  mate c k c_lt k_lt := (equiv.mate c k (equiv.n ▸ c_lt) ((equiv.E c (equiv.n ▸ c_lt)) ▸ k_lt)).symm

/-! ### Subdivision of an edge -/

/-- A cut: edge `e₀` of child `c₀` is cut into three edges. If `two`, it is glued to edge `e₁` of child `c₁`, which is
cut too (the same physical edge); otherwise it lies on the parent's rim. -/
structure Cut where
  c₀ : Nat
  e₀ : Nat
  c₁ : Nat
  e₁ : Nat
  two : Bool

namespace Cut

variable (κ : Cut)

/-- Where vertex `p` (or edge `p`) of child `c` goes: positions after the cut move on by 2. -/
def sh (c p : Nat) : Nat :=
  if c = κ.c₀ ∧ κ.e₀ < p then p + 2 else if κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ < p then p + 2 else p

/-- Back from the subdivided numbering (for positions that are not new). -/
def unsh (c k : Nat) : Nat :=
  if c = κ.c₀ ∧ κ.e₀ + 2 < k then k - 2 else if κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ + 2 < k then k - 2 else k

/-- A port of the old gluing, in the subdivided one. -/
def port (x : GPort) : GPort := (x.1, κ.sh x.1 x.2.1, x.2.2)

end Cut

/-- `G` with the cut `κ` made: the cut edge becomes three edges, and positions after it move on by 2. -/
def subdiv (G : Gluing) (κ : Cut) : Gluing where
  n := G.n
  E c := G.E c + (if c = κ.c₀ then 2 else 0) + (if κ.two = true ∧ c = κ.c₁ then 2 else 0)
  A c := κ.sh c (G.A c)
  B c := κ.sh c (G.B c)
  mate c k :=
    if c = κ.c₀ ∧ κ.e₀ ≤ k ∧ k ≤ κ.e₀ + 2 then
      (if κ.two = true then some (κ.c₁, κ.e₁ + 2 - (k - κ.e₀)) else none)
    else if κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ ≤ k ∧ k ≤ κ.e₁ + 2 then some (κ.c₀, κ.e₀ + 2 - (k - κ.e₁))
    else (G.mate c (κ.unsh c k)).map fun (c₂, k₂) => (c₂, κ.sh c₂ k₂)

/-- When a cut can be made: the cut edge is not the last edge of its child (so nothing wraps round), and it is glued
to an edge of a different child, also not the last, or lies on the rim. -/
structure Cut.OK (G : Gluing) (κ : Cut) : Prop where
  wf : G.WF
  c₀ : κ.c₀ < G.n
  e₀ : κ.e₀ + 1 < G.E κ.c₀
  mate : G.mate κ.c₀ κ.e₀ = if κ.two = true then some (κ.c₁, κ.e₁) else none
  ne : κ.two = true → κ.c₁ ≠ κ.c₀
  e₁ : κ.two = true → κ.e₁ + 1 < G.E κ.c₁

/-- Crossing from port `R` at vertex `u`: across edge `u` itself, to port `R` at the vertex where the edge glued to it
starts. -/
theorem sigmaR (G : Gluing) (c u : Nat) :
    G.sigma (c, u, true) = (G.mate c u).map fun (c', k') => (c', k', true) := rfl

/-- Crossing from port `L` at vertex `u`: across the edge before `u`, to port `L` at the vertex after the edge glued to
it. -/
theorem sigmaL (G : Gluing) (c u : Nat) :
    G.sigma (c, u, false) = (G.mate c (prv (G.E c) u)).map fun (c', k') => (c', nxt (G.E c') k', false) := rfl

/-- The vertex before `q + 1` is `q`. -/
theorem prv_succ' (E q : Nat) : prv E (q + 1) = q := by simp [prv]

/-- The vertex after `q` is `q + 1` when that is not the end of the rim. -/
theorem nxt_of_lt' {E q : Nat} (succ_lt : q + 1 < E) : nxt E q = q + 1 := by simp [nxt]; omega

/-! ### A shared path of three edges -/

/-- The ports along a path of three edges `ea, ea + 1, ea + 2` of child `a`, glued to edges `eb + 2, eb + 1, eb` of
child `b`: `u_k` is vertex `ea + k` of `a`, which is vertex `eb + 3 - k` of `b`. -/
def pathPort (a ea b eb : Nat) : Strip → GPort
  | .c hand k => (a, ea + k, hand.isR)
  | .d hand k => (b, eb + 3 - k, hand.isR)

/-- **A shared path of three edges, by the zigzag lemma (Lemma 5.1 with `n = 3`).** Let edges `ea, ea + 1, ea + 2` of
child `a` be glued, in reverse order, to edges `eb + 2, eb + 1, eb` of child `b`, with hooks at the inner vertices
`ea + 1, ea + 2` of `a` and `eb + 1, eb + 2` of `b`. Then the crossings from `R_a(ea)` are forced along the path to
`R_b(eb)`, and those from `L_b(eb + 3)` to `L_a(ea + 3)`: the two connections for odd `n`. -/
theorem cross_three {G : Gluing} {a ea b eb : Nat} (a_room : ea + 3 < G.E a)
    (glued_a : ∀ i, i ≤ 2 → G.mate a (ea + i) = some (b, eb + 2 - i))
    (glued_b : ∀ i, i ≤ 2 → G.mate b (eb + i) = some (a, ea + 2 - i))
    (hook_a : ∀ i, 1 ≤ i → i ≤ 2 → G.corner a (ea + i) = false)
    (hook_b : ∀ i, 1 ≤ i → i ≤ 2 → G.corner b (eb + i) = false) :
    G.Cross (a, ea, true) (b, eb, true) ∧ G.Cross (b, eb + 3, false) (a, ea + 3, false) := by
  obtain ⟨from_R, from_L, _⟩ := Zigzag.zigzag G.sigma G.tau (pathPort a ea b eb) 3 (by omega)
    (fun k k_lt => by
      -- across edge `ea + k` of `a`, to `R_b` at vertex `eb + 2 - k`, where that edge of `b` starts
      simp only [pathPort, Hand.isR, sigmaR, glued_a k (by omega), Option.map_some, Option.some.injEq,
        Prod.mk.injEq, true_and, and_true]
      omega)
    (fun k k_lt => by
      -- across the edge of `b` before its vertex `eb + 3 - k`, edge `eb + 2 - k`, to `L_a` after edge `ea + k`
      simp only [pathPort, Hand.isR, sigmaL]
      rw [show eb + 3 - k = (eb + (2 - k)) + 1 by omega, prv_succ', glued_b (2 - k) (by omega)]
      simp only [Option.map_some, show ea + 2 - (2 - k) = ea + k by omega,
        nxt_of_lt' (show ea + k + 1 < G.E a by omega), Nat.add_assoc])
    (fun k k_pos k_lt => by
      -- the hook of `a` at its inner vertex `ea + k`
      simp only [pathPort, Hand.isR]
      rw [tau_of_not_corner (hook_a k k_pos (by omega))]; rfl)
    (fun k k_pos k_lt => by
      -- the hook of `b` at its inner vertex `eb + 3 - k`
      simp only [pathPort, Hand.isR]
      rw [show eb + 3 - k = eb + (3 - k) by omega, tau_of_not_corner (hook_b (3 - k) (by omega) (by omega))]; rfl)
  simp only [pathPort, Hand.isR, Nat.add_zero, show 3 % 2 = 1 by rfl, Nat.one_ne_zero, ite_false,
    show eb + 3 - 3 = eb by omega, show eb + 3 - 0 = eb + 3 by omega] at from_R from_L
  exact ⟨from_R, from_L⟩

namespace Cut.OK

set_option linter.unusedSectionVars false

variable {G : Gluing} {κ : Cut} (cut_ok : κ.OK G)

include cut_ok

/-- If the cut edge is glued (`two`), its partner is an edge of `c₁`, glued back to it. -/
theorem two_mate (cut_glued : κ.two = true) :
    κ.c₁ < G.n ∧ κ.e₁ < G.E κ.c₁ ∧ G.mate κ.c₁ κ.e₁ = some (κ.c₀, κ.e₀) := by
  -- the cut edge is glued to edge `e₁` of `c₁`
  have glued := cut_ok.mate
  rw [ite_eq_left cut_glued] at glued
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  exact cut_ok.wf.mate_valid _ _ _ _ cut_ok.c₀ (by omega) glued

/-- On `c₀`, positions up to the cut edge stay put. -/
theorem sh_c₀_le {p : Nat} (p_le : p ≤ κ.e₀) : κ.sh κ.c₀ p = p := by
  unfold Cut.sh
  -- `c₀` is not the partner child `c₁`
  have not_c₁ : ¬ (κ.two = true ∧ κ.c₀ = κ.c₁ ∧ κ.e₁ < p) :=
    fun ⟨cut_glued, same, _⟩ => cut_ok.ne cut_glued same.symm
  rw [ite_eq_right (by omega), ite_eq_right not_c₁]

/-- On `c₀`, positions after the cut edge move on by 2. -/
theorem sh_c₀_gt {p : Nat} (p_gt : κ.e₀ < p) : κ.sh κ.c₀ p = p + 2 := by
  unfold Cut.sh; rw [ite_eq_left ⟨rfl, p_gt⟩]

/-- On `c₁` (when the cut edge is glued), positions up to the partner edge stay put. -/
theorem sh_c₁_le (cut_glued : κ.two = true) {p : Nat} (p_le : p ≤ κ.e₁) : κ.sh κ.c₁ p = p := by
  unfold Cut.sh
  rw [ite_eq_right (fun ⟨same, _⟩ => cut_ok.ne cut_glued same), ite_eq_right (by omega)]

/-- On `c₁` (when the cut edge is glued), positions after the partner edge move on by 2. -/
theorem sh_c₁_gt (cut_glued : κ.two = true) {p : Nat} (p_gt : κ.e₁ < p) : κ.sh κ.c₁ p = p + 2 := by
  unfold Cut.sh
  rw [ite_eq_right (fun ⟨same, _⟩ => cut_ok.ne cut_glued same), ite_eq_left ⟨cut_glued, rfl, p_gt⟩]

/-- On every other child, positions stay put. -/
theorem sh_other {c p : Nat} (not_c₀ : c ≠ κ.c₀) (not_c₁ : ¬ (κ.two = true ∧ c = κ.c₁)) : κ.sh c p = p := by
  unfold Cut.sh
  rw [ite_eq_right (fun ⟨is_c₀, _⟩ => not_c₀ is_c₀),
    ite_eq_right (fun ⟨cut_glued, is_c₁, _⟩ => not_c₁ ⟨cut_glued, is_c₁⟩)]

/-- The cut child `c₀` has two more edges after the cut. -/
theorem E_c₀ : (subdiv G κ).E κ.c₀ = G.E κ.c₀ + 2 := by
  dsimp only [subdiv]
  rw [ite_eq_left rfl, ite_eq_right (fun ⟨cut_glued, same⟩ => cut_ok.ne cut_glued same.symm)]

/-- The partner child `c₁` (when the cut edge is glued) has two more edges after the cut. -/
theorem E_c₁ (cut_glued : κ.two = true) : (subdiv G κ).E κ.c₁ = G.E κ.c₁ + 2 := by
  dsimp only [subdiv]
  rw [ite_eq_right (cut_ok.ne cut_glued), ite_eq_left ⟨cut_glued, rfl⟩]

/-- Every other child keeps its rim length. -/
theorem E_other {c : Nat} (not_c₀ : c ≠ κ.c₀) (not_c₁ : ¬ (κ.two = true ∧ c = κ.c₁)) :
    (subdiv G κ).E c = G.E c := by
  dsimp only [subdiv]
  rw [ite_eq_right not_c₀, ite_eq_right not_c₁]; simp

/-- Positions move only forwards, and never onto the new vertices. -/
theorem sh_cases (c p : Nat) :
    (κ.sh c p = p ∧ (c = κ.c₀ → p ≤ κ.e₀) ∧ (κ.two = true ∧ c = κ.c₁ → p ≤ κ.e₁)) ∨
    (κ.sh c p = p + 2 ∧ ((c = κ.c₀ ∧ κ.e₀ < p) ∨ (κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ < p))) := by
  by_cases is_c₀ : c = κ.c₀
  · subst is_c₀
    by_cases after : κ.e₀ < p
    · exact Or.inr ⟨cut_ok.sh_c₀_gt after, Or.inl ⟨rfl, after⟩⟩
    · exact Or.inl ⟨cut_ok.sh_c₀_le (by omega), fun _ => by omega,
        fun ⟨cut_glued, same⟩ => absurd same.symm (cut_ok.ne cut_glued)⟩
  · by_cases is_c₁ : κ.two = true ∧ c = κ.c₁
    · obtain ⟨cut_glued, rfl⟩ := is_c₁
      by_cases after : κ.e₁ < p
      · exact Or.inr ⟨cut_ok.sh_c₁_gt cut_glued after, Or.inr ⟨cut_glued, rfl, after⟩⟩
      · exact Or.inl ⟨cut_ok.sh_c₁_le cut_glued (by omega), fun same => absurd same is_c₀, fun _ => by omega⟩
    · exact Or.inl ⟨cut_ok.sh_other is_c₀ is_c₁, fun same => absurd same is_c₀, fun same => absurd same is_c₁⟩

/-- The shift is one to one on each child. -/
theorem sh_inj {c p q : Nat} (same : κ.sh c p = κ.sh c q) : p = q := by
  rcases cut_ok.sh_cases c p with ⟨p_stays, p_le₀, p_le₁⟩ | ⟨p_moves, p_after⟩ <;>
  rcases cut_ok.sh_cases c q with ⟨q_stays, q_le₀, q_le₁⟩ | ⟨q_moves, q_after⟩
  · omega
  · rw [p_stays, q_moves] at same
    rcases q_after with ⟨rfl, q_gt⟩ | ⟨cut_glued, rfl, q_gt⟩
    · have := p_le₀ rfl  -- `p` is at most the cut edge, `q` past it
      omega
    · have := p_le₁ ⟨cut_glued, rfl⟩  -- `p` is at most the partner edge, `q` past it
      omega
  · rw [p_moves, q_stays] at same
    rcases p_after with ⟨rfl, p_gt⟩ | ⟨cut_glued, rfl, p_gt⟩
    · have := q_le₀ rfl  -- `q` is at most the cut edge, `p` past it
      omega
    · have := q_le₁ ⟨cut_glued, rfl⟩  -- `q` is at most the partner edge, `p` past it
      omega
  · omega

/-- A position of child `c` is still a position of `c` after the cut. -/
theorem sh_lt {c p : Nat} (p_lt : p < G.E c) : κ.sh c p < (subdiv G κ).E c := by
  rcases cut_ok.sh_cases c p with ⟨stays, _, _⟩ | ⟨moves, after⟩
  · rw [stays]; dsimp only [subdiv]; omega
  · rw [moves]
    rcases after with ⟨rfl, _⟩ | ⟨cut_glued, rfl, _⟩
    · rw [cut_ok.E_c₀]; omega
    · rw [cut_ok.E_c₁ cut_glued]; omega

/-- The three edges that the cut edge of `c₀` becomes: glued, in reverse order, to the three that the partner edge
becomes, or on the parent's rim like the cut edge. -/
theorem mate_new₀ {i : Nat} (i_le : i ≤ 2) :
    (subdiv G κ).mate κ.c₀ (κ.e₀ + i) = if κ.two = true then some (κ.c₁, κ.e₁ + 2 - i) else none := by
  dsimp only [subdiv]
  rw [ite_eq_left ⟨rfl, by omega, by omega⟩, show κ.e₀ + i - κ.e₀ = i by omega]

/-- The three edges that the partner edge of `c₁` becomes: glued, in reverse order, to the three new edges of `c₀`. -/
theorem mate_new₁ (cut_glued : κ.two = true) {i : Nat} (i_le : i ≤ 2) :
    (subdiv G κ).mate κ.c₁ (κ.e₁ + i) = some (κ.c₀, κ.e₀ + 2 - i) := by
  dsimp only [subdiv]
  rw [ite_eq_right (fun ⟨same, _⟩ => cut_ok.ne cut_glued same), ite_eq_left ⟨cut_glued, rfl, by omega, by omega⟩,
    show κ.e₁ + i - κ.e₁ = i by omega]

/-- An edge that is not cut is glued as before (with positions moved on). -/
theorem mate_old {c k : Nat} (not_cut₀ : ¬ (c = κ.c₀ ∧ k = κ.e₀))
    (not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ k = κ.e₁)) :
    (subdiv G κ).mate c (κ.sh c k) = (G.mate c k).map fun (c₂, k₂) => (c₂, κ.sh c₂ k₂) := by
  dsimp only [subdiv]
  -- undoing the shift gives back `k`
  have unshift : κ.unsh c (κ.sh c k) = k := by
    unfold Cut.unsh
    rcases cut_ok.sh_cases c k with ⟨stays, le₀, le₁⟩ | ⟨moves, after⟩
    · rw [stays]
      by_cases is_c₀ : c = κ.c₀
      · have k_le := le₀ is_c₀  -- `k` is at most the cut edge
        rw [ite_eq_right (by omega), ite_eq_right (fun ⟨cut_glued, is_c₁, _⟩ => cut_ok.ne cut_glued (is_c₁ ▸ is_c₀))]
      · rw [ite_eq_right (fun ⟨on_c₀, _⟩ => is_c₀ on_c₀)]
        by_cases is_c₁ : κ.two = true ∧ c = κ.c₁
        · have k_le := le₁ is_c₁  -- `k` is at most the partner edge
          rw [ite_eq_right (by omega)]
        · rw [ite_eq_right (fun ⟨cut_glued, on_c₁, _⟩ => is_c₁ ⟨cut_glued, on_c₁⟩)]
    · rw [moves]
      rcases after with ⟨rfl, k_gt⟩ | ⟨cut_glued, rfl, k_gt⟩
      · rw [ite_eq_left ⟨rfl, by omega⟩]; omega
      · rw [ite_eq_right (fun ⟨same, _⟩ => cut_ok.ne cut_glued same), ite_eq_left ⟨cut_glued, rfl, by omega⟩]; omega
  -- the shifted position is not one of the three new edges of `c₀`
  have not_new₀ : ¬ (c = κ.c₀ ∧ κ.e₀ ≤ κ.sh c k ∧ κ.sh c k ≤ κ.e₀ + 2) := by
    rintro ⟨rfl, ge_cut, le_cut⟩
    rcases cut_ok.sh_cases κ.c₀ k with ⟨stays, le₀, _⟩ | ⟨moves, after⟩
    · have k_le := le₀ rfl  -- `k` is at most the cut edge, so it would be the cut edge
      rw [stays] at ge_cut le_cut; exact not_cut₀ ⟨rfl, by omega⟩
    · rw [moves] at ge_cut le_cut
      rcases after with ⟨_, k_gt⟩ | ⟨cut_glued, same, _⟩
      · omega
      · exact cut_ok.ne cut_glued same.symm
  -- the shifted position is not one of the three new edges of `c₁`
  have not_new₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ ≤ κ.sh c k ∧ κ.sh c k ≤ κ.e₁ + 2) := by
    rintro ⟨cut_glued, rfl, ge_cut, le_cut⟩
    rcases cut_ok.sh_cases κ.c₁ k with ⟨stays, _, le₁⟩ | ⟨moves, after⟩
    · have k_le := le₁ ⟨cut_glued, rfl⟩  -- `k` is at most the partner edge, so it would be the partner edge
      rw [stays] at ge_cut le_cut; exact not_cut₁ ⟨cut_glued, rfl, by omega⟩
    · rw [moves] at ge_cut le_cut
      rcases after with ⟨same, _⟩ | ⟨_, _, k_gt⟩
      · exact cut_ok.ne cut_glued same
      · omega
  rw [ite_eq_right not_new₀, ite_eq_right not_new₁, unshift]

/-- Going back one vertex commutes with the shift, except at the old vertex just after a cut edge. -/
theorem prv_sh {c p : Nat} (p_lt : p < G.E c) (not_after₀ : ¬ (c = κ.c₀ ∧ p = κ.e₀ + 1))
    (not_after₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ p = κ.e₁ + 1)) :
    prv ((subdiv G κ).E c) (κ.sh c p) = κ.sh c (prv (G.E c) p) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  -- going back from vertex 0 wraps round to the last vertex
  have prv_zero : ∀ E, prv E 0 = E - 1 := fun E => by simp [prv]
  -- going back from any other vertex subtracts one
  have prv_pos : ∀ E q, 0 < q → prv E q = q - 1 := fun E q q_pos => by simp [prv]; omega
  by_cases is_c₀ : c = κ.c₀
  · subst is_c₀
    rw [cut_ok.E_c₀]
    by_cases at_zero : p = 0
    · subst at_zero; rw [cut_ok.sh_c₀_le (by omega), prv_zero, prv_zero, cut_ok.sh_c₀_gt (by omega)]; omega
    · rw [prv_pos _ p (by omega)]
      by_cases before : p ≤ κ.e₀
      · rw [cut_ok.sh_c₀_le before, cut_ok.sh_c₀_le (by omega), prv_pos _ p (by omega)]
      -- `p` is past the vertex just after the cut edge
      · have p_gt : κ.e₀ + 1 < p := by
          -- by assumption, `p` is not the vertex just after the cut edge
          have not_next : ¬ p = κ.e₀ + 1 := fun same => not_after₀ ⟨rfl, same⟩
          omega
        rw [cut_ok.sh_c₀_gt (p := p) (by omega), cut_ok.sh_c₀_gt (p := p - 1) (by omega),
          prv_pos _ (p + 2) (by omega)]
        omega
  · by_cases is_c₁ : κ.two = true ∧ c = κ.c₁
    · obtain ⟨cut_glued, rfl⟩ := is_c₁
      -- the partner edge is not the last edge of `c₁`
      have e₁_lt := cut_ok.e₁ cut_glued
      rw [cut_ok.E_c₁ cut_glued]
      by_cases at_zero : p = 0
      · subst at_zero
        rw [cut_ok.sh_c₁_le cut_glued (by omega), prv_zero, prv_zero, cut_ok.sh_c₁_gt cut_glued (by omega)]; omega
      · rw [prv_pos _ p (by omega)]
        by_cases before : p ≤ κ.e₁
        · rw [cut_ok.sh_c₁_le cut_glued before, cut_ok.sh_c₁_le cut_glued (by omega), prv_pos _ p (by omega)]
        -- `p` is past the vertex just after the partner edge
        · have p_gt : κ.e₁ + 1 < p := by
            -- by assumption, `p` is not the vertex just after the partner edge
            have not_next : ¬ p = κ.e₁ + 1 := fun same => not_after₁ ⟨cut_glued, rfl, same⟩
            omega
          rw [cut_ok.sh_c₁_gt cut_glued (p := p) (by omega), cut_ok.sh_c₁_gt cut_glued (p := p - 1) (by omega),
            prv_pos _ (p + 2) (by omega)]
          omega
    · rw [cut_ok.E_other is_c₀ is_c₁, cut_ok.sh_other is_c₀ is_c₁, cut_ok.sh_other is_c₀ is_c₁]

/-- Going forward one vertex from the start of an edge that is not cut commutes with the shift. -/
theorem nxt_sh {c k : Nat} (k_lt : k < G.E c) (not_cut₀ : ¬ (c = κ.c₀ ∧ k = κ.e₀))
    (not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ k = κ.e₁)) :
    nxt ((subdiv G κ).E c) (κ.sh c k) = κ.sh c (nxt (G.E c) k) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  by_cases is_c₀ : c = κ.c₀
  · subst is_c₀
    rw [cut_ok.E_c₀]
    unfold nxt
    by_cases before : k < κ.e₀
    · rw [cut_ok.sh_c₀_le (p := k) (by omega), ite_eq_right (show ¬ (k + 1 = G.E κ.c₀ + 2) by omega),
        ite_eq_right (show ¬ (k + 1 = G.E κ.c₀) by omega), cut_ok.sh_c₀_le (p := k + 1) (by omega)]
    -- `k` is past the cut edge
    · have k_gt : κ.e₀ < k := by
        -- by assumption, `k` is not the cut edge
        have not_cut : ¬ k = κ.e₀ := fun same => not_cut₀ ⟨rfl, same⟩
        omega
      rw [cut_ok.sh_c₀_gt k_gt]
      by_cases at_end : k + 1 = G.E κ.c₀
      · rw [ite_eq_left (show k + 2 + 1 = G.E κ.c₀ + 2 by omega), ite_eq_left at_end,
          cut_ok.sh_c₀_le (p := 0) (by omega)]
      · rw [ite_eq_right (show ¬ (k + 2 + 1 = G.E κ.c₀ + 2) by omega), ite_eq_right at_end,
          cut_ok.sh_c₀_gt (p := k + 1) (by omega)]
  · by_cases is_c₁ : κ.two = true ∧ c = κ.c₁
    · obtain ⟨cut_glued, rfl⟩ := is_c₁
      -- the partner edge is not the last edge of `c₁`
      have e₁_lt := cut_ok.e₁ cut_glued
      rw [cut_ok.E_c₁ cut_glued]
      unfold nxt
      by_cases before : k < κ.e₁
      · rw [cut_ok.sh_c₁_le cut_glued (p := k) (by omega), ite_eq_right (show ¬ (k + 1 = G.E κ.c₁ + 2) by omega),
          ite_eq_right (show ¬ (k + 1 = G.E κ.c₁) by omega), cut_ok.sh_c₁_le cut_glued (p := k + 1) (by omega)]
      -- `k` is past the partner edge
      · have k_gt : κ.e₁ < k := by
          -- by assumption, `k` is not the partner edge
          have not_cut : ¬ k = κ.e₁ := fun same => not_cut₁ ⟨cut_glued, rfl, same⟩
          omega
        rw [cut_ok.sh_c₁_gt cut_glued k_gt]
        by_cases at_end : k + 1 = G.E κ.c₁
        · rw [ite_eq_left (show k + 2 + 1 = G.E κ.c₁ + 2 by omega), ite_eq_left at_end,
            cut_ok.sh_c₁_le cut_glued (p := 0) (by omega)]
        · rw [ite_eq_right (show ¬ (k + 2 + 1 = G.E κ.c₁ + 2) by omega), ite_eq_right at_end,
            cut_ok.sh_c₁_gt cut_glued (p := k + 1) (by omega)]
    · rw [cut_ok.E_other is_c₀ is_c₁, cut_ok.sh_other is_c₀ is_c₁, cut_ok.sh_other is_c₀ is_c₁]

/-- The other end of an edge that is not cut is not a cut edge either. -/
theorem target_not_cut {c k c₂ k₂ : Nat} (c_lt : c < G.n) (k_lt : k < G.E c) (glued : G.mate c k = some (c₂, k₂))
    (not_cut₀ : ¬ (c = κ.c₀ ∧ k = κ.e₀)) (not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ k = κ.e₁)) :
    ¬ (c₂ = κ.c₀ ∧ k₂ = κ.e₀) ∧ ¬ (κ.two = true ∧ c₂ = κ.c₁ ∧ k₂ = κ.e₁) := by
  obtain ⟨_, _, glued_back⟩ := cut_ok.wf.mate_valid c k c₂ k₂ c_lt k_lt glued
  constructor
  · rintro ⟨rfl, rfl⟩
    -- the cut edge is glued back to edge `k` of `c`, so that is the partner edge
    have cut_mate := cut_ok.mate
    rw [glued_back] at cut_mate
    by_cases cut_glued : κ.two = true
    · rw [ite_eq_left cut_glued] at cut_mate
      simp only [Option.some.injEq, Prod.mk.injEq] at cut_mate
      exact not_cut₁ ⟨cut_glued, cut_mate.1, cut_mate.2⟩
    · rw [ite_eq_right cut_glued] at cut_mate; contradiction
  · rintro ⟨cut_glued, rfl, rfl⟩
    rw [(cut_ok.two_mate cut_glued).2.2] at glued_back
    simp only [Option.some.injEq, Prod.mk.injEq] at glued_back
    exact not_cut₀ ⟨glued_back.1.symm, glued_back.2.symm⟩

/-- `τ` commutes with the shift (corners go to corners, and the shift is one to one). -/
theorem tau_port (x : GPort) : (subdiv G κ).tau (κ.port x) = κ.port (G.tau x) := by
  obtain ⟨c, p, s⟩ := x
  -- the piece of the subdivided gluing, at the shifted corners
  have lhs : (subdiv G κ).tau (κ.port (c, p, s)) =
      if κ.sh c p = κ.sh c (G.A c) then (c, κ.sh c (G.B c), s)
      else if κ.sh c p = κ.sh c (G.B c) then (c, κ.sh c (G.A c), s) else (c, κ.sh c p, !s) := rfl
  rw [lhs]
  by_cases at_A : p = G.A c
  -- at corner `A` the piece goes to corner `B`
  · have tau_A : G.tau (c, p, s) = (c, G.B c, s) := by simp [Gluing.tau, at_A]
    rw [tau_A, ite_eq_left (by rw [at_A])]; rfl
  · rw [ite_eq_right (fun same => at_A (cut_ok.sh_inj same))]
    by_cases at_B : p = G.B c
    -- at corner `B` the piece goes to corner `A`
    · have tau_B : G.tau (c, p, s) = (c, G.A c, s) := by simp [Gluing.tau, at_A, at_B]
      rw [tau_B, ite_eq_left (by rw [at_B])]; rfl
    -- elsewhere the piece goes to the other port at the same vertex
    · have tau_other : G.tau (c, p, s) = (c, p, !s) := by simp [Gluing.tau, at_A, at_B]
      rw [tau_other, ite_eq_right (fun same => at_B (cut_ok.sh_inj same))]; rfl

/-- The new vertices of `c₀` are not corners. -/
theorem corner_new₀ {i : Nat} (i_ge : 1 ≤ i) (i_le : i ≤ 2) : (subdiv G κ).corner κ.c₀ (κ.e₀ + i) = false := by
  simp only [Gluing.corner, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  dsimp only [subdiv]
  constructor <;> intro at_corner <;>
  · rcases cut_ok.sh_cases κ.c₀ _ with ⟨stays, le₀, _⟩ | ⟨moves, after⟩
    · rw [stays] at at_corner
      -- the corner is at most the cut edge, so it is not a new vertex
      have := le₀ rfl
      omega
    · rw [moves] at at_corner
      rcases after with ⟨_, _⟩ | ⟨cut_glued, same, _⟩
      · omega
      · exact cut_ok.ne cut_glued same.symm

/-- The new vertices of `c₁` (when the cut edge is glued) are not corners. -/
theorem corner_new₁ (cut_glued : κ.two = true) {i : Nat} (i_ge : 1 ≤ i) (i_le : i ≤ 2) :
    (subdiv G κ).corner κ.c₁ (κ.e₁ + i) = false := by
  simp only [Gluing.corner, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  dsimp only [subdiv]
  constructor <;> intro at_corner <;>
  · rcases cut_ok.sh_cases κ.c₁ _ with ⟨stays, _, le₁⟩ | ⟨moves, after⟩
    · rw [stays] at at_corner
      -- the corner is at most the partner edge, so it is not a new vertex
      have := le₁ ⟨cut_glued, rfl⟩
      omega
    · rw [moves] at at_corner
      rcases after with ⟨same, _⟩ | ⟨_, _, _⟩
      · exact cut_ok.ne cut_glued same
      · omega

/-- Every position of the subdivided child that is not new comes from an old one. -/
theorem preimage {c k : Nat} (k_lt : k < (subdiv G κ).E c) (not_new₀ : ¬ (c = κ.c₀ ∧ κ.e₀ < k ∧ k ≤ κ.e₀ + 2))
    (not_new₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ < k ∧ k ≤ κ.e₁ + 2)) : ∃ u, u < G.E c ∧ κ.sh c u = k := by
  by_cases is_c₀ : c = κ.c₀
  · subst is_c₀
    rw [cut_ok.E_c₀] at k_lt
    -- the cut edge is not the last edge of `c₀`
    have e₀_lt := cut_ok.e₀
    -- `k` is not one of the two new vertices of `c₀`
    have not_new : ¬ (κ.e₀ < k ∧ k ≤ κ.e₀ + 2) := fun ⟨k_gt, k_le⟩ => not_new₀ ⟨rfl, k_gt, k_le⟩
    by_cases before : k ≤ κ.e₀
    · exact ⟨k, by omega, cut_ok.sh_c₀_le before⟩
    · refine ⟨k - 2, by omega, ?_⟩
      rw [cut_ok.sh_c₀_gt (by omega)]; omega
  · by_cases is_c₁ : κ.two = true ∧ c = κ.c₁
    · obtain ⟨cut_glued, rfl⟩ := is_c₁
      rw [cut_ok.E_c₁ cut_glued] at k_lt
      -- the partner edge is not the last edge of `c₁`
      have e₁_lt := cut_ok.e₁ cut_glued
      -- `k` is not one of the two new vertices of `c₁`
      have not_new : ¬ (κ.e₁ < k ∧ k ≤ κ.e₁ + 2) := fun ⟨k_gt, k_le⟩ => not_new₁ ⟨cut_glued, rfl, k_gt, k_le⟩
      by_cases before : k ≤ κ.e₁
      · exact ⟨k, by omega, cut_ok.sh_c₁_le cut_glued before⟩
      · refine ⟨k - 2, by omega, ?_⟩
        rw [cut_ok.sh_c₁_gt cut_glued (by omega)]; omega
    · rw [cut_ok.E_other is_c₀ is_c₁] at k_lt
      exact ⟨k, k_lt, cut_ok.sh_other is_c₀ is_c₁⟩

/-- If the cut edge lies on the parent's rim, only it is cut. -/
theorem two_false (on_rim : G.mate κ.c₀ κ.e₀ = none) : κ.two = false := by
  -- what `OK` says about the gluing of the cut edge
  have cut_mate := cut_ok.mate
  rw [on_rim] at cut_mate
  cases cut_glued : κ.two
  · rfl
  · rw [cut_glued] at cut_mate; simp at cut_mate

/-- If the cut edge is glued, its partner is cut too, and it is the edge it is glued to. -/
theorem two_true {q : Nat × Nat} (glued : G.mate κ.c₀ κ.e₀ = some q) : κ.two = true ∧ q = (κ.c₁, κ.e₁) := by
  -- what `OK` says about the gluing of the cut edge
  have cut_mate := cut_ok.mate
  rw [glued] at cut_mate
  cases cut_glued : κ.two
  · rw [cut_glued] at cut_mate; simp at cut_mate
  · rw [cut_glued] at cut_mate; simp only [ite_true, Option.some.injEq] at cut_mate; exact ⟨rfl, cut_mate⟩

/-- The first new edge of `c₀` (where the cut edge began) is glued to the last new edge of `c₁`, or lies on the rim. -/
theorem mate_cut₀ : (subdiv G κ).mate κ.c₀ κ.e₀ = if κ.two = true then some (κ.c₁, κ.e₁ + 2) else none := by
  -- `mate_new₀` at the first new edge
  have first := cut_ok.mate_new₀ (i := 0) (by omega)
  simpa using first

/-- The first new edge of `c₁` (where the partner edge began) is glued to the last new edge of `c₀`. -/
theorem mate_cut₁ (cut_glued : κ.two = true) : (subdiv G κ).mate κ.c₁ κ.e₁ = some (κ.c₀, κ.e₀ + 2) := by
  -- `mate_new₁` at the first new edge
  have first := cut_ok.mate_new₁ cut_glued (i := 0) (by omega)
  simpa using first

/-- At a new vertex of `c₀` the piece joins the two ports at that vertex. -/
theorem tau_new₀ {i : Nat} (i_ge : 1 ≤ i) (i_le : i ≤ 2) (s : Bool) :
    (subdiv G κ).tau (κ.c₀, κ.e₀ + i, s) = (κ.c₀, κ.e₀ + i, !s) := tau_of_not_corner (cut_ok.corner_new₀ i_ge i_le)

/-- At a new vertex of `c₁` the piece joins the two ports at that vertex. -/
theorem tau_new₁ (cut_glued : κ.two = true) {i : Nat} (i_ge : 1 ≤ i) (i_le : i ≤ 2) (s : Bool) :
    (subdiv G κ).tau (κ.c₁, κ.e₁ + i, s) = (κ.c₁, κ.e₁ + i, !s) :=
  tau_of_not_corner (cut_ok.corner_new₁ cut_glued i_ge i_le)

/-- The vertex before an old vertex is the start of the cut edge only right after the cut edge. -/
theorem prv_cut {c p : Nat} (p_lt : p < G.E c) (prev_cut : c = κ.c₀ ∧ prv (G.E c) p = κ.e₀) : p = κ.e₀ + 1 := by
  obtain ⟨rfl, prev_eq⟩ := prev_cut
  -- the cut edge is not the last edge of `c₀`
  have := cut_ok.e₀
  unfold prv at prev_eq; split at prev_eq <;> omega

/-- The vertex before an old vertex is the start of the partner edge only right after the partner edge. -/
theorem prv_cut₁ (cut_glued : κ.two = true) {c p : Nat} (p_lt : p < G.E c)
    (prev_cut : c = κ.c₁ ∧ prv (G.E c) p = κ.e₁) : p = κ.e₁ + 1 := by
  obtain ⟨rfl, prev_eq⟩ := prev_cut
  -- the partner edge is not the last edge of `c₁`
  have := cut_ok.e₁ cut_glued
  unfold prv at prev_eq; split at prev_eq <;> omega

/-- The new path of a glued cut edge, read from `c₀` (Lemma 7.1 with the zigzag lemma for `n = 3`): from `R_{c₀}(e₀)` to
`R_{c₁}(e₁)`, and from `L_{c₁}(e₁ + 3)` to `L_{c₀}(e₀ + 3)`. -/
theorem cross_cut₀ (cut_glued : κ.two = true) :
    (subdiv G κ).Cross (κ.c₀, κ.e₀, true) (κ.c₁, κ.e₁, true) ∧
    (subdiv G κ).Cross (κ.c₁, κ.e₁ + 3, false) (κ.c₀, κ.e₀ + 3, false) := by
  -- the cut edge is not the last edge of `c₀`
  have e₀_lt := cut_ok.e₀
  exact cross_three (by rw [cut_ok.E_c₀]; omega)
    (fun i i_le => by rw [cut_ok.mate_new₀ i_le, ite_eq_left cut_glued])
    (fun i i_le => cut_ok.mate_new₁ cut_glued i_le)
    (fun i i_ge i_le => cut_ok.corner_new₀ i_ge i_le)
    (fun i i_ge i_le => cut_ok.corner_new₁ cut_glued i_ge i_le)

/-- The new path of a glued cut edge, read from `c₁`: from `R_{c₁}(e₁)` to `R_{c₀}(e₀)`, and from `L_{c₀}(e₀ + 3)` to
`L_{c₁}(e₁ + 3)`. -/
theorem cross_cut₁ (cut_glued : κ.two = true) :
    (subdiv G κ).Cross (κ.c₁, κ.e₁, true) (κ.c₀, κ.e₀, true) ∧
    (subdiv G κ).Cross (κ.c₀, κ.e₀ + 3, false) (κ.c₁, κ.e₁ + 3, false) := by
  -- the partner edge is not the last edge of `c₁`
  have e₁_lt := cut_ok.e₁ cut_glued
  exact cross_three (by rw [cut_ok.E_c₁ cut_glued]; omega)
    (fun i i_le => cut_ok.mate_new₁ cut_glued i_le)
    (fun i i_le => by rw [cut_ok.mate_new₀ i_le, ite_eq_left cut_glued])
    (fun i i_ge i_le => cut_ok.corner_new₁ cut_glued i_ge i_le)
    (fun i i_ge i_le => cut_ok.corner_new₀ i_ge i_le)

/-- **Subdividing an edge is a simulation.** -/
theorem sim : Sim G (subdiv G κ) κ.port where
  valid x x_valid := ⟨x_valid.1, cut_ok.sh_lt x_valid.2⟩
  tau x _ := cut_ok.tau_port x
  rim := by
    rintro ⟨c, p, s⟩ ⟨c_lt, p_lt⟩ on_rim
    -- the cut edge is not the last edge of `c₀`
    have e₀_lt := cut_ok.e₀
    cases s with
    | true =>
      simp only [Cut.port]
      rw [sigmaR] at on_rim ⊢
      rw [Option.map_eq_none_iff] at on_rim ⊢
      by_cases is_cut₀ : c = κ.c₀ ∧ p = κ.e₀
      · obtain ⟨rfl, rfl⟩ := is_cut₀
        -- the cut edge is on the rim, so only it is cut
        have cut_on_rim := cut_ok.two_false on_rim
        rw [cut_ok.sh_c₀_le (Nat.le_refl _), cut_ok.mate_cut₀, cut_on_rim]; rfl
      · by_cases is_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ p = κ.e₁
        · obtain ⟨cut_glued, rfl, rfl⟩ := is_cut₁
          rw [(cut_ok.two_mate cut_glued).2.2] at on_rim; contradiction
        · rw [cut_ok.mate_old is_cut₀ is_cut₁, on_rim]; rfl
    | false =>
      simp only [Cut.port]
      rw [sigmaL] at on_rim ⊢
      rw [Option.map_eq_none_iff] at on_rim ⊢
      by_cases after_cut₀ : c = κ.c₀ ∧ p = κ.e₀ + 1
      · obtain ⟨rfl, rfl⟩ := after_cut₀
        rw [prv_succ'] at on_rim
        -- the cut edge is on the rim, so only it is cut
        have cut_on_rim := cut_ok.two_false on_rim
        rw [cut_ok.sh_c₀_gt (by omega), cut_ok.E_c₀, show κ.e₀ + 1 + 2 = (κ.e₀ + 2) + 1 by omega, prv_succ',
          cut_ok.mate_new₀ (by omega), cut_on_rim]; rfl
      · by_cases after_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ p = κ.e₁ + 1
        · obtain ⟨cut_glued, rfl, rfl⟩ := after_cut₁
          rw [prv_succ', (cut_ok.two_mate cut_glued).2.2] at on_rim; contradiction
        · rw [cut_ok.prv_sh p_lt after_cut₀ after_cut₁]
          -- the edge before `p` is not the cut edge
          have not_cut₀ : ¬ (c = κ.c₀ ∧ prv (G.E c) p = κ.e₀) :=
            fun prev_cut => after_cut₀ ⟨prev_cut.1, cut_ok.prv_cut p_lt prev_cut⟩
          -- nor the partner edge
          have not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ prv (G.E c) p = κ.e₁) := fun ⟨cut_glued, is_c₁, prev_eq⟩ =>
            after_cut₁ ⟨cut_glued, is_c₁, cut_ok.prv_cut₁ cut_glued p_lt ⟨is_c₁, prev_eq⟩⟩
          rw [cut_ok.mate_old not_cut₀ not_cut₁, on_rim]; rfl
  cross := by
    rintro ⟨c, p, s⟩ y ⟨c_lt, p_lt⟩ crosses
    -- the cut edge is not the last edge of `c₀`
    have e₀_lt := cut_ok.e₀
    cases s with
    | true =>
      simp only [Cut.port]
      rw [sigmaR] at crosses
      rw [Option.map_eq_some_iff] at crosses
      obtain ⟨⟨c', k'⟩, glued, rfl⟩ := crosses
      by_cases is_cut₀ : c = κ.c₀ ∧ p = κ.e₀
      · obtain ⟨rfl, rfl⟩ := is_cut₀
        -- the cut edge: across the new path, from R(e₀) of c₀ to R(e₁) of c₁, by the zigzag lemma
        obtain ⟨cut_glued, partner⟩ := cut_ok.two_true glued
        simp only [Prod.mk.injEq] at partner
        obtain ⟨rfl, rfl⟩ := partner
        rw [cut_ok.sh_c₀_le (Nat.le_refl _), cut_ok.sh_c₁_le cut_glued (Nat.le_refl _)]
        exact (cut_ok.cross_cut₀ cut_glued).1
      · by_cases is_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ p = κ.e₁
        · obtain ⟨cut_glued, rfl, rfl⟩ := is_cut₁
          -- the partner of the cut edge: across the new path, from R(e₁) of c₁ to R(e₀) of c₀
          rw [(cut_ok.two_mate cut_glued).2.2] at glued
          simp only [Option.some.injEq, Prod.mk.injEq] at glued
          obtain ⟨rfl, rfl⟩ := glued
          rw [cut_ok.sh_c₁_le cut_glued (Nat.le_refl _), cut_ok.sh_c₀_le (Nat.le_refl _)]
          exact (cut_ok.cross_cut₁ cut_glued).1
        · refine .one ?_
          rw [sigmaR, cut_ok.mate_old is_cut₀ is_cut₁, glued]; rfl
    | false =>
      simp only [Cut.port]
      rw [sigmaL] at crosses
      rw [Option.map_eq_some_iff] at crosses
      obtain ⟨⟨c', k'⟩, glued, rfl⟩ := crosses
      by_cases after_cut₀ : c = κ.c₀ ∧ p = κ.e₀ + 1
      · obtain ⟨rfl, rfl⟩ := after_cut₀
        rw [prv_succ'] at glued
        obtain ⟨cut_glued, partner⟩ := cut_ok.two_true glued
        simp only [Prod.mk.injEq] at partner
        obtain ⟨rfl, rfl⟩ := partner
        -- the partner edge is not the last edge of `c₁`
        have e₁_lt := cut_ok.e₁ cut_glued
        -- across the new path, from L(e₀+3) of c₀ to L(e₁+3) of c₁, by the zigzag lemma
        rw [cut_ok.sh_c₀_gt (by omega)]
        simp only
        rw [nxt_of_lt' e₁_lt, cut_ok.sh_c₁_gt cut_glued (by omega)]
        exact (cut_ok.cross_cut₁ cut_glued).2
      · by_cases after_cut₁ : κ.two = true ∧ c = κ.c₁ ∧ p = κ.e₁ + 1
        · obtain ⟨cut_glued, rfl, rfl⟩ := after_cut₁
          rw [prv_succ', (cut_ok.two_mate cut_glued).2.2] at glued
          simp only [Option.some.injEq, Prod.mk.injEq] at glued
          obtain ⟨rfl, rfl⟩ := glued
          -- across the new path, from L(e₁+3) of c₁ to L(e₀+3) of c₀, by the zigzag lemma
          rw [cut_ok.sh_c₁_gt cut_glued (by omega)]
          simp only
          rw [nxt_of_lt' e₀_lt, cut_ok.sh_c₀_gt (by omega)]
          exact (cut_ok.cross_cut₀ cut_glued).2
        · refine .one ?_
          -- the edge before `p` is not the cut edge
          have not_cut₀ : ¬ (c = κ.c₀ ∧ prv (G.E c) p = κ.e₀) :=
            fun prev_cut => after_cut₀ ⟨prev_cut.1, cut_ok.prv_cut p_lt prev_cut⟩
          -- nor the partner edge
          have not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ prv (G.E c) p = κ.e₁) := fun ⟨cut_glued, is_c₁, prev_eq⟩ =>
            after_cut₁ ⟨cut_glued, is_c₁, cut_ok.prv_cut₁ cut_glued p_lt ⟨is_c₁, prev_eq⟩⟩
          -- the edge before `p` is an edge of `c`
          have prev_lt : prv (G.E c) p < G.E c := prv_lt p_lt
          obtain ⟨c'_lt, k'_lt, _⟩ := cut_ok.wf.mate_valid c _ c' k' c_lt prev_lt glued
          obtain ⟨mate_not_cut₀, mate_not_cut₁⟩ := cut_ok.target_not_cut c_lt prev_lt glued not_cut₀ not_cut₁
          rw [sigmaL, cut_ok.prv_sh p_lt after_cut₀ after_cut₁, cut_ok.mate_old not_cut₀ not_cut₁, glued]
          simp only [Option.map_some]
          rw [cut_ok.nxt_sh k'_lt mate_not_cut₀ mate_not_cut₁]

/-- The subdivided gluing is well formed. -/
theorem wf_subdiv : (subdiv G κ).WF where
  E_pos c c_lt := by
    -- every child had an edge before the cut
    have := cut_ok.wf.E_pos c c_lt
    dsimp only [subdiv]; omega
  A_lt c c_lt := cut_ok.sh_lt (cut_ok.wf.A_lt c c_lt)
  B_lt c c_lt := cut_ok.sh_lt (cut_ok.wf.B_lt c c_lt)
  A_ne_B c c_lt same := cut_ok.wf.A_ne_B c c_lt (cut_ok.sh_inj same)
  mate_valid := by
    intro c k c' k' c_lt k_lt glued
    -- the cut edge is not the last edge of `c₀`
    have e₀_lt := cut_ok.e₀
    by_cases new₀ : c = κ.c₀ ∧ κ.e₀ ≤ k ∧ k ≤ κ.e₀ + 2
    · obtain ⟨rfl, k_ge, k_le⟩ := new₀
      rw [show k = κ.e₀ + (k - κ.e₀) by omega, cut_ok.mate_new₀ (by omega)] at glued
      by_cases cut_glued : κ.two = true
      · rw [ite_eq_left cut_glued] at glued
        simp only [Option.some.injEq, Prod.mk.injEq] at glued
        obtain ⟨rfl, rfl⟩ := glued
        -- the partner edge is not the last edge of `c₁`
        have e₁_lt := cut_ok.e₁ cut_glued
        refine ⟨(cut_ok.two_mate cut_glued).1, by rw [cut_ok.E_c₁ cut_glued]; omega, ?_⟩
        rw [show κ.e₁ + 2 - (k - κ.e₀) = κ.e₁ + (2 - (k - κ.e₀)) by omega, cut_ok.mate_new₁ cut_glued (by omega)]
        congr 2; omega
      · rw [ite_eq_right cut_glued] at glued; contradiction
    · by_cases new₁ : κ.two = true ∧ c = κ.c₁ ∧ κ.e₁ ≤ k ∧ k ≤ κ.e₁ + 2
      · obtain ⟨cut_glued, rfl, k_ge, k_le⟩ := new₁
        rw [show k = κ.e₁ + (k - κ.e₁) by omega, cut_ok.mate_new₁ cut_glued (by omega)] at glued
        simp only [Option.some.injEq, Prod.mk.injEq] at glued
        obtain ⟨rfl, rfl⟩ := glued
        refine ⟨cut_ok.c₀, by rw [cut_ok.E_c₀]; omega, ?_⟩
        rw [show κ.e₀ + 2 - (k - κ.e₁) = κ.e₀ + (2 - (k - κ.e₁)) by omega, cut_ok.mate_new₀ (by omega),
          ite_eq_left cut_glued]
        congr 2; omega
      · obtain ⟨u, u_lt, rfl⟩ := cut_ok.preimage k_lt (fun ⟨is_c₀, k_gt, k_le⟩ => new₀ ⟨is_c₀, by omega, k_le⟩)
          (fun ⟨cut_glued, is_c₁, k_gt, k_le⟩ => new₁ ⟨cut_glued, is_c₁, by omega, k_le⟩)
        -- the edge is not the cut edge (whose position would be a new edge)
        have not_cut₀ : ¬ (c = κ.c₀ ∧ u = κ.e₀) := by
          rintro ⟨rfl, rfl⟩; exact new₀ ⟨rfl, by rw [cut_ok.sh_c₀_le (Nat.le_refl _)]; omega,
            by rw [cut_ok.sh_c₀_le (Nat.le_refl _)]; omega⟩
        -- nor the partner edge
        have not_cut₁ : ¬ (κ.two = true ∧ c = κ.c₁ ∧ u = κ.e₁) := by
          rintro ⟨cut_glued, rfl, rfl⟩
          exact new₁ ⟨cut_glued, rfl, by rw [cut_ok.sh_c₁_le cut_glued (Nat.le_refl _)]; omega,
            by rw [cut_ok.sh_c₁_le cut_glued (Nat.le_refl _)]; omega⟩
        rw [cut_ok.mate_old not_cut₀ not_cut₁, Option.map_eq_some_iff] at glued
        obtain ⟨⟨c₂, u₂⟩, glued_old, shifted⟩ := glued
        simp only [Prod.mk.injEq] at shifted
        obtain ⟨rfl, rfl⟩ := shifted
        obtain ⟨c₂_lt, u₂_lt, glued_back⟩ := cut_ok.wf.mate_valid c u c₂ u₂ c_lt u_lt glued_old
        obtain ⟨mate_not_cut₀, mate_not_cut₁⟩ := cut_ok.target_not_cut c_lt u_lt glued_old not_cut₀ not_cut₁
        refine ⟨c₂_lt, cut_ok.sh_lt u₂_lt, ?_⟩
        rw [cut_ok.mate_old mate_not_cut₀ mate_not_cut₁, glued_back]; rfl

end Cut.OK

end SpectreKnot.Gluing

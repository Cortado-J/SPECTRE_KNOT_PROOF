/-
**Prop 5.4 (reduced composition)**, for every well-formed gluing.

(b) is proved in a stronger form than the paper states: from *every* port (not only the parent ports at marks), the
full walk of Lemma 4.2 and the reduced walk end at the same rim port. The proof follows the paper: along a run, the
full walk is forced through the zigzag of Lemma 5.1 (`Zigzag.walk_core`), and arrives where `σ_red` jumps to.
-/
import SpectreKnot.Gluing
import SpectreKnot.Zigzag

namespace SpectreKnot

/-- `R` as `true`, `L` as `false`, as in `GPort`. -/
def Hand.isR : Hand → Bool
  | .R => true
  | .L => false

namespace Gluing

variable {G : Gluing}

/-- `σ` made total (it is applied only where it is defined), for the zigzag lemma. -/
def sigmaTot (G : Gluing) (p : GPort) : GPort := (G.sigma p).getD p

/-- One step of the full walk inside a run: `τ ∘ σ`. -/
abbrev Z (G : Gluing) : GPort → GPort := Zigzag.zz G.sigmaTot G.tau

/-- The ports along a run of child `c` starting at its vertex `u`, glued to child `c'` whose vertex `b` is at `u`:
`c h k` is `h_c` at the `k`-th vertex of the run, `d h k` is `h_{c'}` at the same point. -/
def runPort (G : Gluing) (c u c' b : Nat) : Strip → GPort
  | .c hand k => (c, iter (nxt (G.E c)) k u, hand.isR)
  | .d hand k => (c', iter (prv (G.E c')) k b, hand.isR)

/-! ### Small facts -/

/-- A vertex that is not a crossover corner is neither `A` nor `B`. -/
theorem corner_false {c u : Nat} (not_corner : G.corner c u = false) : u ≠ G.A c ∧ u ≠ G.B c := by
  simp [corner] at not_corner; exact not_corner

/-- A smooth vertex is not a crossover corner. -/
theorem smooth_corner {c u : Nat} (smooth_u : G.smooth c u = true) : G.corner c u = false := by
  simp only [smooth, Bool.and_eq_true, Bool.not_eq_true'] at smooth_u; exact smooth_u.1

/-- What `smooth` says, as a proposition. -/
theorem smooth_iff {c x : Nat} : G.smooth c x = true ↔ G.corner c x = false ∧
    ((G.mate c x = none ∧ G.mate c (prv (G.E c) x) = none) ∨
     ∃ c' k', G.mate c x = some (c', k') ∧ G.mate c (prv (G.E c) x) = some (c', nxt (G.E c') k') ∧
       G.corner c' (nxt (G.E c') k') = false) := by
  unfold smooth
  cases mate_after : G.mate c x with
  | none => cases mate_before : G.mate c (prv (G.E c) x) <;> simp
  | some p =>
    obtain ⟨c1, k1⟩ := p
    cases mate_before : G.mate c (prv (G.E c) x) with
    | none => simp
    | some p =>
      obtain ⟨c2, k2⟩ := p
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, reduceCtorEq, false_and, false_or,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · intro smooth_data
        obtain ⟨not_corner, ⟨same_child, next_edge⟩, far_not_corner⟩ := smooth_data
        exact ⟨not_corner, _, _, ⟨rfl, rfl⟩, ⟨same_child, next_edge⟩, far_not_corner⟩
      · intro smooth_data
        obtain ⟨not_corner, c', k', ⟨child_eq, edge_eq⟩, ⟨same_child, next_edge⟩, far_not_corner⟩ := smooth_data
        subst child_eq edge_eq
        exact ⟨not_corner, ⟨same_child, next_edge⟩, far_not_corner⟩

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

/-- The reduced `σ` is undefined exactly where `σ` is: on the parent's rim. -/
theorem sigmaRed_eq_none_iff {q : GPort} : G.sigmaRed q = none ↔ G.sigma q = none := by
  obtain ⟨c, u, s⟩ := q
  cases s <;> simp only [sigmaRed, sigma] <;> split <;> simp_all

/-! ### Runs -/

/-- The search for the next mark, started at the vertex `x` reached after `k` steps from `u`, with fuel `f`: its
result lies between `k` and `k + f`; every vertex before it is smooth; and if it stops before the fuel runs out, it
stops at a mark. -/
theorem firstMark_spec (c u : Nat) : ∀ f x k, x = iter (nxt (G.E c)) k u →
    k ≤ G.firstMark c x k f ∧ G.firstMark c x k f ≤ k + f ∧
    (∀ j, k ≤ j → j < G.firstMark c x k f → G.smooth c (iter (nxt (G.E c)) j u) = true) ∧
    (G.firstMark c x k f < k + f → G.smooth c (iter (nxt (G.E c)) (G.firstMark c x k f) u) = false) := by
  intro f
  induction f with
  | zero =>
    -- no fuel: the search returns `k` at once
    intro x k _
    simp only [firstMark]
    exact ⟨Nat.le_refl _, by omega, fun j k_le_j j_lt => absurd j_lt (by omega),
      fun stopped_early => absurd stopped_early (by omega)⟩
  | succ f ih =>
    intro x k x_at
    simp only [firstMark]
    split
    · -- `x` is smooth: the search moves on to the next vertex
      rename_i x_smooth
      obtain ⟨k_lt, le_fuel, smooth_before, mark_at⟩ := ih (nxt (G.E c) x) (k + 1) (by rw [x_at, iter_succ])
      refine ⟨by omega, by omega, ?_, fun stopped_early => mark_at (by omega)⟩
      intro j k_le_j j_lt
      by_cases j_eq : j = k
      · subst j_eq; rw [← x_at]; exact x_smooth
      · exact smooth_before j (by omega) j_lt
    · -- `x` is a mark: the search stops here
      rename_i x_mark
      refine ⟨Nat.le_refl _, by omega, fun j k_le_j j_lt => absurd j_lt (by omega), fun _ => ?_⟩
      rw [← x_at]; simpa using x_mark

/-- A run has length at least 1 and at most `E`, and passes only through smooth vertices. -/
theorem runLen_spec (c u : Nat) (E_pos : 0 < G.E c) :
    1 ≤ G.runLen c u ∧ G.runLen c u ≤ G.E c ∧
    (∀ j, 1 ≤ j → j < G.runLen c u → G.smooth c (iter (nxt (G.E c)) j u) = true) ∧
    (G.runLen c u < G.E c → G.smooth c (iter (nxt (G.E c)) (G.runLen c u) u) = false) := by
  obtain ⟨one_le, le_fuel, smooth_before, mark_at⟩ :=
    firstMark_spec (G := G) c u (G.E c - 1) (nxt (G.E c) u) 1 rfl
  refine ⟨one_le, by unfold runLen; omega, smooth_before,
    fun short => mark_at (by unfold runLen at short; omega)⟩

/-- A run ends at a mark (the corner `A` guarantees that there is one). -/
theorem runLen_mark (wf : G.WF) {c u : Nat} (c_lt : c < G.n) (u_lt : u < G.E c) :
    G.smooth c (iter (nxt (G.E c)) (G.runLen c u) u) = false := by
  obtain ⟨one_le, le_E, smooth_before, mark_at⟩ := runLen_spec (G := G) c u (wf.E_pos c c_lt)
  by_cases short : G.runLen c u < G.E c
  · exact mark_at short
  · have full_round : G.runLen c u = G.E c := by omega  -- otherwise the run goes all the way round
    obtain ⟨j, one_le_j, j_le, reach_A⟩ := iter_nxt_cover u_lt (wf.A_lt c c_lt)
    -- the corner `A` is a mark
    have A_mark : G.smooth c (G.A c) = false := by simp [smooth, corner]
    by_cases j_lt : j < G.E c
    · have A_smooth := smooth_before j one_le_j (by omega)  -- `A` inside the run would be smooth
      rw [reach_A, A_mark] at A_smooth
      contradiction
    · -- `A` is reached after the whole round, at the end of the run
      rw [show G.runLen c u = j by omega, reach_A]; exact A_mark

/-- Marks look the same from both sides: if edge `v` of child `c` is edge `y` of `c'`, then vertex `v` of `c` is
smooth exactly when the same point, vertex `y + 1` of `c'`, is. -/
theorem smooth_symm (wf : G.WF) {c v c' y : Nat} (c_lt : c < G.n) (v_lt : v < G.E c)
    (glued : G.mate c v = some (c', y)) : G.smooth c v = G.smooth c' (nxt (G.E c') y) := by
  obtain ⟨c'_lt, y_lt, glued_back⟩ := wf.mate_valid c v c' y c_lt v_lt glued
  -- the vertex before `v` on `c` is a vertex of `c`
  have prev_lt : prv (G.E c) v < G.E c := prv_lt v_lt
  -- the same point on `c'`, vertex `y + 1`, is a vertex of `c'`
  have next_lt : nxt (G.E c') y < G.E c' := nxt_lt y_lt
  rw [Bool.eq_iff_iff, smooth_iff, smooth_iff, prv_nxt y_lt, glued, glued_back]
  constructor
  · rintro ⟨not_corner, ⟨on_rim, _⟩ | ⟨c1, k1, mate_eq, prev_glued, far_not_corner⟩⟩
    · cases on_rim
    · cases mate_eq
      obtain ⟨_, _, next_glued⟩ := wf.mate_valid c _ c' _ c_lt prev_lt prev_glued
      exact ⟨far_not_corner, Or.inr ⟨c, prv (G.E c) v, next_glued, by rw [nxt_prv v_lt],
        by rw [nxt_prv v_lt]; exact not_corner⟩⟩
  · rintro ⟨not_corner, ⟨_, on_rim⟩ | ⟨c2, k2, next_glued, mate_eq, far_not_corner⟩⟩
    · cases on_rim
    · cases mate_eq
      obtain ⟨_, k2_lt, prev_glued⟩ := wf.mate_valid c' _ c k2 c'_lt next_lt next_glued
      refine ⟨far_not_corner, Or.inr ⟨c', y, rfl, ?_, not_corner⟩⟩
      rw [prv_nxt k2_lt]; exact prev_glued

/-- The invariant of a run: along the run of `c` from `u`, whose first edge is edge `k0` of `c'`, the `k`-th edge of
`c` is glued to `c'`, at the edges of `c'` read backwards from `k0`; and the vertices inside the run are not corners of
either child. -/
theorem run_inv (wf : G.WF) {c u c' k0 : Nat} (c_lt : c < G.n) (u_lt : u < G.E c)
    (glued : G.mate c u = some (c', k0)) :
    ∀ k, k < G.runLen c u →
      G.mate c (iter (nxt (G.E c)) k u) = some (c', iter (prv (G.E c')) (k + 1) (nxt (G.E c') k0)) ∧
      (0 < k → G.corner c (iter (nxt (G.E c)) k u) = false ∧
               G.corner c' (iter (prv (G.E c')) k (nxt (G.E c') k0)) = false) := by
  obtain ⟨c'_lt, k0_lt, _⟩ := wf.mate_valid c u c' k0 c_lt u_lt glued
  obtain ⟨_, _, smooth_inside, _⟩ := runLen_spec (G := G) c u (wf.E_pos c c_lt)
  intro k k_lt
  induction k with
  | zero =>
    refine ⟨?_, fun k_pos => absurd k_pos (by omega)⟩
    simp only [iter_zero, iter_succ, prv_nxt k0_lt]; exact glued
  | succ k ih =>
    obtain ⟨glued_k, _⟩ := ih (by omega)
    -- the vertex reached after `k` steps is a vertex of `c`
    have at_lt : iter (nxt (G.E c)) k u < G.E c := iter_nxt_lt u_lt k
    -- the next vertex lies inside the run, so it is smooth
    have next_smooth := smooth_inside (k + 1) (by omega) k_lt
    rw [iter_succ] at next_smooth ⊢
    obtain ⟨not_corner, ⟨_, on_rim⟩ | ⟨c1, k1, glued_next, glued_prev, far_not_corner⟩⟩ :=
      smooth_iff.mp next_smooth
    · rw [prv_nxt at_lt, glued_k] at on_rim; cases on_rim
    · rw [prv_nxt at_lt, glued_k] at glued_prev
      simp only [Option.some.injEq, Prod.mk.injEq] at glued_prev
      obtain ⟨same_child, edge_eq⟩ := glued_prev
      rw [← same_child] at glued_next far_not_corner edge_eq
      obtain ⟨_, k1_lt, _⟩ := wf.mate_valid c _ c' k1 c_lt (nxt_lt at_lt) glued_next
      refine ⟨?_, fun _ => ⟨not_corner, ?_⟩⟩
      · rw [glued_next, iter_succ (prv _) (k + 1), edge_eq, prv_nxt k1_lt]
      · rw [edge_eq]; exact far_not_corner

/-- The four local rules of the zigzag lemma hold along a run. -/
theorem run_rules (wf : G.WF) {c u c' k0 : Nat} (c_lt : c < G.n) (u_lt : u < G.E c)
    (glued : G.mate c u = some (c', k0)) :
    let ι := G.runPort c u c' (nxt (G.E c') k0)
    let N := G.runLen c u
    (∀ k, k < N → G.sigma (ι (.c .R k)) = some (ι (.d .R (k + 1)))) ∧
    (∀ k, 0 < k → k < N → G.tau (ι (.d .R k)) = ι (.d .L k)) ∧
    (∀ k, k < N → G.sigma (ι (.d .L k)) = some (ι (.c .L (k + 1)))) ∧
    (∀ k, 0 < k → k < N → G.tau (ι (.c .L k)) = ι (.c .R k)) := by
  intro ι N
  -- along the run, the edges are glued to `c'` and the inner vertices are not corners
  have inv := run_inv wf c_lt u_lt glued
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k k_lt
    simp only [ι, runPort, Hand.isR, sigma, (inv k k_lt).1, Option.map_some]
  · intro k k_pos k_lt
    simp only [ι, runPort, Hand.isR]
    rw [tau_of_not_corner ((inv k k_lt).2 k_pos).2]; rfl
  · intro k k_lt
    -- the vertex reached after `k` steps is a vertex of `c`
    have at_lt : iter (nxt (G.E c)) k u < G.E c := iter_nxt_lt u_lt k
    obtain ⟨_, _, glued_back⟩ := wf.mate_valid c _ c' _ c_lt at_lt (inv k k_lt).1
    simp only [ι, runPort, Hand.isR, sigma]
    rw [← iter_succ (prv (G.E c')) k, glued_back]; rfl
  · intro k k_pos k_lt
    simp only [ι, runPort, Hand.isR]
    rw [tau_of_not_corner ((inv k k_lt).2 k_pos).1]; rfl

/-- The end of a run seen from the sibling's side is a mark too. -/
theorem run_end_mark (wf : G.WF) {c u c' k0 : Nat} (c_lt : c < G.n) (u_lt : u < G.E c)
    (glued : G.mate c u = some (c', k0)) :
    G.smooth c' (iter (prv (G.E c')) (G.runLen c u) (nxt (G.E c') k0)) = false := by
  obtain ⟨len_pos, _, _, _⟩ := runLen_spec (G := G) c u (wf.E_pos c c_lt)
  obtain ⟨N, len_eq⟩ : ∃ N, G.runLen c u = N + 1 := ⟨G.runLen c u - 1, by omega⟩
  -- the run's last edge, edge `N` from `u`, is glued to `c'`
  have last_glued := (run_inv wf c_lt u_lt glued N (by omega)).1
  -- the start of the last edge is a vertex of `c`
  have last_lt : iter (nxt (G.E c)) N u < G.E c := iter_nxt_lt u_lt N
  obtain ⟨_, _, glued_back⟩ := wf.mate_valid c _ c' _ c_lt last_lt last_glued
  -- the end of the run, seen on `c'`, is a vertex of `c'`
  have far_lt : iter (prv (G.E c')) (N + 1) (nxt (G.E c') k0) < G.E c' :=
    iter_prv_lt (nxt_lt (wf.mate_valid c u c' k0 c_lt u_lt glued).2.1) _
  rw [len_eq, smooth_symm wf (wf.mate_valid c u c' k0 c_lt u_lt glued).1 far_lt glued_back,
    ← iter_succ (nxt (G.E c)) N u, ← len_eq]
  exact runLen_mark wf c_lt u_lt

/-! ### The forced chain along a run -/

/-- If the full walk from `x` (with `q = τ x`) is forced along `N` crossings (each `σ` defined), it either stops after
them or not at all: every walk from `x` passes the end of those crossings, and every walk from there extends back to
`x`. -/
theorem chain {x q : GPort} {N : Nat} (N_pos : 1 ≤ N) (tau_x : G.tau x = q)
    (defined : ∀ k, k < N → G.sigma (iter G.Z k q) = some (G.sigmaTot (iter G.Z k q))) :
    (∀ m r, G.FReach m x r → N ≤ m ∧ G.FReach (m - N) (G.sigmaTot (iter G.Z (N - 1) q)) r) ∧
    (∀ j r, G.FReach j (G.sigmaTot (iter G.Z (N - 1) q)) r → G.FReach (j + N) x r) := by
  -- after a crossing, `τ` takes one more step of the zigzag
  have tau_step : ∀ k, G.tau (G.sigmaTot (iter G.Z k q)) = iter G.Z (k + 1) q := fun k => rfl
  -- forwards: a walk from `x` makes its first `k + 1` crossings along the zigzag
  have forced : ∀ k, k < N → ∀ m r, G.FReach m x r → k + 1 ≤ m ∧
      G.FReach (m - (k + 1)) (G.sigmaTot (iter G.Z k q)) r := by
    intro k
    induction k with
    | zero =>
      intro _ m r reach
      cases reach with
      | stop stops =>
        rw [tau_x] at stops
        -- `σ` is defined at the first port of the zigzag, so the walk cannot stop there
        have first := defined 0 N_pos
        simp only [iter_zero] at first
        rw [first] at stops
        contradiction
      | step crosses rest =>
        rw [tau_x] at crosses
        -- the first crossing is the zigzag's
        have first := defined 0 N_pos
        simp only [iter_zero] at first
        rw [first] at crosses
        cases crosses; simpa using rest
    | succ k ih =>
      intro k_lt m r reach
      obtain ⟨le_m, rest⟩ := ih (by omega) m r reach
      generalize rest_len_eq : m - (k + 1) = rest_len at rest
      cases rest with
      | stop stops => rw [tau_step, defined (k + 1) k_lt] at stops; contradiction
      | step crosses rest' =>
        rw [tau_step, defined (k + 1) k_lt] at crosses; cases crosses
        refine ⟨by omega, ?_⟩
        rw [show m - (k + 1 + 1) = _ from (by omega : m - (k + 1 + 1) = (m - (k + 1)) - 1), rest_len_eq]
        simpa using rest'
  -- backwards: a walk from the end of the first `k + 1` crossings extends to a walk from `x`
  have extend : ∀ k, k < N → ∀ j r, G.FReach j (G.sigmaTot (iter G.Z k q)) r → G.FReach (j + (k + 1)) x r := by
    intro k
    induction k with
    | zero =>
      intro _ j r reach
      -- the first crossing, from `τ x = q`
      have first := defined 0 N_pos
      simp only [iter_zero] at first
      exact .step (by rw [tau_x]; exact first) reach
    | succ k ih =>
      intro k_lt j r reach
      -- prepend crossing `k + 1`, then the first `k + 1` crossings
      have longer := ih (by omega) (j + 1) r (.step (by rw [tau_step]; exact defined (k + 1) k_lt) reach)
      rwa [show j + 1 + (k + 1) = j + (k + 1 + 1) by omega] at longer
  refine ⟨fun m r reach => ?_, fun j r reach => ?_⟩
  · obtain ⟨le_m, rest⟩ := forced (N - 1) (by omega) m r reach
    rw [show N - 1 + 1 = N by omega] at le_m rest; exact ⟨le_m, rest⟩
  · have whole := extend (N - 1) (by omega) j r reach  -- all `N` crossings
    rwa [show N - 1 + 1 = N by omega] at whole

/-- **The run step.** From a port `q` on a glued edge, the full walk is forced along the whole run, through the
zigzag, and arrives at `σ_red q`, which is a valid port at a mark. -/
theorem run_step (wf : G.WF) {q : GPort} (q_valid : G.Valid q) (crosses : G.sigma q ≠ none) :
    ∃ N, 1 ≤ N ∧
      (∀ k, k < N → G.sigma (iter G.Z k q) = some (G.sigmaTot (iter G.Z k q))) ∧
      G.sigmaRed q = some (G.sigmaTot (iter G.Z (N - 1) q)) ∧
      G.Valid (G.sigmaTot (iter G.Z (N - 1) q)) ∧
      G.smooth (G.sigmaTot (iter G.Z (N - 1) q)).1 (G.sigmaTot (iter G.Z (N - 1) q)).2.1 = false := by
  obtain ⟨c, u, s⟩ := q
  obtain ⟨c_lt, u_lt⟩ : c < G.n ∧ u < G.E c := q_valid
  -- where `σ` is defined, `sigmaTot` is `σ`
  have tot : ∀ {p p' : GPort}, G.sigma p = some p' → G.sigmaTot p = p' :=
    fun sigma_eq => by simp [sigmaTot, sigma_eq]
  cases s with
  | true =>
    -- R_c(u): the run of c from u
    cases glued : G.mate c u with
    | none => simp [sigma, glued] at crosses
    | some p =>
      obtain ⟨c', k0⟩ := p
      obtain ⟨c'_lt, k0_lt, _⟩ := wf.mate_valid c u c' k0 c_lt u_lt glued
      obtain ⟨across_R, hook_d, across_L, hook_c⟩ := run_rules wf c_lt u_lt glued
      obtain ⟨len_pos, _, _, _⟩ := runLen_spec (G := G) c u (wf.E_pos c c_lt)
      -- the zigzag lemma's core along the run
      have core := Zigzag.walk_core G.sigmaTot G.tau (G.runPort c u c' (nxt (G.E c') k0)) (G.runLen c u)
        (fun k k_lt => tot (across_R k k_lt)) hook_d (fun k k_lt => tot (across_L k k_lt)) hook_c
      -- the zigzag starts at `R_c(u)` itself
      have start : G.runPort c u c' (nxt (G.E c') k0) (.c .R 0) = (c, u, true) := rfl
      rw [start] at core
      -- where the last crossing of the run lands
      have last := (core (G.runLen c u - 1) (by omega)).2
      rw [show G.runLen c u - 1 + 1 = G.runLen c u by omega] at last
      refine ⟨G.runLen c u, len_pos, fun k k_lt => ?_, ?_, ?_, ?_⟩
      · rw [(core k k_lt).1]; split
        · rw [across_R k k_lt, tot (across_R k k_lt)]
        · rw [across_L k k_lt, tot (across_L k k_lt)]
      · rw [last]
        simp only [sigmaRed, glued]
        by_cases len_even : G.runLen c u % 2 = 0
        · rw [ite_eq_left len_even, ite_eq_right (show ¬ ((G.runLen c u - 1) % 2 = 0) by omega)]; rfl
        · rw [ite_eq_right len_even, ite_eq_left (show (G.runLen c u - 1) % 2 = 0 by omega)]; rfl
      · rw [last]
        split
        · exact ⟨c'_lt, iter_prv_lt (nxt_lt k0_lt) _⟩
        · exact ⟨c_lt, iter_nxt_lt u_lt _⟩
      · rw [last]
        split
        · exact run_end_mark wf c_lt u_lt glued
        · exact runLen_mark wf c_lt u_lt
  | false =>
    -- L_c(u): the run of the sibling c' from the point u, seen from c
    cases glued : G.mate c (prv (G.E c) u) with
    | none => simp [sigma, glued] at crosses
    | some p =>
      obtain ⟨c', k0⟩ := p
      obtain ⟨c'_lt, k0_lt, glued_back⟩ := wf.mate_valid c _ c' k0 c_lt (prv_lt u_lt) glued
      obtain ⟨across_R, hook_d, across_L, hook_c⟩ := run_rules wf c'_lt k0_lt glued_back
      rw [nxt_prv u_lt] at across_R hook_d across_L hook_c
      obtain ⟨len_pos, _, _, _⟩ := runLen_spec (G := G) c' k0 (wf.E_pos c' c'_lt)
      -- the zigzag lemma's core along the run of `c'`, relabelled so that it starts at `L_c(u)`
      have core := Zigzag.walk_core G.sigmaTot G.tau (fun s => G.runPort c' k0 c u (Zigzag.swap s)) (G.runLen c' k0)
        (fun k k_lt => by simp only [Zigzag.swap]; exact tot (across_L k k_lt))
        (fun k k_pos k_lt => by simp only [Zigzag.swap]; exact hook_c k k_pos k_lt)
        (fun k k_lt => by simp only [Zigzag.swap]; exact tot (across_R k k_lt))
        (fun k k_pos k_lt => by simp only [Zigzag.swap]; exact hook_d k k_pos k_lt)
      simp only [Zigzag.swap] at core
      -- the relabelled zigzag starts at `L_c(u)` itself
      have start : G.runPort c' k0 c u (.d .L 0) = (c, u, false) := rfl
      rw [start] at core
      -- where the last crossing of the run lands
      have last := (core (G.runLen c' k0 - 1) (by omega)).2
      rw [show G.runLen c' k0 - 1 + 1 = G.runLen c' k0 by omega] at last
      refine ⟨G.runLen c' k0, len_pos, fun j j_lt => ?_, ?_, ?_, ?_⟩
      · rw [(core j j_lt).1]; split
        · rw [across_L j j_lt, tot (across_L j j_lt)]
        · rw [across_R j j_lt, tot (across_R j j_lt)]
      · rw [last]
        simp only [sigmaRed, glued]
        by_cases len_even : G.runLen c' k0 % 2 = 0
        · rw [ite_eq_left len_even, ite_eq_right (show ¬ ((G.runLen c' k0 - 1) % 2 = 0) by omega)]; rfl
        · rw [ite_eq_right len_even, ite_eq_left (show (G.runLen c' k0 - 1) % 2 = 0 by omega)]; rfl
      · rw [last]
        split
        · exact ⟨c'_lt, iter_nxt_lt k0_lt _⟩
        · exact ⟨c_lt, iter_prv_lt u_lt _⟩
      · rw [last]
        split
        · exact runLen_mark wf c'_lt k0_lt
        · have far_mark := run_end_mark wf c'_lt k0_lt glued_back  -- the end of the run of `c'`, seen from `c`
          rwa [nxt_prv u_lt] at far_mark

/-! ### Prop 5.4 -/

/-- A full walk from a valid port `x` to `r` gives a reduced walk from `x` to `r`: each run the full walk crosses
is one step of the reduced walk. -/
theorem full_to_red (wf : G.WF) : ∀ m x r, G.Valid x → G.FReach m x r → G.RedReach x r := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro x r x_valid reach
    -- the hook or crossover at `x` leads to a port of the same child
    have next_valid := tau_valid wf x_valid
    cases cross : G.sigma (G.tau x) with
    | none =>
      cases reach with
      | stop _ => exact .stop (sigmaRed_eq_none_iff.mpr cross)
      | step crosses _ => rw [cross] at crosses; contradiction
    | some y0 =>
      obtain ⟨N, N_pos, defined, red_eq, end_valid, _⟩ := run_step wf next_valid (by rw [cross]; simp)
      obtain ⟨N_le, rest⟩ := (chain N_pos rfl defined).1 m r reach
      exact .step red_eq (ih (m - N) (by omega) _ r end_valid rest)

/-- A reduced walk from a valid port `x` to `r` gives a full walk from `x` to `r`: each step of the reduced walk is
a whole run of the full walk. -/
theorem red_to_full (wf : G.WF) : ∀ x r, G.RedReach x r → G.Valid x → G.FullReach x r := by
  intro x r reach
  induction reach with
  | stop stops => intro _; exact ⟨0, .stop (sigmaRed_eq_none_iff.mp stops)⟩
  | @step x y r crosses_red _ ih =>
    intro x_valid
    -- the hook or crossover at `x` leads to a port of the same child
    have next_valid := tau_valid wf x_valid
    -- the reduced walk crosses here, so the full walk does too
    have crosses : G.sigma (G.tau x) ≠ none := by
      intro on_rim; rw [sigmaRed_eq_none_iff.mpr on_rim] at crosses_red; contradiction
    obtain ⟨N, N_pos, defined, red_eq, end_valid, _⟩ := run_step wf next_valid crosses
    rw [red_eq] at crosses_red; cases crosses_red
    obtain ⟨j, rest⟩ := ih end_valid
    exact ⟨j + N, (chain N_pos rfl defined).2 j r rest⟩

/-- **Prop 5.4(b)**, from every port: the full walk (Lemma 4.2) and the reduced walk end at the same rim port. In
particular, at a parent port `p` on a mark, `π_P(p)` is the end of the reduced walk. -/
theorem prop_5_4_b (wf : G.WF) {x : GPort} (x_valid : G.Valid x) (r : GPort) :
    G.FullReach x r ↔ G.RedReach x r :=
  ⟨fun ⟨m, reach⟩ => full_to_red wf m x r x_valid reach, fun reach => red_to_full wf x r reach x_valid⟩

/-- **Prop 5.4(a).** A rim vertex of a child that is not a mark and whose rim edges lie on the parent's rim is a hook
of the parent. -/
theorem prop_5_4_a {c u : Nat} (smooth_u : G.smooth c u = true) (on_rim : G.mate c u = none) :
    G.FullReach (c, u, false) (c, u, true) := by
  -- a smooth vertex is not a corner, so `τ` is the hook there
  have not_corner := smooth_corner smooth_u
  refine ⟨0, ?_⟩
  -- the hook leads to `R_c(u)`, on the parent's rim, where the walk stops
  have stops_here := FReach.stop (G := G) (x := (c, u, false))
    (by rw [tau_of_not_corner not_corner]; simp [sigma, on_rim])
  rwa [tau_of_not_corner not_corner] at stops_here

/-- **Prop 5.4(c)**, in the form the induction uses: if the reduced walk from every port at a mark reaches the
parent's rim, then so does the full walk from every port, so the parent has no closed strand (`κ(P) = 0`). -/
theorem prop_5_4_c (wf : G.WF)
    (red_ends : ∀ x, G.Valid x → G.smooth x.1 x.2.1 = false → ∃ r, G.RedReach x r) :
    ∀ x, G.Valid x → ∃ r, G.FullReach x r := by
  intro x x_valid
  by_cases at_mark : G.smooth x.1 x.2.1 = false
  · obtain ⟨r, reach⟩ := red_ends x x_valid at_mark
    exact ⟨r, (prop_5_4_b wf x_valid r).mpr reach⟩
  · have smooth_x : G.smooth x.1 x.2.1 = true := by simpa using at_mark  -- inside a run, or on the parent's rim
    -- the hook at `x` leads to a port of the same child
    have next_valid := tau_valid wf x_valid
    cases cross : G.sigma (G.tau x) with
    | none => exact ⟨G.tau x, 0, .stop cross⟩
    | some _ =>
      -- inside a run: the full walk runs to its end, a mark, and the reduced walk goes on from there
      obtain ⟨N, N_pos, defined, _, end_valid, end_mark⟩ := run_step wf next_valid (by rw [cross]; simp)
      obtain ⟨r, reach⟩ := red_ends _ end_valid end_mark
      obtain ⟨j, rest⟩ := (prop_5_4_b wf end_valid r).mpr reach
      exact ⟨r, j + N, (chain N_pos rfl defined).2 j r rest⟩

/-- The full walk is deterministic, so `FullReach x` names one port: `π_P(x)`. -/
theorem fullReach_unique {x r r' : GPort} (reach : G.FullReach x r) (reach' : G.FullReach x r') : r = r' := by
  obtain ⟨k, walk⟩ := reach
  obtain ⟨k', walk'⟩ := reach'
  induction walk generalizing k' with
  | stop stops => cases walk' with
    | stop _ => rfl
    | step crosses' _ => rw [stops] at crosses'; contradiction
  | step crosses _ ih => cases walk' with
    | stop stops' => rw [crosses] at stops'; contradiction
    | step crosses' rest' => rw [crosses] at crosses'; cases crosses'; exact ih _ rest'

end Gluing

end SpectreKnot

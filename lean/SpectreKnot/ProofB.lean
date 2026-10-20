/-
**Theorem B** (`theoremB`, `theoremB_sharp`): the nest has no boundary, no closed strand, and any two ports of a
block lie on one strand of the block three levels up (`b` even) or four (`b` odd).

The merging (the paper's proof of Thm 9.1): a strand of `N_m` leaves it at a rim port; in `N_{m+1}` it runs on to the
parent hook at the junction that the junction map names (`step_tile`, `NestStep.lean`), or, on child 1's side 2, the
rim port is itself a parent hook (`stretch_eq`) (Lemma 9.3). The junctions lie inside the parent's sides 2–5
(Lemma 9.4), and inside side `J` the map depends only on `J` (`adv_some`, `adv_none`). Following the sides level by
level, every strand of `N_b` reaches the hook at junction 12 of `N_{b+3}` (even `b`) or `N_{b+4}` (odd `b`).
-/
import SpectreKnot.NestStep

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### Child 1's side 2: its rim ports are parent hooks -/

/-- The parent vertex at child 1's vertex `u` on its side 2 (piece 16 of the parent's rim, traversed backwards). -/
def stp (L : Nat → Nat → Nat) (u : Nat) : Nat := jpos L 16 + (pos (L 1) 3 - u)

/-- Piece 16 of the Δ-supertile's rim is child 1's side 2. -/
theorem piece16 : pieceD 16 = (1, 2) := by decide

/-- Piece 17 starts where piece 16, child 1's side 2, ends. -/
theorem jpos17 (L : Nat → Nat → Nat) : jpos L 17 = jpos L 16 + L 1 2 := by
  -- piece 17 starts where piece 16 does, plus its length
  have next_start := jpos_succ L (q := 16) (by omega)
  rw [piece16] at next_start
  exact next_start

/-- Rim position `jpos 16 + i` of the Δ-supertile is child 1's edge `pos 2 + L 1 2 - 1 - i`, on its side 2. -/
theorem ownGo16 (L : Nat → Nat → Nat) {i : Nat} (hi : i < L 1 2) :
    ownGo L (pcs .Delta) (jpos L 16 + i) = (1, pos (L 1) 2 + L 1 2 - 1 - i) := by
  -- the `i`-th edge of piece 16
  have on_piece := ownGo_jpos L (q := 16) (by omega) (by rw [piece16]; exact hi)
  rw [piece16] at on_piece
  exact on_piece

/-- The gluing's port `(1, u, s)` of `N_{m+1}` is port `(u, s)` of `N_m`, taken one level up. -/
theorem iota1 (m : Nat) (u : Nat) (s : Bool) :
    ιP (kidsD m) (ori m) (1, u, s) = upPort m 1 ((N m).bport (ori m) (u, s)) := rfl

/-- **On child 1's side 2, rim ports of `N_m` are rim ports of `N_{m+1}`**: for `u` strictly inside side 2, port
`(u, s)` of `N_m`, one level up, is port `(stp u, !s)` of `N_{m+1}` (the hand swaps with the orientation). -/
theorem stretch_eq {m : Nat} (m_pos : 1 ≤ m) {u : Nat} (after_two : pos (Lk m .Delta 1) 2 < u)
    (before_three : u < pos (Lk m .Delta 1) 3) (s : Bool) :
    upPort m 1 ((N m).bport (ori m) (u, s)) = (N (m + 1)).bport (ori (m + 1)) (stp (Lk m .Delta) u, !s) := by
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- child 1's side 2 ends `L 1 2` edges after it starts
  have side_two_len : pos (Lk m .Delta 1) 3 = pos (Lk m .Delta 1) 2 + Lk m .Delta 1 2 := pos_succ _ 2
  -- and no later than the rim
  have three_le_six := pos_mono (Lk m .Delta 1) (show 3 ≤ 6 by omega)
  -- piece 17 starts where piece 16 ends
  have piece17 := jpos17 (Lk m .Delta)
  -- and the rim ends at least 25 edges later
  have to_end := jpos_le (Lk m .Delta) (len5 m_pos) (q := 17) (q' := 22) (by omega) (by omega)
  -- so the parent vertex is on the parent's rim
  have stp_lt : stp (Lk m .Delta) u < rimN .Delta (Lk m .Delta) := by
    rw [← jpos_full]; simp only [stp]; omega
  -- piece 16 starts at least 5 edges along
  have piece16_far := jpos_pos m_pos (q := 16) (by omega) (by omega)
  rw [N_succ m_pos, ori_succ]
  cases s
  · rw [Bool.not_false, kids.bport_R stp_lt]
    -- the parent's rim edge at `stp u` is child 1's edge `u - 1`
    have edge_at := ownGo16 (Lk m .Delta) (i := pos (Lk m .Delta 1) 3 - u) (by omega)
    -- so the gluing's port there is `L` at child 1's vertex `u`
    have gR_eq : gR .Delta (Lk m .Delta) (dOff m) (ori m) (stp (Lk m .Delta) u) = (1, u, false) := by
      -- the end of edge `u - 1` is vertex `u`
      have next_vertex : nxt (pos (Lk m .Delta 1) 6) (pos (Lk m .Delta 1) 2 + Lk m .Delta 1 2 - 1 -
          (pos (Lk m .Delta 1) 3 - u)) = u := by
        simp only [nxt]; rw [ite_eq_right (by omega)]; omega
      simp only [gR, stp, edge_at, ofLens_E (show 1 < nk .Delta by decide), next_vertex]
    rw [gR_eq, iota1]
  · rw [Bool.not_true, kids.bport_L stp_lt]
    -- the rim position before `stp u`
    have before_stp : prv (rimN .Delta (Lk m .Delta)) (stp (Lk m .Delta) u) =
        jpos (Lk m .Delta) 16 + (pos (Lk m .Delta 1) 3 - u - 1) := by
      -- `stp u` is not rim position 0
      have stp_ne : stp (Lk m .Delta) u ≠ 0 := by simp only [stp]; omega
      simp only [prv]; rw [ite_eq_right stp_ne]; simp only [stp]; omega
    -- the parent's rim edge there is child 1's edge `u`
    have edge_at := ownGo16 (Lk m .Delta) (i := pos (Lk m .Delta 1) 3 - u - 1) (by omega)
    -- so the gluing's port there is `R` at child 1's vertex `u`
    have gL_eq : gL .Delta (Lk m .Delta) (stp (Lk m .Delta) u) = (1, u, true) := by
      -- the edge's number is `u`
      have edge_u : pos (Lk m .Delta 1) 2 + Lk m .Delta 1 2 - 1 - (pos (Lk m .Delta 1) 3 - u - 1) = u := by omega
      simp only [gL, before_stp, edge_at, edge_u]
    rw [gL_eq, iota1]

/-! ### Sides -/

/-- `v` lies inside side `J` of `N_n`, at least two vertices from either end. -/
def Inside (n J v : Nat) : Prop := pos (Lk n .Delta 1) J + 2 ≤ v ∧ v + 2 ≤ pos (Lk n .Delta 1) (J + 1)

/-- Side `J` of `N_{n+1}` starts where piece `sJ J` of its rim starts (with the level-`n` lengths). -/
theorem pos_up {n : Nat} (n_pos : 1 ≤ n) {J : Nat} (hJ : J ≤ 6) :
    pos (Lk (n + 1) .Delta 1) J = jpos (Lk n .Delta) (sJ J) := by
  rw [show pos (Lk (n + 1) .Delta 1) J = vpos (n + 1) .Delta J from rfl, vpos_eq n_pos .Delta hJ, vpos_jpos _ hJ]

/-- The sides start at pieces `0 … 22`. -/
theorem sJ_le : ∀ J, J ≤ 6 → sJ J ≤ 22 := by decide

/-- A junction `q` at least one piece after the start of side `J` and one piece before its end lies inside side `J`
of `N_{n+1}`. -/
theorem inside_of {n J q k₁ k₂ : Nat} (n_pos : 1 ≤ n) (hJ : J < 6) (after_start : sJ J + k₁ = q)
    (before_end : q + k₂ = sJ (J + 1)) (k₁_pos : 1 ≤ k₁) (k₂_pos : 1 ≤ k₂) :
    Inside (n + 1) J (jpos (Lk n .Delta) q) := by
  -- the side ends within the rim's 22 pieces
  have end_le := sJ_le (J + 1) (by omega)
  -- `k₁` pieces from the side's start to `q`, each of at least 5 edges
  have from_start := jpos_le_add (Lk n .Delta) (len5 n_pos) (sJ J) k₁ (by omega)
  -- and `k₂` pieces from `q` to the side's end
  have to_end := jpos_le_add (Lk n .Delta) (len5 n_pos) q k₂ (by omega)
  rw [after_start] at from_start
  rw [before_end] at to_end
  refine ⟨?_, ?_⟩
  · rw [pos_up n_pos (by omega)]; omega
  · rw [pos_up n_pos (by omega)]; omega

/-- Junction 9 lies inside side 2 of `N_{n+1}`. -/
theorem inside_9 {n : Nat} (n_pos : 1 ≤ n) : Inside (n + 1) 2 (jpos (Lk n .Delta) 9) :=
  inside_of n_pos (k₁ := 2) (k₂ := 2) (by omega) rfl rfl (by omega) (by omega)
/-- Junction 12 lies inside side 3 of `N_{n+1}`. -/
theorem inside_12 {n : Nat} (n_pos : 1 ≤ n) : Inside (n + 1) 3 (jpos (Lk n .Delta) 12) :=
  inside_of n_pos (k₁ := 1) (k₂ := 2) (by omega) rfl rfl (by omega) (by omega)
/-- Junction 16 lies inside side 4 of `N_{n+1}`. -/
theorem inside_16 {n : Nat} (n_pos : 1 ≤ n) : Inside (n + 1) 4 (jpos (Lk n .Delta) 16) :=
  inside_of n_pos (k₁ := 2) (k₂ := 3) (by omega) rfl rfl (by omega) (by omega)
/-- Junction 17 lies inside side 4 of `N_{n+1}`. -/
theorem inside_17 {n : Nat} (n_pos : 1 ≤ n) : Inside (n + 1) 4 (jpos (Lk n .Delta) 17) :=
  inside_of n_pos (k₁ := 3) (k₂ := 2) (by omega) rfl rfl (by omega) (by omega)
/-- Junction 21 lies inside side 5 of `N_{n+1}`. -/
theorem inside_21 {n : Nat} (n_pos : 1 ≤ n) : Inside (n + 1) 5 (jpos (Lk n .Delta) 21) :=
  inside_of n_pos (k₁ := 2) (k₂ := 1) (by omega) rfl rfl (by omega) (by omega)

/-- The parent vertex at a vertex strictly inside child 1's side 2 lies inside side 4 of `N_{n+1}`. -/
theorem inside_stp {n : Nat} (n_pos : 1 ≤ n) {u : Nat} (after_two : pos (Lk n .Delta 1) 2 < u)
    (before_three : u < pos (Lk n .Delta 1) 3) : Inside (n + 1) 4 (stp (Lk n .Delta) u) := by
  -- child 1's side 2 ends `L 1 2` edges after it starts
  have side_two_len : pos (Lk n .Delta 1) 3 = pos (Lk n .Delta 1) 2 + Lk n .Delta 1 2 := pos_succ _ 2
  -- piece 17 starts where piece 16 ends
  have piece17 := jpos17 (Lk n .Delta)
  -- side 4 starts (at piece 14) at least 10 edges before piece 16
  have side4_start := jpos_le (Lk n .Delta) (len5 n_pos) (q := 14) (q' := 16) (by omega) (by omega)
  -- and ends (at piece 19) at least 10 edges after piece 17
  have side4_end := jpos_le (Lk n .Delta) (len5 n_pos) (q := 17) (q' := 19) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [pos_up n_pos (by omega)]
    show jpos (Lk n .Delta) 14 + 2 ≤ jpos (Lk n .Delta) 16 + (pos (Lk n .Delta 1) 3 - u)
    omega
  · rw [pos_up n_pos (by omega)]
    show jpos (Lk n .Delta) 16 + (pos (Lk n .Delta 1) 3 - u) + 2 ≤ jpos (Lk n .Delta) 19
    omega

/-- A vertex inside a side is at least two vertices from both ends of the rim. -/
theorem inside_bounds {n J v : Nat} (hJ : J < 6) (inside : Inside n J v) :
    2 ≤ v ∧ v + 2 ≤ pos (Lk n .Delta 1) 6 := by
  -- `v` is at least two vertices after the start of side `J`
  have after_start := inside.1
  exact ⟨by omega, Nat.le_trans inside.2 (pos_mono _ (by omega))⟩

/-! ### The map read side by side -/

/-- From a vertex inside side `J` of `N_n` where the map names junction `q`, the strand runs on, one level up, to
the hook at junction `q` of `N_{n+1}`. -/
theorem adv_some {n : Nat} (n_pos : 1 ≤ n) {J v q : Nat} (hJ : J < 6) (inside : Inside n J v)
    (side_tgt : sideTgt (ori n) J = some q) :
    (N (n + 1)).Linked (upPort n 1 ((N n).bport (ori n) (v, true)))
      ((N (n + 1)).bport (ori (n + 1)) (jpos (Lk n .Delta) q, true)) := by
  -- `v` is a rim vertex of `N_n`, away from the corners
  have v_bounds := inside_bounds hJ inside
  exact step_tile n_pos (by omega) (by rw [tgt_side true hJ inside.1 inside.2]; exact side_tgt)

/-- From a vertex inside side 2 of `N_n` (on the parent's rim), the strand is, one level up, on the hook at the same
vertex of `N_{n+1}`. -/
theorem adv_none {n : Nat} (n_pos : 1 ≤ n) {v : Nat} (inside : Inside n 2 v) :
    (N (n + 1)).Linked (upPort n 1 ((N n).bport (ori n) (v, true)))
      ((N (n + 1)).bport (ori (n + 1)) (stp (Lk n .Delta) v, true)) := by
  -- `v` lies at least two vertices after the start of side 2
  have after_start := inside.1
  -- and two before its end, vertex `pos 3`
  have before_three : v + 2 ≤ pos (Lk n .Delta 1) 3 := inside.2
  rw [stretch_eq n_pos (by omega) (by omega), Bool.not_true]
  -- the parent vertex lies inside side 4 of `N_{n+1}`, so it is a hook
  have stp_inside := inside_stp n_pos (show pos (Lk n .Delta 1) 2 < v by omega) (by omega)
  exact hook (by omega) (inside_bounds (by omega) stp_inside).1 (inside_bounds (by omega) stp_inside).2

/-- `x` is on the strand of the hook at a vertex inside side `J` of `N_n`. -/
def Reach (n J : Nat) (x : Port) : Prop :=
  (N n).IsPort x ∧ ∃ v, Inside n J v ∧ (N n).Linked x ((N n).bport (ori n) (v, true))

/-- A strand that reaches a hook inside side `J` of `N_n` reaches, one level up, the hook at the junction the map
names for side `J`. -/
theorem reach_some {n : Nat} (n_pos : 1 ≤ n) {J q : Nat} (hJ : J < 6) {x : Port} (reach : Reach n J x)
    (side_tgt : sideTgt (ori n) J = some q) :
    (N (n + 1)).Linked (upPort n 1 x) ((N (n + 1)).bport (ori (n + 1)) (jpos (Lk n .Delta) q, true)) := by
  obtain ⟨x_port, v, inside, linked⟩ := reach
  exact (lift_nest n_pos linked x_port).trans (adv_some n_pos hJ inside side_tgt)

/-- A strand that reaches a hook inside side 2 of `N_n` (on the parent's rim) reaches, one level up, a hook inside
side 4 of `N_{n+1}`. -/
theorem reach_none {n : Nat} (n_pos : 1 ≤ n) {x : Port} (reach : Reach n 2 x) : Reach (n + 1) 4 (upPort n 1 x) := by
  obtain ⟨x_port, v, inside, linked⟩ := reach
  -- `v` lies at least two vertices after the start of side 2
  have after_start := inside.1
  -- and two before its end, vertex `pos 3`
  have before_three : v + 2 ≤ pos (Lk n .Delta 1) 3 := inside.2
  exact ⟨isPort_up n_pos x_port, _, inside_stp n_pos (by omega) (by omega),
    (lift_nest n_pos linked x_port).trans (adv_none n_pos inside)⟩

/-- A port of `N_{n+1}` on the strand of the hook at a junction inside side `J` reaches side `J`. -/
theorem reach_of {n J q : Nat} {y : Port} (y_port : (N (n + 1)).IsPort y)
    (inside : Inside (n + 1) J (jpos (Lk n .Delta) q))
    (linked : (N (n + 1)).Linked y ((N (n + 1)).bport (ori (n + 1)) (jpos (Lk n .Delta) q, true))) :
    Reach (n + 1) J y :=
  ⟨y_port, _, inside, linked⟩

/-! ### The first step: from a port of `N_b` -/

/-- The map names no junction only strictly inside side 2. -/
theorem tgt_none {ω : Bool} {f : Nat → Nat} {u : Nat} {s : Bool} (tgt_eq : tgt ω f u s = none) :
    pos f 2 < u ∧ u < pos f 3 := by
  unfold tgt at tgt_eq
  revert tgt_eq
  cases ω <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> (repeat' split) <;> intro tgt_eq <;>
    first | omega | (exfalso; simp at tgt_eq)

/-- For `ω = true` the map names only junctions 17, 9, 16 and 12. -/
theorem tgt_vals_t {f : Nat → Nat} {u : Nat} {s : Bool} {q : Nat} (tgt_eq : tgt true f u s = some q) :
    q = 17 ∨ q = 9 ∨ q = 16 ∨ q = 12 := by
  unfold tgt at tgt_eq
  revert tgt_eq
  cases s <;> simp only [ite_true] <;> (repeat' split) <;> intro tgt_eq <;>
    simp only [Option.some.injEq, reduceCtorEq] at tgt_eq <;> omega

/-- For `ω = false` the map names only junctions 21, 16 and 17. -/
theorem tgt_vals_f {f : Nat → Nat} {u : Nat} {s : Bool} {q : Nat} (tgt_eq : tgt false f u s = some q) :
    q = 21 ∨ q = 16 ∨ q = 17 := by
  unfold tgt at tgt_eq
  revert tgt_eq
  cases s <;> simp only [Bool.false_eq_true, ite_false] <;> (repeat' split) <;> intro tgt_eq <;>
    simp only [Option.some.injEq, reduceCtorEq] at tgt_eq <;> omega

/-- **The first step**: one level up, every port of `N_b` reaches a hook inside side 2, 3 or 4 of `N_{b+1}` (if
`ω_b = true`, that is `b` even) or inside side 4 or 5 (if `ω_b = false`). Inside side 2, the hook is the one at
junction 9. -/
theorem first {b : Nat} (b_pos : 1 ≤ b) {x : Port} (x_port : (N b).IsPort x) :
    ∃ J, Reach (b + 1) J (upPort b 1 x) ∧ (ori b = true → J = 2 ∨ J = 3 ∨ J = 4) ∧
      (ori b = false → J = 4 ∨ J = 5) ∧
      (J = 2 → (N (b + 1)).Linked (upPort b 1 x) ((N (b + 1)).bport (ori (b + 1)) (jpos (Lk b .Delta) 9, true))) := by
  -- `N_b` has the signature
  have good_b := good b .Delta b_pos
  -- following the ribbon from `x` leaves `N_b` at a port `r`
  obtain ⟨r, follows⟩ := good_b.sig.noClosed x x_port
  obtain ⟨nothing_across, r_tile, r_vertex⟩ := Patch.Follow.end_ good_b.sig follows x_port.1 x_port.2
  -- `r` is port `s` at a rim vertex `u`
  obtain ⟨u, s, hu, rfl⟩ := Patch.rim_port good_b.sig r_tile r_vertex nothing_across
  -- the rim of `N_b`
  have rim_len := E_N b_pos
  unfold N at rim_len
  rw [rim_len] at hu
  -- one level up, `x` is on the strand of that rim port
  have lifted := lift_nest b_pos (.of_follow follows) x_port
  -- and is a port of `N_{b+1}`
  have x_up_port := isPort_up b_pos x_port
  cases tgt_eq : tgt (ori b) (Lk b .Delta 1) u s with
  | none =>
    -- strictly inside child 1's side 2: the rim port is a hook of `N_{b+1}`, inside its side 4
    obtain ⟨after_two, before_three⟩ := tgt_none tgt_eq
    refine ⟨4, ⟨x_up_port, _, inside_stp b_pos after_two before_three, lifted.trans ?_⟩, fun _ => by omega,
      fun _ => by omega, fun wrong => absurd wrong (by decide)⟩
    -- the rim port of `N_b`, one level up, is a rim port of `N_{b+1}`
    have same_port := stretch_eq b_pos after_two before_three s
    rw [show N b = super b .Delta from rfl] at same_port
    rw [same_port]
    -- inside side 4 of `N_{b+1}`
    have stp_inside := inside_stp b_pos after_two before_three
    cases s
    · exact .refl
    · exact hook (by omega) (inside_bounds (by omega) stp_inside).1 (inside_bounds (by omega) stp_inside).2
  | some q =>
    -- one level up, the strand runs on to the hook at junction `q`
    have to_junction := lifted.trans (step_tile b_pos hu tgt_eq)
    cases orient : ori b
    · rw [orient] at tgt_eq
      rcases tgt_vals_f tgt_eq with rfl | rfl | rfl
      · exact ⟨5, reach_of x_up_port (inside_21 b_pos) to_junction, fun wrong => by simp at wrong, fun _ => by omega,
          fun wrong => absurd wrong (by decide)⟩
      · exact ⟨4, reach_of x_up_port (inside_16 b_pos) to_junction, fun wrong => by simp at wrong, fun _ => by omega,
          fun wrong => absurd wrong (by decide)⟩
      · exact ⟨4, reach_of x_up_port (inside_17 b_pos) to_junction, fun wrong => by simp at wrong, fun _ => by omega,
          fun wrong => absurd wrong (by decide)⟩
    · rw [orient] at tgt_eq
      rcases tgt_vals_t tgt_eq with rfl | rfl | rfl | rfl
      · exact ⟨4, reach_of x_up_port (inside_17 b_pos) to_junction, fun _ => by omega, fun wrong => by simp at wrong,
          fun wrong => absurd wrong (by decide)⟩
      · exact ⟨2, reach_of x_up_port (inside_9 b_pos) to_junction, fun _ => by omega, fun wrong => by simp at wrong,
          fun _ => to_junction⟩
      · exact ⟨4, reach_of x_up_port (inside_16 b_pos) to_junction, fun _ => by omega, fun wrong => by simp at wrong,
          fun wrong => absurd wrong (by decide)⟩
      · exact ⟨3, reach_of x_up_port (inside_12 b_pos) to_junction, fun _ => by omega, fun wrong => by simp at wrong,
          fun wrong => absurd wrong (by decide)⟩

/-! ### The chain -/

/-- The hook at junction 12 of `N_{n+1}`, where every strand of the block three or four levels down ends up. -/
def Zp (n : Nat) : Port := (N (n + 1)).bport (ori (n + 1)) (jpos (Lk n .Delta) 12, true)

/-- Even levels have `ω = true`. -/
theorem ori_even {n : Nat} (even : n % 2 = 0) : ori n = true := by simp [ori, even]
/-- Odd levels have `ω = false`. -/
theorem ori_odd {n : Nat} (odd : n % 2 = 1) : ori n = false := by simp [ori, odd]

/-- **Even `b`**: every port of `N_b` lies, in `N_{b+3}`, on the strand of the hook at junction 12. -/
theorem chain_even {b : Nat} (b_pos : 1 ≤ b) (even : b % 2 = 0) {x : Port} (x_port : (N b).IsPort x) :
    (N (b + 3)).Linked (upPort b 3 x) (Zp (b + 2)) := by
  -- level `b` is even
  have ori_b := ori_even even
  -- level `b + 1` odd
  have ori_b1 : ori (b + 1) = false := ori_odd (by omega)
  -- and level `b + 2` even
  have ori_b2 : ori (b + 2) = true := ori_even (by omega)
  -- one level up: inside side 2, 3 or 4
  obtain ⟨J, reach_J, sides_even, _, _⟩ := first b_pos x_port
  -- two levels up: inside side 4
  have reach_four : Reach (b + 2) 4 (upPort (b + 1) 1 (upPort b 1 x)) := by
    -- the port, one level up, is a port of `N_{b+1}`
    have up_port := isPort_up (show 1 ≤ b + 1 by omega) reach_J.1
    rcases sides_even ori_b with rfl | rfl | rfl
    · exact reach_none (by omega) reach_J
    · exact reach_of up_port (inside_16 (by omega)) (reach_some (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
    · exact reach_of up_port (inside_16 (by omega)) (reach_some (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
  -- three levels up: the hook at junction 12
  exact reach_some (n := b + 2) (by omega) (by omega) reach_four (by rw [ori_b2]; rfl)

/-- **Odd `b`**: every port of `N_b` lies, in `N_{b+4}`, on the strand of the hook at junction 12. -/
theorem chain_odd {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) {x : Port} (x_port : (N b).IsPort x) :
    (N (b + 4)).Linked (upPort b 4 x) (Zp (b + 3)) := by
  -- level `b` is odd
  have ori_b := ori_odd odd
  -- level `b + 1` even
  have ori_b1 : ori (b + 1) = true := ori_even (by omega)
  -- level `b + 2` odd
  have ori_b2 : ori (b + 2) = false := ori_odd (by omega)
  -- and level `b + 3` even
  have ori_b3 : ori (b + 3) = true := ori_even (by omega)
  -- one level up: inside side 4 or 5
  obtain ⟨J, reach_J, _, sides_odd, _⟩ := first b_pos x_port
  -- the port, one level up, is a port of `N_{b+1}`
  have up_port := isPort_up (show 1 ≤ b + 1 by omega) reach_J.1
  -- three levels up: inside side 4
  have reach_four : Reach (b + 3) 4 (upPort (b + 2) 1 (upPort (b + 1) 1 (upPort b 1 x))) := by
    -- the port, two levels up, is a port of `N_{b+2}`
    have up_port2 := isPort_up (show 1 ≤ b + 2 by omega) up_port
    rcases sides_odd ori_b with rfl | rfl
    · -- from side 4
      -- two levels up, inside side 3
      have reach_three : Reach (b + 2) 3 (upPort (b + 1) 1 (upPort b 1 x)) :=
        reach_of up_port (inside_12 (by omega)) (reach_some (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
      exact reach_of up_port2 (inside_16 (by omega))
        (reach_some (by omega) (by omega) reach_three (by rw [ori_b2]; rfl))
    · -- from side 5
      -- two levels up, inside side 2
      have reach_two : Reach (b + 2) 2 (upPort (b + 1) 1 (upPort b 1 x)) :=
        reach_of up_port (inside_9 (by omega)) (reach_some (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
      exact reach_none (by omega) reach_two
  -- four levels up: the hook at junction 12
  exact reach_some (n := b + 3) (by omega) (by omega) reach_four (by rw [ori_b3]; rfl)

/-- Any number of levels up, a port of `N_b` is still a port. -/
theorem isPort_upk {b : Nat} (b_pos : 1 ≤ b) {x : Port} (x_port : (N b).IsPort x) :
    ∀ k, (N (b + k)).IsPort (upPort b k x)
  | 0 => x_port
  | k + 1 => by rw [upPort_succ]; exact isPort_up (m := b + k) (by omega) (isPort_upk b_pos x_port k)

/-- **Theorem B with the paper's bound.** -/
theorem theoremB_sharp : TheoremB_sharp := by
  intro b p q b_pos hp hq
  rcases Nat.mod_two_eq_zero_or_one b with even | odd
  · -- even `b`
    -- both ports reach the hook at junction 12 of `N_{b+3}`, so they lie on one strand there
    have linked3 : (N (b + 3)).Linked (upPort b 3 p) (upPort b 3 q) :=
      (chain_even b_pos even hp).trans
        (linked_symm (m := b + 3) (by omega) (chain_even b_pos even hq) (isPort_upk b_pos hq 3))
    refine ⟨?_, fun _ => linked3⟩
    -- and one level further up, in `N_{b+4}`
    have linked4 := lift_nest (m := b + 3) (by omega) linked3 (isPort_upk b_pos hp 3)
    rw [← upPort_succ, ← upPort_succ] at linked4
    exact linked4
  · -- odd `b`: both ports reach the hook at junction 12 of `N_{b+4}`
    exact ⟨(chain_odd b_pos odd hp).trans
      (linked_symm (m := b + 4) (by omega) (chain_odd b_pos odd hq) (isPort_upk b_pos hq 4)),
      fun is_even => absurd is_even (by omega)⟩

/-! ### No boundary -/

/-- An edge glued in `N_m` stays glued in `N_{m+1}`. -/
theorem glue_up {m : Nat} (m_pos : 1 ≤ m) {t i : Nat} (ht : t < (N m).tiles) {e : Nat × Nat}
    (glued : (N m).glue t i = some e) : ∃ e', (N (m + 1)).glue (up m 1 t) i = some e' := by
  rw [N_succ m_pos]
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the same gluing, in child 1
  have glued_child : (kidsD m 1).glue t i = some e := glued
  show ∃ e', (Par m).glue (t + offC (kidsD m) 1) i = some e'
  rw [kids.glue_shift (c := 1) (by decide) ht]
  unfold glueAt
  rw [glued_child]
  exact ⟨_, rfl⟩

/-- Child 1's sides other than side 2 are glued to siblings. -/
theorem mate_some {n : Nat} (n_pos : 1 ≤ n) {p j : Nat} (hj : j < 6) (not_two : j ≠ 2)
    (after_start : pos (Lk n .Delta 1) j ≤ p) (before_end : p < pos (Lk n .Delta 1) (j + 1)) :
    ∃ e, (Comp.ofLens .Delta (Lk n .Delta) (dOff n) (ori n)).toGluing.mate 1 p = some e := by
  -- side `j` has `L 1 j` edges
  have side_len := pos_succ (Lk n .Delta 1) j
  obtain ⟨o, rfl⟩ : ∃ o, p = pos (Lk n .Delta 1) j + o := ⟨p - pos (Lk n .Delta 1) j, by omega⟩
  show ∃ e, (Comp.ofLens .Delta (Lk n .Delta) (dOff n) (ori n)).mate 1 (pos (Lk n .Delta 1) j + o) = some e
  rw [ofLens_mate (fun c _ j _ => by
    -- every side has an edge
    have := len5 n_pos c j
    omega) (by decide) hj (by omega)]
  cases adj : adjAt .Delta 1 j with
  | none => exact absurd (adj_one_none j hj adj) not_two
  | some _ => exact ⟨_, rfl⟩

/-- **No boundary** (Lemma 8.3(b)): every edge of `N_b` is glued in `N_{b+2}`. -/
theorem no_boundary {b : Nat} (b_pos : 1 ≤ b) {t i : Nat} (ht : t < (N b).tiles) (hi : i < 14) :
    ((N (b + 2)).glue (up b 2 t) i).isSome := by
  -- `N_b` has the signature
  have good_b := good b .Delta b_pos
  -- so does `N_{b+1}`, of level at least 1
  have b1_pos : 1 ≤ b + 1 := by omega
  -- the tile, one level up, is a tile of `N_{b+1}`
  have t_up : up b 1 t < (N (b + 1)).tiles := (isPort_up b_pos (x := (t, i, true)) ⟨ht, hi⟩).1
  -- an edge glued in `N_{b+1}` is glued in `N_{b+2}`
  have glued_up : ∀ e, (N (b + 1)).glue (up b 1 t) i = some e → ((N (b + 2)).glue (up b 2 t) i).isSome := by
    intro e glued
    obtain ⟨e', glued'⟩ := glue_up b1_pos t_up glued
    rw [show up b 2 t = up (b + 1) 1 (up b 1 t) from rfl, glued']; rfl
  cases glued_b : (N b).glue t i with
  | some e =>
    -- glued in `N_b`, so in `N_{b+1}`
    obtain ⟨e', glued'⟩ := glue_up b_pos ht glued_b
    exact glued_up e' glued'
  | none =>
    -- a rim edge of `N_b`, at rim position `k`
    obtain ⟨k, hk, at_k⟩ := good_b.sig.rim_all t i ht hi glued_b
    -- the children of `N_{b+1}`
    have kids := KD b_pos
    -- the rim of `N_b`
    have rim_len := E_N b_pos
    unfold N at rim_len
    -- so `k` is a rim position of child 1
    have k_lt : k < pos (Lk b .Delta 1) 6 := by rw [← rim_len]; exact hk
    -- `N_{b+1}` glues the edge as the gluing's `mate` says
    have formula := kids.glue_rimEdge (c := 1) (by decide) hk
    -- the edge, as rim edge `k` of child 1
    have at_k' : (kidsD b 1).edgeAt k = (t, i) := at_k
    rw [at_k'] at formula
    -- its side `j` and offset `o`
    obtain ⟨j, o, hj, ho, k_eq⟩ := decomp (Lk b .Delta 1) 6 (Nat.le_refl _) k k_lt
    -- side `j` has `L 1 j` edges
    have side_len := pos_succ (Lk b .Delta 1) j
    by_cases side_two : j = 2
    · -- on child 1's side 2: a rim edge of `N_{b+1}`, on its side 4
      subst side_two
      -- side 2 of child 1 lies on the parent's rim
      have on_rim : (Comp.ofLens .Delta (Lk b .Delta) (dOff b) (ori b)).toGluing.mate 1 k = none := by
        rw [k_eq]
        exact ofLens_mate_none (fun c j => by
          -- every side has an edge
          have := len5 b_pos c j
          omega) (by decide) (by omega) ho rfl
      -- so the edge is the parent's rim edge at some position `p`
      obtain ⟨p, hp, own_p⟩ := own_surj (d := dOff b) (ω := ori b) kids.len_pos (by decide) k_lt on_rim
      -- piece 17 starts where piece 16 ends
      have piece17 := jpos17 (Lk b .Delta)
      -- and the rim ends at least 25 edges later
      have to_end := jpos_le (Lk b .Delta) (len5 b_pos) (q := 17) (q' := 22) (by omega) (by omega)
      -- where the pieces end
      have pieces_end := jpos_full (Lk b .Delta)
      -- `p` is on piece 16, child 1's side 2
      have p_eq : p = jpos (Lk b .Delta) 16 + (Lk b .Delta 1 2 - 1 - o) := by
        apply own_inj kids.len_pos hp (by omega)
        rw [own_p, ownGo16 _ (by omega), k_eq]
        -- the same edge of child 1
        have edge_eq : pos (Lk b .Delta 1) 2 + Lk b .Delta 1 2 - 1 - (Lk b .Delta 1 2 - 1 - o) =
            pos (Lk b .Delta 1) 2 + o := by omega
        rw [edge_eq]
      -- the edge at rim position `p` of `N_{b+1}` is `(up b 1 t, i)`
      have edge_p : (kidsD (b + 1) 1).edgeAt p = (up b 1 t, i) := by
        show (N (b + 1)).edgeAt p = _
        rw [N_succ b_pos, rim_edgeAt kids.shape hp, own_p, at_k']
        rfl
      -- the children of `N_{b+2}`
      have kids' := KD b1_pos
      -- `p` is a rim position of `N_{b+1}`, child 1 of `N_{b+2}`
      have p_lt : p < (kidsD (b + 1) 1).E := by
        show p < (N (b + 1)).E
        rw [N_succ b_pos, compose_E kids.shape]; exact hp
      -- `N_{b+2}` glues it as `mate` says
      have formula' := kids'.glue_rimEdge (c := 1) (by decide) p_lt
      rw [edge_p] at formula'
      -- side 4 of `N_{b+1}` starts at piece 14
      have side4_start := pos_up b_pos (J := 4) (by omega)
      -- and side 5 at piece 19
      have side5_start := pos_up b_pos (J := 5) (by omega)
      -- piece 16 starts at least 10 edges after piece 14
      have from14 := jpos_le (Lk b .Delta) (len5 b_pos) (q := 14) (q' := 16) (by omega) (by omega)
      -- and piece 19 at least 10 edges after piece 17
      have to19 := jpos_le (Lk b .Delta) (len5 b_pos) (q := 17) (q' := 19) (by omega) (by omega)
      -- side 4 of child 1 of `N_{b+2}` is glued to a sibling
      obtain ⟨e, mated⟩ := mate_some b1_pos (j := 4) (p := p) (by omega) (by omega)
        (by rw [side4_start]; show jpos (Lk b .Delta) 14 ≤ p; omega)
        (by rw [side5_start]; show p < jpos (Lk b .Delta) 19; omega)
      rw [mated] at formula'
      rw [N_succ (show 1 ≤ b + 1 by omega)]
      show ((Par (b + 1)).glue (up b 1 t + offC (kidsD (b + 1)) 1) i).isSome
      rw [formula']; rfl
    · -- on another side: glued to a sibling in `N_{b+1}`
      obtain ⟨e, mated⟩ := mate_some b_pos (j := j) (p := k) hj side_two (by omega) (by omega)
      rw [mated, Option.map_some] at formula
      exact glued_up _ (by rw [N_succ b_pos]; exact formula)

/-! ### Theorem B -/

/-- **Theorem B** (as stated in `Statement.lean`). -/
theorem theoremB : TheoremB := by
  refine ⟨fun b b_pos t i ht hi => no_boundary b_pos ht hi, fun b => theoremA b .Delta, ?_⟩
  intro b p q hp hq
  rcases Nat.eq_zero_or_pos b with rfl | b_pos
  · -- `N_0` is one tile, tile 1 of `N_1`
    -- `N_1` has nine tiles
    have nine : (N 1).tiles = 9 := by decide
    -- `p` is on the one tile of `N_0`
    have p_tile : p.1 < 1 := hp.1
    -- and so is `q`
    have q_tile : q.1 < 1 := hq.1
    -- one level up, `p` is a port of `N_1`
    have p_up : (N 1).IsPort (upPort 0 1 p) := ⟨show p.1 + 1 < (N 1).tiles by omega, hp.2⟩
    -- and so is `q`
    have q_up : (N 1).IsPort (upPort 0 1 q) := ⟨show q.1 + 1 < (N 1).tiles by omega, hq.2⟩
    exact ⟨5, (theoremB_sharp 1 _ _ (Nat.le_refl _) p_up q_up).1⟩
  · exact ⟨4, (theoremB_sharp b p q b_pos hp hq).1⟩

end SpectreKnot.Statement

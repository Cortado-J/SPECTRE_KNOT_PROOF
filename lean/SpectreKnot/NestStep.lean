/-
**The junction map at tile level.** `N_{m+1}` is the Δ composition whose child 1 is `N_m`. A rim port of `N_m`
(outside child 1's side 2) lies, in `N_{m+1}`, on the strand of the parent hook at the junction that `StepMap.lean`'s
map names (`step_tile`; the paper's Lemma 9.3). Also: where the pieces of the parent's rim start (`jpos`), lifting strands up the nest
(`lift_nest`), and the hooks of `N_m` (`hook`).
-/
import SpectreKnot.StepMap
import SpectreKnot.Linked

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### Where the pieces of the Δ-supertile's rim start -/

/-- Where piece `q` of the Δ-supertile's rim starts, for children's side lengths `L`. -/
def jpos (L : Nat → Nat → Nat) (q : Nat) : Nat := totL L ((pcs .Delta).take q)

/-- Table 3 lists 22 pieces for the Δ-supertile's rim. -/
theorem pcs_len : (pcs .Delta).length = 22 := by decide

/-- Piece `q < 22` of the flattened Table 3 is `pieceD q`. -/
theorem pcs_get {q : Nat} (hq : q < 22) : (pcs .Delta)[q]? = some (pieceD q) := by
  rw [List.getElem?_eq_getElem (by rw [pcs_len]; exact hq)]
  simp only [pieceD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q < (pcs .Delta).length by
    rw [pcs_len]; exact hq), Option.getD_some]

/-- Piece `q + 1` starts where piece `q` starts, plus the length of piece `q`. -/
theorem jpos_succ (L : Nat → Nat → Nat) {q : Nat} (hq : q < 22) :
    jpos L (q + 1) = jpos L q + L (pieceD q).1 (pieceD q).2 := by
  simp only [jpos]
  rw [List.take_succ, totL_append, pcs_get hq]
  simp [totL]

/-- With every side at least 5 edges long, the piece `k` places after piece `q` starts at least `5 k` edges later. -/
theorem jpos_le_add (L : Nat → Nat → Nat) (len_ge : ∀ c j, 5 ≤ L c j) (q : Nat) :
    ∀ k, q + k ≤ 22 → jpos L q + 5 * k ≤ jpos L (q + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro fits
    -- the first `k` pieces
    have := ih (by omega)
    rw [← Nat.add_assoc, jpos_succ L (by omega)]
    -- then piece `q + k`, of at least 5 edges
    have := len_ge (pieceD (q + k)).1 (pieceD (q + k)).2
    omega

/-- With every side at least 5 edges long, piece `q'` starts at least `5 (q' - q)` edges after piece `q`. -/
theorem jpos_le (L : Nat → Nat → Nat) (len_ge : ∀ c j, 5 ≤ L c j) {q q' : Nat} (q_le : q ≤ q') (q'_le : q' ≤ 22) :
    jpos L q + 5 * (q' - q) ≤ jpos L q' := by
  -- `q' - q` pieces on from piece `q`
  have spread := jpos_le_add L len_ge q (q' - q) (by omega)
  rwa [show q + (q' - q) = q' by omega] at spread

/-- The 22 pieces make up the whole rim. -/
theorem jpos_full (L : Nat → Nat → Nat) : jpos L 22 = rimN .Delta L := by
  simp only [jpos, rimN]
  rw [List.take_of_length_le (by rw [pcs_len]; exact Nat.le_refl _)]

/-- The rim position `jpos q + i` lies on piece `q`, at its `i`-th edge (counted in the parent's sense). -/
theorem ownGo_jpos (L : Nat → Nat → Nat) {q i : Nat} (hq : q < 22) (hi : i < L (pieceD q).1 (pieceD q).2) :
    ownGo L (pcs .Delta) (jpos L q + i) =
      ((pieceD q).1, pos (L (pieceD q).1) (pieceD q).2 + L (pieceD q).1 (pieceD q).2 - 1 - i) := by
  -- the pieces from `q` on: piece `q`, then the rest
  have drop_q : (pcs .Delta).drop q = pieceD q :: (pcs .Delta).drop (q + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [pcs_len]; exact hq)]
    congr 1
    -- piece `q` of the list
    have get_q := pcs_get hq
    rw [List.getElem?_eq_getElem (by rw [pcs_len]; exact hq)] at get_q
    simpa using get_q
  conv => lhs; rw [← List.take_append_drop q (pcs .Delta)]
  rw [ownGo_append, drop_q, show totL L ((pcs .Delta).take q) = jpos L q from rfl, if_neg (by omega),
    Nat.add_sub_cancel_left]
  simp only [ownGo]
  rw [if_pos hi]

/-- Where side `J` of the Δ-supertile starts, as a piece number. -/
def sJ (J : Nat) : Nat := [0, 5, 7, 11, 14, 19, 22].getD J 0

/-- Table 3's pieces for sides `0 … J - 1` of the Δ-supertile are its first `sJ J` pieces. -/
theorem pside_take : ∀ J, J ≤ 6 → ((pside .Delta).take J).flatMap id = (pcs .Delta).take (sJ J) := by decide

/-- Side `J` of the Δ-supertile starts where piece `sJ J` does. -/
theorem vpos_jpos (L : Nat → Nat → Nat) {J : Nat} (hJ : J ≤ 6) : pos (parentLen .Delta L) J = jpos L (sJ J) := by
  rw [← totL_take L .Delta J hJ, pside_take J hJ]; rfl

/-! ### The nest -/

/-- `N_{m+1}`, as `compose` builds it. -/
abbrev Par (m : Nat) : Patch := compose .Delta fun c => super m (kidAt .Delta c)

/-- The children of `N_{m+1}`: the level-`m` supertiles of the kinds Table 1 lists for Δ. -/
abbrev kidsD (m : Nat) : Nat → Patch := fun c => super m (kidAt .Delta c)

/-- For `m ≥ 1`, `N_{m+1}` is the Δ composition of its level-`m` children. -/
theorem N_succ {m : Nat} (m_pos : 1 ≤ m) : N (m + 1) = Par m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

/-- Going `k + 1` levels up the nest is going `k` levels up, then one more. -/
theorem up_succ : ∀ (k b t : Nat), up b (k + 1) t = up (b + k) 1 (up b k t)
  | 0, _, _ => rfl
  | k + 1, b, t => by
    show up (b + 1) (k + 1) (t + nestShift b) = _
    rw [up_succ k (b + 1) (t + nestShift b), show b + 1 + k = b + (k + 1) by omega]
    rfl

/-- The same for ports: `k + 1` levels up is `k` levels up, then one more. -/
theorem upPort_succ (b k : Nat) (p : Port) : upPort b (k + 1) p = upPort (b + k) 1 (upPort b k p) := by
  simp only [upPort]; rw [up_succ]

/-- The children of `N_{m+1}`, with the bridge's hypotheses. -/
theorem KD {m : Nat} (m_pos : 1 ≤ m) :
    Kids .Delta (kidsD m) (Lk m .Delta) (dOff m) (ori m) (ori m) :=
  kids_at m_pos .Delta (fun K => good m K m_pos)

/-- Every side of a level-`m` supertile has at least 5 edges (Lemma 6.5). -/
theorem len5 {m : Nat} (m_pos : 1 ≤ m) (c j : Nat) : 5 ≤ Lk m .Delta c j := (bounds m m_pos).1 _

/-- One level up, a port of `N_m` is still a port. -/
theorem isPort_up {m : Nat} (m_pos : 1 ≤ m) {x : Port} (x_port : (N m).IsPort x) :
    (N (m + 1)).IsPort (upPort m 1 x) := by
  rw [N_succ m_pos]
  exact ⟨tile_lt (kidsD m) (show 1 < nk .Delta by decide) x_port.1, x_port.2⟩

/-- **A strand of `N_m` is part of a strand of `N_{m+1}`.** -/
theorem lift_nest {m : Nat} (m_pos : 1 ≤ m) {x y : Port} (linked : (N m).Linked x y) (x_port : (N m).IsPort x) :
    (N (m + 1)).Linked (upPort m 1 x) (upPort m 1 y) := by
  rw [N_succ m_pos]
  exact (KD m_pos).linked_lift (c := 1) (by decide) linked x_port

/-- The rim of `N_m` has the length that its side lengths give. -/
theorem E_N {m : Nat} (m_pos : 1 ≤ m) : (N m).E = pos (Lk m .Delta 1) 6 := (good m .Delta m_pos).len

/-- The corners of `N_m`: `A = 0`, and `B` is `1` or `E - 1`. -/
theorem corners_N {m : Nat} (m_pos : 1 ≤ m) :
    aPos m .Delta = 0 ∧ (bPos m .Delta = 1 ∨ bPos m .Delta = pos (Lk m .Delta 1) 6 - 1) := by
  -- a Δ is not a Σ, so `A = 0`
  have A_zero : aPos m .Delta = 0 := by simp [aPos]
  -- the rim has at least two edges
  have rim_two : 2 ≤ pos (Lk m .Delta 1) 6 := by
    -- side 0 has at least 5 edges
    have := len5 m_pos 1 0
    -- and ends no later than the rim
    have := pos_mono (Lk m .Delta 1) (show 1 ≤ 6 by omega)
    simp only [pos] at *; omega
  refine ⟨A_zero, ?_⟩
  simp only [bPos, A_zero]
  show (if ori m = true then nxt (pos (Lk m .Delta 1) 6) 0 else prv (pos (Lk m .Delta 1) 6) 0) = 1 ∨ _
  split
  · left; simp only [nxt]; rw [if_neg (by omega)]
  · right; simp only [prv, if_true]; rfl

/-- **A hook**: at a rim vertex of `N_m` other than the corners, the two ports lie on one strand. -/
theorem hook {m : Nat} (m_pos : 1 ≤ m) {v : Nat} (two_le_v : 2 ≤ v) (v_le : v + 2 ≤ pos (Lk m .Delta 1) 6) :
    (N m).Linked ((N m).bport (ori m) (v, false)) ((N m).bport (ori m) (v, true)) := by
  -- `N_m` has the signature
  have good_m := good m .Delta m_pos
  -- with corners `0` and `1` or `E - 1`
  obtain ⟨A_zero, B_next⟩ := corners_N m_pos
  -- and its rim length
  have rim_len := E_N m_pos
  unfold N at rim_len
  -- from `L(v)` the ribbon leads to the port the signature pairs it with
  have follows := good_m.sig.sig v false (by rw [rim_len]; omega)
  -- which is `R(v)`, since `v` is not a corner
  have paired : btau (aPos m .Delta) (bPos m .Delta) (v, false) = (v, true) := by
    simp only [btau]
    rw [if_neg (by omega), if_neg (by omega)]; rfl
  rw [paired] at follows
  exact .of_follow follows

/-! ### One level up, at tile level -/

/-- The gluing's port at the parent's port `R` of the junction where piece `q` starts is `jR`. -/
theorem gR_jpos {m : Nat} (m_pos : 1 ≤ m) {q : Nat} (hq : q < 22) :
    gR .Delta (Lk m .Delta) (dOff m) (ori m) (jpos (Lk m .Delta) q) = jR (Lk m .Delta) q := by
  -- piece `q` is a side of an actual child
  obtain ⟨hc, hj⟩ := piece_ok q hq
  -- which has an edge
  have len_pos : 0 < Lk m .Delta (pieceD q).1 (pieceD q).2 := by
    -- at least 5, in fact
    have := len5 m_pos (pieceD q).1 (pieceD q).2
    omega
  -- the first edge of piece `q` (the last edge of the child's side)
  have first_edge := ownGo_jpos (Lk m .Delta) hq len_pos
  rw [Nat.add_zero] at first_edge
  simp only [gR, first_edge, Nat.sub_zero, ofLens_E hc]
  rw [nxt_last (fun i => by
    -- every side of the child has an edge
    have := len5 m_pos (pieceD q).1 i
    omega) hj]
  rfl

/-- Piece `q ≥ 1` starts at least 5 edges along the rim. -/
theorem jpos_pos {m : Nat} (m_pos : 1 ≤ m) {q : Nat} (q_pos : 1 ≤ q) (hq : q ≤ 22) : 5 ≤ jpos (Lk m .Delta) q := by
  -- `q` pieces from the start, each of at least 5 edges
  have spread := jpos_le_add (Lk m .Delta) (len5 m_pos) 0 q (by omega)
  simp only [Nat.zero_add] at spread
  omega

/-- The gluing's port at the parent's port `L` of the junction where piece `q ≥ 1` starts is `jL`. -/
theorem gL_jpos {m : Nat} (m_pos : 1 ≤ m) {q : Nat} (q_pos : 1 ≤ q) (hq : q < 22) :
    gL .Delta (Lk m .Delta) (jpos (Lk m .Delta) q) = jL (Lk m .Delta) q := by
  -- piece `q - 1` has at least 5 edges
  have prev_len := len5 m_pos (pieceD (q - 1)).1 (pieceD (q - 1)).2
  -- and piece `q` starts where it ends
  have prev_end := jpos_succ (Lk m .Delta) (show q - 1 < 22 by omega)
  rw [show q - 1 + 1 = q by omega] at prev_end
  -- the rim position just before piece `q` is the last edge of piece `q - 1`
  have before_start : prv (rimN .Delta (Lk m .Delta)) (jpos (Lk m .Delta) q) =
      jpos (Lk m .Delta) (q - 1) + (Lk m .Delta (pieceD (q - 1)).1 (pieceD (q - 1)).2 - 1) := by
    simp only [prv]; rw [if_neg (by omega)]; omega
  -- that edge, as an edge of the child (the first edge of its side)
  have last_edge := ownGo_jpos (Lk m .Delta) (show q - 1 < 22 by omega)
    (show Lk m .Delta (pieceD (q - 1)).1 (pieceD (q - 1)).2 - 1 < _ by omega)
  simp only [gL, before_start, last_edge]
  simp only [jL]
  congr 2
  omega

/-- **The junction map at tile level**: a rim port of `N_m` (outside child 1's side 2) lies, in `N_{m+1}`, on the
strand of the parent hook at junction `q`. -/
theorem step_tile {m : Nat} (m_pos : 1 ≤ m) {u : Nat} (hu : u < pos (Lk m .Delta 1) 6) {s : Bool} {q : Nat}
    (tgt_eq : tgt (ori m) (Lk m .Delta 1) u s = some q) :
    (N (m + 1)).Linked (upPort m 1 ((N m).bport (ori m) (u, s)))
      ((N (m + 1)).bport (ori (m + 1)) (jpos (Lk m .Delta) q, true)) := by
  -- the junction is one of the pieces `1 … 21`
  obtain ⟨q_pos, q_lt⟩ := tgt_lt tgt_eq
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the pieces end where the rim does
  have pieces_end := jpos_full (Lk m .Delta)
  -- so the junction is on the rim
  have junction_lt : jpos (Lk m .Delta) q < rimN .Delta (Lk m .Delta) := by
    -- the pieces from `q` to the end
    have spread := jpos_le_add (Lk m .Delta) (len5 m_pos) q (22 - q) (by omega)
    rw [show q + (22 - q) = 22 by omega] at spread; omega
  -- the rim of `N_{m+1}`
  have rim_len : (N (m + 1)).E = rimN .Delta (Lk m .Delta) := by
    rw [N_succ m_pos, compose_E kids.shape]
  -- the junction is a hook of `N_{m+1}`: its two ports lie on one strand
  have junction_hook : (N (m + 1)).Linked ((N (m + 1)).bport (ori (m + 1)) (jpos (Lk m .Delta) q, false))
      ((N (m + 1)).bport (ori (m + 1)) (jpos (Lk m .Delta) q, true)) := by
    -- the last piece has at least 5 edges
    have := len5 m_pos (pieceD 21).1 (pieceD 21).2
    -- piece 21 starts at least `5 (21 - q)` edges after piece `q`
    have to_last := jpos_le_add (Lk m .Delta) (len5 m_pos) q (21 - q) (by omega)
    rw [show q + (21 - q) = 21 by omega] at to_last
    -- and the rim ends where piece 21 does
    have last_end : jpos (Lk m .Delta) 22 = jpos (Lk m .Delta) 21 + Lk m .Delta (pieceD 21).1 (pieceD 21).2 :=
      jpos_succ (Lk m .Delta) (q := 21) (by omega)
    refine hook (by omega) (by
      -- the junction is at least 5 edges along
      have := jpos_pos m_pos q_pos (by omega)
      omega) ?_
    rw [← E_N (by omega), rim_len]; omega
  -- the junction map: the walk from `(1, u, s)` ends at a port of the junction's hook
  obtain ⟨r, walk, at_junction⟩ := step_level m m_pos (ori m) u hu s q tgt_eq
  -- at tile level: following the ribbon from the port of `N_m` leads there
  have follows := kids.follow_of_fullReach walk ⟨by rw [ofLens_n]; exact (by decide : 1 < nk .Delta),
    show u < _ by rw [ofLens_E (c := 1) (by decide)]; exact hu⟩
  rw [N_succ m_pos, ori_succ] at junction_hook ⊢
  rcases at_junction with rfl | rfl
  · rw [kids.bport_R junction_lt, gR_jpos m_pos q_lt]
    exact .of_follow follows
  · rw [kids.bport_L junction_lt, gL_jpos m_pos q_pos q_lt] at junction_hook
    exact (Patch.Linked.of_follow follows).trans junction_hook

end SpectreKnot.Statement

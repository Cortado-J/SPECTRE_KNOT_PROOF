/-
**The bound is exact** (`theoremB_exact`, the last two rows of the paper's Table 5): for `b ≥ 1`, the ports of `N_b`
lie on exactly two strands of `N_{b+2}`, and, if `b` is odd, on exactly two strands of `N_{b+3}`.

The paper's argument (the end of its proof of Thm 9.1), at tile level. Following the junction map as `ProofB.lean`
does, every strand of `N_b` reaches one of two hooks of `N_{b+2}` (and, for odd `b`, of `N_{b+3}`), and each of the two
is reached, from a hook well inside one of two chosen sides of `N_b`. Hooks at different rim vertices lie on different
strands (`hooks_apart`): along a strand its two ends on the rim stay the same (`Linked.ends`), and the ends of a hook's
strand are the hook's own two ports.
-/
import SpectreKnot.ProofB

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### A strand is determined by its ends -/

namespace Patch

variable {P : Patch}

/-- Following a ribbon has one result. -/
theorem Follow.unique {p r r' : Port} (follows : P.Follow p r) (follows' : P.Follow p r') : r = r' := by
  induction follows generalizing r' with
  | leave leaves =>
    cases follows' with
    | leave _ => rfl
    | next crosses _ => rw [leaves] at crosses; contradiction
  | next crosses _ ih =>
    cases follows' with
    | leave leaves => rw [crosses] at leaves; contradiction
    | next crosses' rest' =>
      rw [crosses] at crosses'
      cases crosses'
      exact ih rest'

/-- **The two ends of the strand through port `q`**: following the ribbon from `q` (along its piece first) leaves the
patch at `a`; going the other way (across `q`'s edge first) it leaves at `b`, which is `q` itself if `q` is on the
rim. -/
def Ends (P : Patch) (q a b : Port) : Prop :=
  P.Follow q a ∧ ((P.across q = none ∧ b = q) ∨ ∃ q', P.across q = some q' ∧ P.Follow q' b)

/-- A port has one pair of ends. -/
theorem Ends.unique {q a b a' b' : Port} (ends : P.Ends q a b) (ends' : P.Ends q a' b') : a = a' ∧ b = b' := by
  refine ⟨ends.1.unique ends'.1, ?_⟩
  rcases ends.2 with ⟨on_rim, rfl⟩ | ⟨q₁, crosses, follows⟩ <;>
    rcases ends'.2 with ⟨on_rim', rfl⟩ | ⟨q₁', crosses', follows'⟩
  · rfl
  · rw [on_rim] at crosses'; contradiction
  · rw [crosses] at on_rim'; contradiction
  · rw [crosses] at crosses'
    cases crosses'
    exact follows.unique follows'

/-- Seen from the other end of `q`'s piece, the ends are the same, the other way round. -/
theorem Ends.piece {q a b : Port} (ends : P.Ends q a b) : P.Ends (pieceEnd q) b a := by
  obtain ⟨follows, beyond⟩ := ends
  refine ⟨?_, ?_⟩
  · rcases beyond with ⟨on_rim, b_eq⟩ | ⟨q₁, crosses, follows₁⟩
    · -- `q` is on the rim: from the other end, the ribbon runs along the piece and leaves at `q`
      have leave := Follow.leave (P := P) (p := pieceEnd q) (by rw [pieceEnd_pieceEnd]; exact on_rim)
      rw [b_eq]
      rwa [pieceEnd_pieceEnd] at leave
    · -- from the other end, the ribbon runs along the piece, across `q`'s edge, and on to `b`
      exact .next (by rw [pieceEnd_pieceEnd]; exact crosses) follows₁
  · -- across the edge at the other end is where following the ribbon from `q` goes
    cases follows with
    | leave leaves => exact .inl ⟨leaves, rfl⟩
    | next crosses rest => exact .inr ⟨_, crosses, rest⟩

/-- Seen from across `q`'s edge, the ends are the same, the other way round. -/
theorem Ends.edge {q q' a b : Port} (ends : P.Ends q a b) (across_eq : P.across q = some q')
    (back : P.across q' = some q) : P.Ends q' b a := by
  obtain ⟨follows, beyond⟩ := ends
  refine ⟨?_, .inr ⟨q, back, follows⟩⟩
  rcases beyond with ⟨on_rim, _⟩ | ⟨q₁, crosses, follows₁⟩
  · rw [across_eq] at on_rim; contradiction
  · rw [across_eq] at crosses
    cases crosses
    exact follows₁

/-- **Along a strand, its ends stay the same** (in a patch with the signature and symmetric gluing, where every move
along a strand can be undone): if `q` is on the strand of `p`, the ends seen from `q` are those seen from `p`, one way
round or the other. -/
theorem Linked.ends {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) {p q a b : Port}
    (linked : P.Linked p q) (p_port : P.IsPort p) (ends : P.Ends p a b) : P.Ends q a b ∨ P.Ends q b a := by
  induction linked with
  | refl => exact .inl ends
  | piece _ ih =>
    rcases ih with same | swapped
    · exact .inr same.piece
    · exact .inl swapped.piece
  | edge to_q across_eq ih =>
    -- the edge can be crossed back
    have back := across_symm sig symm (to_q.valid sig p_port) across_eq
    rcases ih with same | swapped
    · exact .inr (same.edge across_eq back)
    · exact .inl (swapped.edge across_eq back)

/-- Nothing lies across a rim port. -/
theorem across_bport {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {k : Nat} (k_lt : k < P.E) (s : Bool) :
    P.across (P.bport o (k, s)) = none := by
  cases s with
  | true =>
    obtain ⟨_, i_lt, unglued⟩ := sig.rim_ok k k_lt
    cases o <;> simp only [bport, across, straightThrough, if_true, if_false, Bool.false_eq_true, mod14 i_lt, unglued,
      Option.map_none]
  | false =>
    obtain ⟨_, i_lt, unglued⟩ := sig.rim_ok _ (prv_lt k_lt)
    cases o <;> simp only [bport, across, straightThrough, if_true, if_false, Bool.false_eq_true, mod14 i_lt, unglued,
      Option.map_none]

/-- A rim port is a port of an actual tile. -/
theorem bport_isPort {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {k : Nat} (k_lt : k < P.E) (s : Bool) :
    P.IsPort (P.bport o (k, s)) := by
  cases s with
  | true =>
    obtain ⟨t_lt, i_lt, _⟩ := sig.rim_ok k k_lt
    cases o <;> exact ⟨t_lt, by simp only [bport]; first | exact i_lt | exact Nat.mod_lt _ (by omega)⟩
  | false =>
    obtain ⟨t_lt, i_lt, _⟩ := sig.rim_ok _ (prv_lt k_lt)
    cases o <;> exact ⟨t_lt, by simp only [bport]; first | exact i_lt | exact Nat.mod_lt _ (by omega)⟩

/-- Different rim ports are different ports. -/
theorem bport_inj {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {k k' : Nat} (k_lt : k < P.E) (k_lt' : k' < P.E)
    {s s' : Bool} (same : P.bport o (k, s) = P.bport o (k', s')) : k = k' ∧ s = s' := by
  -- the rim edges at the two positions are actual edges
  obtain ⟨_, i_lt, _⟩ := sig.rim_ok k k_lt
  -- (the second)
  obtain ⟨_, i_lt', _⟩ := sig.rim_ok k' k_lt'
  -- and so are those before them
  obtain ⟨_, j_lt, _⟩ := sig.rim_ok _ (prv_lt k_lt)
  -- (the second)
  obtain ⟨_, j_lt', _⟩ := sig.rim_ok _ (prv_lt k_lt')
  -- the same edge at two rim positions: the same position
  have at_same : ∀ x y, x < P.E → y < P.E → (P.edgeAt x).1 = (P.edgeAt y).1 → (P.edgeAt x).2 = (P.edgeAt y).2 →
      x = y := fun x y x_lt y_lt same_tile same_edge => sig.rim_inj x y x_lt y_lt (Prod.ext same_tile same_edge)
  cases o <;> cases s <;> cases s' <;>
    simp only [bport, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq, reduceCtorEq, and_false,
      and_true] at same ⊢
  · exact prv_inj k_lt k_lt' (at_same _ _ (prv_lt k_lt) (prv_lt k_lt') same.1 (by omega))
  · exact at_same _ _ k_lt k_lt' same.1 (by omega)
  · exact prv_inj k_lt k_lt' (at_same _ _ (prv_lt k_lt) (prv_lt k_lt') same.1 (by omega))
  · exact at_same _ _ k_lt k_lt' same.1 same.2

end Patch

/-! ### Hooks at different vertices lie on different strands -/

/-- The port `R` at rim vertex `v` of `N_m`, a port of the hook there. -/
abbrev hookAt (m v : Nat) : Port := (N m).bport (ori m) (v, true)

/-- At a rim vertex of `N_m` other than the corners, the strand of the hook ends at the vertex's two ports. -/
theorem hook_ends {m : Nat} (m_pos : 1 ≤ m) {v : Nat} (two_le_v : 2 ≤ v) (v_le : v + 2 ≤ pos (Lk m .Delta 1) 6) :
    (N m).Ends (hookAt m v) ((N m).bport (ori m) (v, false)) (hookAt m v) := by
  -- `N_m` has the signature
  have good_m := good m .Delta m_pos
  -- with corners `0` and `1` or `E - 1`
  obtain ⟨A_zero, B_next⟩ := corners_N m_pos
  -- and its rim length
  have rim_len := E_N m_pos
  unfold N at rim_len
  -- from `R(v)` the ribbon leads to the port the signature pairs it with
  have follows := good_m.sig.sig v true (by rw [rim_len]; omega)
  -- which is `L(v)`, since `v` is not a corner
  have paired : btau (aPos m .Delta) (bPos m .Delta) (v, true) = (v, false) := by
    simp only [btau]
    rw [if_neg (by omega), if_neg (by omega)]; rfl
  rw [paired] at follows
  exact ⟨follows, .inl ⟨Patch.across_bport good_m.sig (by rw [rim_len]; omega) true, rfl⟩⟩

/-- **Hooks at different rim vertices of `N_m` (other than the corners) lie on different strands.** -/
theorem hooks_apart {m : Nat} (m_pos : 1 ≤ m) {v w : Nat} (two_le_v : 2 ≤ v) (v_le : v + 2 ≤ pos (Lk m .Delta 1) 6)
    (two_le_w : 2 ≤ w) (w_le : w + 2 ≤ pos (Lk m .Delta 1) 6) (v_ne_w : v ≠ w) :
    ¬ (N m).Linked (hookAt m v) (hookAt m w) := by
  intro linked
  -- `N_m` has the signature
  have good_m := good m .Delta m_pos
  -- and its rim length
  have rim_len := E_N m_pos
  unfold N at rim_len
  -- seen from `R(w)`, the ends are those of the hook at `v`, one way round or the other
  have ends_v := linked.ends good_m.sig (super_glueSymm m .Delta)
    (Patch.bport_isPort good_m.sig (by rw [rim_len]; omega) true) (hook_ends m_pos two_le_v v_le)
  -- but they are those of the hook at `w`
  have ends_w := hook_ends m_pos two_le_w w_le
  rcases ends_v with same | swapped
  · -- the same way round: `R(v) = R(w)`
    have equal := (same.unique ends_w).2
    exact v_ne_w (Patch.bport_inj good_m.sig (by rw [rim_len]; omega) (by rw [rim_len]; omega) equal).1
  · -- the other way round: `R(v) = L(w)`
    have equal := (swapped.unique ends_w).1
    exact absurd (Patch.bport_inj good_m.sig (by rw [rim_len]; omega) (by rw [rim_len]; omega) equal).2
      (by decide)

/-- **Two strands, from two hooks**: if every port of `N_b` lies, in `N_{b+k}`, on the strand of the hook at `vA` or
of the hook at `vB` (two different rim vertices, not corners), and some port of `N_b` lies on each, then the ports of
`N_b` lie on exactly two strands of `N_{b+k}`. -/
theorem twoStrands_of {b k vA vB : Nat} (b_pos : 1 ≤ b) (two_le_vA : 2 ≤ vA)
    (vA_le : vA + 2 ≤ pos (Lk (b + k) .Delta 1) 6) (two_le_vB : 2 ≤ vB) (vB_le : vB + 2 ≤ pos (Lk (b + k) .Delta 1) 6)
    (vA_ne_vB : vA ≠ vB) {pA pB : Port} (pA_port : (N b).IsPort pA) (pB_port : (N b).IsPort pB)
    (to_A : (N (b + k)).Linked (upPort b k pA) (hookAt (b + k) vA))
    (to_B : (N (b + k)).Linked (upPort b k pB) (hookAt (b + k) vB))
    (to_either : ∀ x, (N b).IsPort x →
      (N (b + k)).Linked (upPort b k x) (hookAt (b + k) vA) ∨ (N (b + k)).Linked (upPort b k x) (hookAt (b + k) vB)) :
    TwoStrands b k := by
  -- the level `b + k` is at least 1
  have level_pos : 1 ≤ b + k := by omega
  -- back from the hook at `vA` to `pA`
  have from_A := linked_symm (m := b + k) level_pos to_A (isPort_upk b_pos pA_port k)
  -- and from the hook at `vB` to `pB`
  have from_B := linked_symm (m := b + k) level_pos to_B (isPort_upk b_pos pB_port k)
  refine ⟨pA, pB, pA_port, pB_port, fun linked => ?_, fun x x_port => ?_⟩
  · -- `pA` and `pB` on one strand would put the two hooks on one strand
    exact hooks_apart level_pos two_le_vA vA_le two_le_vB vB_le vA_ne_vB (from_A.trans (linked.trans to_B))
  · rcases to_either x x_port with to_vA | to_vB
    · exact .inl (to_vA.trans from_A)
    · exact .inr (to_vB.trans from_B)

/-! ### Hooks well inside a side -/

/-- A rim vertex well inside side `J` of `N_n`: two edges after the side's start. -/
theorem inside_two {n J : Nat} (n_pos : 1 ≤ n) : Inside n J (pos (Lk n .Delta 1) J + 2) := by
  -- side `J` has at least 5 edges
  have side_len := len5 n_pos 1 J
  -- and ends where side `J + 1` starts
  have side_end := pos_succ (Lk n .Delta 1) J
  exact ⟨Nat.le_refl _, by omega⟩

/-- The hook port at a vertex inside a side of `N_n` is a port of `N_n`. -/
theorem hook_port {n J v : Nat} (n_pos : 1 ≤ n) (hJ : J < 6) (inside : Inside n J v) : (N n).IsPort (hookAt n v) := by
  -- `v` is a rim vertex away from the corners
  have bounds := inside_bounds hJ inside
  -- of a rim of this length
  have rim_len := E_N n_pos
  unfold N at rim_len
  exact Patch.bport_isPort (good n .Delta n_pos).sig (by rw [rim_len]; omega) true

/-- The hook at a vertex `u` strictly inside child 1's side 2 lies at a different vertex of `N_{n+1}` from junction
16 (where that side ends), and both lie well inside side 4 of `N_{n+1}`. -/
theorem stp_apart {n u : Nat} (n_pos : 1 ≤ n) (after_two : pos (Lk n .Delta 1) 2 + 2 ≤ u)
    (before_three : u + 2 ≤ pos (Lk n .Delta 1) 3) :
    (2 ≤ jpos (Lk n .Delta) 16 ∧ jpos (Lk n .Delta) 16 + 2 ≤ pos (Lk (n + 1) .Delta 1) 6) ∧
    (2 ≤ stp (Lk n .Delta) u ∧ stp (Lk n .Delta) u + 2 ≤ pos (Lk (n + 1) .Delta 1) 6) ∧
    jpos (Lk n .Delta) 16 ≠ stp (Lk n .Delta) u := by
  refine ⟨inside_bounds (by omega) (inside_16 n_pos),
    inside_bounds (by omega) (inside_stp n_pos (by omega) (by omega)), ?_⟩
  simp only [stp]; omega

/-! ### Even `b` -/

/-- **Even `b`, two levels up**: every port of `N_b` lies, in `N_{b+2}`, on the strand of the hook at junction 16, or
on that of the hook at junction 9 of `N_{b+1}`, which lies on the rim of `N_{b+2}`. -/
theorem even_two {b : Nat} (b_pos : 1 ≤ b) (even : b % 2 = 0) {x : Port} (x_port : (N b).IsPort x) :
    (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 16)) ∨
    (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (stp (Lk (b + 1) .Delta) (jpos (Lk b .Delta) 9))) := by
  -- level `b` is even
  have ori_b := ori_even even
  -- level `b + 1` odd
  have ori_b1 : ori (b + 1) = false := ori_odd (by omega)
  -- one level up: inside side 2 (at junction 9), 3 or 4
  obtain ⟨J, reach_J, sides_even, _, at_nine⟩ := first b_pos x_port
  rw [show upPort b 2 x = upPort (b + 1) 1 (upPort b 1 x) from upPort_succ b 1 x]
  rcases sides_even ori_b with rfl | rfl | rfl
  · -- inside side 2, at junction 9: a hook of `N_{b+1}` on the rim of `N_{b+2}`
    exact .inr ((lift_nest (m := b + 1) (by omega) (at_nine rfl) reach_J.1).trans (adv_none (by omega) (inside_9 b_pos)))
  · -- inside side 3: on to junction 16
    exact .inl (reach_some (q := 16) (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
  · -- inside side 4: on to junction 16
    exact .inl (reach_some (q := 16) (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))

/-- **Even `b`**: the ports of `N_b` lie on exactly two strands of `N_{b+2}`. -/
theorem two_even {b : Nat} (b_pos : 1 ≤ b) (even : b % 2 = 0) : TwoStrands b 2 := by
  -- level `b` is even
  have ori_b := ori_even even
  -- level `b + 1` odd
  have ori_b1 : ori (b + 1) = false := ori_odd (by omega)
  -- junction 9 of `N_{b+1}` lies well inside its side 2
  have nine_start : pos (Lk (b + 1) .Delta 1) 2 + 2 ≤ jpos (Lk b .Delta) 9 := (inside_9 b_pos).1
  -- (its end)
  have nine_end : jpos (Lk b .Delta) 9 + 2 ≤ pos (Lk (b + 1) .Delta 1) 3 := (inside_9 b_pos).2
  -- the two hooks of `N_{b+2}`: different, and away from the corners
  obtain ⟨⟨two_le_A, A_le⟩, ⟨two_le_B, B_le⟩, A_ne_B⟩ := stp_apart (n := b + 1) (by omega) nine_start nine_end
  -- a hook well inside side 4 of `N_b`
  have inside_A := inside_two (n := b) (J := 4) b_pos
  -- and one well inside side 5
  have inside_B := inside_two (n := b) (J := 5) b_pos
  -- one level up, the first reaches junction 12, inside side 3 of `N_{b+1}`
  have A_one := adv_some (q := 12) b_pos (by omega) inside_A (by rw [ori_b]; rfl)
  -- and the second junction 9, inside side 2
  have B_one := adv_some (q := 9) b_pos (by omega) inside_B (by rw [ori_b]; rfl)
  refine twoStrands_of b_pos two_le_A A_le two_le_B B_le A_ne_B (hook_port b_pos (by omega) inside_A)
    (hook_port b_pos (by omega) inside_B) ?_ ?_ (fun x x_port => even_two b_pos even x_port)
  · -- two levels up, the first reaches junction 16
    rw [show upPort b 2 (hookAt b _) = upPort (b + 1) 1 (upPort b 1 (hookAt b _)) from upPort_succ b 1 _]
    exact reach_some (q := 16) (by omega) (by omega)
      ⟨isPort_up b_pos (hook_port b_pos (by omega) inside_A), _, inside_12 b_pos, A_one⟩ (by rw [ori_b1]; rfl)
  · -- and the second the hook at junction 9 of `N_{b+1}`
    rw [show upPort b 2 (hookAt b _) = upPort (b + 1) 1 (upPort b 1 (hookAt b _)) from upPort_succ b 1 _]
    exact (lift_nest (m := b + 1) (by omega) B_one (isPort_up b_pos (hook_port b_pos (by omega) inside_B))).trans
      (adv_none (by omega) (inside_9 b_pos))

/-! ### Odd `b` -/

/-- **Odd `b`, two levels up**: every port of `N_b` lies, in `N_{b+2}`, on the strand of the hook at junction 12 or
of the hook at junction 9. -/
theorem odd_two {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) {x : Port} (x_port : (N b).IsPort x) :
    (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 12)) ∨
    (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 9)) := by
  -- level `b` is odd
  have ori_b := ori_odd odd
  -- level `b + 1` even
  have ori_b1 : ori (b + 1) = true := ori_even (by omega)
  -- one level up: inside side 4 or 5
  obtain ⟨J, reach_J, _, sides_odd, _⟩ := first b_pos x_port
  rw [show upPort b 2 x = upPort (b + 1) 1 (upPort b 1 x) from upPort_succ b 1 x]
  rcases sides_odd ori_b with rfl | rfl
  · -- inside side 4: on to junction 12
    exact .inl (reach_some (q := 12) (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))
  · -- inside side 5: on to junction 9
    exact .inr (reach_some (q := 9) (by omega) (by omega) reach_J (by rw [ori_b1]; rfl))

/-- Odd `b`, from two levels up to three: the strand of the hook at junction 12 of `N_{b+2}` runs on to the hook at
junction 16 of `N_{b+3}`. -/
theorem odd_up_12 {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) {x : Port} (x_port : (N b).IsPort x)
    (linked : (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 12))) :
    (N (b + 3)).Linked (upPort b 3 x) (hookAt (b + 3) (jpos (Lk (b + 2) .Delta) 16)) := by
  -- level `b + 2` is odd
  have ori_b2 : ori (b + 2) = false := ori_odd (by omega)
  rw [show upPort b 3 x = upPort (b + 2) 1 (upPort b 2 x) from upPort_succ b 2 x]
  exact reach_some (q := 16) (by omega) (by omega)
    ⟨isPort_upk b_pos x_port 2, _, inside_12 (n := b + 1) (by omega), linked⟩ (by rw [ori_b2]; rfl)

/-- Odd `b`, from two levels up to three: the hook at junction 9 of `N_{b+2}` lies on the rim of `N_{b+3}`, and its
strand is a hook there. -/
theorem odd_up_9 {b : Nat} (b_pos : 1 ≤ b) {x : Port} (x_port : (N b).IsPort x)
    (linked : (N (b + 2)).Linked (upPort b 2 x) (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 9))) :
    (N (b + 3)).Linked (upPort b 3 x) (hookAt (b + 3) (stp (Lk (b + 2) .Delta) (jpos (Lk (b + 1) .Delta) 9))) := by
  rw [show upPort b 3 x = upPort (b + 2) 1 (upPort b 2 x) from upPort_succ b 2 x]
  exact (lift_nest (m := b + 2) (by omega) linked (isPort_upk b_pos x_port 2)).trans
    (adv_none (by omega) (inside_9 (n := b + 1) (by omega)))

/-- The two witnesses for odd `b`: a hook well inside side 4 of `N_b` reaches junction 12 of `N_{b+2}`, and one well
inside side 0 reaches junction 9. -/
theorem odd_witnesses {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) :
    (N (b + 2)).Linked (upPort b 2 (hookAt b (pos (Lk b .Delta 1) 4 + 2)))
      (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 12)) ∧
    (N (b + 2)).Linked (upPort b 2 (hookAt b (pos (Lk b .Delta 1) 0 + 2)))
      (hookAt (b + 2) (jpos (Lk (b + 1) .Delta) 9)) := by
  -- level `b` is odd
  have ori_b := ori_odd odd
  -- level `b + 1` even
  have ori_b1 : ori (b + 1) = true := ori_even (by omega)
  -- a hook well inside side 4 of `N_b`
  have inside_A := inside_two (n := b) (J := 4) b_pos
  -- and one well inside side 0
  have inside_B := inside_two (n := b) (J := 0) b_pos
  -- one level up, the first reaches junction 16, inside side 4 of `N_{b+1}`
  have A_one := adv_some (q := 16) b_pos (by omega) inside_A (by rw [ori_b]; rfl)
  -- and the second junction 21, inside side 5
  have B_one := adv_some (q := 21) b_pos (by omega) inside_B (by rw [ori_b]; rfl)
  rw [show upPort b 2 (hookAt b (pos (Lk b .Delta 1) 4 + 2)) =
      upPort (b + 1) 1 (upPort b 1 (hookAt b (pos (Lk b .Delta 1) 4 + 2))) from upPort_succ b 1 _,
    show upPort b 2 (hookAt b (pos (Lk b .Delta 1) 0 + 2)) =
      upPort (b + 1) 1 (upPort b 1 (hookAt b (pos (Lk b .Delta 1) 0 + 2))) from upPort_succ b 1 _]
  exact ⟨reach_some (q := 12) (by omega) (by omega)
      ⟨isPort_up b_pos (hook_port b_pos (by omega) inside_A), _, inside_16 b_pos, A_one⟩ (by rw [ori_b1]; rfl),
    reach_some (q := 9) (by omega) (by omega)
      ⟨isPort_up b_pos (hook_port b_pos (by omega) inside_B), _, inside_21 b_pos, B_one⟩ (by rw [ori_b1]; rfl)⟩

/-- **Odd `b`**: the ports of `N_b` lie on exactly two strands of `N_{b+2}`. -/
theorem two_odd {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) : TwoStrands b 2 := by
  -- junction 9 lies well inside side 2 of `N_{b+2}`
  have nine_end : jpos (Lk (b + 1) .Delta) 9 + 2 ≤ pos (Lk (b + 2) .Delta 1) 3 := (inside_9 (n := b + 1) (by omega)).2
  -- and junction 12 well inside side 3
  have twelve_start : pos (Lk (b + 2) .Delta 1) 3 + 2 ≤ jpos (Lk (b + 1) .Delta) 12 :=
    (inside_12 (n := b + 1) (by omega)).1
  -- both away from the corners
  obtain ⟨two_le_A, A_le⟩ := inside_bounds (by omega) (inside_12 (n := b + 1) (by omega))
  -- (the second)
  obtain ⟨two_le_B, B_le⟩ := inside_bounds (by omega) (inside_9 (n := b + 1) (by omega))
  -- the two witnesses
  obtain ⟨to_A, to_B⟩ := odd_witnesses b_pos odd
  exact twoStrands_of b_pos two_le_A A_le two_le_B B_le (by omega)
    (hook_port b_pos (by omega) (inside_two (n := b) (J := 4) b_pos))
    (hook_port b_pos (by omega) (inside_two (n := b) (J := 0) b_pos)) to_A to_B
    (fun x x_port => odd_two b_pos odd x_port)

/-- **Odd `b`**: the ports of `N_b` lie on exactly two strands of `N_{b+3}`. -/
theorem three_odd {b : Nat} (b_pos : 1 ≤ b) (odd : b % 2 = 1) : TwoStrands b 3 := by
  -- junction 9 of `N_{b+2}` lies well inside its side 2
  have nine_start : pos (Lk (b + 2) .Delta 1) 2 + 2 ≤ jpos (Lk (b + 1) .Delta) 9 :=
    (inside_9 (n := b + 1) (by omega)).1
  -- (its end)
  have nine_end : jpos (Lk (b + 1) .Delta) 9 + 2 ≤ pos (Lk (b + 2) .Delta 1) 3 := (inside_9 (n := b + 1) (by omega)).2
  -- the two hooks of `N_{b+3}`: different, and away from the corners
  obtain ⟨⟨two_le_A, A_le⟩, ⟨two_le_B, B_le⟩, A_ne_B⟩ := stp_apart (n := b + 2) (by omega) nine_start nine_end
  -- the two witnesses, two levels up
  obtain ⟨to_A, to_B⟩ := odd_witnesses b_pos odd
  -- the first witness is a port of `N_b`
  have pA_port := hook_port b_pos (by omega) (inside_two (n := b) (J := 4) b_pos)
  -- and so is the second
  have pB_port := hook_port b_pos (by omega) (inside_two (n := b) (J := 0) b_pos)
  refine twoStrands_of b_pos two_le_A A_le two_le_B B_le A_ne_B pA_port pB_port
    (odd_up_12 b_pos odd pA_port to_A) (odd_up_9 b_pos pB_port to_B) (fun x x_port => ?_)
  rcases odd_two b_pos odd x_port with to_12 | to_9
  · exact .inl (odd_up_12 b_pos odd x_port to_12)
  · exact .inr (odd_up_9 b_pos x_port to_9)

/-! ### The theorem -/

/-- **The bound is exact** (as stated in `Statement.lean`). -/
theorem theoremB_exact : TheoremB_exact := by
  intro b b_pos
  rcases Nat.mod_two_eq_zero_or_one b with even | odd
  · exact ⟨two_even b_pos even, fun odd => absurd odd (by omega)⟩
  · exact ⟨two_odd b_pos odd, fun _ => three_odd b_pos odd⟩

end SpectreKnot.Statement

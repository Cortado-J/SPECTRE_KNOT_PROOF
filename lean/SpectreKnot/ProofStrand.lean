/-
**Theorem B, final form** (`theoremB_strand`): the ribbons of the nest tiling form one two-way infinite strand.

The nest tiling is built as one tiling (`Statement.lean` §6): its tiles are numbered so that every block `N_b` keeps
its own numbering, and its gluing is read off the blocks (`nestModel`). Its ports, with the two pairings "other end of
the piece" and "straight across the edge", form a `StrandSystem` (`nestSys`). In it no strand is closed, because a
closed strand would stay inside one block, which has no closed strand (Theorem A); and any two ports lie on one strand,
because they do in a large enough block (Theorem B (3)). Lemma 3.4 (`StrandSystem.closed_or_path`) then says the
strand is a two-way infinite path, and it runs through every port.
-/
import SpectreKnot.ProofB
import SpectreKnot.Strands

/-! ### The strand of a port, port by port (for any strand system) -/

namespace SpectreKnot.StrandSystem

variable {P : Type} (S : StrandSystem P)

/-- `S.Same p q`: port `q` is reached from port `p` by moving along pieces and across edges, any number of times:
`q` is on the strand of `p`. -/
inductive Same (p : P) : P → Prop
  | refl : Same p p
  | inside {q : P} : Same p q → Same p (S.inside q)
  | across {q : P} : Same p q → Same p (S.across q)

/-- **A strand, port by port**: every port on the strand of `p` is reached by following it forwards or backwards
from `p`, or is the other end of the piece of a port so reached. -/
theorem same_orbit {p q : P} (same : S.Same p q) : ∃ k, q = S.walk p k ∨ q = iter S.prev k p ∨
    q = S.inside (S.walk p k) ∨ q = S.inside (iter S.prev k p) := by
  induction same with
  | refl => exact ⟨0, Or.inl rfl⟩
  | @inside q _ ih =>
    -- the other end of the piece swaps the first two forms with the last two
    obtain ⟨k, reached | reached | reached | reached⟩ := ih <;> subst reached
    · exact ⟨k, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨k, Or.inr (Or.inr (Or.inr rfl))⟩
    · exact ⟨k, Or.inl (S.inside_inside _)⟩
    · exact ⟨k, Or.inr (Or.inl (S.inside_inside _))⟩
  | @across q _ ih =>
    obtain ⟨k, reached | reached | reached | reached⟩ := ih <;> subst reached
    · cases k with
      | zero =>
        -- across the start: the other end of the piece of the port one step back
        refine ⟨1, Or.inr (Or.inr (Or.inr ?_))⟩
        show S.across p = S.inside (S.inside (S.across p))
        rw [S.inside_inside]
      | succ k =>
        -- across a port reached forwards: the other end of the piece of the port before it
        exact ⟨k, Or.inr (Or.inr (Or.inl (by rw [walk_succ, next, S.across_across])))⟩
    · -- across a port reached backwards: the other end of the piece of the next port back
      exact ⟨k + 1, Or.inr (Or.inr (Or.inr (by rw [iter_succ, prev, S.inside_inside])))⟩
    · -- across the other end of the piece of a port reached forwards: one step further forwards
      exact ⟨k + 1, Or.inl rfl⟩
    · cases k with
      | zero =>
        -- across the other end of the start's piece: one step forwards
        exact ⟨1, Or.inl rfl⟩
      | succ k =>
        -- across the other end of the piece of a port reached backwards: one step less back
        refine ⟨k, Or.inr (Or.inl ?_)⟩
        show S.next (iter S.prev (k + 1) p) = _
        rw [iter_succ, next_prev]

end SpectreKnot.StrandSystem

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### How the blocks grow -/

/-- Child 0 of `N_{b+1}`, which comes before `N_b`, has at least one tile. -/
theorem nestShift_pos (b : Nat) : 1 ≤ nestShift b := by
  rcases Nat.eq_zero_or_pos b with rfl | b_pos
  · -- level 0: child 0 is a single tile
    decide
  · -- level b ≥ 1: a supertile with the signature has a tile
    exact (good b .Xi b_pos).sig.tiles_pos

/-- `N_{b+1}` holds child 0 (`nestShift b` tiles) and then `N_b`, so it has at least that many tiles. -/
theorem tiles_succ (b : Nat) : (N b).tiles + nestShift b ≤ (N (b + 1)).tiles := by
  rcases Nat.eq_zero_or_pos b with rfl | b_pos
  · -- N_0 is one tile and N_1 has nine
    decide
  · rw [N_succ b_pos]
    -- the first two children together: child 0, then child 1 = N_b
    have first_two : offC (kidsD b) 2 = nestShift b + (N b).tiles := by
      rw [offC_succ, offC_succ, show offC (kidsD b) 0 = 0 from rfl, Nat.zero_add]; rfl
    -- the parent has at least the tiles of its first two children
    have two_le_all := offC_mono (kidsD b) (show 2 ≤ nk .Delta by decide)
    show _ ≤ offC (kidsD b) (nk .Delta)
    omega

/-- `N_b` has more than `b` tiles. -/
theorem tiles_ge : ∀ b, b + 1 ≤ (N b).tiles
  | 0 => by decide
  | b + 1 => by
    -- one more tile at least, at each level: `N_{b+1}` holds `N_b` and child 0
    have grow := tiles_succ b
    -- which has a tile
    have shift_pos := nestShift_pos b
    -- and `N_b` has more than `b` tiles
    have before := tiles_ge b
    omega

/-! ### The numbering of the nest tiling's tiles -/

/-- `gid b` sends the tiles of `N_b` into 0 … |N_b| - 1, and `loc b` undoes it. -/
theorem loc_gid : ∀ b t, t < (N b).tiles → gid b t < (N b).tiles ∧ loc b (gid b t) = t
  | 0, _, ht => ⟨ht, rfl⟩
  | b + 1, t, ht => by
    -- `N_{b+1}` holds `N_b` and child 0
    have grow := tiles_succ b
    by_cases in_child1 : nestShift b ≤ t ∧ t < nestShift b + (N b).tiles
    · -- a tile of child 1 (that is, of N_b): numbered as in N_b
      obtain ⟨bound, inverse⟩ := loc_gid b (t - nestShift b) (by omega)
      simp only [gid, loc, ite_eq_left in_child1, ite_eq_left bound, inverse]
      exact ⟨by omega, by omega⟩
    · by_cases in_child0 : t < nestShift b
      · -- a tile of child 0: numbered just after N_b
        simp only [gid, loc, ite_eq_right in_child1, ite_eq_left in_child0]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact ⟨by omega, by omega⟩
      · -- a tile of a later child: keeps its number
        simp only [gid, loc, ite_eq_right in_child1, ite_eq_right in_child0]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨ht, rfl⟩

/-- `loc b` sends 0 … |N_b| - 1 to tiles of `N_b`, and `gid b` undoes it. -/
theorem gid_loc : ∀ b g, g < (N b).tiles → loc b g < (N b).tiles ∧ gid b (loc b g) = g
  | 0, _, hg => ⟨hg, rfl⟩
  | b + 1, g, hg => by
    -- `N_{b+1}` holds `N_b` and child 0
    have grow := tiles_succ b
    by_cases old : g < (N b).tiles
    · -- a number of N_b: its tile in child 1
      obtain ⟨bound, inverse⟩ := gid_loc b g old
      simp only [loc, ite_eq_left old, gid]
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel, inverse]
      exact ⟨by omega, rfl⟩
    · by_cases from_child0 : g < (N b).tiles + nestShift b
      · -- a number just after N_b: a tile of child 0
        simp only [loc, ite_eq_right old, ite_eq_left from_child0, gid]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact ⟨by omega, by omega⟩
      · -- a later number: a tile of a later child, same number
        simp only [loc, ite_eq_right old, ite_eq_right from_child0, gid]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨hg, rfl⟩

/-- `gid b` is one to one on the tiles of `N_b`. -/
theorem gid_inj {b t t' : Nat} (ht : t < (N b).tiles) (ht' : t' < (N b).tiles) (same : gid b t = gid b t') :
    t = t' := by
  -- apply `loc b` to both sides: it takes `gid b t` back to `t`
  have back := (loc_gid b t ht).2
  -- and `gid b t'` back to `t'`
  have back' := (loc_gid b t' ht').2
  rw [← back, ← back', same]

/-- One level up, a tile of `N_b` is still a tile, and keeps its number. -/
theorem gid_up1 {b t : Nat} (ht : t < (N b).tiles) :
    up b 1 t < (N (b + 1)).tiles ∧ gid (b + 1) (up b 1 t) = gid b t := by
  -- `N_{b+1}` holds child 0 and then `N_b`
  have grow := tiles_succ b
  -- `up b 1 t` is `t` moved past child 0
  show t + nestShift b < _ ∧ gid (b + 1) (t + nestShift b) = gid b t
  refine ⟨by omega, ?_⟩
  simp only [gid]
  rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]

/-- Any number of levels up, a tile of `N_b` is still a tile, and keeps its number. -/
theorem gid_up {b t : Nat} (ht : t < (N b).tiles) :
    ∀ k, up b k t < (N (b + k)).tiles ∧ gid (b + k) (up b k t) = gid b t
  | 0 => ⟨ht, rfl⟩
  | k + 1 => by
    -- one more level on top of `k` levels
    obtain ⟨bound, same⟩ := gid_up ht k
    obtain ⟨bound', same'⟩ := gid_up1 bound
    rw [up_succ]
    exact ⟨bound', same'.trans same⟩

/-! ### Gluing goes up the nest -/

/-- An edge glued in `N_b` is glued the same way, renumbered, in `N_{b+1}`. -/
theorem glue_lift1 {b t i t' j : Nat} (ht : t < (N b).tiles) (glued : (N b).glue t i = some (t', j)) :
    (N (b + 1)).glue (up b 1 t) i = some (up b 1 t', j) := by
  rcases Nat.eq_zero_or_pos b with rfl | b_pos
  · -- `N_0` is a single tile: nothing is glued
    exact absurd glued (by simp [N, super, tile])
  · rw [N_succ b_pos]
    -- the children of `N_{b+1}`
    have kids := KD b_pos
    -- the same gluing, seen in child 1
    have glued_child : (kidsD b 1).glue t i = some (t', j) := glued
    show (Par b).glue (t + offC (kidsD b) 1) i = some (t' + offC (kidsD b) 1, j)
    rw [kids.glue_shift (c := 1) (by decide) ht]
    unfold glueAt
    rw [glued_child]

/-- An edge glued in `N_b` is glued the same way any number of levels up. -/
theorem glue_lift {b t i t' j : Nat} (ht : t < (N b).tiles) (glued : (N b).glue t i = some (t', j)) :
    ∀ k, (N (b + k)).glue (up b k t) i = some (up b k t', j)
  | 0 => glued
  | k + 1 => by
    rw [up_succ k b t, up_succ k b t']
    exact glue_lift1 (gid_up ht k).1 (glue_lift ht glued k)

/-! ### No tile is glued to itself -/

/-- No edge of a tile is glued to an edge of the same tile. -/
def NoSelf (P : Patch) : Prop := ∀ t i t' j, t < P.tiles → i < 14 → P.glue t i = some (t', j) → t' ≠ t

/-- The kernel's check of the level-1 data. -/
def level1NoSelf (K : Kind) : Bool :=
  (List.range (level1 K).tiles).all fun t => (List.range 14).all fun i =>
    match (level1 K).glue t i with
    | none => true
    | some (t', _) => t' != t

/-- The check passes for all nine kinds. -/
theorem level1NoSelf_all : ∀ K, level1NoSelf K = true := by intro K; cases K <;> decide +kernel

/-- No level-1 supertile glues a tile to itself. -/
theorem level1_noSelf (K : Kind) : NoSelf (level1 K) := by
  intro t i t' j ht hi glued
  -- the kernel's check
  have check := level1NoSelf_all K
  simp only [level1NoSelf, List.all_eq_true, List.mem_range] at check
  -- at tile `t` and edge `i`
  have at_edge := check t ht i hi
  rw [glued] at at_edge
  simpa using at_edge

/-- A sibling glued to side `j` of child `c` is a different child. -/
theorem mate_other_child {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} (len_pos : ∀ c j, 1 ≤ L c j)
    {c k c' k' : Nat} (hc : c < nk T) (hk : k < pos (L c) 6)
    (mated : (Comp.ofLens T L d ω).toGluing.mate c k = some (c', k')) : c' ≠ c := by
  -- the side `j` and offset `o` of the edge `k`
  obtain ⟨j, o, hj, ho, rfl⟩ := decomp (L c) 6 (Nat.le_refl _) k hk
  -- the gluing formula: across side `j` lies whatever Table 2 says
  have formula := ofLens_mate (d := d) (ω := ω) (fun c _ j _ => len_pos c j) hc hj ho
  change (Comp.ofLens T L d ω).mate c (pos (L c) j + o) = some (c', k') at mated
  rw [formula] at mated
  cases table : adjAt T c j with
  | none => rw [table] at mated; contradiction
  | some sib =>
    obtain ⟨sib_child, sib_side⟩ := sib
    rw [table] at mated
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at mated
    obtain ⟨rfl, _⟩ := mated
    -- Table 2 never glues a child to itself
    exact (adj_valid hc hj table).2.2.1

/-- If no child glues a tile to itself, neither does the parent. -/
theorem Kids.noSelf {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool}
    (kids : Kids T child L d ω o) (children : ∀ c, c < nk T → NoSelf (child c)) : NoSelf (compose T child) := by
  -- the composition is well formed
  have wf := kids.csig.wf
  intro t i t' j ht hi glued
  -- the child `c` that tile `t` belongs to, and its number `t₀` there
  obtain ⟨c, hc, lo, hi_c⟩ := owner_exists child (nk T) t ht
  obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + offC child c := ⟨t - offC child c, by omega⟩
  -- `t₀` is a tile of child `c`
  have ht₀ : t₀ < (child c).tiles := by omega
  -- which has the signature
  have sig := kids.sig c hc
  cases inside : (child c).glue t₀ i with
  | some e =>
    -- glued inside the child: the child's own tile, shifted
    obtain ⟨t₂, j₂⟩ := e
    rw [kids.glue_shift hc ht₀] at glued
    simp only [glueAt, inside, Option.some.injEq, Prod.mk.injEq] at glued
    obtain ⟨rfl, rfl⟩ := glued
    -- the child glues it to a different tile
    have differ := children c hc t₀ i t₂ j₂ ht₀ hi inside
    omega
  | none =>
    -- on the child's rim, at rim edge `k`: glued to a sibling's edge
    obtain ⟨k, hk, at_k⟩ := sig.rim_all t₀ i ht₀ hi inside
    -- the parent glues rim edge `k` as the gluing's `mate` says
    have formula := kids.glue_rimEdge hc hk
    rw [at_k] at formula
    rw [formula] at glued
    cases mated : (Comp.ofLens T L d ω).toGluing.mate c k with
    | none => rw [mated] at glued; contradiction
    | some m =>
      obtain ⟨c', k'⟩ := m
      rw [mated] at glued
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at glued
      obtain ⟨rfl, rfl⟩ := glued
      -- `c` is a child of the gluing
      have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact hc
      -- the sibling is an actual child, and the edge a real rim edge of it
      obtain ⟨sib_lt_n, sib_edge_lt, _⟩ := wf.mate_valid c k c' k' c_lt_n (by rw [kids.E_eq hc]; exact hk) mated
      -- the sibling is a child of the composition
      have sib_lt : c' < nk T := by rwa [ofLens_n] at sib_lt_n
      -- its rim edge `k'` is an edge of an actual tile of it
      have on_rim := (kids.sig c' sib_lt).rim_ok k' (by rw [← kids.E_eq sib_lt]; exact sib_edge_lt)
      -- it is a different child
      have other := mate_other_child (d := d) (ω := ω) kids.len_pos hc
        (by rw [← ofLens_E (d := d) (ω := ω) hc, kids.E_eq hc]; exact hk) mated
      intro same
      -- two tiles of different children have different numbers in the parent
      have same_child := owner_unique child on_rim.1 ht₀ (by omega)
      exact other same_child.1

/-- No supertile glues a tile to itself. -/
theorem super_noSelf : ∀ m K, NoSelf (super m K)
  | 0, _ => fun _ _ _ _ _ _ glued => by simp [super, tile] at glued
  | 1, K => level1_noSelf K
  | m + 2, T => (kids_at (m := m + 1) (by omega) T (fun K => good (m + 1) K (by omega))).noSelf
      (fun c _ => super_noSelf (m + 1) _)

/-! ### The nest tiling is a tiling -/

/-- A gluing in `N_b` joins actual tiles and edges. -/
theorem glue_ok_N (b : Nat) {t i t' j : Nat} (ht : t < (N b).tiles) (hi : i < 14)
    (glued : (N b).glue t i = some (t', j)) : t' < (N b).tiles ∧ j < 14 := by
  rcases Nat.eq_zero_or_pos b with rfl | b_pos
  · -- `N_0` is a single tile: nothing is glued
    exact absurd glued (by simp [N, super, tile])
  · exact (good b .Delta b_pos).sig.glue_ok t i t' j ht hi glued

/-- **Part (d)**: the nest tiling glues as every block does. -/
theorem nestGlue_ext {b t i t' j : Nat} (ht : t < (N b).tiles) (hi : i < 14)
    (glued : (N b).glue t i = some (t', j)) : nestGlue (gid b t) i = some (gid b t', j) := by
  -- the far tile is an actual tile of `N_b`
  have far_bound := (glue_ok_N b ht hi glued).1
  generalize gid_eq : gid b t = g
  -- `nestGlue` reads tile number `g` off `N_{g+3}`, where it is `up (g + 1) 2 (loc (g + 1) g)`
  have big := tiles_ge (g + 1)
  obtain ⟨loc_bound, gid_of_loc⟩ := gid_loc (g + 1) g (by omega)
  obtain ⟨up_bound, gid_of_up⟩ := gid_up loc_bound 2
  -- `N_{g+3}` glues every edge of that tile
  have edge_glued := no_boundary (b := g + 1) (by omega) loc_bound hi
  obtain ⟨⟨t'', j''⟩, glued''⟩ := Option.isSome_iff_exists.mp edge_glued
  -- the far tile there is an actual tile of `N_{g+3}`
  have far_bound'' := (glue_ok_N (g + 1 + 2) up_bound hi glued'').1
  -- both gluings, seen in `N_{b+g+3}`, which contains both blocks: the gluing in `N_b`
  have lift_b := glue_lift ht glued (g + 1 + 2)
  -- and the gluing in `N_{g+3}`
  have lift_g := glue_lift up_bound glued'' b
  -- the tile keeps its number up there, from `N_b`
  have tile_b := gid_up ht (g + 1 + 2)
  -- and from `N_{g+3}`
  have tile_g := gid_up up_bound b
  -- so do the far tiles, from `N_b`
  have far_b := gid_up far_bound (g + 1 + 2)
  -- and from `N_{g+3}`
  have far_g := gid_up far_bound'' b
  rw [show g + 1 + 2 + b = b + (g + 1 + 2) by omega] at lift_g tile_g far_g
  -- the tile has the same number either way, so it is the same tile up there
  have same_tile : up (g + 1 + 2) b (up (g + 1) 2 (loc (g + 1) g)) = up b (g + 1 + 2) t := by
    apply gid_inj tile_g.1 tile_b.1
    rw [tile_g.2, tile_b.2, gid_of_up, gid_of_loc, gid_eq]
  rw [same_tile, lift_b] at lift_g
  -- so the two gluings agree: the same far tile, the same edge
  simp only [Option.some.injEq, Prod.mk.injEq] at lift_g
  obtain ⟨same_far, rfl⟩ := lift_g
  -- the far tile's number, read off either block
  have far_number := far_g.2
  rw [← same_far, far_b.2] at far_number
  unfold nestGlue
  rw [show g + 3 = g + 1 + 2 from rfl, glued'']
  simp only [Option.map_some, far_number]

/-- **Part (e)**: every edge of every tile of the nest tiling is glued, to an edge of another tile, which is glued
back to it. -/
theorem nestGlue_some (g i : Nat) (hi : i < 14) :
    ∃ g' j, nestGlue g i = some (g', j) ∧ g' ≠ g ∧ j < 14 ∧ nestGlue g' j = some (g, i) := by
  -- tile number `g` as a tile of `N_{g+1}`, and of `N_{g+3}`
  have big := tiles_ge (g + 1)
  obtain ⟨loc_bound, gid_of_loc⟩ := gid_loc (g + 1) g (by omega)
  obtain ⟨up_bound, gid_of_up⟩ := gid_up loc_bound 2
  -- `N_{g+3}` glues the edge, to an actual edge of an actual tile
  obtain ⟨⟨t', j⟩, glued⟩ := Option.isSome_iff_exists.mp (no_boundary (b := g + 1) (by omega) loc_bound hi)
  obtain ⟨far_bound, hj⟩ := glue_ok_N (g + 1 + 2) up_bound hi glued
  -- and glues it back
  have back := super_glueSymm (g + 1 + 2) .Delta _ i t' j up_bound hi glued
  -- the tile's number in the nest tiling is `g`
  have number : gid (g + 1 + 2) (up (g + 1) 2 (loc (g + 1) g)) = g := by rw [gid_of_up, gid_of_loc]
  refine ⟨gid (g + 1 + 2) t', j, ?_, ?_, hj, ?_⟩
  · -- `nestGlue` reads exactly this gluing
    unfold nestGlue
    rw [show g + 3 = g + 1 + 2 from rfl, glued]
    rfl
  · -- a different tile of `N_{g+3}`, so a different number
    intro same
    -- `N_{g+3}` glues no tile to itself
    have differ := super_noSelf (g + 1 + 2) .Delta _ i t' j up_bound hi glued
    exact differ (gid_inj far_bound up_bound (same.trans number.symm))
  · have glued_back := nestGlue_ext far_bound hj back -- the gluing back, read by part (d)
    rw [number] at glued_back
    exact glued_back

/-- **`NestModel`**: the nest tiling is a tiling, and it is the union of the blocks. -/
theorem nestModel : NestModel :=
  ⟨fun g => by
    -- `N_{g+1}` has more than `g + 1` tiles
    have := tiles_ge (g + 1)
    omega,
   loc_gid,
   gid_loc,
   fun _ _ ht => (gid_up1 ht).2,
   fun _ _ _ _ _ ht hi glued => nestGlue_ext ht hi glued,
   nestGlue_some⟩

/-! ### The nest tiling's strands -/

/-- The ports of the nest tiling: a tile number, a vertex `0 … 13` of the tile, and a hand. -/
abbrev NPort := {p : Port // p.2.1 < 14}

/-- The other end of a piece is a different port. -/
theorem pieceEnd_ne (p : Port) : pieceEnd p ≠ p := by
  obtain ⟨t, i, s⟩ := p
  rcases i with _ | _ | i <;> cases s <;> simp [pieceEnd]

/-- Across every port of the nest tiling there is a port of another tile, and across that one lies the first. -/
theorem nestAcross_some {p : Port} (hp : p.2.1 < 14) :
    ∃ q, nestTiling.across p = some q ∧ q.2.1 < 14 ∧ q.1 ≠ p.1 ∧ nestTiling.across q = some p := by
  obtain ⟨g, i, s⟩ := p
  simp only at hp
  cases s with
  | true =>
    -- port `R(v_i)` lies on edge `e_i`
    obtain ⟨g', j, glued, other, hj, back⟩ := nestGlue_some g i hp
    refine ⟨(g', j, true), ?_, hj, other, ?_⟩
    · show (nestGlue g i).map _ = _
      rw [glued]; rfl
    · show (nestGlue g' j).map _ = _
      rw [back]; rfl
  | false =>
    -- port `L(v_i)` lies on edge `e_{i-1}`
    obtain ⟨g', j, glued, other, hj, back⟩ := nestGlue_some g ((i + 13) % 14) (by omega)
    refine ⟨(g', (j + 1) % 14, false), ?_, Nat.mod_lt _ (by omega), other, ?_⟩
    · show (nestGlue g ((i + 13) % 14)).map _ = _
      rw [glued]; rfl
    · show (nestGlue g' (((j + 1) % 14 + 13) % 14)).map _ = _
      -- vertex `i - 1`, then one on, is vertex `i` again
      have round : ((i + 13) % 14 + 1) % 14 = i := by omega
      rw [mod14 hj, back]
      simp only [Option.map_some, round]

/-- **The nest tiling's ports, with its two pairings**: the two ends of a piece (`pieceEnd`), and straight across an
edge (`nestTiling.across`). Both pair every port with a different port, and undo themselves. -/
def nestSys : StrandSystem NPort where
  inside x := ⟨pieceEnd x.1, (pieceEnd_valid x.2).2⟩
  across x := ⟨(nestTiling.across x.1).getD x.1, by
    obtain ⟨q, across_x, q_valid, _, _⟩ := nestAcross_some x.2
    rw [across_x]; exact q_valid⟩
  inside_inside x := Subtype.ext (Patch.pieceEnd_pieceEnd x.1)
  across_across x := by
    obtain ⟨q, across_x, _, _, back⟩ := nestAcross_some x.2
    apply Subtype.ext
    show (nestTiling.across ((nestTiling.across x.1).getD x.1)).getD ((nestTiling.across x.1).getD x.1) = x.1
    rw [across_x]
    simp only [Option.getD_some, back]
  inside_ne x same := pieceEnd_ne x.1 (congrArg Subtype.val same)
  across_ne x same := by
    obtain ⟨q, across_x, _, other, _⟩ := nestAcross_some x.2
    -- the port across lies on another tile
    have same_tile := congrArg (fun y : NPort => y.1.1) same
    simp only [across_x, Option.getD_some] at same_tile
    exact other same_tile

/-! ### The blocks inside the nest tiling -/

/-- Port `p` of `N_b`, as a port of the nest tiling. -/
def gP (b : Nat) (p : Port) : Port := (gid b p.1, p.2.1, p.2.2)

/-- The other end of a piece, before or after renumbering. -/
theorem pieceEnd_gP (b : Nat) (p : Port) : pieceEnd (gP b p) = gP b (pieceEnd p) := by
  obtain ⟨t, i, s⟩ := p
  rcases i with _ | _ | i <;> rfl

/-- Across a port of `N_b`, the nest tiling continues as `N_b` does. -/
theorem across_gP {b : Nat} {p q : Port} (p_port : (N b).IsPort p) (across_p : (N b).across p = some q) :
    nestTiling.across (gP b p) = some (gP b q) := by
  obtain ⟨t, i, s⟩ := p
  obtain ⟨ht, hi⟩ := p_port
  simp only at ht hi
  -- the port, renumbered
  have renumbered : gP b (t, i, s) = (gid b t, i, s) := rfl
  rw [renumbered]
  cases s with
  | true =>
    simp only [Patch.across, straightThrough] at across_p
    cases glued : (N b).glue t i with
    | none => rw [glued] at across_p; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_p
      simp only [Option.map_some, Option.some.injEq] at across_p
      subst across_p
      show (nestGlue (gid b t) i).map _ = _
      rw [nestGlue_ext ht hi glued]; rfl
  | false =>
    simp only [Patch.across, straightThrough] at across_p
    cases glued : (N b).glue t ((i + 13) % 14) with
    | none => rw [glued] at across_p; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_p
      simp only [Option.map_some, Option.some.injEq] at across_p
      subst across_p
      show (nestGlue (gid b t) ((i + 13) % 14)).map _ = _
      rw [nestGlue_ext ht (by omega) glued]; rfl

/-- Where every edge of a tile is glued, something lies across every port of it. -/
theorem across_isSome {P : Patch} {t : Nat} (all_glued : ∀ i, i < 14 → (P.glue t i).isSome) {q : Port}
    (on_tile : q.1 = t) (hi : q.2.1 < 14) : (P.across q).isSome := by
  obtain ⟨t', i, s⟩ := q
  simp only at on_tile hi
  subst on_tile
  cases s with
  | true =>
    -- port `R(v_i)` lies on edge `e_i`, which is glued
    have edge := all_glued i hi
    simp only [Patch.across, straightThrough]
    cases glued : P.glue t' i with
    | none => rw [glued] at edge; contradiction
    | some _ => rfl
  | false =>
    -- port `L(v_i)` lies on edge `e_{i-1}`, which is glued
    have edge := all_glued ((i + 13) % 14) (by omega)
    simp only [Patch.across, straightThrough]
    cases glued : P.glue t' ((i + 13) % 14) with
    | none => rw [glued] at edge; contradiction
    | some _ => rfl

/-! ### No closed strand -/

/-- A strand of the nest tiling cannot stay among the tiles of one block `N_B` (`B ≥ 1`): in `N_{B+2}` every edge of
those tiles is glued, so following it from a port there would never reach the rim of `N_{B+2}`. -/
theorem follow_bounded {B : Nat} (B_pos : 1 ≤ B) : ∀ p r, (N (B + 2)).Follow p r → (N (B + 2)).IsPort p →
    ∀ x : NPort, gP (B + 2) p = x.1 → (∀ k, (nestSys.walk x k).1.1 < (N B).tiles) → False := by
  -- `N_{B+2}` has the signature
  have sig := (good (B + 2) .Delta (by omega)).sig
  intro p r follows
  induction follows with
  | @leave p nothing_across =>
    intro p_port x x_eq bounded
    -- the tile of `p` is a tile of `N_B`, seen in `N_{B+2}`
    have in_B : gid (B + 2) p.1 < (N B).tiles := by
      -- the strand starts at `x`, on a tile of `N_B`
      have start := bounded 0
      change x.1.1 < _ at start
      rw [← x_eq] at start; exact start
    obtain ⟨loc_bound, gid_of_loc⟩ := gid_loc B _ in_B
    obtain ⟨up_bound, gid_of_up⟩ := gid_up loc_bound 2
    -- that tile, taken into `N_B` and back up to `N_{B+2}`, is the tile of `p`
    have same_tile : up B 2 (loc B (gid (B + 2) p.1)) = p.1 :=
      gid_inj up_bound p_port.1 (by rw [gid_of_up, gid_of_loc])
    -- every edge of it is glued in `N_{B+2}`
    have all_glued : ∀ i, i < 14 → ((N (B + 2)).glue p.1 i).isSome := by
      intro i hi
      rw [← same_tile]
      exact no_boundary B_pos loc_bound hi
    -- the other end of the piece is on the same tile
    have end_valid := pieceEnd_valid p_port.2
    -- so something lies across it, yet the strand leaves `N_{B+2}` there
    have across_end := across_isSome all_glued end_valid.1 end_valid.2
    rw [nothing_across] at across_end
    contradiction
  | @next p q r across_end _ ih =>
    intro p_port x x_eq bounded
    -- the next port of the strand, in `N_{B+2}` and in the nest tiling
    -- the other end of the piece is on the same tile
    have end_valid := pieceEnd_valid p_port.2
    -- so it is a port of `N_{B+2}`
    have end_port : (N (B + 2)).IsPort (pieceEnd p) := ⟨end_valid.1 ▸ p_port.1, end_valid.2⟩
    -- and so is the port `q` across from it
    have q_port : (N (B + 2)).IsPort q := Patch.across_valid sig end_port.1 end_port.2 across_end
    -- `q` is the next port of the strand in the nest tiling
    have next_is : (nestSys.next x).1 = gP (B + 2) q := by
      show (nestTiling.across (pieceEnd x.1)).getD (pieceEnd x.1) = _
      rw [← x_eq, pieceEnd_gP, across_gP end_port across_end]
      rfl
    -- the strand from there is the rest of the strand from `x`
    refine ih q_port (nestSys.next x) next_is.symm (fun k => ?_)
    -- its ports are ports of the strand from `x`, so on tiles of `N_B`
    have later := bounded (k + 1)
    rw [StrandSystem.walk, iter_succ'] at later
    exact later

/-- **No strand of the nest tiling is closed.** A closed strand visits finitely many tiles, so it stays in one block.
-/
theorem not_closed (x : NPort) : ¬ nestSys.Closed x := by
  rintro ⟨n, n_pos, back⟩
  -- the strand only ever visits the ports reached in its first `n` steps
  have periodic : ∀ k, ∃ j, j < n ∧ nestSys.walk x k = nestSys.walk x j := by
    intro k
    induction k with
    | zero => exact ⟨0, n_pos, rfl⟩
    | succ k ih =>
      obtain ⟨j, hj, same⟩ := ih
      by_cases wraps : j + 1 = n
      · refine ⟨0, n_pos, ?_⟩
        rw [StrandSystem.walk_succ, same, ← StrandSystem.walk_succ, wraps, back]
        rfl
      · exact ⟨j + 1, by omega, by rw [StrandSystem.walk_succ, same, ← StrandSystem.walk_succ]⟩
  -- the tiles of those ports have numbers below some bound `M`
  have bounded : ∀ m, ∃ M, ∀ j, j < m → (nestSys.walk x j).1.1 < M := by
    intro m
    induction m with
    | zero => exact ⟨0, fun j hj => absurd hj (by omega)⟩
    | succ m ih =>
      obtain ⟨M, below⟩ := ih
      refine ⟨M + (nestSys.walk x m).1.1 + 1, fun j hj => ?_⟩
      by_cases earlier : j < m
      · have := below j earlier -- an earlier port: below `M`
        omega
      · have is_m : j = m := by omega -- port `m` itself
        subst is_m; omega
  obtain ⟨M, below⟩ := bounded n
  -- so they are all tiles of `N_{M+1}`, which has more than `M` tiles
  have big := tiles_ge (M + 1)
  -- every port of the strand is on a tile of `N_{M+1}`
  have in_block : ∀ k, (nestSys.walk x k).1.1 < (N (M + 1)).tiles := by
    intro k
    obtain ⟨j, hj, same⟩ := periodic k
    rw [same]
    -- the `j`-th port is below `M`
    have := below j hj
    omega
  -- start at the port `x`, seen in `N_{M+3}`
  obtain ⟨loc_bound, gid_of_loc⟩ := gid_loc (M + 1) x.1.1 (in_block 0)
  obtain ⟨up_bound, gid_of_up⟩ := gid_up loc_bound 2
  -- it is a port of `N_{M+3}`
  have start : (N (M + 1 + 2)).IsPort (up (M + 1) 2 (loc (M + 1) x.1.1), x.1.2.1, x.1.2.2) := ⟨up_bound, x.2⟩
  -- Theorem A says the strand leaves `N_{M+3}`
  obtain ⟨r, follows⟩ := theoremA (M + 1 + 2) .Delta _ start
  refine follow_bounded (B := M + 1) (by omega) _ r follows start x ?_ in_block
  show (gid (M + 1 + 2) (up (M + 1) 2 (loc (M + 1) x.1.1)), x.1.2.1, x.1.2.2) = x.1
  rw [gid_of_up, gid_of_loc]

/-! ### One strand -/

/-- A strand of a block is part of a strand of the nest tiling. -/
theorem linked_same {m : Nat} (m_pos : 1 ≤ m) {u v : Port} (linked : (N m).Linked u v) (u_port : (N m).IsPort u) :
    ∀ x y : NPort, x.1 = gP m u → y.1 = gP m v → nestSys.Same x y := by
  -- `N_m` has the signature
  have sig := (good m .Delta m_pos).sig
  intro x y x_eq y_eq
  induction linked generalizing y with
  | refl =>
    -- the same port
    have same_port : x = y := Subtype.ext (x_eq.trans y_eq.symm)
    subst same_port
    exact .refl
  | @piece q reach ih =>
    -- along the piece at `q`, a port of `N_m`
    have q_port := reach.valid sig u_port
    -- one move along the piece, in the nest tiling
    have step := StrandSystem.Same.inside (S := nestSys) (ih ⟨gP m q, q_port.2⟩ rfl)
    -- which lands on `y`
    have is_y : nestSys.inside ⟨gP m q, q_port.2⟩ = y := Subtype.ext (by rw [y_eq]; exact pieceEnd_gP m q)
    rwa [is_y] at step
  | @edge q q' reach across_q ih =>
    -- across the edge at `q`, a port of `N_m`
    have q_port := reach.valid sig u_port
    -- one move across the edge, in the nest tiling
    have step := StrandSystem.Same.across (S := nestSys) (ih ⟨gP m q, q_port.2⟩ rfl)
    -- which lands on `y`
    have is_y : nestSys.across ⟨gP m q, q_port.2⟩ = y := Subtype.ext (by
      show (nestTiling.across (gP m q)).getD _ = _
      rw [across_gP q_port across_q, y_eq]; rfl)
    rwa [is_y] at step

/-- Port `z` of the nest tiling, as a port of the block `N_b`. -/
def toBlock (b : Nat) (z : NPort) : Port := (loc b z.1.1, z.1.2.1, z.1.2.2)

/-- Port `z` of the nest tiling is a port of `N_b` if its tile is. -/
theorem toBlock_port {b : Nat} {z : NPort} (in_block : z.1.1 < (N b).tiles) : (N b).IsPort (toBlock b z) :=
  ⟨(gid_loc b z.1.1 in_block).1, z.2⟩

/-- Taken into `N_b` and then up `k` levels, port `z` keeps its number. -/
theorem gP_toBlock {b : Nat} {z : NPort} (in_block : z.1.1 < (N b).tiles) (k : Nat) :
    gP (b + k) (upPort b k (toBlock b z)) = z.1 := by
  obtain ⟨loc_bound, gid_of_loc⟩ := gid_loc b z.1.1 in_block
  simp only [gP, upPort, toBlock]
  rw [(gid_up loc_bound k).2, gid_of_loc]

/-- Two ports of the nest tiling whose tiles lie in `N_b` (`b ≥ 1`) lie on one strand: they do in `N_{b+4}`
(Theorem B with the paper's bound). -/
theorem same_in_block {b : Nat} (b_pos : 1 ≤ b) {x y : NPort} (x_in : x.1.1 < (N b).tiles)
    (y_in : y.1.1 < (N b).tiles) : nestSys.Same x y := by
  -- one strand of `N_{b+4}`
  have linked := (theoremB_sharp b (toBlock b x) (toBlock b y) b_pos (toBlock_port x_in) (toBlock_port y_in)).1
  -- with `x`, four levels up, a port of `N_{b+4}`
  have x_port := isPort_upk b_pos (toBlock_port x_in) 4
  -- read in the nest tiling
  exact linked_same (m := b + 4) (by omega) linked x_port x y (gP_toBlock x_in 4).symm (gP_toBlock y_in 4).symm

/-- **Any two ports of the nest tiling lie on one strand**: both tiles lie in a large enough block. -/
theorem all_same (x y : NPort) : nestSys.Same x y := by
  -- `N_{x+y+1}` contains both tiles
  have big := tiles_ge (x.1.1 + y.1.1 + 1)
  exact same_in_block (b := x.1.1 + y.1.1 + 1) (by omega) (by omega) (by omega)

/-! ### Lemma 3.4 -/

/-- **Theorem B, final form** (as stated in `Statement.lean`): the ribbons of the nest tiling form one two-way
infinite strand. -/
theorem theoremB_strand : TheoremB_strand := by
  -- the start: port `R(v_0)` of the original tile
  let start : NPort := ⟨(0, 0, true), by decide⟩
  -- following the strand forwards, as ports
  have forwards : ∀ k, iter nestTiling.forward k (0, 0, true) = (nestSys.walk start k).1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih]; rfl
  -- and backwards
  have backwards : ∀ k, iter nestTiling.backward k (0, 0, true) = (iter nestSys.prev k start).1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih]; rfl
  -- Lemma 3.4: the strand is closed or a two-way infinite path; it is not closed
  obtain ⟨distinct, back_distinct, apart, no_piece_twice⟩ :=
    (nestSys.closed_or_path start).resolve_left (not_closed start)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) forwards, no port twice
    intro i j same
    rw [forwards, forwards] at same
    exact distinct i j (Subtype.ext same)
  · -- (2) backwards, no port twice
    intro a a' same
    rw [backwards, backwards] at same
    exact back_distinct a a' (Subtype.ext same)
  · -- (3) backwards never meets forwards, except at the start
    intro a b same
    rw [backwards, forwards] at same
    exact apart a b (Subtype.ext same)
  · -- (4) no piece twice
    intro i j same
    rw [forwards, forwards] at same
    exact no_piece_twice i j (Subtype.ext same)
  · -- (5) every port is on the strand
    intro q hq
    obtain ⟨k, reached | reached | reached | reached⟩ := nestSys.same_orbit (all_same start ⟨q, hq⟩)
    · exact ⟨k, Or.inl (by rw [forwards]; exact congrArg Subtype.val reached)⟩
    · exact ⟨k, Or.inr (Or.inl (by rw [backwards]; exact congrArg Subtype.val reached))⟩
    · exact ⟨k, Or.inr (Or.inr (Or.inl (by rw [forwards]; exact congrArg Subtype.val reached)))⟩
    · exact ⟨k, Or.inr (Or.inr (Or.inr (by rw [backwards]; exact congrArg Subtype.val reached)))⟩

end SpectreKnot.Statement

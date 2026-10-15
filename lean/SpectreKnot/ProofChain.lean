/-
**Theorem A in strand form** (`theoremA_strand`): in a tiling whose hierarchy covers the plane, every strand is a
two-way infinite path.

The tiling is the union of a chain X_1 ⊂ X_2 ⊂ ⋯ of supertiles (`Statement.lean` §7). Its tiles are numbered so that
every block keeps its own numbering, and any tiling `T` that contains every block glues every edge (`chainModel`).
Its ports, with the two pairings "other end of the piece" and "straight across the edge", form a `StrandSystem`
(`tilingSys`). A closed strand would visit finitely many tiles. Every edge of each of them is glued in some block, so
all of them are glued in one block X_L; following the strand inside X_L would then never reach the rim of X_L, but by
Theorem A it does. So no strand is closed, and Lemma 3.4 (`StrandSystem.closed_or_path`) says that each strand is a
two-way infinite path. This is the nest argument of `ProofStrand.lean` without Theorem B: for a chain the level at
which an edge is glued has no fixed bound, so the closed strand's tiles are handled together (`all_glued_at`).
-/
import SpectreKnot.ProofStrand

namespace SpectreKnot.Statement

open Pattern Compose Gluing

namespace Chain

/-! ### The blocks as compositions -/

/-- The children of X_{m+1}: the level-`m` supertiles of the kinds that Table 1 lists for `K (m + 1)`. -/
abbrev kidsAt (X : Chain) (m : Nat) : Nat → Patch := fun c => super m (kidAt (X.K (m + 1)) c)

/-- For `m ≥ 1`, X_{m+1} is the composition of its level-`m` children. -/
theorem block_succ (X : Chain) {m : Nat} (m_pos : 1 ≤ m) : X.block (m + 1) = compose (X.K (m + 1)) (X.kidsAt m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rfl

/-- Child `c m` of X_{m+1} is X_m. -/
theorem kid_eq (X : Chain) {m : Nat} (m_pos : 1 ≤ m) : X.kidsAt m (X.c m) = X.block m := by
  show super m (kidAt (X.K (m + 1)) (X.c m)) = super m (X.K m)
  rw [show kidAt (X.K (m + 1)) (X.c m) = X.K m from X.child_kind m m_pos]

/-- X_m starts at tile `X.shift m` of X_{m+1}: after the tiles of the children before it. -/
theorem shift_eq (X : Chain) (m : Nat) : X.shift m = offC (X.kidsAt m) (X.c m) := rfl

/-- The children of X_{m+1}, with the bridge's hypotheses. -/
theorem kids_ok (X : Chain) {m : Nat} (m_pos : 1 ≤ m) :
    Kids (X.K (m + 1)) (X.kidsAt m) (Lk m (X.K (m + 1))) (dOff m) (ori m) (ori m) :=
  kids_at m_pos (X.K (m + 1)) (fun K => good m K m_pos)

/-! ### How the blocks grow -/

/-- Every supertile has at least seven children. -/
theorem seven_kids : ∀ T : Kind, 7 ≤ nk T := by intro T; cases T <;> decide

/-- X_{m+1} holds the children before X_m (`X.shift m` tiles) and then X_m; and it has more tiles than X_m. -/
theorem tiles_succ (X : Chain) {m : Nat} (m_pos : 1 ≤ m) :
    (X.block m).tiles + X.shift m ≤ (X.block (m + 1)).tiles ∧ (X.block m).tiles < (X.block (m + 1)).tiles := by
  -- the children of X_{m+1}
  have kids := X.kids_ok m_pos
  -- X_m is child `c m`
  have child_lt : X.c m < nk (X.K (m + 1)) := X.child_lt m m_pos
  -- which has the tiles of X_m
  have child_tiles : (X.kidsAt m (X.c m)).tiles = (X.block m).tiles := by rw [X.kid_eq m_pos]
  -- the children up to and including X_m
  have upto := offC_succ (X.kidsAt m) (X.c m)
  -- are among all the children
  have upto_le := offC_mono (X.kidsAt m) (show X.c m + 1 ≤ nk (X.K (m + 1)) from child_lt)
  rw [X.block_succ m_pos, X.shift_eq]
  show _ ≤ offC (X.kidsAt m) (nk (X.K (m + 1))) ∧ _ < offC (X.kidsAt m) (nk (X.K (m + 1)))
  refine ⟨by omega, ?_⟩
  by_cases last : X.c m + 1 = nk (X.K (m + 1))
  · -- X_m is the last child: there is a child before it, with a tile
    have seven := seven_kids (X.K (m + 1))
    -- the children before X_m include child 0
    have first_le := offC_mono (X.kidsAt m) (show 1 ≤ X.c m by omega)
    -- whose tiles come first
    have first := offC_succ (X.kidsAt m) 0
    -- child 0 has a tile
    have first_pos := kids.tiles_pos 0 (by omega)
    simp only [Nat.zero_add, show offC (X.kidsAt m) 0 = 0 from rfl] at first
    omega
  · -- X_m is not the last child: the next child has a tile
    have next_le := offC_mono (X.kidsAt m) (show X.c m + 1 + 1 ≤ nk (X.K (m + 1)) by omega)
    -- the tiles of the next child come after X_m
    have next := offC_succ (X.kidsAt m) (X.c m + 1)
    -- the next child has a tile
    have next_pos := kids.tiles_pos (X.c m + 1) (by omega)
    omega

/-- Every level-1 supertile has at least two tiles. -/
theorem level1_two : ∀ K, 2 ≤ (super 1 K).tiles := by intro K; cases K <;> decide

/-- X_{m+1} has at least `m + 2` tiles. -/
theorem tiles_ge (X : Chain) : ∀ m, m + 2 ≤ (X.block (m + 1)).tiles
  | 0 => level1_two (X.K 1)
  | m + 1 => by
    -- one more tile at least, at each level
    have grow := (X.tiles_succ (m := m + 1) (by omega)).2
    -- and X_{m+1} has at least `m + 2`
    have before := X.tiles_ge m
    omega

/-- Larger blocks have at least as many tiles. -/
theorem tiles_mono (X : Chain) {m : Nat} (m_pos : 1 ≤ m) : ∀ k, (X.block m).tiles ≤ (X.block (m + k)).tiles
  | 0 => Nat.le_refl _
  | k + 1 => by
    -- up to X_{m+k}
    have before := X.tiles_mono m_pos k
    -- and one more level
    have grow := (X.tiles_succ (m := m + k) (by omega)).2
    show _ ≤ (X.block (m + k + 1)).tiles
    omega

/-! ### The numbering of the union's tiles -/

/-- `X.gid m` sends the tiles of X_m into 0 … |X_m| - 1, and `X.loc m` undoes it. -/
theorem loc_gid (X : Chain) : ∀ m t, 1 ≤ m → t < (X.block m).tiles →
    X.gid m t < (X.block m).tiles ∧ X.loc m (X.gid m t) = t
  | 0, _, m_pos, _ => absurd m_pos (by decide)
  | 1, _, _, ht => ⟨ht, rfl⟩
  | m + 2, t, _, ht => by
    -- X_{m+2} holds X_{m+1} and the children before it
    have grow : (X.block (m + 1)).tiles + X.shift (m + 1) ≤ (X.block (m + 2)).tiles :=
      (X.tiles_succ (m := m + 1) (by omega)).1
    by_cases in_child : X.shift (m + 1) ≤ t ∧ t < X.shift (m + 1) + (X.block (m + 1)).tiles
    · -- a tile of X_{m+1}: numbered as in X_{m+1}
      obtain ⟨bound, inverse⟩ := X.loc_gid (m + 1) (t - X.shift (m + 1)) (by omega) (by omega)
      simp only [Chain.gid, Chain.loc, ite_eq_left in_child, ite_eq_left bound, inverse]
      exact ⟨by omega, by omega⟩
    · by_cases before : t < X.shift (m + 1)
      · -- a tile of an earlier child: numbered just after X_{m+1}
        simp only [Chain.gid, Chain.loc, ite_eq_right in_child, ite_eq_left before]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact ⟨by omega, by omega⟩
      · -- a tile of a later child: keeps its number
        simp only [Chain.gid, Chain.loc, ite_eq_right in_child, ite_eq_right before]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨ht, rfl⟩

/-- `X.loc m` sends 0 … |X_m| - 1 to tiles of X_m, and `X.gid m` undoes it. -/
theorem gid_loc (X : Chain) : ∀ m g, 1 ≤ m → g < (X.block m).tiles →
    X.loc m g < (X.block m).tiles ∧ X.gid m (X.loc m g) = g
  | 0, _, m_pos, _ => absurd m_pos (by decide)
  | 1, _, _, hg => ⟨hg, rfl⟩
  | m + 2, g, _, hg => by
    -- X_{m+2} holds X_{m+1} and the children before it
    have grow : (X.block (m + 1)).tiles + X.shift (m + 1) ≤ (X.block (m + 2)).tiles :=
      (X.tiles_succ (m := m + 1) (by omega)).1
    by_cases old : g < (X.block (m + 1)).tiles
    · -- a number of X_{m+1}: its tile in X_{m+1}
      obtain ⟨bound, inverse⟩ := X.gid_loc (m + 1) g (by omega) old
      simp only [Chain.loc, ite_eq_left old, Chain.gid]
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel, inverse]
      exact ⟨by omega, rfl⟩
    · by_cases from_before : g < (X.block (m + 1)).tiles + X.shift (m + 1)
      · -- a number just after X_{m+1}: a tile of an earlier child
        simp only [Chain.loc, ite_eq_right old, ite_eq_left from_before, Chain.gid]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact ⟨by omega, by omega⟩
      · -- a later number: a tile of a later child, same number
        simp only [Chain.loc, ite_eq_right old, ite_eq_right from_before, Chain.gid]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨hg, rfl⟩

/-- `X.gid m` is one to one on the tiles of X_m. -/
theorem gid_inj (X : Chain) {m t t' : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles)
    (ht' : t' < (X.block m).tiles) (same : X.gid m t = X.gid m t') : t = t' := by
  -- apply `X.loc m` to both sides: it takes `X.gid m t` back to `t`
  have back := (X.loc_gid m t m_pos ht).2
  -- and `X.gid m t'` back to `t'`
  have back' := (X.loc_gid m t' m_pos ht').2
  rw [← back, ← back', same]

/-- Going `k + 1` levels up the chain is going `k` levels up, then one more. -/
theorem up_succ (X : Chain) : ∀ (k m t : Nat), X.up m (k + 1) t = X.up (m + k) 1 (X.up m k t)
  | 0, _, _ => rfl
  | k + 1, m, t => by
    show X.up (m + 1) (k + 1) (t + X.shift m) = _
    rw [X.up_succ k (m + 1) (t + X.shift m), show m + 1 + k = m + (k + 1) by omega]
    rfl

/-- One level up, a tile of X_m is still a tile, and keeps its number. -/
theorem gid_up1 (X : Chain) {m t : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles) :
    X.up m 1 t < (X.block (m + 1)).tiles ∧ X.gid (m + 1) (X.up m 1 t) = X.gid m t := by
  -- X_{m+1} holds the children before X_m, then X_m
  have grow := (X.tiles_succ m_pos).1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- `X.up m 1 t` is `t` moved past the children before X_m
  show t + X.shift (m' + 1) < _ ∧ X.gid (m' + 2) (t + X.shift (m' + 1)) = _
  refine ⟨by omega, ?_⟩
  simp only [Chain.gid]
  rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]

/-- Any number of levels up, a tile of X_m is still a tile, and keeps its number. -/
theorem gid_up (X : Chain) {m t : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles) :
    ∀ k, X.up m k t < (X.block (m + k)).tiles ∧ X.gid (m + k) (X.up m k t) = X.gid m t
  | 0 => ⟨ht, rfl⟩
  | k + 1 => by
    -- `k` levels up
    obtain ⟨bound, same⟩ := X.gid_up m_pos ht k
    -- and one more
    obtain ⟨bound', same'⟩ := X.gid_up1 (m := m + k) (by omega) bound
    rw [X.up_succ]
    exact ⟨bound', same'.trans same⟩

/-- The tile numbered `g`, found in X_{m+k}, is the one found in X_m, taken `k` levels up. -/
theorem loc_up (X : Chain) {m g : Nat} (m_pos : 1 ≤ m) (hg : g < (X.block m).tiles) (k : Nat) :
    X.loc (m + k) g = X.up m k (X.loc m g) := by
  -- the tile of X_m numbered `g`
  obtain ⟨loc_bound, gid_of_loc⟩ := X.gid_loc m g m_pos hg
  -- taken `k` levels up, it keeps its number
  obtain ⟨up_bound, gid_of_up⟩ := X.gid_up m_pos loc_bound k
  -- so `X.loc (m + k)` finds it
  have found := (X.loc_gid (m + k) _ (by omega) up_bound).2
  rw [gid_of_up, gid_of_loc] at found
  exact found

/-! ### Gluing goes up the chain -/

/-- An edge glued in X_m is glued the same way, renumbered, in X_{m+1}. -/
theorem glue_lift1 (X : Chain) {m t i t' j : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles)
    (glued : (X.block m).glue t i = some (t', j)) : (X.block (m + 1)).glue (X.up m 1 t) i = some (X.up m 1 t', j) := by
  -- the children of X_{m+1}
  have kids := X.kids_ok m_pos
  -- `t` is a tile of child `c m`, which is X_m
  have ht_child : t < (X.kidsAt m (X.c m)).tiles := by rw [X.kid_eq m_pos]; exact ht
  -- and the child glues it as X_m does
  have glued_child : (X.kidsAt m (X.c m)).glue t i = some (t', j) := by rw [X.kid_eq m_pos]; exact glued
  rw [X.block_succ m_pos]
  show (compose (X.K (m + 1)) (X.kidsAt m)).glue (t + offC (X.kidsAt m) (X.c m)) i =
    some (t' + offC (X.kidsAt m) (X.c m), j)
  rw [kids.glue_shift (X.child_lt m m_pos) ht_child]
  unfold glueAt
  rw [glued_child]

/-- An edge glued in X_m is glued the same way any number of levels up. -/
theorem glue_lift (X : Chain) {m t i t' j : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles)
    (glued : (X.block m).glue t i = some (t', j)) : ∀ k, (X.block (m + k)).glue (X.up m k t) i = some (X.up m k t', j)
  | 0 => glued
  | k + 1 => by
    rw [X.up_succ k m t, X.up_succ k m t']
    exact X.glue_lift1 (m := m + k) (by omega) (X.gid_up m_pos ht k).1 (X.glue_lift m_pos ht glued k)

/-- A gluing in X_m joins actual tiles and edges. -/
theorem glue_ok (X : Chain) {m t i t' j : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles) (hi : i < 14)
    (glued : (X.block m).glue t i = some (t', j)) : t' < (X.block m).tiles ∧ j < 14 :=
  (good m (X.K m) m_pos).sig.glue_ok t i t' j ht hi glued

/-- **Two blocks agree.** If X_m and X_{m'} both glue edge `e_i` of the tile numbered `g`, they glue it to the same
edge of the same numbered tile. -/
theorem glue_agree (X : Chain) {m m' t t₂ i u j u₂ j₂ : Nat} (m_pos : 1 ≤ m) (m'_pos : 1 ≤ m')
    (ht : t < (X.block m).tiles) (ht₂ : t₂ < (X.block m').tiles) (hi : i < 14) (same : X.gid m t = X.gid m' t₂)
    (glued : (X.block m).glue t i = some (u, j)) (glued₂ : (X.block m').glue t₂ i = some (u₂, j₂)) :
    X.gid m u = X.gid m' u₂ ∧ j = j₂ := by
  -- the far tiles are actual tiles
  have far := (X.glue_ok m_pos ht hi glued).1
  -- in both blocks
  have far₂ := (X.glue_ok m'_pos ht₂ hi glued₂).1
  -- both gluings, seen in X_{m+m'}, which contains both blocks: the gluing in X_m
  have lift := X.glue_lift m_pos ht glued m'
  -- and the gluing in X_{m'}
  have lift₂ := X.glue_lift m'_pos ht₂ glued₂ m
  -- the tile keeps its number up there, from X_m
  have tile := X.gid_up m_pos ht m'
  -- and from X_{m'}
  have tile₂ := X.gid_up m'_pos ht₂ m
  -- so do the far tiles, from X_m
  have far_up := X.gid_up m_pos far m'
  -- and from X_{m'}
  have far_up₂ := X.gid_up m'_pos far₂ m
  rw [show m' + m = m + m' from Nat.add_comm _ _] at lift₂ tile₂ far_up₂
  -- the tile has the same number either way, so it is the same tile up there
  have same_tile : X.up m' m t₂ = X.up m m' t := by
    apply X.gid_inj (m := m + m') (by omega) tile₂.1 tile.1
    rw [tile₂.2, tile.2, same]
  rw [same_tile, lift] at lift₂
  -- so the two gluings agree: the same far tile, the same edge
  simp only [Option.some.injEq, Prod.mk.injEq] at lift₂
  obtain ⟨same_far, same_edge⟩ := lift₂
  refine ⟨?_, same_edge⟩
  rw [← far_up.2, ← far_up₂.2, same_far]

/-! ### Every edge is glued in some block, and finitely many edges in one block -/

/-- `X.GluedAt L g i`: the tile numbered `g` is a tile of X_L, and X_L glues its edge `e_i`. -/
def GluedAt (X : Chain) (L g i : Nat) : Prop := g < (X.block L).tiles ∧ ((X.block L).glue (X.loc L g) i).isSome

/-- An edge glued in X_L stays glued in every larger block. -/
theorem gluedAt_up (X : Chain) {L g i : Nat} (L_pos : 1 ≤ L) (glued : X.GluedAt L g i) (k : Nat) :
    X.GluedAt (L + k) g i := by
  obtain ⟨hg, is_glued⟩ := glued
  -- the tile of X_L numbered `g`
  have loc_bound := (X.gid_loc L g L_pos hg).1
  obtain ⟨⟨u, j⟩, glued⟩ := Option.isSome_iff_exists.mp is_glued
  refine ⟨?_, ?_⟩
  · -- larger blocks have more tiles
    have more := X.tiles_mono L_pos k
    omega
  · rw [X.loc_up L_pos hg, X.glue_lift L_pos loc_bound glued k]; rfl

/-- **Where the chain covers the plane, every edge of every tile is glued in some block.** -/
theorem gluedAt_exists (X : Chain) (covers : X.Covers) {g i : Nat} (hi : i < 14) : ∃ L, 1 ≤ L ∧ X.GluedAt L g i := by
  -- the tile numbered `g` is a tile of X_{g+1}
  have big := X.tiles_ge g
  -- found there
  obtain ⟨loc_bound, gid_of_loc⟩ := X.gid_loc (g + 1) g (by omega) (by omega)
  -- some block X_{g+1+k} glues its edge `e_i`
  obtain ⟨k, is_glued⟩ := covers (g + 1) _ i (by omega) loc_bound hi
  refine ⟨g + 1 + k, by omega, ?_, ?_⟩
  · -- larger blocks have more tiles
    have more := X.tiles_mono (m := g + 1) (by omega) k
    omega
  · rw [X.loc_up (by omega) (by omega)]; exact is_glued

/-- If each of finitely many claims holds from some level on, all of them hold from one level on. -/
theorem exists_common {P : Nat → Nat → Prop} (mono : ∀ L k x, P L x → P (L + k) x) :
    ∀ n, (∀ x, x < n → ∃ L, P L x) → ∃ L, ∀ x, x < n → P L x
  | 0, _ => ⟨0, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩
  | n + 1, each => by
    -- a common level for the first `n`
    obtain ⟨L₁, below⟩ := exists_common mono n (fun x hx => each x (by omega))
    -- a level for the last one
    obtain ⟨L₂, at_n⟩ := each n (by omega)
    refine ⟨L₁ + L₂, fun x hx => ?_⟩
    by_cases earlier : x < n
    · exact mono L₁ L₂ x (below x earlier)
    · have is_n : x = n := by omega -- the last one
      subst is_n
      rw [Nat.add_comm]; exact mono L₂ L₁ x at_n

/-- **All edges of the first `M` tiles are glued in one block** X_L, which contains those tiles. -/
theorem all_glued_at (X : Chain) (covers : X.Covers) (M : Nat) :
    ∃ L, 1 ≤ L ∧ M ≤ (X.block L).tiles ∧ ∀ g i, g < M → i < 14 → X.GluedAt L g i := by
  -- number the edges `e_i` of the tiles `g < M` as `14 g + i`, and find one level for all of them
  obtain ⟨L, all⟩ := exists_common (P := fun L x => X.GluedAt (L + 1) (x / 14) (x % 14))
    (fun L k x glued => by
      rw [show L + k + 1 = L + 1 + k by omega]
      exact X.gluedAt_up (by omega) glued k)
    (14 * M) (fun x _ => by
      obtain ⟨L, L_pos, glued⟩ := X.gluedAt_exists covers (g := x / 14) (Nat.mod_lt x (by decide))
      exact ⟨L - 1, by rw [show L - 1 + 1 = L by omega]; exact glued⟩)
  -- go up `M` more levels, so that the block has at least `M` tiles
  refine ⟨L + 1 + M, by omega, ?_, fun g i hg hi => ?_⟩
  · have big := X.tiles_ge (L + M) -- X_{L+M+1} has at least `L + M + 2` tiles
    rw [show L + 1 + M = L + M + 1 by omega]
    omega
  · -- the edge `14 g + i`
    have glued := all (14 * g + i) (by omega)
    rw [show (14 * g + i) / 14 = g by omega, show (14 * g + i) % 14 = i by omega] at glued
    exact X.gluedAt_up (by omega) glued M

end Chain

/-! ### Any tiling as a strand system -/

/-- `T` glues every edge of every tile to an edge of a different tile, and that edge back to it. -/
def IsTiling (T : Tiling) : Prop :=
  ∀ g i, i < 14 → ∃ g' j, T.glue g i = some (g', j) ∧ g' ≠ g ∧ j < 14 ∧ T.glue g' j = some (g, i)

/-- Across every port of a tiling there is a port of another tile, and across that one lies the first. -/
theorem tilingAcross_some {T : Tiling} (tiling : IsTiling T) {p : Port} (hp : p.2.1 < 14) :
    ∃ q, T.across p = some q ∧ q.2.1 < 14 ∧ q.1 ≠ p.1 ∧ T.across q = some p := by
  obtain ⟨g, i, s⟩ := p
  simp only at hp
  cases s with
  | true =>
    -- port `R(v_i)` lies on edge `e_i`
    obtain ⟨g', j, glued, other, hj, back⟩ := tiling g i hp
    refine ⟨(g', j, true), ?_, hj, other, ?_⟩
    · show (T.glue g i).map _ = _
      rw [glued]; rfl
    · show (T.glue g' j).map _ = _
      rw [back]; rfl
  | false =>
    -- port `L(v_i)` lies on edge `e_{i-1}`
    obtain ⟨g', j, glued, other, hj, back⟩ := tiling g ((i + 13) % 14) (by omega)
    refine ⟨(g', (j + 1) % 14, false), ?_, Nat.mod_lt _ (by omega), other, ?_⟩
    · show (T.glue g ((i + 13) % 14)).map _ = _
      rw [glued]; rfl
    · show (T.glue g' (((j + 1) % 14 + 13) % 14)).map _ = _
      -- vertex `i - 1`, then one on, is vertex `i` again
      have round : ((i + 13) % 14 + 1) % 14 = i := by omega
      rw [mod14 hj, back]
      simp only [Option.map_some, round]

/-- **A tiling's ports, with its two pairings**: the two ends of a piece (`pieceEnd`), and straight across an edge.
Both pair every port with a different port, and undo themselves. -/
def tilingSys {T : Tiling} (tiling : IsTiling T) : StrandSystem NPort where
  inside x := ⟨pieceEnd x.1, (pieceEnd_valid x.2).2⟩
  across x := ⟨(T.across x.1).getD x.1, by
    obtain ⟨q, across_x, q_valid, _, _⟩ := tilingAcross_some tiling x.2
    rw [across_x]; exact q_valid⟩
  inside_inside x := Subtype.ext (Patch.pieceEnd_pieceEnd x.1)
  across_across x := by
    obtain ⟨q, across_x, _, _, back⟩ := tilingAcross_some tiling x.2
    apply Subtype.ext
    show (T.across ((T.across x.1).getD x.1)).getD ((T.across x.1).getD x.1) = x.1
    rw [across_x]
    simp only [Option.getD_some, back]
  inside_ne x same := pieceEnd_ne x.1 (congrArg Subtype.val same)
  across_ne x same := by
    obtain ⟨q, across_x, _, other, _⟩ := tilingAcross_some tiling x.2
    -- the port across lies on another tile
    have same_tile := congrArg (fun y : NPort => y.1.1) same
    simp only [across_x, Option.getD_some] at same_tile
    exact other same_tile

namespace Chain

/-! ### The union of the chain is a tiling -/

/-- **A gluing that contains every block** (chosen, not computed). For the tile numbered `g` and its edge `e_i`: if
some block X_{g+1+k} glues that edge, read the gluing off one such block (`Classical.choose` picks the `k`);
otherwise nothing is glued. -/
noncomputable def chainGlue (X : Chain) (g i : Nat) : Option (Nat × Nat) :=
  open Classical in
  if found : ∃ k, ((X.block (g + 1 + k)).glue (X.loc (g + 1 + k) g) i).isSome then
    ((X.block (g + 1 + Classical.choose found)).glue (X.loc (g + 1 + Classical.choose found) g) i).map
      fun e => (X.gid (g + 1 + Classical.choose found) e.1, e.2)
  else none

/-- The tile numbered `X.gid m t`, found in X_{m+k}, is tile `t` taken `k` levels up. -/
theorem loc_gid_up (X : Chain) {m t : Nat} (m_pos : 1 ≤ m) (ht : t < (X.block m).tiles) (k : Nat) :
    X.loc (m + k) (X.gid m t) = X.up m k t := by
  -- tile `t` taken up keeps its number
  obtain ⟨up_bound, gid_of_up⟩ := X.gid_up m_pos ht k
  -- so `X.loc (m + k)` finds it
  have found := (X.loc_gid (m + k) _ (by omega) up_bound).2
  rw [gid_of_up] at found
  exact found

/-- **The tiling glued by `chainGlue`.** -/
noncomputable def chainTiling (X : Chain) : Tiling := ⟨X.chainGlue⟩

/-- **`chainTiling` contains every block.** -/
theorem chainTiling_contains (X : Chain) : X.Contains X.chainTiling := by
  intro m t i t' j m_pos ht hi glued
  show X.chainGlue (X.gid m t) i = some (X.gid m t', j)
  -- the far tile is an actual tile
  have far := (X.glue_ok m_pos ht hi glued).1
  -- the number of the tile
  generalize number : X.gid m t = g
  -- the tile numbered `g` is a tile of X_{g+1}
  have big := X.tiles_ge g
  -- the edge is glued in some block above X_{g+1}: in X_{g+1+m}, which also lies above X_m
  have found : ∃ k, ((X.block (g + 1 + k)).glue (X.loc (g + 1 + k) g) i).isSome := by
    refine ⟨m, ?_⟩
    rw [show g + 1 + m = m + (g + 1) by omega, ← number, X.loc_gid_up m_pos ht, X.glue_lift m_pos ht glued]
    rfl
  unfold chainGlue
  rw [dite_eq_left found]
  -- the block that `chainGlue` reads glues the edge
  have spec := Classical.choose_spec found
  generalize Classical.choose found = k at spec ⊢
  obtain ⟨⟨u, j₂⟩, glued₂⟩ := Option.isSome_iff_exists.mp spec
  -- there the tile numbered `g` is found
  obtain ⟨loc_bound, gid_of_loc⟩ := X.gid_loc (g + 1 + k) g (by omega)
    (by have more := X.tiles_mono (m := g + 1) (by omega) k; omega) -- X_{g+1+k} is at least as large as X_{g+1}
  -- and X_m and that block glue the edge alike
  have agree := X.glue_agree m_pos (by omega) ht loc_bound hi (by rw [number, gid_of_loc]) glued glued₂
  rw [glued₂, agree.1, agree.2]
  rfl

/-- **Where the chain covers the plane, a gluing that contains every block is a tiling**: every edge of every tile is
glued, to an edge of another tile, which is glued back. -/
theorem isTiling (X : Chain) (covers : X.Covers) {T : Tiling} (contains : X.Contains T) : IsTiling T := by
  intro g i hi
  -- some block X_L glues the edge
  obtain ⟨L, L_pos, hg, is_glued⟩ := X.gluedAt_exists covers (g := g) hi
  obtain ⟨⟨t', j⟩, glued⟩ := Option.isSome_iff_exists.mp is_glued
  -- the tile numbered `g` in X_L
  obtain ⟨loc_bound, gid_of_loc⟩ := X.gid_loc L g L_pos hg
  -- the far tile and edge are actual ones
  obtain ⟨far, hj⟩ := X.glue_ok L_pos loc_bound hi glued
  refine ⟨X.gid L t', j, ?_, ?_, hj, ?_⟩
  · -- `T` glues as X_L does
    have read := contains L _ i t' j L_pos loc_bound hi glued
    rwa [gid_of_loc] at read
  · -- X_L glues no tile to itself, and different tiles have different numbers
    intro same
    -- the far tile differs from the tile
    have differ := super_noSelf L (X.K L) _ i t' j loc_bound hi glued
    exact differ (X.gid_inj L_pos far loc_bound (same.trans gid_of_loc.symm))
  · -- X_L glues the edge back, and `T` reads that too
    have back := super_glueSymm L (X.K L) _ i t' j loc_bound hi glued
    -- read by `T`
    have read := contains L t' j _ i L_pos far hj back
    rwa [gid_of_loc] at read

/-! ### The blocks inside the tiling -/

/-- Port `p` of X_m, as a port of the whole tiling. -/
def gP (X : Chain) (m : Nat) (p : Port) : Port := (X.gid m p.1, p.2.1, p.2.2)

/-- The other end of a piece, before or after renumbering. -/
theorem pieceEnd_gP (X : Chain) (m : Nat) (p : Port) : pieceEnd (X.gP m p) = X.gP m (pieceEnd p) := by
  obtain ⟨t, i, s⟩ := p
  rcases i with _ | _ | i <;> rfl

/-- Across a port of X_m, the tiling continues as X_m does. -/
theorem across_gP (X : Chain) {T : Tiling} (contains : X.Contains T) {m : Nat}
    (m_pos : 1 ≤ m) {p q : Port} (p_port : (X.block m).IsPort p) (across_p : (X.block m).across p = some q) :
    T.across (X.gP m p) = some (X.gP m q) := by
  obtain ⟨t, i, s⟩ := p
  obtain ⟨ht, hi⟩ := p_port
  simp only at ht hi
  -- the port, renumbered
  have renumbered : X.gP m (t, i, s) = (X.gid m t, i, s) := rfl
  rw [renumbered]
  cases s with
  | true =>
    simp only [Patch.across, straightThrough] at across_p
    cases glued : (X.block m).glue t i with
    | none => rw [glued] at across_p; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_p
      simp only [Option.map_some, Option.some.injEq] at across_p
      subst across_p
      show (T.glue (X.gid m t) i).map _ = _
      rw [contains m t i t' j m_pos ht hi glued]; rfl
  | false =>
    simp only [Patch.across, straightThrough] at across_p
    cases glued : (X.block m).glue t ((i + 13) % 14) with
    | none => rw [glued] at across_p; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_p
      simp only [Option.map_some, Option.some.injEq] at across_p
      subst across_p
      show (T.glue (X.gid m t) ((i + 13) % 14)).map _ = _
      rw [contains m t _ t' j m_pos ht (by omega) glued]; rfl

/-! ### No closed strand -/

/-- A strand of the tiling cannot stay among the first `M` tiles if all their edges are glued in one block X_L:
following it from a port of X_L would never reach the rim of X_L. -/
theorem follow_stays (X : Chain) {T : Tiling} (contains : X.Contains T)
    (tiling : IsTiling T) {L M : Nat} (L_pos : 1 ≤ L) (all_glued : ∀ g i, g < M → i < 14 → X.GluedAt L g i) :
    ∀ p r, (X.block L).Follow p r → (X.block L).IsPort p →
      ∀ x : NPort, X.gP L p = x.1 → (∀ k, ((tilingSys tiling).walk x k).1.1 < M) → False := by
  -- X_L has the signature
  have sig := (good L (X.K L) L_pos).sig
  intro p r follows
  induction follows with
  | @leave p nothing_across =>
    intro p_port x x_eq bounded
    -- the tile of `p` is among the first `M`
    have below : X.gid L p.1 < M := by
      -- the strand starts at `x`, on one of them
      have start := bounded 0
      change x.1.1 < _ at start
      rw [← x_eq] at start; exact start
    -- X_L finds the tile of `p` by its number
    have found := (X.loc_gid L p.1 L_pos p_port.1).2
    -- every edge of it is glued in X_L
    have edges_glued : ∀ i, i < 14 → ((X.block L).glue p.1 i).isSome := by
      intro i hi
      have glued := (all_glued _ i below hi).2 -- glued at the tile numbered `X.gid L p.1`
      rwa [found] at glued
    -- the other end of the piece is on the same tile
    have end_valid := pieceEnd_valid p_port.2
    -- so something lies across it, yet the strand leaves X_L there
    have across_end := across_isSome edges_glued end_valid.1 end_valid.2
    rw [nothing_across] at across_end
    contradiction
  | @next p q r across_end _ ih =>
    intro p_port x x_eq bounded
    -- the other end of the piece is on the same tile
    have end_valid := pieceEnd_valid p_port.2
    -- so it is a port of X_L
    have end_port : (X.block L).IsPort (pieceEnd p) := ⟨end_valid.1 ▸ p_port.1, end_valid.2⟩
    -- and so is the port `q` across from it
    have q_port : (X.block L).IsPort q := Patch.across_valid sig end_port.1 end_port.2 across_end
    -- `q` is the next port of the strand in the tiling
    have next_is : ((tilingSys tiling).next x).1 = X.gP L q := by
      show (T.across (pieceEnd x.1)).getD (pieceEnd x.1) = _
      rw [← x_eq, X.pieceEnd_gP, X.across_gP contains L_pos end_port across_end]
      rfl
    -- the strand from there is the rest of the strand from `x`
    refine ih q_port ((tilingSys tiling).next x) next_is.symm (fun k => ?_)
    -- its ports are ports of the strand from `x`, so on the first `M` tiles
    have later := bounded (k + 1)
    rw [StrandSystem.walk, iter_succ'] at later
    exact later

/-- **No strand of the tiling is closed.** A closed strand visits finitely many tiles; all their edges are glued in
one block, and following the strand there never reaches the rim, against Theorem A. -/
theorem not_closed (X : Chain) (covers : X.Covers) {T : Tiling} (contains : X.Contains T)
    (tiling : IsTiling T) (x : NPort) : ¬ (tilingSys tiling).Closed x := by
  rintro ⟨n, n_pos, back⟩
  -- the strand only ever visits the ports reached in its first `n` steps
  have periodic : ∀ k, ∃ j, j < n ∧ (tilingSys tiling).walk x k = (tilingSys tiling).walk x j := by
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
  have bounded : ∀ m, ∃ M, ∀ j, j < m → ((tilingSys tiling).walk x j).1.1 < M := by
    intro m
    induction m with
    | zero => exact ⟨0, fun j hj => absurd hj (by omega)⟩
    | succ m ih =>
      obtain ⟨M, below⟩ := ih
      refine ⟨M + ((tilingSys tiling).walk x m).1.1 + 1, fun j hj => ?_⟩
      by_cases earlier : j < m
      · have := below j earlier -- an earlier port: below `M`
        omega
      · have is_m : j = m := by omega -- port `m` itself
        subst is_m; omega
  obtain ⟨M, below⟩ := bounded n
  -- every port of the strand is on one of the first `M` tiles
  have in_first : ∀ k, ((tilingSys tiling).walk x k).1.1 < M := by
    intro k
    obtain ⟨j, hj, same⟩ := periodic k
    rw [same]; exact below j hj
  -- one block X_L glues every edge of those tiles, and contains them
  obtain ⟨L, L_pos, M_le, all_glued⟩ := X.all_glued_at covers M
  -- the start `x`, as a port of X_L
  obtain ⟨loc_bound, gid_of_loc⟩ := X.gid_loc L x.1.1 L_pos (by have := in_first 0; exact Nat.lt_of_lt_of_le this M_le)
  -- it is a port of X_L
  have start : (X.block L).IsPort (X.loc L x.1.1, x.1.2.1, x.1.2.2) := ⟨loc_bound, x.2⟩
  -- Theorem A says the strand leaves X_L
  obtain ⟨r, follows⟩ := theoremA L (X.K L) _ start
  refine X.follow_stays contains tiling L_pos all_glued _ r follows start x ?_ in_first
  show (X.gid L (X.loc L x.1.1), x.1.2.1, x.1.2.2) = x.1
  rw [gid_of_loc]

end Chain

/-! ### The theorems -/

/-- **`ChainModel`**: the union of a chain is a tiling. -/
theorem chainModel : ChainModel := fun X =>
  ⟨fun g => by
    -- X_{g+1} has at least `g + 2` tiles
    have := X.tiles_ge g
    omega,
   fun m t m_pos ht => X.loc_gid m t m_pos ht,
   fun m g m_pos hg => X.gid_loc m g m_pos hg,
   fun _ _ m_pos ht => (X.gid_up1 m_pos ht).2,
   ⟨X.chainTiling, X.chainTiling_contains⟩,
   fun covers _ contains => X.isTiling covers contains⟩

/-- **Theorem A in strand form** (as stated in `Statement.lean`): in a tiling whose hierarchy covers the plane, every
strand is a two-way infinite path. -/
theorem theoremA_strand : TheoremA_strand := by
  intro X T covers contains p hp
  -- the union of the chain is a tiling
  have tiling := X.isTiling covers contains
  -- its strand system, and the start
  let S := tilingSys tiling
  let start : NPort := ⟨p, hp⟩
  -- following the strand forwards, as ports
  have forwards : ∀ k, iter T.forward k p = (S.walk start k).1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih]; rfl
  -- and backwards
  have backwards : ∀ k, iter T.backward k p = (iter S.prev k start).1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih]; rfl
  -- Lemma 3.4: the strand is closed or a two-way infinite path; it is not closed
  obtain ⟨distinct, apart, no_piece_twice⟩ :=
    (S.closed_or_path start).resolve_left (X.not_closed covers contains tiling start)
  -- going back `d` steps never returns to the start, unless `d = 0`
  have back_ne : ∀ d, iter S.prev d start = start → d = 0 := fun d back_at_start =>
    (apart d 0 back_at_start).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) forwards, no port twice
    intro i j same
    rw [forwards, forwards] at same
    exact distinct i j (Subtype.ext same)
  · -- (2) backwards, no port twice: undo the shorter walk back
    intro a a' same
    rw [backwards, backwards] at same
    -- the same ports of the tiling
    have same' := Subtype.ext same
    rcases Nat.le_total a a' with le | le
    · obtain ⟨d, rfl⟩ : ∃ d, a' = a + d := ⟨a' - a, by omega⟩
      rw [iter_add] at same'
      -- go `a` steps forwards from both
      have undone := congrArg (iter S.next a) same'
      rw [S.forward_back, S.forward_back] at undone
      -- so going `d` steps back returns to the start: `d = 0`
      have := back_ne d undone.symm
      omega
    · obtain ⟨d, rfl⟩ : ∃ d, a = a' + d := ⟨a - a', by omega⟩
      rw [iter_add] at same'
      -- go `a'` steps forwards from both
      have undone := congrArg (iter S.next a') same'
      rw [S.forward_back, S.forward_back] at undone
      -- so going `d` steps back returns to the start: `d = 0`
      have := back_ne d undone
      omega
  · -- (3) backwards never meets forwards, except at the start
    intro a b same
    rw [backwards, forwards] at same
    exact apart a b (Subtype.ext same)
  · -- (4) no piece twice
    intro i j same
    rw [forwards, forwards] at same
    exact no_piece_twice i j (Subtype.ext same)

/-! ### The nest is a chain that covers -/

/-- **The nest as a chain**: every block a Δ, child 1 of the next (Table 1: child 1 of a Δ is a Δ). -/
def nestChain : Chain where
  K _ := .Delta
  c _ := 1
  child_lt _ _ := show 1 < (Pattern.kids .Delta).length by decide
  child_kind _ _ := rfl

/-- In the nest chain, a block starts where it does in the nest: after child 0, a Ξ. -/
theorem nestChain_shift (b : Nat) : nestChain.shift b = nestShift b := rfl

/-- In the nest chain, a tile goes up as in the nest. -/
theorem nestChain_up : ∀ k b t, nestChain.up b k t = up b k t
  | 0, _, _ => rfl
  | k + 1, b, t => by
    show nestChain.up (b + 1) k (t + nestChain.shift b) = up (b + 1) k (t + nestShift b)
    rw [nestChain_shift]
    exact nestChain_up k (b + 1) _

/-- **`NestCovers`** (as stated in `Statement.lean`): the nest chain covers, since every edge of `N_b` is glued in
`N_{b+2}` (`no_boundary`, the paper's Lemma 8.3(b)). -/
theorem nestCovers : NestCovers := by
  refine ⟨nestChain, fun _ => ⟨rfl, rfl⟩, fun b t i b_pos ht hi => ⟨2, ?_⟩⟩
  -- two levels up, as in the nest
  rw [nestChain_up]
  -- where the edge is glued
  exact no_boundary b_pos ht hi

end SpectreKnot.Statement

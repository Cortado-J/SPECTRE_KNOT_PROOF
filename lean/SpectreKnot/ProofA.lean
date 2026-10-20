/-
**Theorem A** (`theoremA`): no supertile of any level or kind contains a closed strand.

The induction of Thm 7.6, at tile level: every level-`m` supertile (`m ≥ 1`) has the signature, with its corners
`A`, `B` at the positions `aPos m K`, `bPos m K` and its vertices where the side lengths ℓ_m put them (`Good m K`).
Level 1 is the kernel's check of the nine clusters (`good_one`, Computation 7.5). From level `m` to `m + 1`: the
children have the signature, the composition has it by Prop 7.4 (`prop_7_4`), so the parent has it (`Kids.parent_sig`),
with its corners where Table 3 puts the Γ child's corners (`aPos_succ`, `bPos_succ`). Level 0 is a tile, which has the
signature (`tile_hasSig`, Lemma 4.4).

On the way, two statements in the paper's terms: side `j` of `super m K` has `ℓ_m(K, j)` edges (`super_side_length`,
Prop 6.1 for the supertiles themselves), and the corner `A` of a supertile is that of its Γ child (`cornerA_succ`, the
paper's definition of `A`, §2.3).
-/
import SpectreKnot.ParentSig

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- `pos f J` depends only on the side lengths before `J`. -/
theorem pos_congr {f g : Nat → Nat} : ∀ J, (∀ i, i < J → f i = g i) → pos f J = pos g J
  | 0, _ => rfl
  | J + 1, agree => by rw [pos_succ, pos_succ, pos_congr J (fun i i_lt => agree i (by omega)), agree J (by omega)]

/-- `totL` is the sum of the side lengths of the pieces. -/
theorem totL_eq (L : Nat → Nat → Nat) : ∀ l : List (Nat × Nat), totL L l = (l.map fun p => L p.1 p.2).sum
  | [] => rfl
  | (c, j) :: rest => by simp only [totL, List.map_cons, List.sum_cons, totL_eq L rest]

/-- The side lengths of the children in a composition of level-`m` supertiles. -/
abbrev Lk (m : Nat) (T : Kind) (c j : Nat) : Nat := letterLen m (letterOf (kidAt T c) j)

/-- The parent's sides have the lengths ℓ_{m+1} (Prop 2.4(c) with Prop 6.1). -/
theorem parentLen_eq {m : Nat} (m_pos : 1 ≤ m) (T : Kind) {J : Nat} (J_lt : J < 6) :
    parentLen T (Lk m T) J = lenAt (m + 1) T J := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [lenAt, ← sideLen_eq_letterLen (m' + 2) (by omega) T J J_lt]
  simp only [sideLen, parentLen, totL_eq]
  congr 1
  apply List.map_congr_left
  intro p mem
  rw [sideLen_eq_letterLen (m' + 1) (by omega) _ _ (pieces_valid T J J_lt p mem)]

/-- The parent's vertices sit where the lengths ℓ_{m+1} put them. -/
theorem vpos_eq {m : Nat} (m_pos : 1 ≤ m) (T : Kind) {J : Nat} (J_le : J ≤ 6) :
    vpos (m + 1) T J = pos (parentLen T (Lk m T)) J :=
  pos_congr J (fun i i_lt => (parentLen_eq m_pos T (by omega)).symm)

/-! ### The induction -/

/-- The children of a composition of level-`m` supertiles satisfy the bridge's hypotheses. -/
theorem kids_at {m : Nat} (m_pos : 1 ≤ m) (T : Kind) (good_m : ∀ K, Good m K) :
    Kids T (fun c => super m (kidAt T c)) (Lk m T) (dOff m) (ori m) (ori m) where
  len_pos c j := by
    -- every side is at least 5 long (Lemma 6.5)
    have := (bounds m m_pos).1 (letterOf (kidAt T c) j)
    simp only [Lk]; omega
  pair c c_lt j j_lt c' j' adj_eq := by simp only [Lk, pair_letter c_lt j_lt adj_eq]
  shape c _ := ⟨(good_m (kidAt T c)).vtx, (good_m (kidAt T c)).len⟩
  sig c c_lt := by
    -- the child has the signature at `aPos`, `bPos`
    have has_sig := (good_m (kidAt T c)).sig
    -- which is where the composition puts its corner `A`
    have A_eq : (Comp.ofLens T (Lk m T) (dOff m) (ori m)).toGluing.A c = aPos m (kidAt T c) := by
      rw [ofLens_A c_lt]; rfl
    -- and its corner `B`
    have B_eq : (Comp.ofLens T (Lk m T) (dOff m) (ori m)).toGluing.B c = bPos m (kidAt T c) := by
      rw [ofLens_B c_lt, A_eq]; rfl
    rw [A_eq, B_eq]; exact has_sig
  csig := prop_7_4 m m_pos T (ori m)

/-- The orientation flips from each level to the next. -/
theorem ori_succ (m : Nat) : ori (m + 1) = !ori m := by
  simp only [ori]
  rcases Nat.mod_two_eq_zero_or_one m with even | odd
  · have succ_odd : (m + 1) % 2 = 1 := by omega -- `m` even, so `m + 1` odd
    simp [even, succ_odd]
  · have succ_even : (m + 1) % 2 = 0 := by omega -- `m` odd, so `m + 1` even
    simp [odd, succ_even]

/-- **The parent's corner `A`**: where the induction puts it (`aPos`, Lemma 6.4) is the rim position `cA` of its Γ
child's corner `A` (Table 3). For a Σ parent, `d_{m+1}` is the length of the pieces `0.2`, `0.1`, `7.0`. -/
theorem aPos_succ {m : Nat} (m_pos : 1 ≤ m) (T : Kind) : aPos (m + 1) T = cA T (Lk m T) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  by_cases is_sigma : T = .Sigma
  · subst is_sigma
    -- `d_{m+1}` is the length of the first three pieces of side 5
    have dOff_eq :
        dOff (m' + 2) = Lk (m' + 1) .Sigma 0 2 + Lk (m' + 1) .Sigma 0 1 + Lk (m' + 1) .Sigma 7 0 := by
      simp only [dOff, sigma_side5_start.1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Lk]
      rw [sideLen_eq_letterLen _ (by omega) _ 2 (by omega), sideLen_eq_letterLen _ (by omega) _ 1 (by omega),
        sideLen_eq_letterLen _ (by omega) _ 0 (by omega)]
      omega
    simp only [aPos, cA]
    rw [vpos_eq m_pos _ (by omega), ← totL_take _ _ 5 (by omega), preS_eq, totL_append, dOff_eq]
    simp [totL]; omega
  · simp only [aPos, cA, ite_eq_right is_sigma]

/-- **The parent's corner `B`**: where the induction puts it (`bPos`, `B = A + ω_{m+1}`) is the rim position `cB`
of its Γ child's corner `B`. -/
theorem bPos_succ {m : Nat} (m_pos : 1 ≤ m) (T : Kind) : bPos (m + 1) T = cB T (Lk m T) (ori m) := by
  simp only [bPos, cB, aPos_succ m_pos T, ori_succ]
  rw [vpos_eq m_pos T (Nat.le_refl _), ← rimN_eq]

/-- **The induction step**: if every level-`m` supertile has the signature, so does every level-`(m+1)` one. -/
theorem good_succ {m : Nat} (m_pos : 1 ≤ m) (good_m : ∀ K, Good m K) (T : Kind) : Good (m + 1) T := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the children satisfy the bridge's hypotheses
  have kids := kids_at m_pos T good_m
  -- the parent is the composition of its children
  have super_eq : super (m' + 1 + 1) T = compose T fun c => super (m' + 1) (kidAt T c) := rfl
  -- the parent's rim length is where its vertex 6 sits
  have rim_len : rimN T (Lk (m' + 1) T) = vpos (m' + 1 + 1) T 6 := by
    rw [rimN_eq, vpos_eq m_pos T (Nat.le_refl _)]
  -- the parent's vertices sit where the lengths ℓ_{m+1} put them
  have vtx_eq :
      (compose T fun c => super (m' + 1) (kidAt T c)).vtx = (List.range 7).map (vpos (m' + 1 + 1) T) := by
    rw [parent_vtx kids.shape]
    apply List.map_congr_left
    intro J J_mem
    rw [vpos_eq m_pos T (by rw [List.mem_range] at J_mem; omega)]
  -- the parent's rim length
  have len_eq : (compose T fun c => super (m' + 1) (kidAt T c)).E = vpos (m' + 1 + 1) T 6 := by
    rw [compose_E kids.shape, rim_len]
  refine ⟨?_, by rw [super_eq]; exact vtx_eq, by rw [super_eq]; exact len_eq⟩
  -- the parent has the signature at its Γ child's corners, which are where the induction puts them
  rw [super_eq, ori_succ, bPos_succ m_pos T, aPos_succ m_pos T]
  exact kids.parent_sig

/-- **Thm 7.6, at tile level**: every supertile of level `m ≥ 1` has the signature. -/
theorem good : ∀ m K, 1 ≤ m → Good m K := by
  intro m
  induction m with
  | zero => intro K one_le_zero; omega
  | succ m ih =>
    intro K _
    rcases Nat.eq_zero_or_pos m with rfl | m_pos
    · exact good_one K
    · exact good_succ m_pos (fun K' => ih K' m_pos) K

/-- **Prop 6.1 for the supertiles themselves** (`m ≥ 1`): side `j` of `super m K` has `ℓ_m(K, j)` edges, the length
`letterLen m` of its letter (Table 4); this is also `sideLen m K j`, the count by Table 3 (`sideLen_eq_letterLen`). -/
theorem super_side_length {m : Nat} (m_pos : 1 ≤ m) (K : Kind) {j : Nat} (j_lt : j < 6) :
    ((super m K).side j).length = letterLen m (letterOf K j) ∧ letterLen m (letterOf K j) = sideLen m K j :=
  ⟨side_length (good m K m_pos).vtx (good m K m_pos).len j_lt, (sideLen_eq_letterLen m m_pos K j j_lt).symm⟩

/-- The claim's corner `A` (`cornerA`, placed by position as in Lemma 6.4) is the induction's (`aPos`), since
`d_m = 2 F_{3m+1}`. -/
theorem cornerA_eq_aPos {m : Nat} (m_pos : 1 ≤ m) (K : Kind) : cornerA m K = aPos m K := by
  -- vertex 5 lies where the side lengths put it
  have vtx5 : (super m K).vtx.getD 5 0 = vpos m K 5 := by rw [(good m K m_pos).vtx]; rfl
  unfold cornerA aPos
  rw [vtx5, (dOff_fib m m_pos).1]

/-- **The corner `A` of a supertile is that of its Γ child** (the paper's recursive definition of `A`, §2.3): for
`m ≥ 1`, the port `L` of `super (m + 1) T` at its corner `A` is the port `R` of its Γ child, the last child, at the
child's own corner `A`, with the child's tiles numbered as in the parent. (Parent and child are oriented oppositely, so
`R` and `L` swap.) -/
theorem cornerA_succ {m : Nat} (m_pos : 1 ≤ m) (T : Kind) :
    (super (m + 1) T).bport (ori (m + 1)) (cornerA (m + 1) T, false) =
      shiftP (fun c => super m (kidAt T c)) (nk T - 1) ((super m .Gamma).bport (ori m) (cornerA m .Gamma, true)) := by
  -- the children have the signature, with the side lengths of the composition
  have kids := kids_at m_pos T (fun K => good m K m_pos)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the parent is the composition of its children
  have super_eq : super (m' + 1 + 1) T = compose T fun c => super (m' + 1) (kidAt T c) := rfl
  -- the Γ child's corner `A` is its vertex 0
  have gamma_A : aPos (m' + 1) .Gamma = 0 := rfl
  -- the claim's corners are the induction's; the parent's is where Table 3 puts the Γ child's corner `A`
  rw [cornerA_eq_aPos (by omega) T, aPos_succ m_pos T, cornerA_eq_aPos m_pos .Gamma, gamma_A, super_eq, ori_succ,
    kids.bport_L kids.csig.cA_lt, kids.csig.at_A, gA_last (Nat.sub_lt (last_lt T) Nat.one_pos)]
  show shiftP _ _ ((super (m' + 1) (kidAt T (nk T - 1))).bport _ _) = _
  rw [kid_last T]

/-- **`compose` never falls back on a default** in the supertiles of the statement. Let `m ≥ 1` and let `(t, i)` be an
unglued edge of child `c` of `super (m + 1) T`. Then `compose` finds the edge on the child's rim list, at the one
position `k` that holds it, so `findIdx?`'s default is not used; and a side of the child that Table 2 glues to a side
of a sibling has as many edges as that side, so the lookup of the edge across stays inside it. (`glue_rim` says more:
across the edge, `compose` glues exactly what the abstract composition says.) -/
theorem compose_no_default {m : Nat} (m_pos : 1 ≤ m) (T : Kind) {c t i : Nat} (c_lt : c < nk T)
    (ht : t < (super m (kidAt T c)).tiles) (hi : i < 14) (unglued : (super m (kidAt T c)).glue t i = none) :
    (∃ k, (super m (kidAt T c)).rim.findIdx? (· == (t, i)) = some k ∧ (super m (kidAt T c)).edgeAt k = (t, i)) ∧
    ∀ j c' j', j < 6 → adjAt T c j = some (c', j') →
      ((super m (kidAt T c')).side j').length = ((super m (kidAt T c)).side j).length := by
  -- the children have the signature, with the side lengths of the composition
  have kids := kids_at m_pos T (fun K => good m K m_pos)
  -- in particular child `c`: its rim lists every unglued edge, each once
  have sig := (good m (kidAt T c) m_pos).sig
  refine ⟨?_, fun j c' j' j_lt glued => ?_⟩
  · obtain ⟨k, k_lt, at_k⟩ := sig.rim_all t i ht hi unglued
    -- the rim list's entries are the edges `edgeAt` gives
    have entry_eq : ∀ k', (k'_lt : k' < (super m (kidAt T c)).rim.length) →
        (super m (kidAt T c)).rim[k'] = (super m (kidAt T c)).edgeAt k' := fun k' k'_lt => by
      simp only [Patch.edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k'_lt, Option.getD_some]
    refine ⟨k, List.findIdx?_eq_some_iff_getElem.mpr ⟨k_lt, ?_, ?_⟩, at_k⟩
    · rw [entry_eq, at_k]; simp
    · intro j j_lt same_edge
      rw [entry_eq, beq_iff_eq] at same_edge
      -- an earlier position holding the edge would be `k` itself
      have := sig.rim_inj j k (by omega) k_lt (same_edge.trans at_k.symm)
      omega
  · -- the two sides have the lengths of their letters, which Table 2 pairs equally
    obtain ⟨c'_lt, j'_lt, _, _⟩ := adj_valid c_lt j_lt glued
    obtain ⟨vtx_eq, len_eq⟩ : (super m (kidAt T c)).vtx = (List.range 7).map (pos (Lk m T c)) ∧
        (super m (kidAt T c)).E = pos (Lk m T c) 6 := kids.shape c c_lt
    obtain ⟨vtx_eq', len_eq'⟩ : (super m (kidAt T c')).vtx = (List.range 7).map (pos (Lk m T c')) ∧
        (super m (kidAt T c')).E = pos (Lk m T c') 6 := kids.shape c' c'_lt
    rw [side_length vtx_eq' len_eq' j'_lt, side_length vtx_eq len_eq j_lt]
    exact kids.pair c c_lt j j_lt c' j' glued

/-- **Theorem A** (as stated in `Statement.lean`): for every level `m` and every kind `K`, the supertile
`super m K` contains no closed strand. -/
theorem theoremA : TheoremA := by
  intro m K
  rcases Nat.eq_zero_or_pos m with rfl | m_pos
  · exact tile_hasSig.noClosed
  · exact (good m K m_pos).sig.noClosed

/-! ### A negative control -/

/-- A one-tile patch with a made-up gluing (not a real one) that traps a ribbon: edges `e_5` and `e_3` are both glued
to `e_4`. -/
def loopPatch : Patch := ⟨1, fun _ i => if i = 5 ∨ i = 3 then some (0, 4) else none, [], []⟩

/-- **Negative control**: `NoClosedStrand` can fail, so `TheoremA` is not true by definition. In `loopPatch` the ribbon
from `L(v_5)` goes round `v_5` to `R(v_5)`, across `e_5` to `R(v_4)`, round `v_4` to `L(v_4)`, and across `e_3` back to
`L(v_5)`, for ever. -/
theorem loopPatch_closed : ¬ loopPatch.NoClosedStrand := by
  intro no_closed
  obtain ⟨r, follow⟩ := no_closed (0, 5, false) ⟨by decide, by decide⟩
  -- no finite walk starts at `L(v_5)` or `R(v_4)`: each only leads on to the other
  have key : ∀ p r, loopPatch.Follow p r → p ≠ (0, 5, false) ∧ p ≠ (0, 4, true) := by
    intro p r follow_pr
    induction follow_pr with
    | @leave p leaves =>
      constructor <;> rintro rfl <;> simp [loopPatch, Patch.across, straightThrough, pieceEnd] at leaves
    | @next p q r crosses _ ih =>
      constructor <;> rintro rfl
      · have q_eq : q = (0, 4, true) := by -- from `L(v_5)` the walk goes on to `R(v_4)`
          simp [loopPatch, Patch.across, straightThrough, pieceEnd] at crosses; exact crosses.symm
        exact ih.2 q_eq
      · have q_eq : q = (0, 5, false) := by -- from `R(v_4)` the walk goes on to `L(v_5)`
          simp [loopPatch, Patch.across, straightThrough, pieceEnd] at crosses; exact crosses.symm
        exact ih.1 q_eq
  exact (key _ _ follow).1 rfl

end SpectreKnot.Statement

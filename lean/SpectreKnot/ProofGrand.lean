/-
**The Grandparent Lemma** (`grandparent`, the paper's Lemma 8.3(a), at the vertices of tiles): for `b ≥ 1`, every
vertex of every tile of `N_b` is surrounded by tiles of `N_{b+2}`.

Every supertile is a disc at its rim (`chains_super`: the nine level-1 clusters by a kernel check, then
`Kids.rimChains` level by level). A vertex of a tile of `N_b` is surrounded in `N_b`, or lies on the chain about a rim
vertex `u` of `N_b` (`surrounded_or_chain`). Then an argument on the tables: the paper's proof of Lemma 8.3(b), carried
from edges to vertices. (For part (a) the paper argues instead from eq. (side2) and the disjointness of the closed sides
2 and 4 of `N_{b+1}`; the second case below replaces that step.)
* `u` not on the closed side 2 of `N_b`, which is child 1 of `N_{b+1}`: turning about vertex `u` of child 1 of the Δ
  composition comes round, in two steps inside a side (`side_cycle`), in three at a vertex (Table 2:
  `delta_cycles`); so the vertex is surrounded in `N_{b+1}` (`surrounded_off_side2`);
* `u` on the closed side 2: in `N_{b+1}` the vertex lies on the chain about a rim vertex well inside side 4 of
  `N_{b+1}` (child 1's side 2 is piece 16 of the rim, inside side 4, and its ends are junctions 16 and 17:
  `chain_stretch`, `chain_j16`, `chain_j17`); side 4 of child 1 of `N_{b+2}` is glued to child 3, so turning about that
  vertex comes round in two steps (`surrounded_side4`).
-/
import SpectreKnot.Turn
import SpectreKnot.ProofB

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### Every supertile is a disc at its rim -/

/-- The chain check, as a computation: from the start of the chain about each rim vertex, turning reaches its end
within `f` turns. -/
def Patch.chainCheck (P : Patch) (o : Bool) (f : Nat) : Bool :=
  (List.range P.E).all fun k => (List.range f).any fun n => P.turns n (P.sC o k) == some (P.fC o k)

/-- The chain check is sound. -/
theorem Patch.chainCheck_sound {P : Patch} {o : Bool} {f : Nat} (check : P.chainCheck o f = true) :
    P.RimChains o := by
  intro k k_lt
  simp only [Patch.chainCheck, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at check
  obtain ⟨n, _, found⟩ := check k k_lt
  exact ⟨n, found⟩

/-- The kernel's check passes for the nine level-1 supertiles. -/
theorem level1Chains : ∀ K, (level1 K).chainCheck (ori 1) 8 = true := by
  intro K; cases K <;> decide +kernel

/-- **Every supertile of level `m ≥ 1` is a disc at its rim.** -/
theorem chains_super : ∀ m K, 1 ≤ m → (super m K).RimChains (ori m) := by
  intro m
  induction m with
  | zero => intro K one_le_zero; omega
  | succ m ih =>
    intro K _
    rcases Nat.eq_zero_or_pos m with rfl | m_pos
    · exact Patch.chainCheck_sound (level1Chains K)
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      -- the children satisfy the bridge's hypotheses
      have kids := kids_at m_pos K (fun K' => good (m' + 1) K' m_pos)
      rw [ori_succ]
      exact kids.rimChains (fun c _ => ih (kidAt K c) m_pos)

/-! ### Turning about a child vertex by the tables -/

/-- One step of turning about vertex `j` of child `c` by Table 2 alone, in the sense of `bstep`: for clockwise
children, across the side that starts at the vertex, to the vertex of the sibling where that side ends; for
counter-clockwise children, across the side that ends at the vertex, to the vertex of the sibling where it starts. -/
def tstep (T : Kind) (o : Bool) (x : Nat × Nat) : Option (Nat × Nat) :=
  if o then adjAt T x.1 ((x.2 + 5) % 6) else (adjAt T x.1 x.2).map fun e => (e.1, (e.2 + 1) % 6)

/-- `n` such steps. -/
def tsteps (T : Kind) (o : Bool) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, x => some x
  | n + 1, x => (tstep T o x).bind (tsteps T o n)

/-- In the Δ composition, turning by Table 2 about vertex 0, 1, 4 or 5 of child 1 comes round in three steps, for
either orientation of the children. -/
theorem delta_cycles : ∀ o, ∀ j ∈ [0, 1, 4, 5], tsteps .Delta o 3 (1, j) = some (1, j) := by decide

section Lens

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- The gluing's `mate` at offset `r` in side `j` of child `c`, as Table 2 gives it. -/
theorem gmate (len_pos : ∀ c j, 1 ≤ L c j) {c j r c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6) (r_lt : r < L c j)
    (adj_eq : adjAt T c j = some (c', j')) :
    (Comp.ofLens T L d ω).toGluing.mate c (pos (L c) j + r) = some (c', pos (L c') j' + L c' j' - 1 - r) := by
  show (Comp.ofLens T L d ω).mate c (pos (L c) j + r) = _
  rw [ofLens_mate (fun c _ j _ => len_pos c j) c_lt j_lt r_lt, adj_eq]; rfl

/-- A side ends no later than the rim. -/
theorem side_end_le (f : Nat → Nat) {j : Nat} (j_lt : j < 6) : pos f j + f j ≤ pos f 6 := by
  rw [← pos_succ]; exact pos_mono f (by omega)

/-- A step by Table 2 is a step of the gluing, at the children's vertices. -/
theorem tstep_sound (len_pos : ∀ c j, 1 ≤ L c j)
    (pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j) {o : Bool}
    {c j c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6) (stepped : tstep T o (c, j) = some (c', j')) :
    c' < nk T ∧ j' < 6 ∧ bstep (Comp.ofLens T L d ω).toGluing o (c, pos (L c) j) = some (c', pos (L c') j') := by
  cases o
  · -- clockwise: across the first edge of side `j`, to the end of the side across
    simp only [tstep, Bool.false_eq_true, ite_false] at stepped
    cases adj_eq : adjAt T c j with
    | none => rw [adj_eq] at stepped; contradiction
    | some e =>
      rw [adj_eq] at stepped
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      obtain ⟨e_lt, e_side_lt, _, _⟩ := adj_valid c_lt j_lt adj_eq
      refine ⟨e_lt, Nat.mod_lt _ (by omega), ?_⟩
      -- the first edge of side `j` is glued to the last edge of the side across
      have mate_eq := gmate (d := d) (ω := ω) len_pos c_lt j_lt (len_pos c j) adj_eq
      rw [Nat.add_zero, Nat.sub_zero] at mate_eq
      simp only [bstep, Bool.false_eq_true, ite_false, mate_eq, Option.map_some, ofLens_E e_lt,
        nxt_last (len_pos e.1) e_side_lt]
  · -- counter-clockwise: across the last edge of side `j - 1`, to the start of the side across
    simp only [tstep, ite_true] at stepped
    -- the side before vertex `j`
    have prev_lt : (j + 5) % 6 < 6 := Nat.mod_lt _ (by omega)
    obtain ⟨c'_lt, j'_lt, _, _⟩ := adj_valid c_lt prev_lt stepped
    refine ⟨c'_lt, j'_lt, ?_⟩
    -- the side before vertex `j` has an edge
    have prev_len := len_pos c ((j + 5) % 6)
    -- the edge before vertex `j` is the last edge of side `j - 1`
    have before : prv (pos (L c) 6) (pos (L c) j) = pos (L c) ((j + 5) % 6) + (L c ((j + 5) % 6) - 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | j_pos
      · -- vertex 0: the edge before it is the last edge of side 5
        show prv (pos (L c) 6) 0 = pos (L c) 5 + (L c 5 - 1)
        -- the rim ends where side 5 does
        have last : pos (L c) 6 = pos (L c) 5 + L c 5 := pos_succ (L c) 5
        -- side 5 has an edge
        have len5' := len_pos c 5
        simp only [prv, ite_true]; omega
      · -- vertex `j ≥ 1`: the edge before it is the last edge of side `j - 1`
        obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
        rw [show (j₀ + 1 + 5) % 6 = j₀ by omega] at prev_len ⊢
        -- side `j₀` ends at vertex `j₀ + 1`
        have side_end := pos_succ (L c) j₀
        simp only [prv]; rw [ite_eq_right (by omega)]; omega
    -- which is glued to the first edge of the side across
    have mate_eq := gmate (d := d) (ω := ω) len_pos c_lt prev_lt (r := L c ((j + 5) % 6) - 1) (by omega) stepped
    rw [pair c c_lt _ prev_lt _ _ stepped] at mate_eq
    simp only [bstep, ite_true, ofLens_E c_lt, before, mate_eq, Option.some.injEq, Prod.mk.injEq, true_and]
    omega

/-- Steps by Table 2 are steps of the gluing, at the children's vertices. -/
theorem tsteps_sound (len_pos : ∀ c j, 1 ≤ L c j)
    (pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j) {o : Bool} :
    ∀ n {c j c' j' : Nat}, c < nk T → j < 6 → tsteps T o n (c, j) = some (c', j') →
      bsteps (Comp.ofLens T L d ω).toGluing o n (c, pos (L c) j) = some (c', pos (L c') j') := by
  intro n
  induction n with
  | zero => intro c j c' j' _ _ stepped; cases stepped; rfl
  | succ n ih =>
    intro c j c' j' c_lt j_lt stepped
    simp only [tsteps] at stepped
    cases step_eq : tstep T o (c, j) with
    | none => rw [step_eq] at stepped; contradiction
    | some y =>
      rw [step_eq] at stepped
      obtain ⟨c₁, j₁⟩ := y
      obtain ⟨c₁_lt, j₁_lt, first⟩ := tstep_sound (d := d) (ω := ω) len_pos pair c_lt j_lt step_eq
      simp only [bsteps, first, Option.bind_some]
      exact ih c₁_lt j₁_lt stepped

/-- **Inside a side, turning comes round in two steps**: about a vertex of child `c` strictly inside a side `j` that
is glued to a sibling, the gluing turns into the sibling and straight back. -/
theorem side_cycle (len_pos : ∀ c j, 1 ≤ L c j)
    (pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j) {o : Bool}
    {c j c' j' r : Nat} (c_lt : c < nk T) (j_lt : j < 6) (adj_eq : adjAt T c j = some (c', j')) (r_pos : 0 < r)
    (r_lt : r < L c j) :
    bsteps (Comp.ofLens T L d ω).toGluing o 2 (c, pos (L c) j + r) = some (c, pos (L c) j + r) := by
  -- the side across has the same length
  have same_len := pair c c_lt j j_lt c' j' adj_eq
  obtain ⟨c'_lt, j'_lt, _, back⟩ := adj_valid c_lt j_lt adj_eq
  -- side `j` ends no later than the rim
  have end_c := side_end_le (L c) j_lt
  -- and so does the side across
  have end_c' := side_end_le (L c') j'_lt
  cases o
  · -- clockwise: across the edge leaving the vertex, and back across the edge leaving the next
    -- the edge leaving the vertex is glued to the side across, `r` edges from its end
    have first := gmate (d := d) (ω := ω) len_pos c_lt j_lt r_lt adj_eq
    -- the edge leaving the vertex reached is glued back
    have second := gmate (d := d) (ω := ω) len_pos c'_lt j'_lt (r := L c j - r) (by omega) back
    -- the vertex reached
    have next1 : nxt (pos (L c') 6) (pos (L c') j' + L c' j' - 1 - r) = pos (L c') j' + (L c j - r) := by
      unfold nxt; rw [ite_eq_right (by omega)]; omega
    -- and the vertex reached back
    have next2 : nxt (pos (L c) 6) (pos (L c) j + L c j - 1 - (L c j - r)) = pos (L c) j + r := by
      unfold nxt; rw [ite_eq_right (by omega)]; omega
    simp only [bsteps, bstep, Bool.false_eq_true, ite_false, first, Option.map_some, Option.bind_some,
      ofLens_E c'_lt, next1, second, ofLens_E c_lt, next2]
  · -- counter-clockwise: across the edge arriving at the vertex, and back across the edge arriving at the next
    -- the edge before the vertex
    have prev0 : prv (pos (L c) 6) (pos (L c) j + r) = pos (L c) j + (r - 1) := by
      unfold prv; rw [ite_eq_right (by omega)]; omega
    -- is glued to the side across, `r - 1` edges from its end
    have first := gmate (d := d) (ω := ω) len_pos c_lt j_lt (r := r - 1) (by omega) adj_eq
    -- the edge before the vertex reached
    have prev1 : prv (pos (L c') 6) (pos (L c') j' + L c' j' - 1 - (r - 1)) = pos (L c') j' + (L c j - r - 1) := by
      unfold prv; rw [ite_eq_right (by omega)]; omega
    -- is glued back
    have second := gmate (d := d) (ω := ω) len_pos c'_lt j'_lt (r := L c j - r - 1) (by omega) back
    -- to the edge before the start vertex
    have back_eq : pos (L c) j + L c j - 1 - (L c j - r - 1) = pos (L c) j + r := by omega
    simp only [bsteps, bstep, ite_true, ofLens_E c_lt, prev0, first, Option.bind_some, ofLens_E c'_lt, prev1, second,
      back_eq]

end Lens

/-- **About a vertex of child 1 of the Δ composition off its side 2, turning comes round**: in two steps inside a
side, in three at a vertex (`delta_cycles`). -/
theorem child1_cycle {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool} (len_pos : ∀ c j, 1 ≤ L c j)
    (pair : ∀ c, c < nk .Delta → ∀ j, j < 6 → ∀ c' j', adjAt .Delta c j = some (c', j') → L c' j' = L c j)
    {u : Nat} (u_lt : u < pos (L 1) 6) (off_side2 : u < pos (L 1) 2 ∨ pos (L 1) 3 < u) :
    ∃ a, 0 < a ∧ bsteps (Comp.ofLens .Delta L d ω).toGluing o a (1, u) = some (1, u) := by
  obtain ⟨j, r, j_lt, r_lt, rfl⟩ := decomp (L 1) 6 (Nat.le_refl _) u u_lt
  -- side 2 ends where side 3 starts
  have side2_end : pos (L 1) 3 = pos (L 1) 2 + L 1 2 := pos_succ (L 1) 2
  rcases Nat.eq_zero_or_pos r with rfl | r_pos
  · -- at vertex `j`, which is not 2 or 3 (the ends of side 2): three steps by Table 2
    have j_mem : j ∈ [0, 1, 4, 5] := by
      rcases off_side2 with before | after
      · -- before side 2
        have j_lt2 : j < 2 := by
          refine Nat.lt_of_not_le fun two_le => ?_
          -- vertex `j` is at or after vertex 2
          have later := pos_mono (L 1) two_le
          omega
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      · -- after side 2
        have three_lt : 3 < j := by
          refine Nat.lt_of_not_le fun le_three => ?_
          -- vertex `j` is at or before vertex 3
          have earlier := pos_mono (L 1) le_three
          omega
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    refine ⟨3, by omega, ?_⟩
    rw [Nat.add_zero]
    exact tsteps_sound len_pos pair 3 (by decide) j_lt (delta_cycles o j j_mem)
  · -- inside side `j`, which is not side 2: two steps
    have j_ne : j ≠ 2 := by
      intro j_two; subst j_two; rcases off_side2 with before | after <;> omega
    cases adj_eq : adjAt .Delta 1 j with
    | none => exact absurd (adj_one_none j j_lt adj_eq) j_ne
    | some e => exact ⟨2, by omega, side_cycle len_pos pair (by decide) j_lt adj_eq r_pos r_lt⟩

/-- **Inside side 4 of child 1 of the Δ composition** (glued to child 3), turning comes round in two steps. -/
theorem side4_cycle {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool} (len_pos : ∀ c j, 1 ≤ L c j)
    (pair : ∀ c, c < nk .Delta → ∀ j, j < 6 → ∀ c' j', adjAt .Delta c j = some (c', j') → L c' j' = L c j)
    {v : Nat} (after_start : pos (L 1) 4 < v) (before_end : v < pos (L 1) 5) :
    bsteps (Comp.ofLens .Delta L d ω).toGluing o 2 (1, v) = some (1, v) := by
  obtain ⟨r, rfl⟩ : ∃ r, v = pos (L 1) 4 + r := ⟨v - pos (L 1) 4, by omega⟩
  -- side 4 ends where side 5 starts
  have side4_end : pos (L 1) 5 = pos (L 1) 4 + L 1 4 := pos_succ (L 1) 4
  exact side_cycle len_pos pair (c' := 3) (j' := 0) (by decide) (by omega) (by decide) (by omega) (by omega)

/-! ### The nest -/

/-- The children of `N_{m+1}` are discs at their rims. -/
theorem kidsD_chains {m : Nat} (m_pos : 1 ≤ m) : ∀ c, c < nk .Delta → (kidsD m c).RimChains (ori m) :=
  fun c _ => chains_super m (kidAt .Delta c) m_pos

/-- Corner `x` of `N_m`, as a corner of `N_{m+1}`. -/
abbrev upC (m : Nat) (x : Nat × Nat) : Nat × Nat := (up m 1 x.1, x.2)

/-- Turning in `N_m` is turning in `N_{m+1}`. -/
theorem turns_up {m : Nat} (m_pos : 1 ≤ m) (n : Nat) {x y : Nat × Nat} (x_tile : x.1 < (N m).tiles)
    (turned : (N m).turns n x = some y) : (N (m + 1)).turns n (upC m x) = some (upC m y) := by
  rw [N_succ m_pos]
  exact (KD m_pos).turns_lift (c := 1) (by decide) n x_tile turned

/-- A vertex surrounded in `N_m` is surrounded in `N_{m+1}`. -/
theorem surrounded_up {m : Nat} (m_pos : 1 ≤ m) {t i : Nat} (t_lt : t < (N m).tiles)
    (surrounded : (N m).Surrounded t i) : (N (m + 1)).Surrounded (up m 1 t) i := by
  obtain ⟨n, n_pos, round⟩ := surrounded
  exact ⟨n, n_pos, turns_up m_pos n (x := (t, i)) t_lt round⟩

/-- **Off its side 2, `N_m` lies inside `N_{m+1}`**: a corner on the chain about a rim vertex of `N_m` that is not on
the closed side 2 is surrounded in `N_{m+1}`. -/
theorem surrounded_off_side2 {m : Nat} (m_pos : 1 ≤ m) {u n : Nat} {x : Nat × Nat} (u_lt : u < (N m).E)
    (off_side2 : u < pos (Lk m .Delta 1) 2 ∨ pos (Lk m .Delta 1) 3 < u)
    (on_chain : (N m).turns n ((N m).sC (ori m) u) = some x) : (N (m + 1)).Surrounded (up m 1 x.1) x.2 := by
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the rim of `N_m`
  have rim_len := E_N m_pos
  obtain ⟨a, a_pos, cycle⟩ := child1_cycle (d := dOff m) (ω := ori m) (o := ori m) kids.len_pos kids.pair
    (by rw [← rim_len]; exact u_lt) off_side2
  rw [N_succ m_pos]
  exact kids.surrounded_of_cycle (kidsD_chains m_pos) (c := 1) (by decide) u_lt a_pos cycle on_chain

/-- **Around side 4 of `N_m`, `N_m` lies inside `N_{m+1}`**: a corner on the chain about a rim vertex well inside
side 4 of `N_m` (which child 1's side 4, glued to child 3, is) is surrounded in `N_{m+1}`. -/
theorem surrounded_side4 {m : Nat} (m_pos : 1 ≤ m) {v n : Nat} {x : Nat × Nat} (inside : Inside m 4 v)
    (on_chain : (N m).turns n ((N m).sC (ori m) v) = some x) : (N (m + 1)).Surrounded (up m 1 x.1) x.2 := by
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the rim of `N_m`
  have rim_len := E_N m_pos
  -- `v` lies two edges inside side 4
  have after_start := inside.1
  -- and two before its end
  have before_end : v + 2 ≤ pos (Lk m .Delta 1) 5 := inside.2
  -- which is no later than the rim
  have five_le := pos_mono (Lk m .Delta 1) (show 5 ≤ 6 by omega)
  -- turning about `v` comes round in two steps
  have cycle := side4_cycle (d := dOff m) (ω := ori m) (o := ori m) kids.len_pos kids.pair (v := v) (by omega)
    (by omega)
  rw [N_succ m_pos]
  exact kids.surrounded_of_cycle (kidsD_chains m_pos) (c := 1) (by decide)
    (show v < (N m).E by rw [rim_len]; omega) (by omega) cycle on_chain

/-- **Strictly inside side 2 of `N_m`** (on the rim of `N_{m+1}`): the chain about rim vertex `u` of `N_m` is, one
level up, the chain about rim vertex `stp u` of `N_{m+1}`, or its start. -/
theorem chain_stretch {m : Nat} (m_pos : 1 ≤ m) {u n : Nat} {x : Nat × Nat} (after_two : pos (Lk m .Delta 1) 2 < u)
    (before_three : u < pos (Lk m .Delta 1) 3) (on_chain : (N m).turns n ((N m).sC (ori m) u) = some x) :
    (N (m + 1)).turns n ((N (m + 1)).sC (ori (m + 1)) (stp (Lk m .Delta) u)) = some (upC m x) := by
  -- the rim of `N_m`
  have rim_len := E_N m_pos
  -- vertex 3 is no later than the rim
  have three_le := pos_mono (Lk m .Delta 1) (show 3 ≤ 6 by omega)
  -- the start of the chain, one level up
  have start : (N (m + 1)).sC (ori (m + 1)) (stp (Lk m .Delta) u) = upC m ((N m).sC (ori m) u) := by
    -- the rim port of `N_m` there is, one level up, the rim port of `N_{m+1}`
    have same_port := stretch_eq m_pos after_two before_three (ori m)
    rw [← ori_succ] at same_port
    show Patch.corner ((N (m + 1)).bport (ori (m + 1)) (stp (Lk m .Delta) u, ori (m + 1))) = _
    rw [← same_port]; rfl
  rw [start]
  exact turns_up m_pos n (Patch.sC_valid (good m .Delta m_pos).sig (show u < (N m).E by rw [rim_len]; omega)).1
    on_chain

/-- Junction `q` of `N_{m+1}` is a rim position. -/
theorem junction_lt {m q : Nat} (m_pos : 1 ≤ m) (q_lt : q < 22) : jpos (Lk m .Delta) q < rimN .Delta (Lk m .Delta) := by
  -- the pieces from `q` to the end
  have spread := jpos_le (Lk m .Delta) (len5 m_pos) (q := q) (q' := 22) (by omega) (Nat.le_refl _)
  rw [jpos_full] at spread
  omega

/-- **At vertex 3 of `N_m`**, an end of its side 2: a corner on the chain about it is, one level up, on the chain
about junction 16 of `N_{m+1}`. -/
theorem chain_j16 {m : Nat} (m_pos : 1 ≤ m) {n : Nat} {x : Nat × Nat}
    (on_chain : (N m).turns n ((N m).sC (ori m) (pos (Lk m .Delta 1) 3)) = some x) :
    ∃ n', (N (m + 1)).turns n' ((N (m + 1)).sC (ori (m + 1)) (jpos (Lk m .Delta) 16)) = some (upC m x) := by
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the parent's chain starts at vertex 1 of child 2, or at vertex 3 of child 1
  have start : vS .Delta (Lk m .Delta) (dOff m) (ori m) (ori m) (jpos (Lk m .Delta) 16) =
      if ori m then (2, pos (Lk m .Delta 2) 1) else (1, pos (Lk m .Delta 1) 3) := by
    simp only [vS, gR_jpos m_pos (show 16 < 22 by omega), gL_jpos m_pos (show 1 ≤ 16 by omega) (show 16 < 22 by omega)]
    rfl
  -- from there, the gluing reaches vertex 3 of child 1 in at most one step
  have path : ∃ a, bsteps (Comp.ofLens .Delta (Lk m .Delta) (dOff m) (ori m)).toGluing (ori m) a
      (vS .Delta (Lk m .Delta) (dOff m) (ori m) (ori m) (jpos (Lk m .Delta) 16)) = some (1, pos (Lk m .Delta 1) 3) := by
    rw [start]
    cases ori m
    · exact ⟨0, rfl⟩
    · exact ⟨1, tsteps_sound kids.len_pos kids.pair 1 (by decide) (by decide) (by decide)⟩
  obtain ⟨a, path⟩ := path
  rw [N_succ m_pos, ori_succ]
  exact kids.on_parent_chain (kidsD_chains m_pos) (junction_lt m_pos (by omega)) path on_chain

/-- **At vertex 2 of `N_m`**, the other end of its side 2: a corner on the chain about it is, one level up, on the chain
about junction 17 of `N_{m+1}`. -/
theorem chain_j17 {m : Nat} (m_pos : 1 ≤ m) {n : Nat} {x : Nat × Nat}
    (on_chain : (N m).turns n ((N m).sC (ori m) (pos (Lk m .Delta 1) 2)) = some x) :
    ∃ n', (N (m + 1)).turns n' ((N (m + 1)).sC (ori (m + 1)) (jpos (Lk m .Delta) 17)) = some (upC m x) := by
  -- the children of `N_{m+1}`
  have kids := KD m_pos
  -- the parent's chain starts at vertex 2 of child 1, or at vertex 5 of child 0
  have start : vS .Delta (Lk m .Delta) (dOff m) (ori m) (ori m) (jpos (Lk m .Delta) 17) =
      if ori m then (1, pos (Lk m .Delta 1) 2) else (0, pos (Lk m .Delta 0) 5) := by
    simp only [vS, gR_jpos m_pos (show 17 < 22 by omega), gL_jpos m_pos (show 1 ≤ 17 by omega) (show 17 < 22 by omega)]
    rfl
  -- from there, the gluing reaches vertex 2 of child 1 in at most one step
  have path : ∃ a, bsteps (Comp.ofLens .Delta (Lk m .Delta) (dOff m) (ori m)).toGluing (ori m) a
      (vS .Delta (Lk m .Delta) (dOff m) (ori m) (ori m) (jpos (Lk m .Delta) 17)) = some (1, pos (Lk m .Delta 1) 2) := by
    rw [start]
    cases ori m
    · exact ⟨1, tsteps_sound kids.len_pos kids.pair 1 (by decide) (by decide) (by decide)⟩
    · exact ⟨0, rfl⟩
  obtain ⟨a, path⟩ := path
  rw [N_succ m_pos, ori_succ]
  exact kids.on_parent_chain (kidsD_chains m_pos) (junction_lt m_pos (by omega)) path on_chain

/-! ### A negative control -/

/-- **Negative control**: in a patch with the signature, no vertex on the rim is surrounded (the corner where the chain
about a rim vertex ends looks across a rim edge). So "surrounded" is not built into the definitions. -/
theorem rim_not_surrounded {P : Patch} {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {k : Nat} (k_lt : k < P.E) :
    ¬ P.Surrounded (P.fC o k).1 (P.fC o k).2 := by
  rintro ⟨n, n_pos, round⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- the corner looks across a rim edge
  have on_rim : P.turn ((P.fC o k).1, (P.fC o k).2) = none := by
    cases o
    · -- clockwise: across rim edge `k`
      obtain ⟨_, i_lt, unglued⟩ := sig.rim_ok k k_lt
      show P.glue (P.edgeAt k).1 ((((P.edgeAt k).2 + 1) % 14 + 13) % 14) = none
      rw [mod14 i_lt]; exact unglued
    · -- counter-clockwise: across rim edge `k - 1`
      obtain ⟨_, i_lt, unglued⟩ := sig.rim_ok _ (prv_lt k_lt)
      show P.glue (P.edgeAt (prv P.E k)).1 ((((P.edgeAt (prv P.E k)).2 + 1) % 14 + 13) % 14) = none
      rw [mod14 i_lt]; exact unglued
  simp only [Patch.turns, on_rim, Option.bind_none, reduceCtorEq] at round

/-! ### The theorem -/

/-- **The Grandparent Lemma** (as stated in `Statement.lean`). -/
theorem grandparent : Grandparent := by
  intro b b_pos t i t_lt i_lt
  -- `N_b` has the signature
  have good_b := good b .Delta b_pos
  -- one level up, the tile is a tile of `N_{b+1}`
  have t_up : up b 1 t < (N (b + 1)).tiles := (isPort_up b_pos (x := (t, i, true)) ⟨t_lt, i_lt⟩).1
  rw [show up b 2 t = up (b + 1) 1 (up b 1 t) from up_succ 1 b t]
  rcases Patch.surrounded_or_chain good_b.sig (super_glueSymm b .Delta) t_lt i_lt with
    surrounded | ⟨u, u_lt, n, on_chain⟩
  · -- surrounded in `N_b` already
    exact surrounded_up (by omega) t_up (surrounded_up b_pos t_lt surrounded)
  · -- on the chain about rim vertex `u` of `N_b`
    -- side 2 ends where side 3 starts
    have side2_end : pos (Lk b .Delta 1) 3 = pos (Lk b .Delta 1) 2 + Lk b .Delta 1 2 := pos_succ (Lk b .Delta 1) 2
    by_cases off_side2 : u < pos (Lk b .Delta 1) 2 ∨ pos (Lk b .Delta 1) 3 < u
    · -- off the closed side 2: surrounded in `N_{b+1}`
      exact surrounded_up (by omega) t_up (surrounded_off_side2 b_pos u_lt off_side2 on_chain)
    · -- on the closed side 2: on a chain of `N_{b+1}` about a vertex well inside its side 4
      rcases (show u = pos (Lk b .Delta 1) 2 ∨ (pos (Lk b .Delta 1) 2 < u ∧ u < pos (Lk b .Delta 1) 3) ∨
          u = pos (Lk b .Delta 1) 3 by omega) with at_two | inside | at_three
      · -- vertex 2: junction 17 of `N_{b+1}`
        subst at_two
        obtain ⟨n', up_chain⟩ := chain_j17 b_pos on_chain
        exact surrounded_side4 (by omega) (inside_17 b_pos) up_chain
      · -- strictly inside: the rim vertex `stp u` of `N_{b+1}`
        exact surrounded_side4 (by omega) (inside_stp b_pos inside.1 inside.2)
          (chain_stretch b_pos inside.1 inside.2 on_chain)
      · -- vertex 3: junction 16 of `N_{b+1}`
        subst at_three
        obtain ⟨n', up_chain⟩ := chain_j16 b_pos on_chain
        exact surrounded_side4 (by omega) (inside_16 b_pos) up_chain

/-! ### The Signature Theorem -/

/-- **The Signature Theorem** (the claim `SignatureTheorem` of `Statement.lean`, the paper's Thm 7.6): the induction's
conclusion `good` and `chains_super`, with the corners written out as the claim writes them. -/
theorem signatureTheorem : SignatureTheorem := by
  intro m K m_pos
  -- the induction's conclusion at level `m`
  have good_m := good m K m_pos
  -- vertex 5 lies where the side lengths put it
  have vtx5 : (super m K).vtx.getD 5 0 = vpos m K 5 := by rw [good_m.vtx]; rfl
  -- the claim's `A` is the induction's: d_m = 2 F_{3m+1} (Lemma 6.4)
  have a_eq : cornerA m K = aPos m K := by
    unfold cornerA aPos
    rw [vtx5, (dOff_fib m m_pos).1]
  -- and so is its `B`
  have b_eq : cornerB m K = bPos m K := by
    unfold cornerB bPos ori
    rw [a_eq, good_m.len]
    by_cases even : m % 2 = 0 <;> simp [even]
  -- vertex 6, the end of the rim, is one side 5 after vertex 5
  have v6 : vpos m K 6 = vpos m K 5 + lenAt m K 5 := pos_succ (lenAt m K) 5
  -- every side has at least 5 edges, and the Σ corner lies at least 4 edges before the end of side 5 (Lemma 6.5)
  have bnd := bounds m m_pos
  -- `A` is a rim vertex
  have a_lt : aPos m K < (super m K).E := by
    rw [good_m.len, v6]
    unfold aPos
    by_cases is_sigma : K = .Sigma
    · subst is_sigma
      -- side 5 of a Σ is a δ side
      have side5 : lenAt m .Sigma 5 = letterLen m .delta := rfl
      rw [ite_eq_left rfl, side5]
      omega
    · -- side 5 has at least 5 edges
      have side5 : 5 ≤ lenAt m K 5 := bnd.1 (letterOf K 5)
      rw [ite_eq_right is_sigma]
      omega
  rw [a_eq, b_eq]
  exact ⟨a_lt, chains_super m K m_pos, good_m.sig⟩

end SpectreKnot.Statement

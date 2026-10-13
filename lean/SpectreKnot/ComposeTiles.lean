/-
`compose` (the statement file's supertile construction) read in terms of the abstract composition `Comp.ofLens`:
which child a tile belongs to, what is glued across a child's rim edge (`glue_rim`: exactly what `Comp.mate`
says), and the parent's rim as a list of children's rim edges (`rim_edgeAt`, via `ownGo`).
-/
import SpectreKnot.PatchSig
import SpectreKnot.Parity

namespace SpectreKnot.Statement

open Pattern Compose

/-! ### Counting the entries of a strictly increasing sequence below a bound -/

/-- A sequence that increases at every step below `n` is monotone on `0 … n`. -/
theorem mono_of_succ {f : Nat → Nat} {n : Nat} (step_lt : ∀ a, a < n → f a < f (a + 1)) :
    ∀ a b, a ≤ b → b ≤ n → f a ≤ f b := by
  intro a b a_le b_le
  induction b with
  | zero =>
    -- `a ≤ 0`, so `a = 0`
    have a_zero : a = 0 := by omega
    subst a_zero; exact Nat.le_refl _
  | succ b ih =>
    by_cases a_eq : a = b + 1
    · subst a_eq; exact Nat.le_refl _
    · have le_b := ih (by omega) (by omega) -- up to `b` by induction
      -- and one step more
      have step := step_lt b (by omega)
      omega

/-- If, below `n`, `f a ≤ x` holds exactly when `a ≤ c`, then `min n (c + 1)` of the entries `f 0 … f (n-1)` are at
most `x`. -/
theorem count_min {f : Nat → Nat} {x : Nat} :
    ∀ n c, (∀ a, a < n → (f a ≤ x ↔ a ≤ c)) →
      ((List.range n).filter fun a => decide (f a ≤ x)).length = min n (c + 1) := by
  intro n
  induction n with
  | zero => intro c _; simp
  | succ n ih =>
    intro c at_most_iff
    rw [List.range_succ, List.filter_append, List.length_append, ih c (fun a a_lt => at_most_iff a (by omega))]
    by_cases n_le : n ≤ c
    · have counted : f n ≤ x := (at_most_iff n (by omega)).mpr n_le -- entry `n` is counted
      simp [counted]; omega
    · have not_counted : ¬ f n ≤ x := -- entry `n` is not counted
        fun at_most => n_le ((at_most_iff n (by omega)).mp at_most)
      simp [not_counted]; omega

/-- In a strictly increasing sequence, the number of entries `f 0 … f (n-1)` at most `x`, less one, is the index
`c` with `f c ≤ x < f (c + 1)`. -/
theorem count_eq {f : Nat → Nat} {n c x : Nat} (step_lt : ∀ a, a < n → f a < f (a + 1)) (c_lt : c < n)
    (at_c : f c ≤ x) (below_next : x < f (c + 1)) :
    ((List.range n).filter fun a => decide (f a ≤ x)).length - 1 = c := by
  -- the sequence is monotone
  have mono := mono_of_succ step_lt
  rw [count_min n c (fun a a_lt => ⟨fun at_most => ?_, fun a_le => ?_⟩)]
  · omega
  · by_cases a_le : a ≤ c
    · exact a_le
    · have := mono (c + 1) a (by omega) (by omega) -- past `c`, the entries exceed `x`
      omega
  · have := mono a c a_le (by omega) -- up to `c`, the entries are at most `f c ≤ x`
    omega

/-! ### Lists of seven positions -/

/-- Entry `j` (for `j < 7`) of the list `g 0, …, g 6` is `g j`. -/
theorem range7_getD (g : Nat → Nat) {j : Nat} (j_lt : j < 7) : ((List.range 7).map g).getD j 0 = g j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### Sides of a patch with its vertices at `pos f` -/

section Side

variable {P : Patch} {f : Nat → Nat}

/-- If a patch's vertices sit where the side lengths `f` put them, side `j` has `f j` edges. -/
theorem side_length (vtx_eq : P.vtx = (List.range 7).map (pos f)) (len_eq : P.E = pos f 6) {j : Nat}
    (j_lt : j < 6) : (P.side j).length = f j := by
  simp only [Patch.side, vtx_eq, range7_getD _ (show j < 7 by omega), range7_getD _ (show j + 1 < 7 by omega),
    List.length_take, List.length_drop, pos_succ]
  -- the rim has `pos f 6` edges
  have rim_len : P.rim.length = pos f 6 := len_eq
  -- side `j` ends no later than the rim
  have side_end := pos_mono f (show j + 1 ≤ 6 by omega)
  rw [pos_succ] at side_end
  omega

/-- If a patch's vertices sit where the side lengths `f` put them, edge `r` of side `j` is rim edge `pos f j + r`. -/
theorem side_getElem? (vtx_eq : P.vtx = (List.range 7).map (pos f)) (len_eq : P.E = pos f 6) {j r : Nat}
    (j_lt : j < 6) (r_lt : r < f j) : (P.side j)[r]? = some (P.edgeAt (pos f j + r)) := by
  simp only [Patch.side, vtx_eq, range7_getD _ (show j < 7 by omega), range7_getD _ (show j + 1 < 7 by omega),
    pos_succ]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
  -- side `j` ends no later than the rim
  have side_end := pos_mono f (show j + 1 ≤ 6 by omega)
  rw [pos_succ] at side_end
  -- so the position is on the rim
  have in_rim : pos f j + r < P.rim.length := by rw [show P.rim.length = P.E from rfl, len_eq]; omega
  simp only [Patch.edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem in_rim, Option.getD_some]

end Side

/-! ### The children's tiles in the parent -/

/-- The number of the first tile of child `c` in the parent. -/
def offC (child : Nat → Patch) (c : Nat) : Nat := ((List.range c).map fun c' => (child c').tiles).sum

/-- Child `c + 1` starts right after the tiles of child `c`. -/
theorem offC_succ (child : Nat → Patch) (c : Nat) : offC child (c + 1) = offC child c + (child c).tiles := by
  simp [offC, List.range_succ, List.map_append, List.sum_append]

/-- Every tile of the parent belongs to a child: it lies between that child's first tile and the next child's.
(`owner_unique`: to only one.) -/
theorem owner_exists (child : Nat → Patch) : ∀ n t, t < offC child n → ∃ c, c < n ∧ offC child c ≤ t ∧
    t < offC child c + (child c).tiles := by
  intro n
  induction n with
  | zero => intro t t_lt; simp [offC] at t_lt
  | succ n ih =>
    intro t t_lt
    rw [offC_succ] at t_lt
    by_cases before_n : t < offC child n
    · -- a tile of one of the first `n` children
      obtain ⟨c, c_lt, start_le, lt_end⟩ := ih t before_n
      exact ⟨c, by omega, start_le, lt_end⟩
    · -- a tile of child `n`
      exact ⟨n, by omega, by omega, t_lt⟩

/-- Tile numbers of the parent do not overlap: tile `t` of child `c` and tile `t'` of child `c'` have the same number
only if `c = c'` and `t = t'`. -/
theorem owner_unique (child : Nat → Patch) {c c' t t' : Nat} (t_lt : t < (child c).tiles)
    (t_lt' : t' < (child c').tiles) (same_num : offC child c + t = offC child c' + t') : c = c' ∧ t = t' := by
  -- later children start later
  have mono : ∀ a b, a ≤ b → offC child a ≤ offC child b := by
    intro a b a_le
    induction b with
    | zero =>
      -- `a ≤ 0`, so `a = 0`
      have a_zero : a = 0 := by omega
      subst a_zero; exact Nat.le_refl _
    | succ b ih =>
      by_cases a_eq : a = b + 1
      · subst a_eq; exact Nat.le_refl _
      · have := ih (by omega) -- up to `b` by induction
        rw [offC_succ]; omega
  rcases Nat.lt_trichotomy c c' with c_lt | rfl | c_gt
  · have c'_after := mono (c + 1) c' c_lt -- child `c'` starts after child `c` ends
    rw [offC_succ] at c'_after; omega
  · exact ⟨rfl, by omega⟩
  · have c_after := mono (c' + 1) c c_gt -- child `c` starts after child `c'` ends
    rw [offC_succ] at c_after; omega

section Compose

variable {T : Kind} {child : Nat → Patch}

/-- The child that tile `t` of the parent belongs to (as `compose` computes it). -/
def ownerC (T : Kind) (child : Nat → Patch) (t : Nat) : Nat :=
  ((List.range (Pattern.kids T).length).filter fun c => decide (offC child c ≤ t)).length - 1

/-- What `compose` glues across edge `e_i` of tile `t` of child `c`. -/
def glueAt (T : Kind) (child : Nat → Patch) (c t i : Nat) : Option (Nat × Nat) :=
  match (child c).glue t i with
  | some e => some (e.1 + offC child c, e.2)
  | none =>
    let pos := ((child c).rim.findIdx? (· == (t, i))).getD 0
    let j := ((List.range 6).filter fun j => (child c).vtx.getD j 0 ≤ pos).length - 1
    let o := pos - (child c).vtx.getD j 0
    match ((Pattern.adj T).getD c []).getD j none with
    | none => none
    | some (c', j') =>
      let s := (child c').side j'
      (s[s.length - 1 - o]?).map fun e => (e.1 + offC child c', e.2)

/-- `compose`'s gluing, unfolded: find the tile's child, then glue as `glueAt` says. -/
theorem compose_glue_def (t i : Nat) :
    (compose T child).glue t i = glueAt T child (ownerC T child t) (t - offC child (ownerC T child t)) i := rfl

/-- If every child has a tile, `compose` finds the right child for tile `t` of child `c`. -/
theorem ownerC_eq (tiles_pos : ∀ c, c < nk T → 0 < (child c).tiles) {c t : Nat} (c_lt : c < nk T)
    (t_lt : t < (child c).tiles) : ownerC T child (offC child c + t) = c :=
  count_eq (f := offC child)
    (fun a a_lt => by
      rw [offC_succ]
      -- child `a` has a tile, so child `a + 1` starts later
      have := tiles_pos a a_lt
      omega)
    c_lt (by omega) (by rw [offC_succ]; omega)

/-- What is glued across edge `e_i` of tile `t` of child `c`, in the parent. -/
theorem compose_glue (tiles_pos : ∀ c, c < nk T → 0 < (child c).tiles) {c t : Nat} (c_lt : c < nk T)
    (t_lt : t < (child c).tiles) (i : Nat) :
    (compose T child).glue (offC child c + t) i = glueAt T child c t i := by
  rw [compose_glue_def, ownerC_eq tiles_pos c_lt t_lt, Nat.add_sub_cancel_left]

end Compose

/-! ### Across a child's rim edge -/

/-- On a rim that lists no edge twice, looking up rim edge `k` finds position `k`. -/
theorem findIdx_rim {P : Patch} {k : Nat} (k_lt : k < P.E)
    (rim_inj : ∀ k', k' < P.E → P.edgeAt k' = P.edgeAt k → k' = k) :
    (P.rim.findIdx? (· == ((P.edgeAt k).1, (P.edgeAt k).2))).getD 0 = k := by
  -- `P.E` is the length of the rim list
  have k_lt_len : k < P.rim.length := k_lt
  -- on the rim, the list entry is the edge `edgeAt` gives
  have entry_eq : ∀ k', (k'_lt : k' < P.rim.length) → P.rim[k'] = P.edgeAt k' := fun k' k'_lt => by
    simp only [Patch.edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k'_lt, Option.getD_some]
  rw [List.findIdx?_eq_some_iff_getElem.mpr ⟨k_lt_len, ?_, ?_⟩]
  · rfl
  · rw [entry_eq]; simp
  · intro j j_lt same_edge
    rw [entry_eq, beq_iff_eq] at same_edge
    -- an earlier position with the same edge would be `k` itself
    have := rim_inj j
      (by
        -- `k` is a rim position
        have : k < P.E := k_lt
        show j < P.rim.length; omega)
      (by rw [same_edge])
    omega

section Rim

variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- **Across a child's rim edge, `compose` glues what `Comp.mate` says.** Edge `k` of child `c`'s rim (counted in
its own orientation, from its vertex 0) is glued to edge `k'` of child `c'`'s rim exactly when the abstract
composition with these side lengths says so. Here `L c j` is the length of side `j` of child `c`. -/
theorem glue_rim (len_pos : ∀ c, c < nk T → ∀ j, j < 6 → 1 ≤ L c j)
    (pair_len : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j)
    (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧ (child c).E = pos (L c) 6)
    {c k : Nat} (c_lt : c < nk T) (k_lt : k < pos (L c) 6)
    (unglued : (child c).glue ((child c).edgeAt k).1 ((child c).edgeAt k).2 = none)
    (rim_inj : ∀ k', k' < (child c).E → (child c).edgeAt k' = (child c).edgeAt k → k' = k) :
    glueAt T child c ((child c).edgeAt k).1 ((child c).edgeAt k).2 =
      ((Comp.ofLens T L d ω).mate c k).map fun (c', k') =>
        (((child c').edgeAt k').1 + offC child c', ((child c').edgeAt k').2) := by
  obtain ⟨vtx_eq, len_eq⟩ := shape c c_lt
  obtain ⟨j, o, j_lt, o_lt, rfl⟩ := decomp (L c) 6 (Nat.le_refl _) k k_lt
  -- `compose` finds the edge at its own rim position
  have found_at := findIdx_rim (P := child c) (k := pos (L c) j + o) (by rw [len_eq]; exact k_lt) rim_inj
  -- and finds that it lies on side `j`
  have side_eq :
      ((List.range 6).filter fun a => decide ((child c).vtx.getD a 0 ≤ pos (L c) j + o)).length - 1 = j := by
    refine count_eq (f := fun j => (child c).vtx.getD j 0) (fun a a_lt => ?_) j_lt ?_ ?_
    · simp only [vtx_eq, range7_getD _ (show a < 7 by omega), range7_getD _ (show a + 1 < 7 by omega), pos_succ]
      have := len_pos c c_lt a a_lt -- side `a` has an edge, so vertex `a + 1` comes after vertex `a`
      omega
    · simp only [vtx_eq, range7_getD _ (show j < 7 by omega)]; omega
    · simp only [vtx_eq, range7_getD _ (show j + 1 < 7 by omega), pos_succ]; omega
  unfold glueAt
  rw [unglued]
  simp only []
  rw [found_at, side_eq, vtx_eq, range7_getD _ (show j < 7 by omega), ofLens_mate len_pos c_lt j_lt o_lt,
    show pos (L c) j + o - pos (L c) j = o by omega]
  simp only [adjAt]
  cases adj_eq : ((Pattern.adj T).getD c []).getD j none with
  | none => rfl
  | some p =>
    obtain ⟨c', j'⟩ := p
    obtain ⟨c_lt', j_lt', _, _⟩ := adj_valid c_lt j_lt adj_eq
    -- the two glued sides have the same length
    have same_len := pair_len c c_lt j j_lt c' j' adj_eq
    obtain ⟨vtx_eq', len_eq'⟩ := shape c' c_lt'
    simp only [Option.map_some]
    rw [side_length vtx_eq' len_eq' j_lt',
      side_getElem? vtx_eq' len_eq' j_lt' (show L c' j' - 1 - o < L c' j' by omega),
      show pos (L c') j' + L c' j' - 1 - o = pos (L c') j' + (L c' j' - 1 - o) by omega]
    rfl

end Rim

end SpectreKnot.Statement

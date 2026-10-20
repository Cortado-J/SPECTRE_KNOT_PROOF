/-
**The induction step of Thm 7.6, at tile level.** If the children of `compose T child` have the signature (with the
corners and side lengths of the abstract composition), and the composition has the signature as §7.1 words it
(`CompSig`), then so does the parent (`Kids.parent_sig`): its rim is Table 3's (`rim_edgeAt`), its six vertices are
where the parent's side lengths put them (`parent_vtx`), and its rim ports are joined as hooks except at the corners
`cA`, `cB`, where they cross over.
-/
import SpectreKnot.Bridge

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- Later children start later: the first tile number `offC child c` grows with `c`. -/
theorem offC_mono (child : Nat → Patch) {a b : Nat} (a_le : a ≤ b) : offC child a ≤ offC child b := by
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

/-- Tile `t` of child `c`, renumbered in the parent, comes before the first tile of any later child `n`. -/
theorem tile_lt (child : Nat → Patch) {c t n : Nat} (c_lt : c < n) (t_lt : t < (child c).tiles) :
    t + offC child c < offC child n := by
  -- child `n` starts no earlier than child `c + 1`
  have later_start := offC_mono child (show c + 1 ≤ n by omega)
  rw [offC_succ] at later_start; omega

/-! ### The parent's rim and vertices -/

section Rim

variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat}

/-- The parent's rim edges, child by child (`compose`'s rim). -/
abbrev rimPiece (child : Nat → Patch) : Nat × Nat → List (Nat × Nat)
  | (c, j) => ((child c).side j).reverse.map fun e => (e.1 + offC child c, e.2)

/-- `compose`'s rim is made of the children's sides listed in Table 3, each backwards and renumbered. -/
theorem compose_rim : (compose T child).rim = (pcs T).flatMap (rimPiece child) := rfl

/-- If the children's vertices sit where the side lengths `L` put them, the rim made of the pieces `l` has length
`totL L l`. -/
theorem rimPiece_length (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) : ∀ (l : List (Nat × Nat)), (∀ x ∈ l, x.1 < nk T ∧ x.2 < 6) →
    (l.flatMap (rimPiece child)).length = totL L l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro valid
    obtain ⟨c_lt, j_lt⟩ := valid (c, j) List.mem_cons_self
    obtain ⟨vtx_eq, len_eq⟩ := shape c c_lt
    rw [List.flatMap_cons, List.length_append, ih (fun x mem => valid x (List.mem_cons_of_mem _ mem))]
    simp only [rimPiece, List.length_map, List.length_reverse, side_length vtx_eq len_eq j_lt, totL]

/-- If the children's vertices sit where the side lengths `L` put them, entry `p` of the rim made of the pieces `l`
is the child's edge `ownGo L l p`, renumbered as an edge of the parent. -/
theorem rimPiece_getD (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) : ∀ (l : List (Nat × Nat)), (∀ x ∈ l, x.1 < nk T ∧ x.2 < 6) →
    ∀ p, p < totL L l → (l.flatMap (rimPiece child)).getD p (0, 0) =
      (((child (ownGo L l p).1).edgeAt (ownGo L l p).2).1 + offC child (ownGo L l p).1,
        ((child (ownGo L l p).1).edgeAt (ownGo L l p).2).2) := by
  intro l
  induction l with
  | nil => intro _ p p_lt; simp [totL] at p_lt
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro valid p p_lt
    obtain ⟨c_lt, j_lt⟩ := valid (c, j) List.mem_cons_self
    obtain ⟨vtx_eq, len_eq⟩ := shape c c_lt
    -- the first piece has the length of its side
    have piece_len : (rimPiece child (c, j)).length = L c j := by
      simp only [rimPiece, List.length_map, List.length_reverse, side_length vtx_eq len_eq j_lt]
    simp only [totL] at p_lt
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    by_cases in_head : p < L c j
    · -- in the first piece: an edge of side `j`, counted from its end
      rw [List.getElem?_append_left (by rw [piece_len]; exact in_head)]
      simp only [ownGo, ite_eq_left in_head]
      -- side `j` has `L c j` edges
      have side_len := side_length vtx_eq len_eq j_lt
      simp only [rimPiece, List.getElem?_map]
      rw [List.getElem?_reverse (by rw [side_len]; exact in_head), side_len,
        side_getElem? vtx_eq len_eq j_lt (show L c j - 1 - p < L c j by omega),
        show pos (L c) j + (L c j - 1 - p) = pos (L c) j + L c j - 1 - p by omega]
      rfl
    · -- in a later piece: by induction
      rw [List.getElem?_append_right (by rw [piece_len]; omega), piece_len, ← List.getD_eq_getElem?_getD,
        ih (fun x mem => valid x (List.mem_cons_of_mem _ mem)) (p - L c j) (by omega)]
      simp only [ownGo, ite_eq_right in_head]

variable (T) in
/-- Table 3's pieces are sides of actual children. -/
theorem pcs_valid' : ∀ x ∈ pcs T, x.1 < nk T ∧ x.2 < 6 :=
  fun x mem => ⟨(pcs_valid T x mem).1, (pcs_valid T x mem).2.1⟩

/-- The parent's rim length. -/
theorem compose_E (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) : (compose T child).E = rimN T L := by
  show (compose T child).rim.length = _
  rw [compose_rim, rimPiece_length shape _ (pcs_valid' T)]

/-- **The parent's rim is Table 3's**: rim edge `p` of the parent is edge `k` of child `c`, `(c, k) = ownGo p`. -/
theorem rim_edgeAt (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) {p : Nat} (p_lt : p < rimN T L) :
    (compose T child).edgeAt p =
      (((child (ownGo L (pcs T) p).1).edgeAt (ownGo L (pcs T) p).2).1 + offC child (ownGo L (pcs T) p).1,
        ((child (ownGo L (pcs T) p).1).edgeAt (ownGo L (pcs T) p).2).2) := by
  show (compose T child).rim.getD p (0, 0) = _
  rw [compose_rim]
  exact rimPiece_getD shape _ (pcs_valid' T) p p_lt

/-- The parent's side lengths: the sum over Table 3's pieces. -/
def parentLen (T : Kind) (L : Nat → Nat → Nat) (J : Nat) : Nat := totL L ((pside T).getD J [])

/-- Table 3 has a row for each of the parent's six sides. -/
theorem pside_length : ∀ T, (pside T).length = 6 := by intro T; cases T <;> rfl

/-- The pieces of the parent's first `J` sides have total length `pos (parentLen T L) J`: where vertex `J` sits. -/
theorem totL_take (L : Nat → Nat → Nat) (T : Kind) : ∀ J, J ≤ 6 →
    totL L (((pside T).take J).flatMap id) = pos (parentLen T L) J := by
  intro J
  induction J with
  | zero => intro _; rfl
  | succ J ih =>
    intro J_le
    -- Table 3 has a row for side `J`
    have J_lt : J < (pside T).length := by rw [pside_length]; omega
    rw [List.take_add_one, List.flatMap_append, totL_append, ih (by omega), pos_succ, List.getElem?_eq_getElem J_lt]
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, id, parentLen,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem J_lt, Option.getD_some]

/-- If the children's vertices sit where the side lengths `L` put them, the sides listed in `l` have total length
`totL L l`. -/
theorem sideLens_sum (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) : ∀ (l : List (Nat × Nat)), (∀ x ∈ l, x.1 < nk T ∧ x.2 < 6) →
    (l.map fun (c, j) => ((child c).side j).length).sum = totL L l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x rest ih =>
    obtain ⟨c, j⟩ := x
    intro valid
    obtain ⟨c_lt, j_lt⟩ := valid (c, j) List.mem_cons_self
    obtain ⟨vtx_eq, len_eq⟩ := shape c c_lt
    simp only [List.map_cons, List.sum_cons, totL, side_length vtx_eq len_eq j_lt,
      ih (fun x mem => valid x (List.mem_cons_of_mem _ mem))]

/-- **The parent's vertices** sit where the parent's side lengths put them. -/
theorem parent_vtx (shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧
    (child c).E = pos (L c) 6) : (compose T child).vtx = (List.range 7).map (pos (parentLen T L)) := by
  show (List.range 7).map (fun J => ((((Pattern.pside T).take J).flatMap id).map fun (c, j) =>
    ((child c).side j).length).sum) = _
  apply List.map_congr_left
  intro J J_mem
  rw [List.mem_range] at J_mem
  -- the pieces of the first `J` sides are sides of actual children
  have first_valid : ∀ x ∈ ((pside T).take J).flatMap id, x.1 < nk T ∧ x.2 < 6 := by
    intro x mem
    apply pcs_valid' T
    simp only [pcs, List.mem_flatMap, id] at mem ⊢
    obtain ⟨l, l_mem, x_mem⟩ := mem
    exact ⟨l, List.mem_of_mem_take l_mem, x_mem⟩
  rw [sideLens_sum shape _ first_valid, totL_take L T J (by omega)]

/-- The parent's rim length is the total of its six side lengths. -/
theorem rimN_eq (L : Nat → Nat → Nat) (T : Kind) : rimN T L = pos (parentLen T L) 6 := by
  rw [← totL_take L T 6 (Nat.le_refl _)]
  simp only [rimN, pcs]
  rw [List.take_of_length_le (by simp [pside_length])]

end Rim

/-! ### The parent's signature -/

namespace Kids

set_option linter.unusedSectionVars false

variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool}
  (kids : Kids T child L d ω o)

include kids

/-- The parent's port `R(p)` (its orientation `!o` is opposite to the children's) is the gluing's port `gR p`. -/
theorem bport_R {p : Nat} (p_lt : p < rimN T L) :
    (compose T child).bport (!o) (p, true) = ιP child o (gR T L d ω p) := by
  obtain ⟨c_lt, k_lt, _⟩ := own_mate (d := d) (ω := ω) kids.len_pos p_lt
  -- the composition's rim length for the child is the child's
  have E_eq := kids.E_eq c_lt
  rw [ofLens_E c_lt] at E_eq
  -- so the edge is on the child's rim
  have k_lt' : (ownGo L (pcs T) p).2 < (child (ownGo L (pcs T) p).1).E := by rw [← E_eq]; exact k_lt
  simp only [gR, ιP, Patch.bport, rim_edgeAt kids.shape p_lt, ofLens_E c_lt, E_eq, prv_nxt k_lt']
  cases o <;> rfl

/-- The parent's port `L(p)` is the gluing's port `gL p`. -/
theorem bport_L {p : Nat} (p_lt : p < rimN T L) :
    (compose T child).bport (!o) (p, false) = ιP child o (gL T L p) := by
  -- the position before `p` is on the rim too
  have prv_lt_N : prv (rimN T L) p < rimN T L := prv_lt p_lt
  simp only [gL, ιP, Patch.bport, compose_E kids.shape, rim_edgeAt kids.shape prv_lt_N]
  cases o <;> rfl

/-- The vertex of `gR p` is a parent rim vertex reached along the rim: the edge before it is unglued. -/
theorem gR_rimL {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.RimL (gR T L d ω p).1 (gR T L d ω p).2.1 :=
  Statement.gR_rimL kids.len_pos p_lt

/-- Turning about the vertex of `gR p` reaches the start of the child edge at position `p - 1`, the vertex of
`gL p`. -/
theorem gR_rot {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.Rot ((gR T L d ω p).1, (gR T L d ω p).2.1) (ownGo L (pcs T) (prv (rimN T L) p)) :=
  Statement.gR_rot kids.len_pos p_lt

/-- `gR p` is a port of an actual child, at an actual rim vertex. -/
theorem gR_valid {p : Nat} (p_lt : p < rimN T L) : (Comp.ofLens T L d ω).toGluing.Valid (gR T L d ω p) :=
  Statement.gR_valid kids.len_pos p_lt

/-- `gL p` is a port of an actual child, at an actual rim vertex. -/
theorem gL_valid {p : Nat} (p_lt : p < rimN T L) : (Comp.ofLens T L d ω).toGluing.Valid (gL T L p) :=
  Statement.gL_valid kids.len_pos p_lt

/-- `gR p` is on the parent's rim: nothing lies across it. -/
theorem gR_sigma {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.sigma (gR T L d ω p) = none :=
  Statement.gR_sigma kids.len_pos p_lt

/-- `gL p` is on the parent's rim: nothing lies across it. -/
theorem gL_sigma {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.sigma (gL T L p) = none :=
  Statement.gL_sigma kids.len_pos p_lt

/-- **The parent has the signature** (Thm 7.6's induction step, at tile level), at the rim positions `cA`, `cB` of the
Γ child's corners: Prop 7.4 for the composition of the children (`Kids.csig`), read port by port. -/
theorem parent_sig : (compose T child).HasSig (!o) (cA T L) (cB T L ω) := by
  -- the composition is well formed
  have wf := kids.csig.wf
  -- the children's vertices sit where the side lengths put them
  have shape := kids.shape
  -- the parent's rim length
  have E_eq := compose_E (child := child) shape
  -- the corners' positions are on the rim
  have pA_lt := kids.csig.cA_lt
  -- (both of them)
  have pB_lt := kids.csig.cB_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, kids.noClosed, ?_⟩
  · -- tiles
    show 0 < offC child (nk T)
    -- there is a child
    have has_child : 0 < nk T := by cases T <;> decide
    -- whose tiles come before the end
    have := tile_lt child has_child (kids.tiles_pos 0 has_child)
    omega
  · -- rim edges
    intro p p_lt
    rw [E_eq] at p_lt
    obtain ⟨c_lt, k_lt, unglued⟩ := own_mate (d := d) (ω := ω) kids.len_pos p_lt
    -- the child edge is on the child's rim
    have k_lt' : (ownGo L (pcs T) p).2 < (child (ownGo L (pcs T) p).1).E := by rw [(shape _ c_lt).2]; exact k_lt
    obtain ⟨t_lt, i_lt, _⟩ := (kids.sig _ c_lt).rim_ok _ k_lt'
    rw [rim_edgeAt shape p_lt]
    refine ⟨tile_lt child c_lt t_lt, i_lt, ?_⟩
    rw [kids.glue_rimEdge c_lt k_lt', unglued]; rfl
  · -- no edge twice
    intro p p' p_lt p_lt' same_edge
    rw [E_eq] at p_lt p_lt'
    rw [rim_edgeAt shape p_lt, rim_edgeAt shape p_lt'] at same_edge
    simp only [Prod.mk.injEq] at same_edge
    obtain ⟨c_lt, k_lt, _⟩ := own_mate (d := d) (ω := ω) kids.len_pos p_lt
    obtain ⟨c_lt', k_lt', _⟩ := own_mate (d := d) (ω := ω) kids.len_pos p_lt'
    -- both child edges are on their children's rims
    have on_rim : (ownGo L (pcs T) p).2 < (child (ownGo L (pcs T) p).1).E := by rw [(shape _ c_lt).2]; exact k_lt
    -- (the second)
    have on_rim' : (ownGo L (pcs T) p').2 < (child (ownGo L (pcs T) p').1).E := by
      rw [(shape _ c_lt').2]; exact k_lt'
    obtain ⟨t_lt, _, _⟩ := (kids.sig _ c_lt).rim_ok _ on_rim
    obtain ⟨t_lt', _, _⟩ := (kids.sig _ c_lt').rim_ok _ on_rim'
    -- the same parent tile: the same child, and the same tile in it
    obtain ⟨same_child, same_tile⟩ := owner_unique child t_lt t_lt' (by omega)
    -- the same child edge, so the same position on the child's rim
    have same_k : (ownGo L (pcs T) p).2 = (ownGo L (pcs T) p').2 := by
      apply (kids.sig _ c_lt).rim_inj _ _ on_rim (by rw [same_child]; exact on_rim')
      rw [same_child]; rw [same_child] at same_tile same_edge; exact Prod.ext same_tile same_edge.2
    exact own_inj kids.len_pos p_lt p_lt' (Prod.ext same_child same_k)
  · -- every unglued edge is a rim edge
    intro t i t_lt i_lt unglued
    -- the child `c` that tile `t` belongs to, and its number `t₀` there
    obtain ⟨c, c_lt, start_le, lt_end⟩ := owner_exists child (nk T) t t_lt
    obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + offC child c := ⟨t - offC child c, by omega⟩
    -- `t₀` is a tile of child `c`
    have t₀_lt : t₀ < (child c).tiles := by omega
    rw [kids.glue_shift c_lt t₀_lt] at unglued
    cases glue_eq : (child c).glue t₀ i with
    | some edge => simp [glueAt, glue_eq] at unglued
    | none =>
      -- unglued in the child: rim edge `k` of the child
      obtain ⟨k, k_lt, at_k⟩ := (kids.sig c c_lt).rim_all t₀ i t₀_lt i_lt glue_eq
      -- what the parent glues there, by the composition
      have rim_glue := kids.glue_rimEdge c_lt k_lt
      rw [at_k, kids.glue_shift c_lt t₀_lt, unglued] at rim_glue
      -- so the composition leaves it unglued
      have mate_none : (Comp.ofLens T L d ω).toGluing.mate c k = none := by
        cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c k with
        | none => rfl
        | some q => rw [mate_eq] at rim_glue; simp at rim_glue
      obtain ⟨p, p_lt, at_p⟩ :=
        own_surj (d := d) (ω := ω) kids.len_pos c_lt (by rw [← (shape c c_lt).2]; exact k_lt) mate_none
      refine ⟨p, by rw [E_eq]; exact p_lt, ?_⟩
      rw [rim_edgeAt shape p_lt, at_p, at_k]
  · -- glued edges are edges of actual tiles
    intro t i t' j t_lt i_lt glued
    -- the child `c` that tile `t` belongs to, and its number `t₀` there
    obtain ⟨c, c_lt, start_le, lt_end⟩ := owner_exists child (nk T) t t_lt
    obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + offC child c := ⟨t - offC child c, by omega⟩
    -- `t₀` is a tile of child `c`
    have t₀_lt : t₀ < (child c).tiles := by omega
    rw [kids.glue_shift c_lt t₀_lt] at glued
    cases glue_eq : (child c).glue t₀ i with
    | some edge =>
      -- glued inside the child
      obtain ⟨t₁, i₁⟩ := edge
      simp only [glueAt, glue_eq, Option.some.injEq, Prod.mk.injEq] at glued
      obtain ⟨rfl, rfl⟩ := glued
      obtain ⟨t₁_lt, i₁_lt⟩ := (kids.sig c c_lt).glue_ok t₀ i t₁ i₁ t₀_lt i_lt glue_eq
      exact ⟨tile_lt child c_lt t₁_lt, i₁_lt⟩
    | none =>
      -- on the child's rim, at rim edge `k`: glued to a sibling's rim edge
      obtain ⟨k, k_lt, at_k⟩ := (kids.sig c c_lt).rim_all t₀ i t₀_lt i_lt glue_eq
      -- what the parent glues there, by the composition
      have rim_glue := kids.glue_rimEdge c_lt k_lt
      rw [at_k, kids.glue_shift c_lt t₀_lt, glued] at rim_glue
      -- `c` is a child of the composition
      have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
      cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c k with
      | none => rw [mate_eq] at rim_glue; simp at rim_glue
      | some q =>
        obtain ⟨c', k'⟩ := q
        rw [mate_eq] at rim_glue
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at rim_glue
        obtain ⟨c'_lt_n, k'_lt, _⟩ := wf.mate_valid c k c' k' c_lt_n (by rw [kids.E_eq c_lt]; exact k_lt) mate_eq
        -- `c'` is a child
        have c'_lt : c' < nk T := by rwa [ofLens_n] at c'_lt_n
        rw [kids.E_eq c'_lt] at k'_lt
        obtain ⟨t'_lt, j_lt, _⟩ := (kids.sig c' c'_lt).rim_ok k' k'_lt
        obtain ⟨tile_eq, edge_eq⟩ := rim_glue
        subst tile_eq edge_eq
        exact ⟨tile_lt child c'_lt t'_lt, j_lt⟩
  · -- the signature
    intro p s p_lt
    rw [E_eq] at p_lt
    by_cases p_eq_A : p = cA T L
    · -- at the corner `cA`
      subst p_eq_A
      simp only [btau, ↓reduceIte]
      cases s with
      | true =>
        -- `R(cA) ↔ R(cB)`: the composition's crossover `L(A) ↔ L(B)`
        rw [kids.bport_R p_lt, kids.bport_R pB_lt]
        exact kids.follow_of_fullReach kids.csig.crossL (kids.gR_valid p_lt)
      | false =>
        -- `L(cA) ↔ L(cB)`: the composition's crossover `R(A) ↔ R(B)`
        rw [kids.bport_L p_lt, kids.bport_L pB_lt]
        exact kids.follow_of_fullReach kids.csig.crossR (kids.gL_valid p_lt)
    · by_cases p_eq_B : p = cB T L ω
      · -- at the corner `cB`: the crossover walks, backwards
        subst p_eq_B
        simp only [btau, ite_eq_right p_eq_A, ↓reduceIte]
        cases s with
        | true =>
          rw [kids.bport_R p_lt, kids.bport_R pA_lt]
          exact kids.follow_of_fullReach (kids.csig.crossL.reverse wf (kids.gR_valid pA_lt) (kids.gR_sigma pA_lt))
            (kids.gR_valid p_lt)
        | false =>
          rw [kids.bport_L p_lt, kids.bport_L pA_lt]
          exact kids.follow_of_fullReach (kids.csig.crossR.reverse wf (kids.gL_valid pA_lt) (kids.gL_sigma pA_lt))
            (kids.gL_valid p_lt)
      · -- a hook of the composition
        simp only [btau, ite_eq_right p_eq_A, ite_eq_right p_eq_B]
        have reach := kids.csig.hooks p p_lt p_eq_A p_eq_B  -- the composition's walk from `gR p` to `gL p`
        cases s with
        | true =>
          rw [kids.bport_R p_lt, Bool.not_true, kids.bport_L p_lt]
          exact kids.follow_of_fullReach reach (kids.gR_valid p_lt)
        | false =>
          rw [kids.bport_L p_lt, Bool.not_false, kids.bport_R p_lt]
          exact kids.follow_of_fullReach (reach.reverse wf (kids.gR_valid p_lt) (kids.gR_sigma p_lt))
            (kids.gL_valid p_lt)

end Kids

end SpectreKnot.Statement

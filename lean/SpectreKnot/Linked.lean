/-
**Strands as an equivalence relation.** `Linked` (same strand, `Statement.lean`) is transitive, contains `Follow`,
lifts from a child to its parent, and in every supertile is symmetric: gluing is symmetric (if edge `e_i` of tile `t`
is glued to edge `e_j` of tile `t'`, then `e_j` of `t'` is glued to `e_i` of `t`), so every move along a strand can be
undone. Used for Theorem B (`ProofB.lean`).
-/
import SpectreKnot.ProofA

namespace SpectreKnot.Statement

open Pattern Compose Gluing

namespace Patch

variable {P : Patch}

/-- **Same strand is transitive**: if `q` is on the strand of `p`, and `r` on the strand of `q`, then `r` is on the
strand of `p`. -/
theorem Linked.trans {p q r : Port} (first : P.Linked p q) (second : P.Linked q r) : P.Linked p r := by
  induction second with
  | refl => exact first
  | piece _ ih => exact .piece ih
  | edge _ across_eq ih => exact .edge ih across_eq

/-- Following a ribbon stays on one strand. -/
theorem Linked.of_follow {p r : Port} (follows : P.Follow p r) : P.Linked p r := by
  induction follows with
  | leave _ => exact .piece .refl
  | next across_eq _ ih => exact (Linked.edge (.piece .refl) across_eq).trans ih

/-- A strand stays among the ports of actual tiles. -/
theorem Linked.valid {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {p q : Port} (linked : P.Linked p q)
    (p_port : P.IsPort p) : P.IsPort q := by
  induction linked with
  | refl => exact p_port
  | piece _ ih =>
    -- the other end of a piece is on the same tile, at an actual vertex
    have end_valid := pieceEnd_valid ih.2
    exact ⟨end_valid.1 ▸ ih.1, end_valid.2⟩
  | edge _ across_eq ih => exact across_valid sig ih.1 ih.2 across_eq

/-- **Gluing is symmetric.** -/
def GlueSymm (P : Patch) : Prop :=
  ∀ t i t' j, t < P.tiles → i < 14 → P.glue t i = some (t', j) → P.glue t' j = some (t, i)

/-- The other end of the piece at the other end is the port itself. -/
theorem pieceEnd_pieceEnd (p : Port) : pieceEnd (pieceEnd p) = p := by
  obtain ⟨t, i, s⟩ := p
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp [pieceEnd]

/-- **Crossing an edge can be undone**: in a patch with the signature and symmetric gluing, if port `q` lies across
the edge from port `p`, then `p` lies across from `q`. -/
theorem across_symm {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) {p q : Port}
    (p_port : P.IsPort p) (across_eq : P.across p = some q) : P.across q = some p := by
  obtain ⟨t, i, s⟩ := p
  obtain ⟨ht, hi⟩ := p_port
  simp only at ht hi
  cases s with
  | true =>
    simp only [across] at across_eq
    cases glued : P.glue t i with
    | none => rw [glued] at across_eq; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      simp only [across, symm t i t' j ht hi glued, Option.map_some]
  | false =>
    simp only [across] at across_eq
    cases glued : P.glue t ((i + 13) % 14) with
    | none => rw [glued] at across_eq; contradiction
    | some e =>
      obtain ⟨t', j⟩ := e
      rw [glued] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      -- the far edge is an actual edge
      have hj := (sig.glue_ok t _ t' j ht (by omega) glued).2
      simp only [across, mod14 hj, symm t _ t' j ht (by omega) glued, Option.map_some, Option.some.injEq,
        Prod.mk.injEq]
      refine ⟨trivial, ?_, trivial⟩
      -- vertex `i - 1`, counted round the 14 vertices, without `%`
      have wrap : (i + 13) % 14 = (i + 13) - 14 ∨ (i + 13) % 14 = i + 13 := by omega
      rcases wrap with wrap_eq | wrap_eq <;> rw [wrap_eq] <;> omega

/-- **Same strand is symmetric** (in a patch with the signature and symmetric gluing). -/
theorem Linked.symm {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) {p q : Port}
    (linked : P.Linked p q) (p_port : P.IsPort p) : P.Linked q p := by
  induction linked with
  | refl => exact .refl
  | @piece q _ ih =>
    -- back along the piece
    have back_along : P.Linked (pieceEnd q) q := by
      -- one move along the piece from its other end
      have along := Linked.piece (P := P) (p := pieceEnd q) .refl
      rwa [pieceEnd_pieceEnd] at along
    exact back_along.trans ih
  | @edge q q' to_q across_eq ih =>
    -- back across the edge
    exact (Linked.edge .refl (across_symm sig symm (to_q.valid sig p_port) across_eq)).trans ih

end Patch

/-! ### Lifting to the parent, and symmetry of the parent's gluing -/

namespace Kids

set_option linter.unusedSectionVars false

-- `kids`: the children satisfy what the composition needs
variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool}
  (kids : Kids T child L d ω o)

include kids

/-- **A strand of a child is part of a strand of the parent.** -/
theorem linked_lift {c : Nat} (hc : c < nk T) {p q : Port} (linked : (child c).Linked p q)
    (p_port : (child c).IsPort p) : (compose T child).Linked (shiftP child c p) (shiftP child c q) := by
  induction linked with
  | refl => exact .refl
  | piece _ ih => rw [← pieceEnd_shift]; exact .piece ih
  | @edge q q' to_q across_eq ih =>
    exact .edge ih (kids.across_in' hc (to_q.valid (kids.sig c hc) p_port).1 across_eq)

/-- The parent's gluing is symmetric if the children's are. -/
theorem glue_symm (children_symm : ∀ c, c < nk T → (child c).GlueSymm) : (compose T child).GlueSymm := by
  -- the composition is well formed
  have wf := kids.gsig.wf
  intro t i t' j ht hi glued
  -- the child `c` that tile `t` belongs to
  obtain ⟨c, hc, after_start, before_end⟩ := owner_exists child (nk T) t ht
  obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + offC child c := ⟨t - offC child c, by omega⟩
  -- its number `t₀` in child `c`
  have ht₀ : t₀ < (child c).tiles := by omega
  -- child `c` has the signature
  have sig := kids.sig c hc
  cases inside : (child c).glue t₀ i with
  | some e =>
    -- glued inside the child: the child's own gluing, shifted, which is symmetric
    obtain ⟨t₂, j₂⟩ := e
    rw [kids.glue_shift hc ht₀] at glued
    simp only [glueAt, inside, Option.some.injEq, Prod.mk.injEq] at glued
    obtain ⟨rfl, rfl⟩ := glued
    -- the far tile is an actual tile of child `c`
    have far_valid := sig.glue_ok t₀ i t₂ j₂ ht₀ hi inside
    rw [kids.glue_shift hc far_valid.1]
    simp only [glueAt, children_symm c hc t₀ i t₂ j₂ ht₀ hi inside]
  | none =>
    -- on the child's rim, at rim edge `k`: glued to a sibling's edge, as the gluing's `mate` says
    obtain ⟨k, hk, at_k⟩ := sig.rim_all t₀ i ht₀ hi inside
    -- `c` is a child of the gluing
    have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact hc
    -- the parent glues rim edge `k` of child `c` as `mate` says
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
      -- the sibling's edge `k'` is an actual rim edge, glued back to edge `k` of `c`
      obtain ⟨sib_lt_n, sib_edge_lt, mated_back⟩ :=
        wf.mate_valid c k c' k' c_lt_n (by rw [kids.E_eq hc]; exact hk) mated
      -- the sibling is an actual child
      have sib_lt : c' < nk T := by rwa [ofLens_n] at sib_lt_n
      -- the parent glues the sibling's rim edge `k'` as `mate` says
      have formula' := kids.glue_rimEdge sib_lt (by rw [← kids.E_eq sib_lt]; exact sib_edge_lt)
      rw [formula', mated_back]
      simp only [Option.map_some, at_k]

end Kids

/-! ### Every supertile has symmetric gluing -/

/-- A single tile glues nothing, so its gluing is symmetric. -/
theorem tile_glueSymm : tile.GlueSymm := fun _ _ _ _ _ _ glued => by simp [tile] at glued

/-- The kernel's check of the level-1 data. -/
def level1Symm (K : Kind) : Bool :=
  (List.range (level1 K).tiles).all fun t => (List.range 14).all fun i =>
    match (level1 K).glue t i with
    | none => true
    | some (t', j) => (level1 K).glue t' j == some (t, i)

/-- The check passes for all nine kinds. -/
theorem level1Symm_all : ∀ K, level1Symm K = true := by intro K; cases K <;> decide +kernel

/-- Every level-1 supertile has symmetric gluing. -/
theorem level1_glueSymm (K : Kind) : (level1 K).GlueSymm := by
  intro t i t' j ht hi glued
  -- the kernel's check
  have check := level1Symm_all K
  simp only [level1Symm, List.all_eq_true, List.mem_range] at check
  -- at tile `t` and edge `i`
  have at_edge := check t ht i hi
  rw [glued] at at_edge
  simpa using at_edge

/-- **Every supertile has symmetric gluing**, by induction on the level. -/
theorem super_glueSymm : ∀ m K, (super m K).GlueSymm
  | 0, _ => tile_glueSymm
  | 1, K => level1_glueSymm K
  | m + 2, T => (kids_at (m := m + 1) (by omega) T (fun K => good (m + 1) K (by omega))).glue_symm
      (fun c _ => super_glueSymm (m + 1) _)

/-- **Same strand is symmetric in every supertile of level `m ≥ 1`.** -/
theorem linked_symm {m : Nat} (m_pos : 1 ≤ m) {K : Kind} {p q : Port} (linked : (super m K).Linked p q)
    (p_port : (super m K).IsPort p) : (super m K).Linked q p :=
  linked.symm (good m K m_pos).sig (super_glueSymm m K) p_port

end SpectreKnot.Statement

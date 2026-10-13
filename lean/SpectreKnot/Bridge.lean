/-
**Lemma 4.2 at tile level.** If the children of `compose T child` have the signature, with the corners and side
lengths of the abstract composition `Comp.ofLens T L d ω`, then following a ribbon of the parent is a walk of that
composition: from a child's rim port, the ribbon runs through the child to the port its signature pairs it with
(`τ`), then straight across into the next child (`σ`) or out of the parent. So the parent has no closed strand when
the composition has none (`Kids.noClosed`), and its rim ports are joined as the composition's walks say
(`Kids.follow_of_reach`).
-/
import SpectreKnot.ParentRim
import SpectreKnot.Reverse

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- Port `q` of child `c`, renumbered as a port of the parent. -/
def shiftP (child : Nat → Patch) (c : Nat) (q : Port) : Port := (q.1 + offC child c, q.2.1, q.2.2)

/-- Renumbering a child's port into the parent commutes with going to the other end of its piece. -/
theorem pieceEnd_shift (child : Nat → Patch) (c : Nat) (q : Port) :
    pieceEnd (shiftP child c q) = shiftP child c (pieceEnd q) := by
  obtain ⟨t, i, s⟩ := q
  rcases i with _ | _ | i <;> rfl

/-- The other end of a piece is on the same tile, at an actual vertex. -/
theorem pieceEnd_valid {q : Port} (i_lt : q.2.1 < 14) : (pieceEnd q).1 = q.1 ∧ (pieceEnd q).2.1 < 14 := by
  obtain ⟨t, i, s⟩ := q
  rcases i with _ | _ | i
  · exact ⟨rfl, (by decide : (1 : Nat) < 14)⟩
  · exact ⟨rfl, (by decide : (0 : Nat) < 14)⟩
  · exact ⟨rfl, i_lt⟩

/-- The edge before vertex `i + 1` (counted round the 14 vertices) is edge `i`. -/
theorem mod14 {i : Nat} (i_lt : i < 14) : ((i + 1) % 14 + 13) % 14 = i := by omega

namespace Patch

variable {P : Patch}

/-- In a patch with the signature, the port across a glued edge is a port of an actual tile. -/
theorem across_valid {o : Bool} {A B : Nat} (has_sig : P.HasSig o A B) {p q : Port}
    (t_lt : p.1 < P.tiles) (i_lt : p.2.1 < 14) (across_eq : P.across p = some q) : q.1 < P.tiles ∧ q.2.1 < 14 := by
  obtain ⟨t, i, s⟩ := p
  simp only at t_lt i_lt
  cases s with
  | true =>
    -- port `R(v_i)`, on edge `e_i`
    simp only [across] at across_eq
    cases glue_eq : P.glue t i with
    | none => rw [glue_eq] at across_eq; contradiction
    | some edge =>
      obtain ⟨t', j⟩ := edge
      rw [glue_eq] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      exact has_sig.glue_ok t i t' j t_lt i_lt glue_eq
  | false =>
    -- port `L(v_i)`, on edge `e_{i-1}`
    simp only [across] at across_eq
    cases glue_eq : P.glue t ((i + 13) % 14) with
    | none => rw [glue_eq] at across_eq; contradiction
    | some edge =>
      obtain ⟨t', j⟩ := edge
      rw [glue_eq] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      exact ⟨(has_sig.glue_ok t _ t' j t_lt (by omega) glue_eq).1, Nat.mod_lt _ (by omega)⟩

/-- Following a ribbon ends at a rim port, and stays among the patch's ports. -/
theorem Follow.end_ {o : Bool} {A B : Nat} (has_sig : P.HasSig o A B) {q r : Port} (follow : P.Follow q r) :
    q.1 < P.tiles → q.2.1 < 14 → P.across r = none ∧ r.1 < P.tiles ∧ r.2.1 < 14 := by
  induction follow with
  | @leave q leaves =>
    intro t_lt i_lt
    -- the other end of the piece is a port of the same tile
    have end_valid := pieceEnd_valid i_lt
    exact ⟨leaves, end_valid.1 ▸ t_lt, end_valid.2⟩
  | @next q q' r crosses _ ih =>
    intro t_lt i_lt
    -- the other end of the piece is a port of the same tile
    have end_valid := pieceEnd_valid i_lt
    -- and the port across from it is a port of an actual tile
    have next_valid := across_valid has_sig (end_valid.1 ▸ t_lt) end_valid.2 crosses
    exact ih next_valid.1 next_valid.2

/-- A port with nothing across it is a rim port: one of the two at a rim vertex. -/
theorem rim_port {o : Bool} {A B : Nat} (has_sig : P.HasSig o A B) {r : Port} (t_lt : r.1 < P.tiles)
    (i_lt : r.2.1 < 14) (unglued : P.across r = none) : ∃ u s, u < P.E ∧ r = P.bport o (u, s) := by
  obtain ⟨t, i, s⟩ := r
  simp only at t_lt i_lt
  -- the rim is not empty, since this port's edge is on it
  have rim_pos : 0 < P.E := by
    cases s with
    | true =>
      simp only [across, Option.map_eq_none_iff] at unglued
      obtain ⟨k, k_lt, _⟩ := has_sig.rim_all t i t_lt i_lt unglued
      omega
    | false =>
      simp only [across, Option.map_eq_none_iff] at unglued
      obtain ⟨k, k_lt, _⟩ := has_sig.rim_all t _ t_lt (Nat.mod_lt _ (by omega)) unglued
      omega
  cases s with
  | true =>
    -- `R(v_i)` lies on rim edge `k`, near its start in the tile's own sense
    simp only [across, Option.map_eq_none_iff] at unglued
    obtain ⟨k, k_lt, at_k⟩ := has_sig.rim_all t i t_lt i_lt unglued
    cases o with
    | true => exact ⟨k, true, k_lt, by simp [bport, at_k]⟩
    | false => exact ⟨nxt P.E k, false, nxt_lt k_lt, by simp [bport, prv_nxt k_lt, at_k]⟩
  | false =>
    -- `L(v_i)` lies on rim edge `k`, near its end in the tile's own sense
    simp only [across, Option.map_eq_none_iff] at unglued
    obtain ⟨k, k_lt, at_k⟩ := has_sig.rim_all t _ t_lt (Nat.mod_lt _ (by omega)) unglued
    -- the vertex after edge `e_{i-1}` is `v_i`
    have mod_eq : ((i + 13) % 14 + 1) % 14 = i := by omega
    cases o with
    | true => exact ⟨nxt P.E k, false, nxt_lt k_lt, by simp [bport, prv_nxt k_lt, at_k, mod_eq]⟩
    | false => exact ⟨k, true, k_lt, by simp [bport, at_k, mod_eq]⟩

end Patch

/-- What the children must satisfy: positive side lengths, glued sides of equal length, vertices where the lengths
put them, the signature with the composition's corners, and the composition itself with the signature. -/
structure Kids (T : Kind) (child : Nat → Patch) (L : Nat → Nat → Nat) (d : Nat) (ω o : Bool) : Prop where
  len_pos : ∀ c j, 1 ≤ L c j
  pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j
  shape : ∀ c, c < nk T → (child c).vtx = (List.range 7).map (pos (L c)) ∧ (child c).E = pos (L c) 6
  sig : ∀ c, c < nk T →
    (child c).HasSig o ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c)
  gsig : Sig (Comp.ofLens T L d ω).toGluing (nk T - 1)

/-- The parent's port for the gluing's port `(c, u, s)`: the port of child `c` at its rim vertex `u`. -/
def ιP (child : Nat → Patch) (o : Bool) : GPort → Port
  | (c, u, s) => shiftP child c ((child c).bport o (u, s))

namespace Kids

set_option linter.unusedSectionVars false

variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool}
  (kids : Kids T child L d ω o)

include kids

/-- Every child has a tile. -/
theorem tiles_pos : ∀ c, c < nk T → 0 < (child c).tiles := fun c c_lt => (kids.sig c c_lt).tiles_pos

/-- The composition's rim length for child `c` is that of child `c`'s rim. -/
theorem E_eq {c : Nat} (c_lt : c < nk T) : (Comp.ofLens T L d ω).toGluing.E c = (child c).E := by
  rw [ofLens_E c_lt, (kids.shape c c_lt).2]

/-- What the parent glues across an edge of tile `t` of child `c` is what `glueAt` says. -/
theorem glue_shift {c t : Nat} (c_lt : c < nk T) (t_lt : t < (child c).tiles) (i : Nat) :
    (compose T child).glue (t + offC child c) i = glueAt T child c t i := by
  rw [Nat.add_comm]; exact compose_glue kids.tiles_pos c_lt t_lt i

/-- Across an edge inside a child, the parent glues as the child does. -/
theorem across_in {c t i : Nat} {s : Bool} {q' : Port} (c_lt : c < nk T) (t_lt : t < (child c).tiles)
    (across_eq : (child c).across (t, i, s) = some q') :
    (compose T child).across (shiftP child c (t, i, s)) = some (shiftP child c q') := by
  cases s with
  | true =>
    -- port `R(v_i)`, on edge `e_i`
    simp only [Patch.across] at across_eq
    cases glue_eq : (child c).glue t i with
    | none => rw [glue_eq] at across_eq; contradiction
    | some edge =>
      obtain ⟨t', j⟩ := edge
      rw [glue_eq] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      simp only [shiftP, Patch.across]
      rw [kids.glue_shift c_lt t_lt]
      simp only [glueAt, glue_eq, Option.map_some]
  | false =>
    -- port `L(v_i)`, on edge `e_{i-1}`
    simp only [Patch.across] at across_eq
    cases glue_eq : (child c).glue t ((i + 13) % 14) with
    | none => rw [glue_eq] at across_eq; contradiction
    | some edge =>
      obtain ⟨t', j⟩ := edge
      rw [glue_eq] at across_eq
      simp only [Option.map_some, Option.some.injEq] at across_eq
      subst across_eq
      simp only [shiftP, Patch.across]
      rw [kids.glue_shift c_lt t_lt]
      simp only [glueAt, glue_eq, Option.map_some]

/-- Across child `c`'s rim edge `k`, the parent glues what the composition's `mate` says. -/
theorem glue_rimEdge {c k : Nat} (c_lt : c < nk T) (k_lt : k < (child c).E) :
    (compose T child).glue (((child c).edgeAt k).1 + offC child c) ((child c).edgeAt k).2 =
      ((Comp.ofLens T L d ω).toGluing.mate c k).map fun (c', k') =>
        (((child c').edgeAt k').1 + offC child c', ((child c').edgeAt k').2) := by
  -- child `c` has the signature
  have has_sig := kids.sig c c_lt
  obtain ⟨t_lt, _, unglued⟩ := has_sig.rim_ok k k_lt
  rw [kids.glue_shift c_lt t_lt]
  exact glue_rim (fun c _ j _ => kids.len_pos c j) kids.pair kids.shape c_lt
    (by rw [← (kids.shape c c_lt).2]; exact k_lt) unglued
    (fun k' k'_lt same_edge => has_sig.rim_inj k' k k'_lt k_lt same_edge)

/-- **Across a child's rim port, the parent continues as `σ` says.** -/
theorem across_rim {c u : Nat} {s : Bool} (c_lt : c < nk T) (u_lt : u < (child c).E) :
    (compose T child).across (ιP child o (c, u, s)) =
      ((Comp.ofLens T L d ω).toGluing.sigma (c, u, s)).map (ιP child o) := by
  -- child `c` has the signature
  have has_sig := kids.sig c c_lt
  -- the composition is well formed
  have wf := kids.gsig.wf
  -- `c` is a child of the composition
  have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
  cases s with
  | true =>
    -- port `R(u)`, on rim edge `u`
    -- the edge is an actual edge of its tile
    have i_lt := (has_sig.rim_ok u u_lt).2.1
    simp only [Gluing.sigma]
    cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c u with
    | none =>
      -- the parent's gluing across rim edge `u`
      have glue_eq := kids.glue_rimEdge c_lt u_lt
      rw [mate_eq] at glue_eq
      cases o <;> simp only [ιP, shiftP, Patch.bport, Patch.across, if_true, if_false, Bool.false_eq_true,
        mod14 i_lt, glue_eq] <;> rfl
    | some p =>
      obtain ⟨c', k'⟩ := p
      -- the parent's gluing across rim edge `u`
      have glue_eq := kids.glue_rimEdge c_lt u_lt
      rw [mate_eq] at glue_eq
      obtain ⟨c'_lt, k'_lt, _⟩ := wf.mate_valid c u c' k' c_lt_n (by rw [kids.E_eq c_lt]; exact u_lt) mate_eq
      -- the edge across is an actual edge of its tile in child `c'`
      have i_lt' := ((kids.sig c' (by rwa [ofLens_n] at c'_lt)).rim_ok k'
        (by rw [← kids.E_eq (by rwa [ofLens_n] at c'_lt)]; exact k'_lt)).2.1
      cases o <;> simp only [ιP, shiftP, Patch.bport, Patch.across, if_true, if_false, Bool.false_eq_true,
        mod14 i_lt, glue_eq, Option.map_some]
  | false =>
    -- port `L(u)`, on rim edge `u - 1`
    -- the edge before `u` is a rim edge
    have prv_lt_E := prv_lt u_lt
    -- and an actual edge of its tile
    have i_lt := (has_sig.rim_ok _ prv_lt_E).2.1
    simp only [Gluing.sigma]
    rw [kids.E_eq c_lt]
    cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c (prv (child c).E u) with
    | none =>
      -- the parent's gluing across rim edge `u - 1`
      have glue_eq := kids.glue_rimEdge c_lt prv_lt_E
      rw [mate_eq] at glue_eq
      cases o <;> simp only [ιP, shiftP, Patch.bport, Patch.across, if_true, if_false, Bool.false_eq_true,
        mod14 i_lt, glue_eq] <;> rfl
    | some p =>
      obtain ⟨c', k'⟩ := p
      -- the parent's gluing across rim edge `u - 1`
      have glue_eq := kids.glue_rimEdge c_lt prv_lt_E
      rw [mate_eq] at glue_eq
      obtain ⟨c'_lt_n, k'_lt, _⟩ := wf.mate_valid c _ c' k' c_lt_n (by rw [kids.E_eq c_lt]; exact prv_lt_E) mate_eq
      -- `c'` is a child
      have c'_lt : c' < nk T := by rwa [ofLens_n] at c'_lt_n
      simp only [Option.map_some]
      rw [kids.E_eq c'_lt] at k'_lt ⊢
      -- the edge across is an actual edge of its tile in child `c'`
      have i_lt' := ((kids.sig c' c'_lt).rim_ok k' k'_lt).2.1
      cases o <;> simp only [ιP, shiftP, Patch.bport, Patch.across, if_true, if_false, Bool.false_eq_true,
        mod14 i_lt, glue_eq, Option.map_some, prv_nxt k'_lt]

/-- `across_in`, for a port not yet split into its tile, vertex and hand. -/
theorem across_in' {c : Nat} {p q' : Port} (c_lt : c < nk T) (t_lt : p.1 < (child c).tiles)
    (across_eq : (child c).across p = some q') :
    (compose T child).across (shiftP child c p) = some (shiftP child c q') := by
  obtain ⟨t, i, s⟩ := p
  exact kids.across_in c_lt t_lt across_eq

/-- A strand of child `c` is a stretch of a strand of the parent. -/
theorem lift {c : Nat} (c_lt : c < nk T) : ∀ q r, (child c).Follow q r → q.1 < (child c).tiles → q.2.1 < 14 →
    ∀ r', ((compose T child).across (shiftP child c r) = none ∧ r' = shiftP child c r) ∨
      (∃ q₁, (compose T child).across (shiftP child c r) = some q₁ ∧ (compose T child).Follow q₁ r') →
    (compose T child).Follow (shiftP child c q) r' := by
  intro q r follow
  induction follow with
  | @leave q leaves =>
    intro _ _ r' after
    rcases after with ⟨on_rim, rfl⟩ | ⟨q₁, crosses, follow_on⟩
    · -- the child's strand ends on the parent's rim too
      -- so the parent's strand leaves there
      have leave :=
        Patch.Follow.leave (P := compose T child) (p := shiftP child c q) (by rw [pieceEnd_shift]; exact on_rim)
      rwa [pieceEnd_shift] at leave
    · -- the child's strand ends on the child's rim, and the parent's strand crosses into a sibling
      exact .next (by rw [pieceEnd_shift]; exact crosses) follow_on
  | @next q q' r crosses _ ih =>
    intro t_lt i_lt r' after
    -- the other end of the piece is a port of the same tile
    have end_valid := pieceEnd_valid i_lt
    -- and the port across from it is a port of an actual tile of the child
    have next_valid := Patch.across_valid (kids.sig c c_lt) (end_valid.1 ▸ t_lt) end_valid.2 crosses
    refine .next ?_ (ih next_valid.1 next_valid.2 r' after)
    rw [pieceEnd_shift]
    exact kids.across_in' c_lt (end_valid.1 ▸ t_lt) crosses

/-- A rim port of child `c` is a port of an actual tile. -/
theorem bport_valid {c u : Nat} {s : Bool} (c_lt : c < nk T) (u_lt : u < (child c).E) :
    ((child c).bport o (u, s)).1 < (child c).tiles ∧ ((child c).bport o (u, s)).2.1 < 14 := by
  -- child `c` has the signature
  have has_sig := kids.sig c c_lt
  cases s with
  | true =>
    obtain ⟨t_lt, i_lt, _⟩ := has_sig.rim_ok u u_lt
    cases o <;> exact ⟨t_lt, by simp only [Patch.bport]; first | exact i_lt | exact Nat.mod_lt _ (by omega)⟩
  | false =>
    obtain ⟨t_lt, i_lt, _⟩ := has_sig.rim_ok _ (prv_lt u_lt)
    cases o <;> exact ⟨t_lt, by simp only [Patch.bport]; first | exact i_lt | exact Nat.mod_lt _ (by omega)⟩

/-- The composition's `τ` on child `c` is the child's signature pairing `btau`, with the composition's corners. -/
theorem tau_btau (c u : Nat) (s : Bool) :
    (Comp.ofLens T L d ω).toGluing.tau (c, u, s) =
      (c, (btau ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c) (u, s)).1,
        (btau ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c) (u, s)).2) := by
  simp only [Gluing.tau, btau]
  by_cases at_A : u = (Comp.ofLens T L d ω).toGluing.A c
  · simp [at_A]
  · by_cases at_B : u = (Comp.ofLens T L d ω).toGluing.B c
    · subst at_B
      by_cases B_eq_A : (Comp.ofLens T L d ω).toGluing.B c = (Comp.ofLens T L d ω).toGluing.A c <;> simp [B_eq_A]
    · simp [at_A, at_B]

/-- The signature pairing keeps rim vertices on the rim. -/
theorem btau_lt {c u : Nat} {s : Bool} (c_lt : c < nk T) (u_lt : u < (child c).E) :
    (btau ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c) (u, s)).1 < (child c).E := by
  -- the composition is well formed
  have wf := kids.gsig.wf
  -- `c` is a child of the composition
  have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
  -- corner `A` is on the child's rim
  have A_lt := wf.A_lt c c_lt_n
  -- and so is corner `B`
  have B_lt := wf.B_lt c c_lt_n
  rw [kids.E_eq c_lt] at A_lt B_lt
  simp only [btau]
  split
  · exact B_lt
  · split
    · exact A_lt
    · exact u_lt

/-- **A walk of the composition is a strand of the parent** (Lemma 4.2). -/
theorem follow_of_reach : ∀ k x r, (Comp.ofLens T L d ω).toGluing.FReach k x r →
    (Comp.ofLens T L d ω).toGluing.Valid x → (compose T child).Follow (ιP child o x) (ιP child o r) := by
  -- the composition is well formed
  have wf := kids.gsig.wf
  intro k x r reach
  induction reach with
  | @stop x on_rim =>
    -- through child `c` by its signature, then out of the parent
    intro valid
    obtain ⟨c, u, s⟩ := x
    obtain ⟨c_lt_n, u_lt_E⟩ := valid
    -- `c` is a child
    have c_lt : c < nk T := by rwa [ofLens_n] at c_lt_n
    -- `u` is a vertex of child `c`'s rim
    have u_lt : u < (child c).E := by rwa [kids.E_eq c_lt] at u_lt_E
    rw [kids.tau_btau] at on_rim ⊢
    -- the start is a port of an actual tile
    have port_valid := kids.bport_valid (s := s) c_lt u_lt
    refine kids.lift c_lt _ _ ((kids.sig c c_lt).sig u s u_lt) port_valid.1 port_valid.2 _ (Or.inl ⟨?_, rfl⟩)
    -- across the far port, the parent continues as `σ` says: nowhere
    have across_eq :=
      kids.across_rim (s := (btau ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c)
        (u, s)).2) c_lt (kids.btau_lt (s := s) c_lt u_lt)
    simp only [ιP] at across_eq
    rw [across_eq, on_rim]; rfl
  | @step k x y r first_step _ ih =>
    -- through child `c` by its signature, then across into the next child, and on by induction
    intro valid
    obtain ⟨c, u, s⟩ := x
    obtain ⟨c_lt_n, u_lt_E⟩ := valid
    -- `c` is a child
    have c_lt : c < nk T := by rwa [ofLens_n] at c_lt_n
    -- `u` is a vertex of child `c`'s rim
    have u_lt : u < (child c).E := by rwa [kids.E_eq c_lt] at u_lt_E
    -- the next port is a port of an actual child
    have y_valid := sigma_valid wf (tau_valid wf ⟨c_lt_n, u_lt_E⟩) first_step
    rw [kids.tau_btau] at first_step
    -- the start is a port of an actual tile
    have port_valid := kids.bport_valid (s := s) c_lt u_lt
    refine kids.lift c_lt _ _ ((kids.sig c c_lt).sig u s u_lt) port_valid.1 port_valid.2 _
      (Or.inr ⟨ιP child o y, ?_, ih y_valid⟩)
    -- across the far port, the parent continues as `σ` says: to `y`
    have across_eq :=
      kids.across_rim (s := (btau ((Comp.ofLens T L d ω).toGluing.A c) ((Comp.ofLens T L d ω).toGluing.B c)
        (u, s)).2) c_lt (kids.btau_lt (s := s) c_lt u_lt)
    simp only [ιP] at across_eq
    rw [across_eq, first_step]; rfl

/-- `follow_of_reach`, for the full walk with any number of crossings. -/
theorem follow_of_fullReach {x r : GPort} (reach : (Comp.ofLens T L d ω).toGluing.FullReach x r)
    (valid : (Comp.ofLens T L d ω).toGluing.Valid x) : (compose T child).Follow (ιP child o x) (ιP child o r) := by
  obtain ⟨k, reach_k⟩ := reach
  exact kids.follow_of_reach k x r reach_k valid

/-- **No closed strand in the parent.** -/
theorem noClosed : (compose T child).NoClosedStrand := by
  -- the composition is well formed
  have wf := kids.gsig.wf
  intro p is_port
  obtain ⟨t, i, s⟩ := p
  obtain ⟨t_lt, i_lt⟩ := is_port
  simp only at t_lt i_lt
  -- the child `c` that tile `t` belongs to, and its number `t₀` there
  obtain ⟨c, c_lt, start_le, lt_end⟩ := owner_exists child (nk T) t t_lt
  obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + offC child c := ⟨t - offC child c, by omega⟩
  -- child `c` has the signature
  have has_sig := kids.sig c c_lt
  -- in the child, the ribbon leaves at a rim port `(u, s')`
  obtain ⟨r, follow⟩ := has_sig.noClosed (t₀, i, s) ⟨by simp only; omega, i_lt⟩
  obtain ⟨leaves, r_tile, r_vertex⟩ := Patch.Follow.end_ has_sig follow (by simp only; omega) i_lt
  obtain ⟨u, s', u_lt, rfl⟩ := Patch.rim_port has_sig r_tile r_vertex leaves
  -- `c` is a child of the composition
  have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
  -- across that rim port, the parent continues as `σ` says
  have across_eq := kids.across_rim (s := s') c_lt u_lt
  simp only [ιP] at across_eq
  cases sigma_eq : (Comp.ofLens T L d ω).toGluing.sigma (c, u, s') with
  | none =>
    -- on the parent's rim: the ribbon leaves the parent there
    exact ⟨_, kids.lift c_lt _ _ follow (by simp only; omega) i_lt _ (Or.inl ⟨by rw [across_eq, sigma_eq]; rfl, rfl⟩)⟩
  | some y =>
    -- into a sibling at `y`
    -- `y` is a port of an actual child
    have y_valid := sigma_valid wf ⟨c_lt_n, by rw [kids.E_eq c_lt]; exact u_lt⟩ sigma_eq
    -- the composition's walk from `y` reaches its rim
    obtain ⟨r', reach'⟩ := kids.gsig.noLoops y y_valid
    exact ⟨_, kids.lift c_lt _ _ follow (by simp only; omega) i_lt _
      (Or.inr ⟨ιP child o y, by rw [across_eq, sigma_eq]; rfl, kids.follow_of_fullReach reach' y_valid⟩)⟩

end Kids

end SpectreKnot.Statement

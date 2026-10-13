/-
The signature of a patch of tiles (Def 4.3 at tile level), for the proof of Theorem A.

A supertile is a *box*: its rim is a cycle of tile edges, and at each rim vertex there are two ports, `R` (on the rim
edge that starts there) and `L` (on the rim edge that ends there). `Patch.HasSig P o A B` says: the rim list is the
set of unglued edges, without repeats; no strand of `P` is closed; and following the ribbon from any rim port leads
to the port the signature pairs it with: the other port at the same vertex (a hook), except at the corners `A` and `B`,
where `R(A) ↔ R(B)` and `L(A) ↔ L(B)`. The rim runs in the patch's own orientation `o` (`true`: counter-clockwise, as
the tiles' own; `false`: clockwise), which decides which end of a tile edge is "near the start".

The base cases: a single tile, and the nine level-1 supertiles (checked by the kernel).
-/
import SpectreKnot.Statement
import SpectreKnot.Lengths
import SpectreKnot.Gluing
import SpectreKnot.Lens

namespace SpectreKnot.Statement

open Pattern

namespace Patch

variable (P : Patch)

/-- The number of rim edges. -/
abbrev E : Nat := P.rim.length

/-- Rim edge number `k`. -/
def edgeAt (k : Nat) : Nat × Nat := P.rim.getD k (0, 0)

/-- The ports at rim vertex `k`, the vertex where rim edge `k` begins (in the orientation `o`): `(k, true)` is `R(k)`,
on rim edge `k` near the vertex; `(k, false)` is `L(k)`, on rim edge `k - 1` near the vertex. Rim edge `(t, i)` is
edge `e_i` of tile `t`, from `v_i` to `v_{i+1}`; it is traversed that way if `o`, the other way if not. -/
def bport (o : Bool) : Nat × Bool → Port
  | (k, true) =>
    if o then ((P.edgeAt k).1, (P.edgeAt k).2, true) else ((P.edgeAt k).1, ((P.edgeAt k).2 + 1) % 14, false)
  | (k, false) =>
    if o then ((P.edgeAt (prv P.E k)).1, ((P.edgeAt (prv P.E k)).2 + 1) % 14, false)
    else ((P.edgeAt (prv P.E k)).1, (P.edgeAt (prv P.E k)).2, true)

end Patch

/-- The signature's pairing of the rim ports of a box with corners `A`, `B` (Def 4.3): a hook at every other vertex
(`L(k) ↔ R(k)`), and `R(A) ↔ R(B)`, `L(A) ↔ L(B)`. -/
def btau (A B : Nat) : Nat × Bool → Nat × Bool
  | (k, s) => if k = A then (B, s) else if k = B then (A, s) else (k, !s)

/-- **A patch with the signature.** -/
structure Patch.HasSig (P : Patch) (o : Bool) (A B : Nat) : Prop where
  tiles_pos : 0 < P.tiles
  /-- the rim edges are edges of actual tiles, and are not glued -/
  rim_ok : ∀ k, k < P.E → (P.edgeAt k).1 < P.tiles ∧ (P.edgeAt k).2 < 14 ∧ P.glue (P.edgeAt k).1 (P.edgeAt k).2 = none
  /-- no edge is listed twice -/
  rim_inj : ∀ k k', k < P.E → k' < P.E → P.edgeAt k = P.edgeAt k' → k = k'
  /-- every unglued edge is listed -/
  rim_all : ∀ t i, t < P.tiles → i < 14 → P.glue t i = none → ∃ k, k < P.E ∧ P.edgeAt k = (t, i)
  /-- glued edges are edges of actual tiles -/
  glue_ok : ∀ t i t' j, t < P.tiles → i < 14 → P.glue t i = some (t', j) → t' < P.tiles ∧ j < 14
  noClosed : P.NoClosedStrand
  /-- following the ribbon from a rim port leads to the port the signature pairs it with -/
  sig : ∀ k s, k < P.E → P.Follow (P.bport o (k, s)) (P.bport o (btau A B (k, s)))

/-! ### Following a ribbon, as a computation -/

namespace Patch

variable (P : Patch)

/-- Following the ribbon from `p`, with at most `f` steps. -/
def follow : Nat → Port → Option Port
  | 0, _ => none
  | f + 1, p =>
    match P.across (pieceEnd p) with
    | none => some (pieceEnd p)
    | some q => follow f q

/-- The computation is sound: if `follow` finds a port within its fuel, following the ribbon really leaves the patch
there. -/
theorem follow_sound : ∀ f p r, P.follow f p = some r → P.Follow p r := by
  intro f
  induction f with
  | zero => intro p r found; simp [follow] at found
  | succ f ih =>
    intro p r found
    simp only [follow] at found
    cases across_eq : P.across (pieceEnd p) with
    | none =>
      -- the other end of the piece is on the rim: the walk leaves there
      rw [across_eq] at found; simp only [Option.some.injEq] at found; subst found; exact .leave across_eq
    | some q =>
      -- the ribbon crosses to `q`, and the rest of the walk starts there
      rw [across_eq] at found; exact .next across_eq (ih q r found)

/-- The checks of `HasSig`, as a computation (`f`: the fuel for each walk). -/
def sigCheck (o : Bool) (A B f : Nat) : Bool :=
  decide (0 < P.tiles) &&
  ((List.range P.E).all fun k =>
    decide ((P.edgeAt k).1 < P.tiles) && decide ((P.edgeAt k).2 < 14) &&
      (P.glue (P.edgeAt k).1 (P.edgeAt k).2).isNone) &&
  ((List.range P.E).all fun k => (List.range P.E).all fun k' => !(P.edgeAt k == P.edgeAt k') || k == k') &&
  ((List.range P.tiles).all fun t => (List.range 14).all fun i =>
    (P.glue t i).isSome || (List.range P.E).any fun k => P.edgeAt k == (t, i)) &&
  ((List.range P.tiles).all fun t => (List.range 14).all fun i =>
    match P.glue t i with
    | none => true
    | some (t', j) => decide (t' < P.tiles) && decide (j < 14)) &&
  ((List.range P.tiles).all fun t => (List.range 14).all fun i => [true, false].all fun s =>
    (P.follow f (t, i, s)).isSome) &&
  ((List.range P.E).all fun k => [true, false].all fun s =>
    P.follow f (P.bport o (k, s)) == some (P.bport o (btau A B (k, s))))

/-- The checker is sound: if `sigCheck` returns `true` (for any fuel), the patch has the signature at `A`, `B`. -/
theorem sigCheck_sound {o : Bool} {A B f : Nat} (check : P.sigCheck o A B f = true) : P.HasSig o A B := by
  simp only [sigCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Option.isNone_iff_eq_none, Bool.not_eq_true', beq_iff_eq, List.any_eq_true, Option.isSome_iff_exists] at check
  obtain ⟨⟨⟨⟨⟨⟨tiles_pos, rim_ok⟩, rim_inj⟩, rim_all⟩, glue_ok⟩, all_leave⟩, sig_ok⟩ := check
  refine ⟨tiles_pos, fun k on_rim => ⟨(rim_ok k on_rim).1.1, (rim_ok k on_rim).1.2, (rim_ok k on_rim).2⟩,
    fun k k' on_rim on_rim' same_edge => ?_, fun t i is_tile is_vertex unglued => ?_,
    fun t i t' j is_tile is_vertex glued => ?_, fun p is_port => ?_, fun k s on_rim => ?_⟩
  · -- two positions with the same edge: the check says they are equal
    rcases rim_inj k on_rim k' on_rim' with differ | equal
    · rw [same_edge] at differ; simp at differ
    · exact equal
  · -- an unglued edge: the check finds it on the rim list
    rcases rim_all t is_tile i is_vertex with ⟨x, glued⟩ | ⟨k, on_rim, at_k⟩
    · rw [unglued] at glued; contradiction
    · exact ⟨k, on_rim, at_k⟩
  · have bound := glue_ok t is_tile i is_vertex -- the check's bound on the edge across this glued edge
    rw [glued] at bound
    simpa using bound
  · obtain ⟨t, i, s⟩ := p
    obtain ⟨is_tile, is_vertex⟩ := is_port
    -- the check found where the walk from this port leaves the patch
    have leaves := all_leave t is_tile i is_vertex s (by cases s <;> simp)
    obtain ⟨r, found⟩ := leaves
    exact ⟨r, P.follow_sound f _ r found⟩
  · have found := sig_ok k on_rim s (by cases s <;> simp) -- the walk from this rim port ends at its partner
    exact P.follow_sound f _ _ found

end Patch

/-! ### The level-`m` data: lengths, orientation, corners -/

/-- ℓ_m(K, j), as a function of the side `j`. -/
def lenAt (m : Nat) (K : Kind) (j : Nat) : Nat := letterLen m (letterOf K j)

/-- The own orientation at level `m`: counter-clockwise (as the tiles) at even levels, clockwise at odd ones
(Def 2.2). It is also the sign `ω_m`: `B = A + 1` at even levels and `B = A - 1` at odd ones. -/
def ori (m : Nat) : Bool := m % 2 == 0

/-- Where vertex `j` of a level-`m` `K`-supertile sits on its rim. -/
def vpos (m : Nat) (K : Kind) (j : Nat) : Nat := Compose.pos (lenAt m K) j

/-- The crossover corner `A` of a level-`m` `K`-supertile: vertex 0, or for Σ the point `d_m` along side 5
(Lemma 6.4). -/
def aPos (m : Nat) (K : Kind) : Nat := if K = .Sigma then vpos m K 5 + dOff m else 0

/-- The other crossover corner `B = A + ω_m`. -/
def bPos (m : Nat) (K : Kind) : Nat :=
  if ori m then nxt (vpos m K 6) (aPos m K) else prv (vpos m K 6) (aPos m K)

/-- **The induction hypothesis of Thm 7.6, at tile level**: the level-`m` `K`-supertile has the signature with its
corners where `aPos`, `bPos` say, its six vertices where the side lengths ℓ_m put them. -/
structure Good (m : Nat) (K : Kind) : Prop where
  sig : (super m K).HasSig (ori m) (aPos m K) (bPos m K)
  vtx : (super m K).vtx = (List.range 7).map (vpos m K)
  len : (super m K).E = vpos m K 6

/-! ### The base cases -/

/-- A single tile has no closed strand: every ribbon leaves it after one piece. -/
theorem tile_noClosed : tile.NoClosedStrand := fun p _ => ⟨pieceEnd p, .leave (by
  obtain ⟨t, i, s⟩ := pieceEnd p
  cases s <;> rfl)⟩

/-- The kernel's check of the nine level-1 supertiles. -/
def level1Check (K : Kind) : Bool :=
  (level1 K).sigCheck (ori 1) (aPos 1 K) (bPos 1 K) 300 &&
  (level1 K).vtx == (List.range 7).map (vpos 1 K) && (level1 K).E == vpos 1 K 6

/-- The kernel's check passes for the level-1 Γ-supertile. -/
theorem level1Check_Gamma : level1Check .Gamma = true := by decide +kernel
/-- The kernel's check passes for the level-1 Δ-supertile. -/
theorem level1Check_Delta : level1Check .Delta = true := by decide +kernel
/-- The kernel's check passes for the level-1 Θ-supertile. -/
theorem level1Check_Theta : level1Check .Theta = true := by decide +kernel
/-- The kernel's check passes for the level-1 Λ-supertile. -/
theorem level1Check_Lambda : level1Check .Lambda = true := by decide +kernel
/-- The kernel's check passes for the level-1 Ξ-supertile. -/
theorem level1Check_Xi : level1Check .Xi = true := by decide +kernel
/-- The kernel's check passes for the level-1 Π-supertile. -/
theorem level1Check_Pi : level1Check .Pi = true := by decide +kernel
/-- The kernel's check passes for the level-1 Σ-supertile. -/
theorem level1Check_Sigma : level1Check .Sigma = true := by decide +kernel
/-- The kernel's check passes for the level-1 Φ-supertile. -/
theorem level1Check_Phi : level1Check .Phi = true := by decide +kernel
/-- The kernel's check passes for the level-1 Ψ-supertile. -/
theorem level1Check_Psi : level1Check .Psi = true := by decide +kernel

/-- The kernel's check passes for all nine level-1 supertiles. -/
theorem level1Check_all : ∀ K, level1Check K = true
  | .Gamma => level1Check_Gamma
  | .Delta => level1Check_Delta
  | .Theta => level1Check_Theta
  | .Lambda => level1Check_Lambda
  | .Xi => level1Check_Xi
  | .Pi => level1Check_Pi
  | .Sigma => level1Check_Sigma
  | .Phi => level1Check_Phi
  | .Psi => level1Check_Psi

/-- **The base of the induction**: the level-1 supertiles have the signature (Computation 7.5). -/
theorem good_one (K : Kind) : Good 1 K := by
  -- the kernel's check for this kind, split into its three parts
  have check := level1Check_all K
  simp only [level1Check, Bool.and_eq_true, beq_iff_eq] at check
  obtain ⟨⟨sig_ok, vtx_eq⟩, len_eq⟩ := check
  exact ⟨(level1 K).sigCheck_sound sig_ok, vtx_eq, len_eq⟩

end SpectreKnot.Statement

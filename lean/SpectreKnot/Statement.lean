/-
# The statements of Theorems A and B

This is the file to read to know what the Lean development proves. It holds every definition the main theorems depend
on, and the theorems themselves, as claims (`def … : Prop`) in §5–§7. The proofs are in other files; Lean's kernel
checks each of them against the claim written here. So "has the right thing been proved?" comes down to: do the
definitions below say what the paper means? A guided reading, with a short introduction to Lean, is the proof site's
page `statement.html`.

Besides `Kind` and `iter` (from `Basic.lean`), the file uses two generated data files: `Data/Pattern.lean`, the paper's
Tables 1–3, and `Data/Clusters.lean`, the nine level-1 supertiles, computed in exact arithmetic.

There is no geometry here: a patch of tiles is described only by which edge of which tile is glued to which edge of
which other tile. The link with real tilings is an assumption, not proved in Lean:

  (M) In every homochiral tiling by Tile(1,1), every level-m supertile of kind K is glued exactly like `super m K`
      (with its tiles suitably numbered). So a tiling whose hierarchy covers the plane is the union of a chain of
      supertiles as in §7, and the nest tiling of the paper is the union of the blocks `N b`.
-/
import SpectreKnot.Basic
import SpectreKnot.Data.Pattern
import SpectreKnot.Data.Clusters

namespace SpectreKnot.Statement

/-! ## 1. Ports and pieces (the paper's §3.1) -/

/-- A **port** `(t, i, s)`: a ribbon end on an edge of tile `t`, beside its vertex `v_i` (`i` = 0 … 13, numbered
counter-clockwise; edge `e_i` runs from `v_i` to `v_{i+1}`). `s = true` is `R(v_i)`, on edge `e_i`; `s = false` is
`L(v_i)`, on edge `e_{i-1}`. Each tile has 28 ports. -/
abbrev Port := Nat × Nat × Bool

/-- **Def 3.1, the decoration.** `pieceEnd p` is the other end of the ribbon piece that ends at port `p`. -/
def pieceEnd : Port → Port
  -- The crossover: R(v_0) ↔ R(v_1) and L(v_0) ↔ L(v_1), two pieces that cross inside the tile.
  | (t, 0, s) => (t, 1, s)
  | (t, 1, s) => (t, 0, s)
  -- Every other vertex: a hook round the corner, L(v_i) ↔ R(v_i).
  | (t, i, s) => (t, i, !s)

/-! ## 2. Patches and strands (the paper's §3.2–3.3) -/

/-- A **patch**: `tiles` tiles, numbered `0 … tiles - 1`, and what lies across each edge. `glue t i = some (t', j)`
means that edge `e_i` of tile `t` is edge `e_j` of tile `t'`; the two tiles run along it in opposite directions, so
`v_i` of `t` is `v_{j+1}` of `t'`. `none` means the edge is on the rim. For supertiles, `rim` lists the rim edges in
order from vertex 0, and `vtx` the positions in `rim` of the six vertices, then the rim's length. -/
structure Patch where
  tiles : Nat
  glue : Nat → Nat → Option (Nat × Nat)
  rim : List (Nat × Nat)
  vtx : List Nat

namespace Patch

variable (P : Patch)

/-- `p` is a port of a tile of the patch. -/
def IsPort (p : Port) : Prop := p.1 < P.tiles ∧ p.2.1 < 14

/-- **Def 3.2, the straight-through rule.** The port where the ribbon at `p` continues across its edge, or `none` if
the edge is on the rim. -/
def across : Port → Option Port
  -- R(v_i) is on e_i. If e_i is e_j of t', the ribbon continues as R(v_j) of t'.
  | (t, i, true) => (P.glue t i).map fun (t', j) => (t', j, true)
  -- L(v_i) is on e_{i-1} (`(i + 13) % 14` is i - 1, round 14). If that is e_j of t', it continues as L(v_{j+1}).
  | (t, i, false) => (P.glue t ((i + 13) % 14)).map fun (t', j) => (t', (j + 1) % 14, false)

/-- **Following a ribbon.** `P.Follow p r`: from `p`, going along a piece, across an edge, along a piece, and so on,
you leave the patch at the rim port `r`. It holds exactly when it follows from the two rules in finitely many steps. -/
inductive Follow : Port → Port → Prop
  -- The far end of p's piece is on the rim: leave there.
  | leave {p : Port} : P.across (pieceEnd p) = none → Follow p (pieceEnd p)
  -- Otherwise cross to q, and carry on from q.
  | next {p q r : Port} : P.across (pieceEnd p) = some q → Follow q r → Follow p r

/-- **No closed strand**: from every port of the patch, following the ribbon leads out of it. (A closed strand
never reaches the rim.) -/
def NoClosedStrand : Prop := ∀ p, P.IsPort p → ∃ r, P.Follow p r

/-- **Same strand.** `P.Linked p q`: `q` is reached from `p` by moves along pieces and across glued edges, inside
the patch. -/
inductive Linked (p : Port) : Port → Prop
  | refl : Linked p p
  | piece {q : Port} : Linked p q → Linked p (pieceEnd q)
  | edge {q q' : Port} : Linked p q → P.across q = some q' → Linked p q'

/-- **Side `j` of a supertile**: its rim edges from vertex `j` to vertex `j+1`. -/
def side (j : Nat) : List (Nat × Nat) :=
  (P.rim.drop (P.vtx.getD j 0)).take (P.vtx.getD (j + 1) 0 - P.vtx.getD j 0)

end Patch

/-! ## 3. Supertiles (the paper's §2.2–2.4) -/

/-- **Prop 2.4, as a construction**: the supertile of kind `T` with children `child 0`, `child 1`, … (Table 1). Its
tiles are the children's, numbered child by child. Where Table 2 says that side `j` of child `c` is side `j'` of child
`c'`, those sides are glued edge by edge, in opposite directions. The rim is the children's sides listed in Table 3,
each traversed backwards (a parent's orientation is opposite to its children's). -/
def compose (T : Kind) (child : Nat → Patch) : Patch :=
  -- n: the number of children (8, or 7 for Γ).
  let n := (Pattern.kids T).length
  -- off c: the number of the first tile of child c.
  let off : Nat → Nat := fun c => ((List.range c).map fun c' => (child c').tiles).sum
  -- owner t: the child that tile t belongs to.
  let owner : Nat → Nat := fun t => ((List.range n).filter fun c => off c ≤ t).length - 1
  -- shift c e: edge e of child c, renumbered as an edge of the parent.
  let shift : Nat → Nat × Nat → Nat × Nat := fun c e => (e.1 + off c, e.2)
  { -- The parent has the tiles of all its children.
    tiles := off n
    glue := fun t i =>
      -- Tile t is tile t₀ of child c.
      let c := owner t
      let t₀ := t - off c
      match (child c).glue t₀ i with
      -- Glued inside the child: glued in the parent.
      | some e => some (shift c e)
      -- On the child's rim: the edge is at position pos of the rim, the o-th edge of side j.
      | none =>
        let pos := ((child c).rim.findIdx? (· == (t₀, i))).getD 0
        let j := ((List.range 6).filter fun j => (child c).vtx.getD j 0 ≤ pos).length - 1
        let o := pos - (child c).vtx.getD j 0
        -- Table 2 for side j of child c.
        match ((Pattern.adj T).getD c []).getD j none with
        -- On the parent's rim: not glued.
        | none => none
        -- Side j' of child c': glued to its o-th edge counted from the end.
        | some (c', j') =>
          let s := (child c').side j'
          (s[s.length - 1 - o]?).map (shift c')
    -- Table 3: the children's sides, each backwards, in order.
    rim := ((Pattern.pside T).flatMap id).flatMap fun (c, j) => ((child c).side j).reverse.map (shift c)
    -- Vertex J: the total length of the pieces of sides 0 … J-1.
    vtx := (List.range 7).map fun J =>
      ((((Pattern.pside T).take J).flatMap id).map fun (c, j) => ((child c).side j).length).sum }

/-- A single tile: nothing glued, its 14 edges round the rim. -/
def tile : Patch := ⟨1, fun _ _ => none, (List.range 14).map fun i => (0, i), []⟩

/-- The level-1 supertile of kind `K`, from the data file (the spectre paper's Fig. 4.1 clusters). -/
def level1 (K : Kind) : Patch :=
  ⟨Clusters.tiles K, fun t i => ((Clusters.glue K).getD t []).getD i none, Clusters.rim K, Clusters.vtx K⟩

/-- **`super m K`: the supertile of level `m` and kind `K`.** Level 0 is a single tile and level 1 the data; level
`m + 2` is composed from children of level `m + 1`, of the kinds Table 1 lists. -/
def super : Nat → Kind → Patch
  | 0, _ => tile
  | 1, K => level1 K
  | m + 2, T => compose T fun c => super (m + 1) ((Pattern.kids T).getD c .Gamma)

/-! ## 4. The nest (the paper's §8) -/

/-- The block `N_b` of the nest: the Δ-supertile of level `b`. -/
def N (b : Nat) : Patch := super b .Delta

/-- `N_b` is child 1 of `N_{b+1}`, after child 0, a Ξ: tile `t` of `N_b` is tile `t + nestShift b` of `N_{b+1}`. -/
def nestShift (b : Nat) : Nat := (super b .Xi).tiles

/-- `up b k t`: tile `t` of `N_b`, renumbered as a tile of `N_{b+k}`. -/
def up (b : Nat) : Nat → Nat → Nat
  | 0, t => t
  | k + 1, t => up (b + 1) k (t + nestShift b)

/-- `upPort b k p`: port `p` of `N_b`, as a port of `N_{b+k}`. -/
def upPort (b k : Nat) (p : Port) : Port := (up b k p.1, p.2.1, p.2.2)

/-! ## 5. The theorems (claims; their proofs are in other files) -/

/-- **Theorem A** (combinatorial form): no supertile contains a closed strand. (Proved in `ProofA.lean`.) -/
def TheoremA : Prop := ∀ m K, (super m K).NoClosedStrand

/-- **Theorem B** (combinatorial form), three claims about the nest:
(1) every edge of a block `N_b` (`b ≥ 1`) is glued to a tile in `N_{b+2}`: the nest has no boundary;
(2) no block contains a closed strand;
(3) any two ports of a block lie on the same strand of a larger block. (Proved in `ProofB.lean`.) -/
def TheoremB : Prop :=
  (∀ b, 1 ≤ b → ∀ t i, t < (N b).tiles → i < 14 → ((N (b + 2)).glue (up b 2 t) i).isSome) ∧
  (∀ b, (N b).NoClosedStrand) ∧
  (∀ b p q, (N b).IsPort p → (N b).IsPort q → ∃ k, (N (b + k)).Linked (upPort b k p) (upPort b k q))

/-- **Theorem B with the paper's bound**: for `b ≥ 1`, any two ports of `N_b` lie on one strand of `N_{b+4}`, and of
`N_{b+3}` if `b` is even. (Proved in `ProofB.lean`.) -/
def TheoremB_sharp : Prop :=
  ∀ b p q, 1 ≤ b → (N b).IsPort p → (N b).IsPort q →
    (N (b + 4)).Linked (upPort b 4 p) (upPort b 4 q) ∧
    (b % 2 = 0 → (N (b + 3)).Linked (upPort b 3 p) (upPort b 3 q))

/-! ## 6. The nest tiling as one patch, and its single strand -/

/-- **`gid b t`: the number, in the whole nest tiling, of tile `t` of `N_b`.** The numbers are chosen so that the
tiles of every block `N_b` get 0 … |N_b| - 1. In `N_{b+1}`: a tile of child 1 (`N_b`) keeps its number in `N_b`; a
tile of child 0 comes next, after those of `N_b`; a tile of a later child keeps its own number. -/
def gid : Nat → Nat → Nat
  | 0, t => t
  | b + 1, t =>
    if nestShift b ≤ t ∧ t < nestShift b + (N b).tiles then gid b (t - nestShift b)
    else if t < nestShift b then (N b).tiles + t
    else t

/-- **`loc b g`**: the tile of `N_b` whose number in the nest tiling is `g`; it undoes `gid b`. -/
def loc : Nat → Nat → Nat
  | 0, g => g
  | b + 1, g =>
    if g < (N b).tiles then loc b g + nestShift b
    else if g < (N b).tiles + nestShift b then g - (N b).tiles
    else g

/-- **The gluing of the nest tiling**: what lies across edge `e_i` of the tile numbered `g`. It is read off `N_{g+3}`,
which contains the tile with two levels to spare. (By `NestModel` (d), every block gives the same answer.) -/
def nestGlue (g i : Nat) : Option (Nat × Nat) :=
  ((N (g + 3)).glue (up (g + 1) 2 (loc (g + 1) g)) i).map fun (t', j) => (gid (g + 3) t', j)

/-- **The nest tiling as one patch.** It has infinitely many tiles, so only `glue` means anything here; the other
fields are placeholders. -/
def nestTiling : Patch := ⟨0, nestGlue, [], []⟩

/-- One step forwards along a strand: along the piece at `p`, then across the edge. -/
def stepF (p : Port) : Port := (nestTiling.across (pieceEnd p)).getD (pieceEnd p)

/-- One step backwards: across the edge at `p`, then along the piece. -/
def stepB (p : Port) : Port := pieceEnd ((nestTiling.across p).getD p)

/-- **The nest tiling is a tiling, and the union of the blocks:**
(a) every number `g` is a tile of `N_{g+1}`;
(b) `gid b` numbers the tiles of `N_b` one to one with 0 … |N_b| - 1, and `loc b` is its inverse;
(c) a tile keeps its number one level up;
(d) whatever `N_b` glues, the nest tiling glues the same way;
(e) every edge of every tile is glued, to an edge of a different tile, which is glued back. -/
def NestModel : Prop :=
  (∀ g, g < (N (g + 1)).tiles) ∧
  (∀ b t, t < (N b).tiles → gid b t < (N b).tiles ∧ loc b (gid b t) = t) ∧
  (∀ b g, g < (N b).tiles → loc b g < (N b).tiles ∧ gid b (loc b g) = g) ∧
  (∀ b t, t < (N b).tiles → gid (b + 1) (up b 1 t) = gid b t) ∧
  (∀ b t i t' j, t < (N b).tiles → i < 14 → (N b).glue t i = some (t', j) →
    nestGlue (gid b t) i = some (gid b t', j)) ∧
  (∀ g i, i < 14 → ∃ g' j, nestGlue g i = some (g', j) ∧ g' ≠ g ∧ j < 14 ∧ nestGlue g' j = some (g, i))

/-- **Theorem B, final form: one two-way infinite strand.** Start at `R(v_0)` of the original tile, `(0, 0, true)`,
and step forwards (`stepF`) and backwards (`stepB`):
(1) forwards, no port is met twice;
(2) backwards, no port is met twice;
(3) no port is met both backwards and forwards, except the start;
(4) no piece is run through twice;
(5) every port of every tile is met, or is the other end of the piece of one that is.
(Proved in `ProofStrand.lean`.) -/
def TheoremB_strand : Prop :=
  (∀ i j, iter stepF i (0, 0, true) = iter stepF j (0, 0, true) → i = j) ∧
  (∀ a a', iter stepB a (0, 0, true) = iter stepB a' (0, 0, true) → a = a') ∧
  (∀ a b, iter stepB a (0, 0, true) = iter stepF b (0, 0, true) → a = 0 ∧ b = 0) ∧
  (∀ i j, iter stepF j (0, 0, true) ≠ pieceEnd (iter stepF i (0, 0, true))) ∧
  (∀ q : Port, q.2.1 < 14 → ∃ k,
    q = iter stepF k (0, 0, true) ∨ q = iter stepB k (0, 0, true) ∨
    q = pieceEnd (iter stepF k (0, 0, true)) ∨ q = pieceEnd (iter stepB k (0, 0, true)))

/-! ## 7. Any chain of supertiles (the paper's Theorem A, for tilings) -/

/-- **A chain of supertiles** X_1 ⊂ X_2 ⊂ ⋯: for every level `m ≥ 1`, the kind `K m` of X_m and its position `c m`
among the children of X_{m+1}, consistent with Table 1. In a tiling, the supertiles containing a given tile form a
chain; the nest is the chain with `K m = Δ`, `c m = 1`. -/
structure Chain where
  K : Nat → Kind
  c : Nat → Nat
  child_lt : ∀ m, 1 ≤ m → c m < (Pattern.kids (K (m + 1))).length
  child_kind : ∀ m, 1 ≤ m → (Pattern.kids (K (m + 1))).getD (c m) .Gamma = K m

namespace Chain

/-- The block X_m: the supertile of level `m` and kind `K m`. -/
def block (X : Chain) (m : Nat) : Patch := super m (X.K m)

/-- Where X_m starts inside X_{m+1}: the number of tiles of the children before it. -/
def shift (X : Chain) (m : Nat) : Nat :=
  ((List.range (X.c m)).map fun c' => (super m ((Pattern.kids (X.K (m + 1))).getD c' .Gamma)).tiles).sum

/-- `X.up m k t`: tile `t` of X_m, renumbered as a tile of X_{m+k}. -/
def up (X : Chain) (m : Nat) : Nat → Nat → Nat
  | 0, t => t
  | k + 1, t => up X (m + 1) k (t + X.shift m)

/-- **`X.gid m t`: the number, in the union of the chain, of tile `t` of X_m**, as `gid` of §6, from level 1. -/
def gid (X : Chain) : Nat → Nat → Nat
  | 0, t => t
  | 1, t => t
  | m + 2, t =>
    if X.shift (m + 1) ≤ t ∧ t < X.shift (m + 1) + (X.block (m + 1)).tiles then gid X (m + 1) (t - X.shift (m + 1))
    else if t < X.shift (m + 1) then (X.block (m + 1)).tiles + t
    else t

/-- **`X.loc m g`**: the tile of X_m whose number in the union is `g`; it undoes `X.gid m`. -/
def loc (X : Chain) : Nat → Nat → Nat
  | 0, g => g
  | 1, g => g
  | m + 2, g =>
    if g < (X.block (m + 1)).tiles then loc X (m + 1) g + X.shift (m + 1)
    else if g < (X.block (m + 1)).tiles + X.shift (m + 1) then g - (X.block (m + 1)).tiles
    else g

/-- **The chain covers the plane**: every edge of every block is glued in some larger block. -/
def Covers (X : Chain) : Prop :=
  ∀ m t i, 1 ≤ m → t < (X.block m).tiles → i < 14 → ∃ k, ((X.block (m + k)).glue (X.up m k t) i).isSome

/-- **`G` contains every block**: whatever X_m glues, the gluing `G` of the whole union glues the same way. -/
def Contains (X : Chain) (G : Nat → Nat → Option (Nat × Nat)) : Prop :=
  ∀ m t i t' j, 1 ≤ m → t < (X.block m).tiles → i < 14 → (X.block m).glue t i = some (t', j) →
    G (X.gid m t) i = some (X.gid m t', j)

end Chain

/-- **The tiling with gluing `G`, as one patch** (as `nestTiling`: only `glue` means anything). -/
def tilingOf (G : Nat → Nat → Option (Nat × Nat)) : Patch := ⟨0, G, [], []⟩

/-- One step forwards along a strand of a patch (`stepF` of §6, for any patch). -/
def Patch.forward (P : Patch) (p : Port) : Port := (P.across (pieceEnd p)).getD (pieceEnd p)

/-- One step backwards (`stepB` of §6, for any patch). -/
def Patch.backward (P : Patch) (p : Port) : Port := pieceEnd ((P.across p).getD p)

/-- **The union of a chain is a tiling.** For every chain X:
(a) every number `g` is a tile of X_{g+1};
(b) `X.gid m` numbers the tiles of X_m one to one, and `X.loc m` is its inverse;
(c) a tile keeps its number one level up;
(d) there is a gluing `G` of the union that contains every block;
(e) if the chain covers the plane, every such `G` glues every edge of every tile, to a different tile, and back. -/
def ChainModel : Prop :=
  ∀ X : Chain,
    (∀ g, g < (X.block (g + 1)).tiles) ∧
    (∀ m t, 1 ≤ m → t < (X.block m).tiles → X.gid m t < (X.block m).tiles ∧ X.loc m (X.gid m t) = t) ∧
    (∀ m g, 1 ≤ m → g < (X.block m).tiles → X.loc m g < (X.block m).tiles ∧ X.gid m (X.loc m g) = g) ∧
    (∀ m t, 1 ≤ m → t < (X.block m).tiles → X.gid (m + 1) (X.up m 1 t) = X.gid m t) ∧
    (∃ G, X.Contains G) ∧
    (X.Covers → ∀ G, X.Contains G →
      ∀ g i, i < 14 → ∃ g' j, G g i = some (g', j) ∧ g' ≠ g ∧ j < 14 ∧ G g' j = some (g, i))

/-- **Theorem A in strand form: in a tiling whose hierarchy covers the plane, every strand is two-way infinite.** For
any chain that covers the plane, any gluing `G` of its union that contains every block, and any port `p`:
(1) forwards, no port is met twice;
(2) backwards, no port is met twice;
(3) no port is met both backwards and forwards, except the start;
(4) no piece is run through twice.
(Proved in `ProofChain.lean`.) -/
def TheoremA_strand : Prop :=
  ∀ (X : Chain) (G : Nat → Nat → Option (Nat × Nat)), X.Covers → X.Contains G → ∀ p : Port, p.2.1 < 14 →
    (∀ i j, iter (tilingOf G).forward i p = iter (tilingOf G).forward j p → i = j) ∧
    (∀ a a', iter (tilingOf G).backward a p = iter (tilingOf G).backward a' p → a = a') ∧
    (∀ a b, iter (tilingOf G).backward a p = iter (tilingOf G).forward b p → a = 0 ∧ b = 0) ∧
    (∀ i j, iter (tilingOf G).forward j p ≠ pieceEnd (iter (tilingOf G).forward i p))

end SpectreKnot.Statement

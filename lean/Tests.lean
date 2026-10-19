/-
Tests of statements on concrete cases (evaluated by the interpreter, not the kernel). They are not part of any proof:
they check that the definitions say what they are meant to say, on the 18 compositions of Computation 7.3.
-/
import SpectreKnot
import SpectreKnot.Data.Level2

open SpectreKnot Compose

/-- All ports of a gluing. -/
def allPorts (G : Gluing) : List GPort :=
  (List.range G.n).flatMap fun c => (List.range (G.E c)).flatMap fun u => [(c, u, true), (c, u, false)]

def cases18 (m : Nat) : List Comp :=
  allKinds.flatMap fun T => [true, false].map fun ω => Comp.ofPattern T (letterLen m) (dOff m) ω

-- the compositions are well formed (Prop 5.4 applies)
#guard (cases18 1).all fun C => C.toGluing.wfCheck
#guard (cases18 2).all fun C => C.toGluing.wfCheck

-- Prop 5.4(b) on instances: the full and the reduced walk agree from every port, at levels 1 and 2
#guard (cases18 1).all fun C =>
  let G := C.toGluing; (allPorts G).all fun x => G.fullWalk C.fuel x == G.redWalk C.fuel x
#guard (cases18 2).all fun C =>
  let G := C.toGluing; (allPorts G).all fun x => G.fullWalk C.fuel x == G.redWalk C.fuel x

-- marks, counted per child (= runs), agree with the paper (Remark 7.8: 52 runs, 45 for Γ)
def runs (G : Gluing) : Nat :=
  ((List.range G.n).map fun c => ((List.range (G.E c)).filter fun u => !G.smooth c u).length).sum
#guard (cases18 1).map (fun C => runs C.toGluing) == [45, 45] ++ List.replicate 16 52

-- rim lengths: E₂(Γ) = 160, E₂(Δ) = 182 (paper Computation 7.3), from the composition of level-1 children
#guard ((Comp.ofPattern .Gamma (letterLen 1) (dOff 1) true).rimEdges.length,
        (Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).rimEdges.length) == (160, 182)

-- the check is not vacuous: wrong orientation sign, or non-adjacent corners in any child, are rejected
#guard (allKinds.all fun T => [true, false].all fun ω => !(Comp.ofPattern T (letterLen 1) (dOff 1) ω).check (!ω))
#guard (List.range 8).all fun c => !((Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).spreadCorners c).check true

-- the parity lemma's base checker (`sigCheck`) holds at level 1, as `sig_base` proves, and is not vacuous: it rejects
-- non-adjacent corners in the first child (non-adjacent corners in the Γ child are caught by `parity_lemma_adj`'s
-- adjacency, which `Sig` itself does not contain)
#guard (cases18 1).all fun C => C.sigCheck
#guard !((Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).spreadCorners 0).sigCheck

-- the paper's negative control for Computation 7.3, as `compositions.py` runs it: with every child's corner `B` placed
-- two vertices from `A` (`B = A ± 2`), all 18 compositions fail the check
def spreadAll (C : Comp) (ω : Bool) : Comp :=
  { C with kids := C.kids.map fun k => { k with B := if ω then (k.A + 2) % k.E else (k.A + k.E - 2) % k.E } }
#guard allKinds.all fun T => [true, false].all fun ω =>
  !(spreadAll (Comp.ofPattern T (letterLen 1) (dOff 1) ω) ω).check ω

/-- The kernel's check of Computation 9.2 (`Statement.stepCheck`), with the junction map `tg` in place of Table 6. -/
def stepCheckWith (tg : Bool → (Nat → Nat) → Nat → Bool → Option Nat) (ω : Bool) : Bool :=
  let C := Comp.ofLens .Delta (L₁ .Delta) (dOff 1) ω
  (List.range (pos (L₁ .Delta 1) 6)).all fun u => [true, false].all fun s =>
    match tg ω (L₁ .Delta 1) u s with
    | none => true
    | some q =>
      C.toGluing.fullWalk C.fuel (1, u, s) == some (Statement.jR (L₁ .Delta) q) ||
        C.toGluing.fullWalk C.fuel (1, u, s) == some (Statement.jL (L₁ .Delta) q)

/-- Table 6 with junctions 12 and 16 exchanged. -/
def tgtSwapped (ω : Bool) (f : Nat → Nat) (u : Nat) (s : Bool) : Option Nat :=
  (Statement.tgt ω f u s).map fun q => if q = 12 then 16 else if q = 16 then 12 else q

-- the check passes with Table 6 (as `step_base` proves in the kernel), and the paper's negative control for
-- Computation 9.2: with junctions 12 and 16 exchanged it fails, for both signs
#guard [true, false].all fun ω => stepCheckWith Statement.tgt ω
#guard [true, false].all fun ω => !stepCheckWith tgtSwapped ω

/-! ## Tests of the statement file (`Statement.lean`)

They check that its definitions mean what they are meant to: the supertiles it builds are the real ones, and the
strand counts of the paper come out of its notions of "following a ribbon" and "the nest". The counts are computed
with a memoised copy of `Statement.super` (`mlevels`), which is checked against `Statement.super` itself at levels
1 and 2. Slower checks at level 5 are in `TestsSlow.lean` (`./build.sh --slow`). -/

namespace StatementTests

open Statement

/-! A memoised copy of `Statement.super`, for tests at higher levels. -/
def kindIdx : Kind → Nat
  | .Gamma => 0 | .Delta => 1 | .Theta => 2 | .Lambda => 3 | .Xi => 4 | .Pi => 5 | .Sigma => 6 | .Phi => 7 | .Psi => 8

structure MPatch where
  tiles : Nat
  glue : Array (Option (Nat × Nat))   -- entry t * 14 + i
  rim : Array (Nat × Nat)
  vtx : Array Nat
  rimPos : Array Nat                  -- entry t * 14 + i: position of (t, i) in rim
  deriving Inhabited

def MPatch.side (M : MPatch) (j : Nat) : Array (Nat × Nat) := M.rim.extract (M.vtx.getD j 0) (M.vtx.getD (j + 1) 0)

def MPatch.toPatch (M : MPatch) : Patch :=
  ⟨M.tiles, fun t i => M.glue.getD (t * 14 + i) none, M.rim.toList, M.vtx.toList⟩

def mkRimPos (tiles : Nat) (rim : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut a := Array.replicate (tiles * 14) 0
  for k in [0:rim.size] do
    let (t, i) := rim[k]!
    a := a.set! (t * 14 + i) k
  return a

def mlevel1 (K : Kind) : MPatch :=
  let P := level1 K
  let rim := P.rim.toArray
  { tiles := P.tiles, glue := ((List.range P.tiles).flatMap fun t => (List.range 14).map fun i => P.glue t i).toArray,
    rim, vtx := P.vtx.toArray, rimPos := mkRimPos P.tiles rim }

def mcompose (T : Kind) (ch : Array MPatch) : MPatch := Id.run do
  let n := ch.size
  let mut off := #[0]
  for c in [0:n] do off := off.push (off[c]! + ch[c]!.tiles)
  let tiles := off[n]!
  let mut glue := Array.replicate (tiles * 14) none
  for c in [0:n] do
    let C := ch[c]!
    for t₀ in [0:C.tiles] do
      for i in [0:14] do
        let g := match C.glue[t₀ * 14 + i]! with
          | some (t', j) => some (t' + off[c]!, j)
          | none =>
            let pos := C.rimPos[t₀ * 14 + i]!
            let j := ((List.range 6).filter fun j => C.vtx.getD j 0 ≤ pos).length - 1
            let o := pos - C.vtx.getD j 0
            match ((Pattern.adj T).getD c []).getD j none with
            | none => none
            | some (c', j') =>
              let s := ch[c']!.side j'
              (s[s.size - 1 - o]?).map fun (t', i') => (t' + off[c']!, i')
        glue := glue.set! ((t₀ + off[c]!) * 14 + i) g
  let mut rim := #[]
  for (c, j) in (Pattern.pside T).flatMap id do
    rim := rim ++ ((ch[c]!.side j).reverse.map fun (t, i) => (t + off[c]!, i))
  let vtx := ((List.range 7).map fun J =>
      ((((Pattern.pside T).take J).flatMap id).map fun (c, j) => (ch[c]!.side j).size).sum).toArray
  return { tiles, glue, rim, vtx, rimPos := mkRimPos tiles rim }

def allK : List Kind := [.Gamma, .Delta, .Theta, .Lambda, .Xi, .Pi, .Sigma, .Phi, .Psi]

/-- `mlevels m`: the nine supertiles of level `m`, by kind index. -/
def mlevels : Nat → Array MPatch
  | 0 => #[]
  | 1 => (allK.map mlevel1).toArray
  | m + 2 => let prev := mlevels (m + 1)
    (allK.map fun T => mcompose T ((Pattern.kids T).map fun K => prev[kindIdx K]!).toArray).toArray

def glueAgree (P Q : Patch) : Bool :=
  P.tiles == Q.tiles && P.rim == Q.rim && P.vtx == Q.vtx &&
  (List.range P.tiles).all fun t => (List.range 14).all fun i => P.glue t i == Q.glue t i


def MPatch.across (M : MPatch) : Port → Option Port
  | (t, i, true) => (M.glue.getD (t * 14 + i) none).map fun (t', j) => (t', j, true)
  | (t, i, false) => (M.glue.getD (t * 14 + (i + 13) % 14) none).map fun (t', j) => (t', (j + 1) % 14, false)

def mfollow (M : MPatch) : Nat → Port → Option Port
  | 0, _ => none
  | f + 1, p => match M.across (pieceEnd p) with
    | none => some (pieceEnd p)
    | some q => mfollow M f q

def code (p : Port) : Nat := p.1 * 28 + p.2.1 * 2 + (if p.2.2 then 1 else 0)

/-- The strand of `M` through port `p`, named by its two ends on the rim. -/
def arcId (M : MPatch) (p : Port) : Nat × Nat :=
  let f := 28 * M.tiles + 1
  let a := code ((mfollow M f p).getD (0, 0, false))
  let b := code ((mfollow M f (pieceEnd p)).getD (0, 0, false))
  (min a b, max a b)

/-- The number of strands of `M` through the tiles `off … off + n - 1` (one port per piece suffices). -/
def strandsThrough (M : MPatch) (off n : Nat) : Nat :=
  let ps := (List.range n).flatMap fun t => (List.range 14).map fun i => (t + off, i, true)
  (ps.map (arcId M)).eraseDups.length

/-- Where `N_b` sits in `N_{b+k}`: the offset of its first tile. -/
def nestOff (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => nestOff (b + 1) k + (if b = 0 then 1 else ((mlevels b)[kindIdx .Xi]!).tiles)

def nestTiles (b : Nat) : Nat := if b = 0 then 1 else ((mlevels b)[kindIdx .Delta]!).tiles

def nestCount (b k : Nat) : Nat :=
  strandsThrough ((mlevels (b + k))[kindIdx .Delta]!) (nestOff b k) (nestTiles b)


/-- The chain of the paper's Remark 10.1: X_m is a Θ for odd m and a Γ for even m; X_m is child 2 of X_{m+1} for odd m
and child 7 for even m. `chainKind m`, and the offset of X_m's first tile in X_{m+1}. -/
def chainKind (m : Nat) : Kind := if m % 2 = 1 then .Theta else .Gamma
def chainStep (m : Nat) : Nat :=
  let T := chainKind (m + 1); let c := if m % 2 = 1 then 2 else 7
  (((Pattern.kids T).take c).map fun K => ((mlevels m)[kindIdx K]!).tiles).sum
def chainOff (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => chainOff (m + 1) k + chainStep m
def chainCount (m k : Nat) : Nat :=
  strandsThrough ((mlevels (m + k))[kindIdx (chainKind (m + k))]!) (chainOff m k)
    ((mlevels m)[kindIdx (chainKind m)]!).tiles


-- `super` at level 2 is the real level-2 supertile: built here from the tables, it equals, edge for edge, the one
-- built directly from the tile placements in exact arithmetic (`Data/Level2.lean`), with the same six vertices.
#guard allK.all fun K =>
  let P := super 2 K
  (List.range P.tiles).map (fun t => (List.range 14).map fun i => P.glue t i) == Level2.glue K && P.vtx == Level2.vtx K

-- level 1: the sides have the lengths of the paper's Prop 6.1
#guard allK.all fun K => (List.range 6).map (fun j => ((super 1 K).side j).length) == Pattern.len1 K

-- the memoised copy agrees with `super` at levels 1 and 2
#guard allK.all fun K => glueAgree (super 1 K) ((mlevels 1)[kindIdx K]!).toPatch
#guard allK.all fun K => glueAgree (super 2 K) ((mlevels 2)[kindIdx K]!).toPatch

-- sizes (paper §6 and Appendix A): tiles 9, 71, 559, 4401 and rims 46, 182, 758, 3198 for Δ; 8, 62, 488, 3842 and
-- 44, 160, 652, 2736 for Γ
#guard (List.range 4).map (fun m => ((mlevels (m + 1))[kindIdx .Delta]!).tiles) == [9, 71, 559, 4401]
#guard (List.range 4).map (fun m => ((mlevels (m + 1))[kindIdx .Delta]!).rim.size) == [46, 182, 758, 3198]
#guard (List.range 4).map (fun m => ((mlevels (m + 1))[kindIdx .Gamma]!).rim.size) == [44, 160, 652, 2736]

-- the paper's Table 5: the strands of N_{b+k} through the tiles of N_b
#guard [nestCount 0 1, nestCount 0 2, nestCount 0 3] == [5, 2, 1]
#guard [nestCount 1 1, nestCount 1 2, nestCount 1 3] == [10, 2, 2]
#guard [nestCount 2 1, nestCount 2 2] == [37, 2]

-- Negative control: along that chain the same definitions give three strands, not one (Remark 10.1). So "one strand"
-- is not built into the definitions.
#guard [chainCount 1 1, chainCount 1 2, chainCount 1 3] == [32, 3, 3]

-- the Grandparent Lemma on instances: every vertex of every tile of N_1 is surrounded in N_3, and of N_2 in N_4; but not
-- one level up (side 2 of N_b lies on the rim of N_{b+1}). So "surrounded" is not built into the definitions.
def surroundedIn (P : Patch) (t i : Nat) : Bool :=
  (List.range 30).any fun n => 0 < n && P.turns n (t, i) == some (t, i)
def nestSurrounded (b k : Nat) : Bool :=
  let P := ((mlevels (b + k))[kindIdx .Delta]!).toPatch
  (List.range (nestTiles b)).all fun t => (List.range 14).all fun i => surroundedIn P (t + nestOff b k) i
#guard nestSurrounded 1 2 && nestSurrounded 2 2
#guard !nestSurrounded 1 1 && !nestSurrounded 2 1

/-- Another decoration, given as a pairing of the 28 ports of a tile: port `2i` is R(v_i), and port `2i - 1` (round
28) is L(v_i). -/
def designEnd (pairing : Array Nat) : Port → Port
  | (t, i, s) =>
    let k := pairing[if s then 2 * i else (2 * i + 27) % 28]!
    if k % 2 = 0 then (t, k / 2, true) else (t, (k + 1) / 2 % 14, false)

/-- Following a ribbon of `M` with the decoration `e`, as `mfollow` does with `pieceEnd`. -/
def dfollow (M : MPatch) (e : Port → Port) : Nat → Port → Option Port
  | 0, _ => none
  | f + 1, p => match M.across (e p) with
    | none => some (e p)
    | some q => dfollow M e f q

/-- The ports of the tiles `off … off + n - 1` of `M` whose ribbon, with the decoration `e`, never reaches the rim: those
on closed strands (an open strand reaches the rim within `28 * M.tiles` steps). -/
def closedPorts (M : MPatch) (e : Port → Port) (off n : Nat) : Nat :=
  ((List.range n).flatMap fun t => (List.range 14).flatMap fun i => [(t + off, i, true), (t + off, i, false)]).countP
    fun p => (dfollow M e (28 * M.tiles + 1) p).isNone

/-- Three decorations, given that way: the Spectre Knot's; the Spectre Knot's with its crossing moved from corner 0 to
corner 5; and no crossing, a hook at every corner. -/
def knotDesign : Array Nat :=
  #[2, 27, 0, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 1]
def crossAt5 : Array Nat :=
  #[27, 2, 1, 4, 3, 6, 5, 8, 7, 11, 12, 9, 10, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 0]
def noCrossing : Array Nat :=
  #[27, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 0]

-- Negative control for Theorem A on real supertiles: the Spectre Knot's pairing, read this way, is `pieceEnd`; with it
-- no port of N_1 inside N_3 lies on a closed strand. With the crossing moved to corner 5, the same gluing and the same
-- rule for following a ribbon find 226 of N_1's 252 ports on closed strands of N_3; with no crossing, 28 ports of the
-- level-1 Δ already lie on closed strands. So "no closed strand" comes from the design, not from the definitions or
-- the gluing.
#guard (List.range 14).all fun i => [true, false].all fun s => designEnd knotDesign (5, i, s) == pieceEnd (5, i, s)
#guard closedPorts ((mlevels 3)[kindIdx .Delta]!) (designEnd knotDesign) (nestOff 1 2) 9 == 0
#guard closedPorts ((mlevels 3)[kindIdx .Delta]!) (designEnd crossAt5) (nestOff 1 2) 9 == 226
#guard closedPorts ((mlevels 1)[kindIdx .Delta]!) (designEnd noCrossing) 0 9 == 28

end StatementTests

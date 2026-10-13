/-
Skeletons and the reduced walk (paper §5.2: Def 5.3, Prop 5.4(b),(c)), as an algorithm, and the check of the
skeleton walks of the paper's Remark 7.8 (corroboration; the main proofs do not use it).

This is the pilot's computational spike. A skeleton is stored as exported from `paper/code/hierarchy/synth.js`: for
each child, its runs in order (run `i` goes from mark `i` to mark `i+1` of the child), with the run's length and its
partner run (or `none` for a rim run); the global id of each mark; and which marks are the child's crossover corners
`A_c`, `B_c`. The rim runs of the parent are listed in order.

`Skel.check` repeats `induction.js`'s test: the reduced walk closes no loop, and gives a hook at every parent rim
mark except the Γ child's `A` and `B`, which are adjacent and carry the crossover. That the reduced walk computes the
parent's box (Prop 5.4) is proved separately, for every well-formed gluing (`Gluing.prop_5_4_*`). Not formalised: that
the exported skeleton is `S_T(ℓ₁, d₁, ω)` (Def 5.3 and the construction of §7.1); this file is the pilot's check
(Remark 7.8), not used by the main results.
-/
import SpectreKnot.Basic

namespace SpectreKnot.Skeleton

/-- A run of a child: its length, and its partner run `(c', j)` in the sibling across it (`none` on the rim). -/
structure Run where
  len : Nat
  partner : Option (Nat × Nat)
  deriving Repr

/-- A child of the composition: its runs in order, the global id of the mark at the start of each run, and the
indices of its crossover corners among its marks. -/
structure Child where
  runs : List Run
  marks : List Nat
  defA : Nat
  defB : Nat
  deriving Repr

/-- A skeleton: the children (the Γ child last), the parent's rim runs `(c, i)` in order, and the sign
`ω` (`true` for `+1`) with `B_c = A_c + ω` in each child's own order. -/
structure Skel where
  kids : List Child
  rim : List (Nat × Nat)
  omega : Bool
  deriving Repr

/-- A reduced port `(c, m, s)`: the port `R_c(u)` (`s = true`) or `L_c(u)` (`s = false`) at mark `u` number `m` of
child `c`. `R_c(u)` lies on the run starting at `u`, `L_c(u)` on the run ending at `u`. -/
abbrev Port := Nat × Nat × Bool

namespace Skel

variable (S : Skel)

def kid (c : Nat) : Child := S.kids.getD c ⟨[], [], 0, 0⟩

def nRuns (c : Nat) : Nat := (S.kid c).runs.length

def run (c i : Nat) : Run := (S.kid c).runs.getD i ⟨0, none⟩

/-- All reduced ports. -/
def ports : List Port :=
  (List.range S.kids.length).flatMap fun c =>
    (List.range (S.nRuns c)).flatMap fun m => [(c, m, true), (c, m, false)]

/-- `τ`: inside a child, by its signature: a hook at every mark except the crossover corners, where
`R(A) ↔ R(B)` and `L(A) ↔ L(B)`. -/
def tau : Port → Port
  | (c, m, s) =>
    let k := S.kid c
    if m = k.defA then (c, k.defB, s) else if m = k.defB then (c, k.defA, s) else (c, m, !s)

/-- `σ`: across an interior run, by the zigzag lemma (odd length: `R ↔ R'` and `L ↔ L'` at the far ends; even
length: back to the same child at the other end of the run). `none` for a port on a rim run. -/
def sigma : Port → Option Port
  | (c, m, s) =>
    let n := S.nRuns c
    let i := if s then m else (m + n - 1) % n
    let r := S.run c i
    match r.partner with
    | none => none
    | some (c2, j) =>
      if r.len % 2 = 1 then
        if s then some (c2, j, true) else some (c2, (j + 1) % S.nRuns c2, false)
      else
        if s then some (c, (i + 1) % n, false) else some (c, i, true)

/-- The parent ports: the two end ports of every rim run. -/
def parentPorts : List Port :=
  S.rim.flatMap fun (c, i) => [(c, i, true), (c, (i + 1) % S.nRuns c, false)]

/-- The parent's ports `R(u_t)` and `L(u_t)` at its `t`-th rim mark (the start of rim run `t`). -/
def rimR (t : Nat) : Port := let (c, i) := S.rim.getD t (0, 0); (c, i, true)

def rimL (t : Nat) : Port :=
  let nR := S.rim.length
  let (c, i) := S.rim.getD ((t + nR - 1) % nR) (0, 0)
  (c, (i + 1) % S.nRuns c, false)

/-- The reduced walk of Prop 5.4(b) from a parent port: `τ`, then `σ` while the port is not a parent port. Returns
the parent port reached and the number of reduced ports visited, or `none` if it runs out of fuel or meets a rim
port that is not a parent port. -/
def walk : Nat → Port → Nat → Option (Port × Nat)
  | 0, _, _ => none
  | f + 1, p, acc =>
    let p2 := S.tau p
    if S.parentPorts.contains p2 then some (p2, acc + 2)
    else match S.sigma p2 with
      | none => none
      | some p3 => walk f p3 (acc + 2)

def fuel : Nat := S.ports.length + 1

/-- The parent's pairing at its parent ports (`π_P` at the parent marks). -/
def pairing (p : Port) : Option Port := (S.walk S.fuel p 0).map (·.1)

/-- Both maps are involutions; `σ` has no fixed point and is undefined exactly at the parent ports. Then the reduced
ports split into paths between parent ports and cycles, and the walks from all parent ports together visit every
port on a path exactly twice. -/
def involutionsOK : Bool :=
  S.ports.all fun p =>
    S.tau (S.tau p) == p &&
    match S.sigma p with
    | none => S.parentPorts.contains p
    | some q => q != p && S.sigma q == some p && !S.parentPorts.contains p

/-- No closed strand (`κ = 0`, Prop 5.4(c)): every walk ends, and the walks visit every reduced port twice. -/
def noLoops : Bool :=
  let ws := S.parentPorts.map fun p => S.walk S.fuel p 0
  ws.all Option.isSome && (ws.map fun w => (w.map (·.2)).getD 0).sum == 2 * S.ports.length

/-- The rim index of the parent mark whose id is `id`. -/
def rimIndexOf (id : Nat) : Nat :=
  (S.rim.findIdx? fun (c, i) => (S.kid c).marks.getD i 0 == id).getD 0

/-- Rim indices of the Γ child's crossover corners `A` and `B` (the Γ child is the last). -/
def tA : Nat := let g := S.kid (S.kids.length - 1); S.rimIndexOf (g.marks.getD g.defA 0)

def tB : Nat := let g := S.kid (S.kids.length - 1); S.rimIndexOf (g.marks.getD g.defB 0)

/-- The rim marks that are not hooks of the parent. -/
def nonHooks : List Nat :=
  (List.range S.rim.length).filter fun t => S.pairing (S.rimL t) != some (S.rimR t)

/-- **The skeleton walk check** (Remark 7.8), the test of `induction.js`: (a) no loop; (b) every parent rim mark is a hook except the Γ
child's `A` and `B`; (c) these are adjacent, `B = A + ω'` with `ω' = -ω` in the parent's own order, and the rim run
between them has length 1; (d) the crossover `R(A) ↔ R(B)`, `L(A) ↔ L(B)`. -/
def check : Bool :=
  let nR := S.rim.length
  let tA := S.tA
  let tB := S.tB
  let adj := if S.omega then tB == (tA + nR - 1) % nR else tB == (tA + 1) % nR
  let runAB := if S.omega then S.rim.getD tB (0, 0) else S.rim.getD tA (0, 0)
  S.involutionsOK && S.noLoops &&
  (S.nonHooks == [min tA tB, max tA tB]) &&
  adj && (S.run runAB.1 runAB.2).len == 1 &&
  S.pairing (S.rimR tA) == some (S.rimR tB) && S.pairing (S.rimL tA) == some (S.rimL tB)

/-- For negative controls: change the length of run `i` of child `c` by one, flipping its parity. -/
def bump (c i : Nat) : Skel :=
  { S with kids := S.kids.modify c fun k => { k with runs := k.runs.modify i fun r => { r with len := r.len + 1 } } }

/-- For negative controls: flip the parity of a shared run and of its partner, which keeps the skeleton consistent
(`involutionsOK`). -/
def flipShared (c i : Nat) : Skel :=
  match (S.run c i).partner with
  | none => S
  | some (c₂, j) => (S.bump c i).bump c₂ j

end Skel

end SpectreKnot.Skeleton

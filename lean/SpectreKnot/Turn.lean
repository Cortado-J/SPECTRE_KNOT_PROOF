/-
**Turning about a point**, for the Grandparent Lemma (`ProofGrand.lean`). A corner `(t, i)` is vertex `v_i` of tile
`t`; turning about it (`Statement.turn`) crosses the edge that ends there into the next tile round the point.

In a patch with the signature, the corners about a rim vertex `k` inside the patch form a chain, from the corner `sC k`
beside one of its rim ports to the corner `fC k` beside the other (`RimChains`: the patch is a disc at its rim). Every
other corner is surrounded, or on such a chain (`surrounded_or_chain`, by counting: turning backwards either comes round
or stops at the start of a chain). In a composition, a chain of the parent is made of chains of children, joined across
the children's glued sides as the abstract gluing turns about a vertex (`bstep`, as `Rot` or `RotB`); so the parent has
`RimChains` if its children do (`Kids.rimChains`), and a corner on a child's chain is surrounded in the parent if the
gluing's turning about that child vertex comes round (`Kids.surrounded_of_cycle`).
-/
import SpectreKnot.Linked

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-! ### Counting -/

/-- **Pigeonhole**: among `M + 1` numbers below `M`, two are equal. -/
theorem pigeonhole : ∀ (M : Nat) (f : Nat → Nat), (∀ j, j ≤ M → f j < M) → ∃ a b, a < b ∧ b ≤ M ∧ f a = f b := by
  intro M
  induction M with
  | zero => intro f below; exact absurd (below 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | succ M ih =>
    intro f below
    by_cases hit : ∃ a, a ≤ M ∧ f a = f (M + 1)
    · obtain ⟨a, a_le, same⟩ := hit
      exact ⟨a, M + 1, by omega, Nat.le_refl _, same⟩
    · -- no earlier number equals the last, so squeezing out its value leaves `M + 1` numbers below `M`
      have missed : ∀ a, a ≤ M → f a ≠ f (M + 1) := fun a a_le same => hit ⟨a, a_le, same⟩
      obtain ⟨a, b, a_lt, b_le, same⟩ := ih (fun j => if f j < f (M + 1) then f j else f j - 1) (fun j j_le => by
        have below_j := below j (by omega) -- the number `j`
        have below_last := below (M + 1) (Nat.le_refl _) -- the last number
        have missed_j := missed j j_le -- they differ
        split <;> omega)
      refine ⟨a, b, a_lt, by omega, ?_⟩
      have missed_a := missed a (by omega) -- `f a` is not the last value
      have missed_b := missed b b_le -- nor is `f b`
      split at same <;> split at same <;> omega

namespace Patch

variable {P : Patch}

/-! ### Turning, several times -/

/-- Turning `n` times, then `m` more. -/
theorem turns_add (n m : Nat) (c : Nat × Nat) : P.turns (n + m) c = (P.turns n c).bind (P.turns m) := by
  induction n generalizing c with
  | zero => simp [turns]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [turns, Option.bind_assoc]
    congr 1
    funext y
    exact ih y

/-- Turning `n + 1` times is turning `n` times, then once more. -/
theorem turns_succ' (n : Nat) (c : Nat × Nat) : P.turns (n + 1) c = (P.turns n c).bind P.turn := by
  rw [turns_add]
  congr 1
  funext y
  show (P.turn y).bind (P.turns 0) = P.turn y
  cases P.turn y <;> rfl

/-- Turning keeps to the corners of actual tiles. -/
theorem turn_valid {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {c d : Nat × Nat} (c_tile : c.1 < P.tiles)
    (turned : P.turn c = some d) : d.1 < P.tiles ∧ d.2 < 14 :=
  sig.glue_ok c.1 _ d.1 d.2 c_tile (Nat.mod_lt _ (by omega)) turned

/-! ### Turning backwards, and where every corner lies -/

/-- Turning backwards about a point: across edge `e_i` (which leaves `v_i`) of corner `(t, i)`. -/
def turnB (P : Patch) (c : Nat × Nat) : Option (Nat × Nat) := (P.glue c.1 c.2).map fun e => (e.1, (e.2 + 1) % 14)

/-- Turning backwards `n` times. -/
def turnsB (P : Patch) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, c => some c
  | n + 1, c => (P.turnB c).bind (P.turnsB n)

/-- Turning backwards, then forwards, comes back (with symmetric gluing). -/
theorem turn_turnB {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) {c d : Nat × Nat}
    (c_tile : c.1 < P.tiles) (c_vertex : c.2 < 14) (back : P.turnB c = some d) :
    P.turn d = some c ∧ d.1 < P.tiles ∧ d.2 < 14 := by
  simp only [turnB] at back
  cases glue_eq : P.glue c.1 c.2 with
  | none => rw [glue_eq] at back; contradiction
  | some e =>
    rw [glue_eq] at back
    simp only [Option.map_some, Option.some.injEq] at back
    subst back
    -- the edge across is an actual edge
    obtain ⟨e_tile, e_edge⟩ := sig.glue_ok c.1 c.2 e.1 e.2 c_tile c_vertex glue_eq
    refine ⟨?_, e_tile, Nat.mod_lt _ (by omega)⟩
    simp only [turn, mod14 e_edge]
    exact symm c.1 c.2 e.1 e.2 c_tile c_vertex glue_eq

/-- Turning backwards `n` times to `d`, then forwards `n` times, comes back. -/
theorem turnsB_sound {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) :
    ∀ n {c d : Nat × Nat}, c.1 < P.tiles → c.2 < 14 → P.turnsB n c = some d →
      P.turns n d = some c ∧ d.1 < P.tiles ∧ d.2 < 14 := by
  intro n
  induction n with
  | zero => intro c d c_tile c_vertex back; cases back; exact ⟨rfl, c_tile, c_vertex⟩
  | succ n ih =>
    intro c d c_tile c_vertex back
    simp only [turnsB] at back
    cases back_eq : P.turnB c with
    | none => rw [back_eq] at back; contradiction
    | some c₁ =>
      rw [back_eq] at back
      -- one step back, and forwards again
      have one := turn_turnB sig symm c_tile c_vertex back_eq
      -- the other `n` steps
      have rest := ih one.2.1 one.2.2 back
      refine ⟨?_, rest.2⟩
      rw [turns_succ', rest.1]
      exact one.1

/-- If turning backwards stops within `n` steps, it stops at some corner with nothing behind it. -/
theorem turnsB_stop : ∀ n {c : Nat × Nat}, P.turnsB n c = none → ∃ m d, P.turnsB m c = some d ∧ P.turnB d = none := by
  intro n
  induction n with
  | zero => intro c stopped; simp [turnsB] at stopped
  | succ n ih =>
    intro c stopped
    simp only [turnsB] at stopped
    cases back_eq : P.turnB c with
    | none => exact ⟨0, c, rfl, back_eq⟩
    | some c₁ =>
      rw [back_eq] at stopped
      obtain ⟨m, d, reached, stops⟩ := ih stopped
      exact ⟨m + 1, d, by simp only [turnsB, back_eq]; exact reached, stops⟩

-- The corners `corner`, `sC`, `fC` and the claim that a patch is a disc at its rim, `RimChains`, are in
-- `Statement.lean`, where the claim `SignatureTheorem` uses them.

/-- The start of a chain is a corner of an actual tile. -/
theorem sC_valid {o : Bool} {A B : Nat} (sig : P.HasSig o A B) {k : Nat} (k_lt : k < P.E) :
    (P.sC o k).1 < P.tiles ∧ (P.sC o k).2 < 14 := by
  cases o
  · exact (sig.rim_ok _ (prv_lt k_lt)).imp id fun rest => rest.1
  · exact (sig.rim_ok k k_lt).imp id fun rest => rest.1

/-- **Every corner is surrounded, or on the chain of a rim vertex** (in a patch with the signature and symmetric
gluing): turning backwards from it either comes round to it again, or stops at the start of the chain of a rim
vertex. -/
theorem surrounded_or_chain {o : Bool} {A B : Nat} (sig : P.HasSig o A B) (symm : P.GlueSymm) {t i : Nat}
    (t_lt : t < P.tiles) (i_lt : i < 14) :
    P.Surrounded t i ∨ ∃ k, k < P.E ∧ ∃ n, P.turns n (P.sC o k) = some (t, i) := by
  by_cases stops : ∃ n, P.turnsB n (t, i) = none
  · -- turning backwards stops at a corner whose edge `e_i` is on the rim: the start of a chain
    right
    obtain ⟨n, stopped⟩ := stops
    obtain ⟨m, d, reached, nothing_behind⟩ := turnsB_stop n stopped
    -- turning forwards from there comes back
    obtain ⟨forwards, d_tile, d_vertex⟩ := turnsB_sound sig symm m t_lt i_lt reached
    -- the edge behind `d` is unglued
    have unglued : P.glue d.1 d.2 = none := by
      simp only [turnB, Option.map_eq_none_iff] at nothing_behind; exact nothing_behind
    -- so it is a rim edge
    obtain ⟨k, k_lt, at_k⟩ := sig.rim_all d.1 d.2 d_tile d_vertex unglued
    cases o
    · -- clockwise: rim edge `k` arrives at rim vertex `k + 1`, beside its rim port `L`
      refine ⟨nxt P.E k, nxt_lt k_lt, m, ?_⟩
      show P.turns m (P.edgeAt (prv P.E (nxt P.E k))) = some (t, i)
      rw [prv_nxt k_lt, at_k]
      exact forwards
    · -- counter-clockwise: rim edge `k` leaves rim vertex `k`, beside its rim port `R`
      refine ⟨k, k_lt, m, ?_⟩
      show P.turns m (P.edgeAt k) = some (t, i)
      rw [at_k]
      exact forwards
  · -- turning backwards never stops: two of the first corners agree, so the turning comes round
    left
    -- the corner reached after `n` steps back
    have reached : ∀ n, ∃ d, P.turnsB n (t, i) = some d := fun n => by
      cases back_n : P.turnsB n (t, i) with
      | none => exact absurd ⟨n, back_n⟩ stops
      | some d => exact ⟨d, rfl⟩
    -- name them
    let y : Nat → Nat × Nat := fun n => (P.turnsB n (t, i)).getD (0, 0)
    -- each is reached
    have y_eq : ∀ n, P.turnsB n (t, i) = some (y n) := fun n => by
      obtain ⟨d, found⟩ := reached n
      simp only [y, found, Option.getD_some]
    -- and turning forwards from it comes back
    have y_back : ∀ n, P.turns n (y n) = some (t, i) ∧ (y n).1 < P.tiles ∧ (y n).2 < 14 :=
      fun n => turnsB_sound sig symm n t_lt i_lt (y_eq n)
    obtain ⟨a, b, a_lt, _, same⟩ := pigeonhole (14 * P.tiles) (fun n => (y n).1 * 14 + (y n).2) (fun j _ => by
      have bounds := (y_back j).2 -- `y j` is a corner of an actual tile
      omega)
    -- the two corners are the same
    have same_corner : y a = y b := by
      have bounds_a := (y_back a).2 -- `y a` is a corner of an actual tile
      have bounds_b := (y_back b).2 -- and so is `y b`
      exact Prod.ext (by omega) (by omega)
    refine ⟨b - a, by omega, ?_⟩
    -- from `y b`, `b` turns reach `(t, i)`; the first `a` of them reach `(t, i)` too, since `y b = y a`
    have split := turns_add (P := P) a (b - a) (y a)
    rw [show a + (b - a) = b by omega, same_corner, (y_back b).1, ← same_corner, (y_back a).1] at split
    exact split.symm

end Patch

/-! ### Turning about a vertex of a child, in the abstract gluing -/

/-- **One step of turning about a point, at the level of the children's rim vertices**, in the sense in which turning
about a tile vertex goes. For children oriented clockwise (`o = false`), across the edge that leaves the vertex, as
`Rot`; for children oriented counter-clockwise, across the edge that arrives, as `RotB`. -/
def bstep (G : Gluing) (o : Bool) (x : Nat × Nat) : Option (Nat × Nat) :=
  if o then G.mate x.1 (prv (G.E x.1) x.2) else (G.mate x.1 x.2).map fun e => (e.1, nxt (G.E e.1) e.2)

/-- `n` such steps. -/
def bsteps (G : Gluing) (o : Bool) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, x => some x
  | n + 1, x => (bstep G o x).bind (bsteps G o n)

/-- Turning about a vertex (`Rot`) is a number of steps, for children oriented clockwise. -/
theorem rot_bsteps {G : Gluing} {x r : Nat × Nat} (turn : G.Rot x r) : ∃ n, bsteps G false n x = some r := by
  induction turn with
  | stop _ => exact ⟨0, rfl⟩
  | @step c u c' k' r glued _ ih =>
    obtain ⟨n, rest⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [bsteps, bstep, Bool.false_eq_true, ite_false, glued, Option.map_some, Option.bind_some]
    exact rest

/-- Turning backwards about a vertex (`RotB`) is a number of steps, for children oriented counter-clockwise. -/
theorem rotB_bsteps {G : Gluing} {x r : Nat × Nat} (turn : G.RotB x r) : ∃ n, bsteps G true n x = some r := by
  induction turn with
  | stop _ => exact ⟨0, rfl⟩
  | @step c u c' k' r glued _ ih =>
    obtain ⟨n, rest⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [bsteps, bstep, ite_true, glued, Option.bind_some]
    exact rest

/-! ### Chains in a composition -/

/-- Corner `x` of child `c`, renumbered as a corner of the parent. -/
def shiftC (child : Nat → Patch) (c : Nat) (x : Nat × Nat) : Nat × Nat := (x.1 + offC child c, x.2)

/-- The child vertex where the parent's chain about its rim position `p` starts: that of the parent's port `R(p)` for
clockwise children, of `L(p)` for counter-clockwise ones. -/
def vS (T : Kind) (L : Nat → Nat → Nat) (d : Nat) (ω o : Bool) (p : Nat) : Nat × Nat :=
  if o then ((gL T L p).1, (gL T L p).2.1) else ((gR T L d ω p).1, (gR T L d ω p).2.1)

namespace Kids

set_option linter.unusedSectionVars false

variable {T : Kind} {child : Nat → Patch} {L : Nat → Nat → Nat} {d : Nat} {ω o : Bool}
  (kids : Kids T child L d ω o)

include kids

/-- Turning inside a child is turning in the parent. -/
theorem turn_lift {c : Nat} (c_lt : c < nk T) {x y : Nat × Nat} (x_tile : x.1 < (child c).tiles)
    (turned : (child c).turn x = some y) : (compose T child).turn (shiftC child c x) = some (shiftC child c y) := by
  simp only [Patch.turn, shiftC] at turned ⊢
  rw [kids.glue_shift c_lt x_tile]
  simp only [glueAt, turned]

/-- Turning several times inside a child is turning in the parent. -/
theorem turns_lift {c : Nat} (c_lt : c < nk T) :
    ∀ n {x y : Nat × Nat}, x.1 < (child c).tiles → (child c).turns n x = some y →
      (compose T child).turns n (shiftC child c x) = some (shiftC child c y) := by
  intro n
  induction n with
  | zero => intro x y _ turned; cases turned; rfl
  | succ n ih =>
    intro x y x_tile turned
    simp only [Patch.turns] at turned ⊢
    cases turn_eq : (child c).turn x with
    | none => rw [turn_eq] at turned; contradiction
    | some x₁ =>
      rw [turn_eq] at turned
      rw [kids.turn_lift c_lt x_tile turn_eq]
      exact ih (Patch.turn_valid (kids.sig c c_lt) x_tile turn_eq).1 turned

/-- A step of the gluing keeps to the rim vertices of actual children. -/
theorem bstep_valid {c u : Nat} (c_lt : c < nk T) (u_lt : u < (child c).E) {y : Nat × Nat}
    (stepped : bstep (Comp.ofLens T L d ω).toGluing o (c, u) = some y) : y.1 < nk T ∧ y.2 < (child y.1).E := by
  -- the composition is well formed
  have wf := kids.csig.wf
  -- `c` is a child of the composition
  have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
  -- and `u` a rim vertex of it
  have u_lt_E : u < (Comp.ofLens T L d ω).toGluing.E c := by rw [kids.E_eq c_lt]; exact u_lt
  cases o
  · simp only [bstep, Bool.false_eq_true, ite_false] at stepped
    cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c u with
    | none => rw [mate_eq] at stepped; contradiction
    | some e =>
      rw [mate_eq] at stepped
      simp only [Option.map_some, Option.some.injEq] at stepped
      subst stepped
      obtain ⟨c'_lt, k'_lt, _⟩ := wf.mate_valid c u e.1 e.2 c_lt_n u_lt_E mate_eq
      -- `e.1` is a child
      have c'_lt' : e.1 < nk T := by rw [ofLens_n] at c'_lt; exact c'_lt
      exact ⟨c'_lt', by rw [← kids.E_eq c'_lt']; exact nxt_lt k'_lt⟩
  · simp only [bstep, ite_true] at stepped
    obtain ⟨c'_lt, k'_lt, _⟩ := wf.mate_valid c _ y.1 y.2 c_lt_n (prv_lt u_lt_E) stepped
    -- `y.1` is a child
    have c'_lt' : y.1 < nk T := by rw [ofLens_n] at c'_lt; exact c'_lt
    exact ⟨c'_lt', by rw [← kids.E_eq c'_lt']; exact k'_lt⟩

/-- Steps of the gluing keep to the rim vertices of actual children. -/
theorem bsteps_valid : ∀ a {c u : Nat} {y : Nat × Nat}, c < nk T → u < (child c).E →
    bsteps (Comp.ofLens T L d ω).toGluing o a (c, u) = some y → y.1 < nk T ∧ y.2 < (child y.1).E := by
  intro a
  induction a with
  | zero => intro c u y c_lt u_lt stepped; cases stepped; exact ⟨c_lt, u_lt⟩
  | succ a ih =>
    intro c u y c_lt u_lt stepped
    simp only [bsteps] at stepped
    cases step_eq : bstep (Comp.ofLens T L d ω).toGluing o (c, u) with
    | none => rw [step_eq] at stepped; contradiction
    | some z =>
      rw [step_eq] at stepped
      -- the next vertex is a rim vertex of an actual child
      have z_valid := kids.bstep_valid c_lt u_lt step_eq
      exact ih z_valid.1 z_valid.2 stepped

/-- **Across the end of a child's chain**: from the corner where the chain about child vertex `u` ends, turning crosses
a rim edge of the child into the sibling the gluing's step names, at the start of its chain; or it reaches the
parent's rim. -/
theorem turn_fC {c u : Nat} (c_lt : c < nk T) (u_lt : u < (child c).E) :
    (compose T child).turn (shiftC child c ((child c).fC o u)) =
      (bstep (Comp.ofLens T L d ω).toGluing o (c, u)).map fun y => shiftC child y.1 ((child y.1).sC o y.2) := by
  -- the composition is well formed
  have wf := kids.csig.wf
  -- `c` is a child of the composition
  have c_lt_n : c < (Comp.ofLens T L d ω).toGluing.n := by rw [ofLens_n]; exact c_lt
  cases o
  · -- clockwise children: the chain ends beside the rim edge `u`
    -- which is an actual edge
    have i_lt := ((kids.sig c c_lt).rim_ok u u_lt).2.1
    show (compose T child).glue (((child c).edgeAt u).1 + offC child c)
      (((((child c).edgeAt u).2 + 1) % 14 + 13) % 14) = _
    rw [mod14 i_lt, kids.glue_rimEdge c_lt u_lt]
    simp only [bstep, Bool.false_eq_true, ite_false]
    cases mate_eq : (Comp.ofLens T L d ω).toGluing.mate c u with
    | none => rfl
    | some e =>
      obtain ⟨c'_lt, k'_lt, _⟩ :=
        wf.mate_valid c u e.1 e.2 c_lt_n (by rw [kids.E_eq c_lt]; exact u_lt) mate_eq
      -- `e.1` is a child
      have c'_lt' : e.1 < nk T := by rw [ofLens_n] at c'_lt; exact c'_lt
      simp only [Option.map_some, shiftC, Patch.sC, Patch.corner, Patch.bport, Bool.false_eq_true, ite_false,
        kids.E_eq c'_lt', prv_nxt (show e.2 < (child e.1).E by rw [← kids.E_eq c'_lt']; exact k'_lt)]
  · -- counter-clockwise children: the chain ends beside the rim edge `u - 1`
    -- which is an actual edge
    have i_lt := ((kids.sig c c_lt).rim_ok _ (prv_lt u_lt)).2.1
    show (compose T child).glue (((child c).edgeAt (prv (child c).E u)).1 + offC child c)
      (((((child c).edgeAt (prv (child c).E u)).2 + 1) % 14 + 13) % 14) = _
    rw [mod14 i_lt, kids.glue_rimEdge c_lt (prv_lt u_lt)]
    simp only [bstep, ite_true, kids.E_eq c_lt]
    cases (Comp.ofLens T L d ω).toGluing.mate c (prv (child c).E u) with
    | none => rfl
    | some e => rfl

/-- **One step of the gluing, at tile level**: from the start of the chain about child vertex `u`, turning runs along
the chain and then, once more, on to what the gluing's step names. -/
theorem chain_step (chains : ∀ c, c < nk T → (child c).RimChains o) {c u : Nat} (c_lt : c < nk T)
    (u_lt : u < (child c).E) :
    ∃ n, (compose T child).turns (n + 1) (shiftC child c ((child c).sC o u)) =
      (bstep (Comp.ofLens T L d ω).toGluing o (c, u)).map fun y => shiftC child y.1 ((child y.1).sC o y.2) := by
  obtain ⟨n, along⟩ := chains c c_lt u u_lt
  refine ⟨n, ?_⟩
  rw [Patch.turns_succ', kids.turns_lift c_lt n (Patch.sC_valid (kids.sig c c_lt) u_lt).1 along]
  exact kids.turn_fC c_lt u_lt

/-- **Steps of the gluing, at tile level**: if `a` steps of the gluing lead from vertex `u` of child `c` to vertex `u'`
of child `c'`, then turning in the parent leads, in at least `a` turns, from the start of the chain about the first to
the start of the chain about the second. -/
theorem chain_path (chains : ∀ c, c < nk T → (child c).RimChains o) :
    ∀ a {c u c' u' : Nat}, c < nk T → u < (child c).E →
      bsteps (Comp.ofLens T L d ω).toGluing o a (c, u) = some (c', u') →
      ∃ n, a ≤ n ∧ (compose T child).turns n (shiftC child c ((child c).sC o u)) =
        some (shiftC child c' ((child c').sC o u')) := by
  intro a
  induction a with
  | zero => intro c u c' u' _ _ stepped; cases stepped; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ a ih =>
    intro c u c' u' c_lt u_lt stepped
    simp only [bsteps] at stepped
    cases step_eq : bstep (Comp.ofLens T L d ω).toGluing o (c, u) with
    | none => rw [step_eq] at stepped; contradiction
    | some y =>
      rw [step_eq] at stepped
      -- the next vertex is a rim vertex of an actual child
      have y_valid := kids.bstep_valid c_lt u_lt step_eq
      obtain ⟨n₁, first⟩ := kids.chain_step chains c_lt u_lt
      rw [step_eq] at first
      obtain ⟨n₂, a_le, rest⟩ := ih y_valid.1 y_valid.2 stepped
      refine ⟨n₁ + 1 + n₂, by omega, ?_⟩
      rw [Patch.turns_add, first]
      exact rest

/-- **A corner on a child's chain is surrounded in the parent** if the gluing's turning about that child vertex comes
round to it. -/
theorem surrounded_of_cycle (chains : ∀ c, c < nk T → (child c).RimChains o) {c u a : Nat} (c_lt : c < nk T)
    (u_lt : u < (child c).E) (a_pos : 0 < a)
    (cycle : bsteps (Comp.ofLens T L d ω).toGluing o a (c, u) = some (c, u)) {m : Nat} {x : Nat × Nat}
    (on_chain : (child c).turns m ((child c).sC o u) = some x) :
    (compose T child).Surrounded (x.1 + offC child c) x.2 := by
  obtain ⟨n, a_le, round⟩ := kids.chain_path chains a c_lt u_lt cycle
  -- the corner, in the parent, on the lifted chain
  have to_x := kids.turns_lift c_lt m (Patch.sC_valid (kids.sig c c_lt) u_lt).1 on_chain
  refine ⟨n, by omega, ?_⟩
  -- `m` turns then `n` from the start of the chain: `n` turns from the corner
  have m_then_n := Patch.turns_add (P := compose T child) m n (shiftC child c ((child c).sC o u))
  -- `n` turns then `m`: round to the start, and on to the corner
  have n_then_m := Patch.turns_add (P := compose T child) n m (shiftC child c ((child c).sC o u))
  rw [to_x, Option.bind_some] at m_then_n
  rw [round, Option.bind_some, to_x, Nat.add_comm n m] at n_then_m
  exact m_then_n.symm.trans n_then_m

/-- Where the parent's chain about rim position `p` starts: at the start of the chain about the child vertex of
`R(p)` (for clockwise children) or of `L(p)` (for counter-clockwise ones). -/
theorem sC_parent {p : Nat} (p_lt : p < rimN T L) :
    (compose T child).sC (!o) p =
      shiftC child (vS T L d ω o p).1 ((child (vS T L d ω o p).1).sC o (vS T L d ω o p).2) := by
  cases o
  · show Patch.corner ((compose T child).bport (!false) (p, true)) = _
    rw [kids.bport_R p_lt]; rfl
  · show Patch.corner ((compose T child).bport (!true) (p, false)) = _
    rw [kids.bport_L p_lt]; rfl

/-- **On the parent's chain**: a corner on the chain about a child vertex that steps of the gluing reach from the
start of the parent's chain about rim position `p` is on that chain. -/
theorem on_parent_chain (chains : ∀ c, c < nk T → (child c).RimChains o) {p : Nat} (p_lt : p < rimN T L)
    {a c u : Nat} (path : bsteps (Comp.ofLens T L d ω).toGluing o a (vS T L d ω o p) = some (c, u)) {n : Nat}
    {x : Nat × Nat} (on_chain : (child c).turns n ((child c).sC o u) = some x) :
    ∃ n', (compose T child).turns n' ((compose T child).sC (!o) p) = some (shiftC child c x) := by
  -- the vertex of `R(p)` and that of `L(p)`, as rim vertices of actual children
  obtain ⟨cR_lt, uR_lt⟩ := kids.gR_valid p_lt
  -- (that of `L(p)`)
  obtain ⟨cL_lt, uL_lt⟩ := kids.gL_valid p_lt
  rw [ofLens_n] at cR_lt cL_lt
  rw [kids.E_eq cR_lt] at uR_lt
  rw [kids.E_eq cL_lt] at uL_lt
  -- the start of the parent's chain is a rim vertex of an actual child
  have start_valid : (vS T L d ω o p).1 < nk T ∧ (vS T L d ω o p).2 < (child (vS T L d ω o p).1).E := by
    cases o
    · exact ⟨cR_lt, uR_lt⟩
    · exact ⟨cL_lt, uL_lt⟩
  obtain ⟨n₁, _, to_vertex⟩ := kids.chain_path chains a start_valid.1 start_valid.2 path
  -- the end of that path is a rim vertex of an actual child
  have end_valid := kids.bsteps_valid a start_valid.1 start_valid.2 path
  refine ⟨n₁ + n, ?_⟩
  rw [kids.sC_parent p_lt, Patch.turns_add, to_vertex]
  exact kids.turns_lift end_valid.1 n (Patch.sC_valid (kids.sig c end_valid.1) end_valid.2).1 on_chain

/-- **The parent is a disc at its rim** if its children are: the chain about a parent rim vertex is made of the
children's chains, joined as the gluing turns about the vertex. -/
theorem rimChains (chains : ∀ c, c < nk T → (child c).RimChains o) : (compose T child).RimChains (!o) := by
  -- the composition is well formed
  have wf := kids.csig.wf
  intro p p_lt
  rw [compose_E kids.shape] at p_lt
  -- the vertex of `R(p)` and that of `L(p)`, as rim vertices of actual children
  obtain ⟨cR_lt, uR_lt⟩ := kids.gR_valid p_lt
  -- (that of `L(p)`)
  obtain ⟨cL_lt, uL_lt⟩ := kids.gL_valid p_lt
  rw [ofLens_n] at cR_lt cL_lt
  rw [kids.E_eq cR_lt] at uR_lt
  rw [kids.E_eq cL_lt] at uL_lt
  -- turning about the vertex of `R(p)` reaches that of `L(p)`
  have turn := kids.gR_rot p_lt
  cases o
  · -- clockwise children: the parent's chain runs from beside `R(p)` to beside `L(p)`
    obtain ⟨a, path⟩ := rot_bsteps turn
    obtain ⟨n₁, _, to_L⟩ := kids.chain_path chains a cR_lt uR_lt path
    obtain ⟨n₂, along⟩ := chains _ cL_lt _ uL_lt
    refine ⟨n₁ + n₂, ?_⟩
    -- the parent's chain starts beside `R(p)`, at the start of the chain about its vertex
    have start_eq : Patch.corner (ιP child false (gR T L d ω p)) =
        shiftC child (gR T L d ω p).1 ((child (gR T L d ω p).1).sC false (gR T L d ω p).2.1) := rfl
    -- and ends beside `L(p)`, at the end of the chain about its vertex
    have end_eq : Patch.corner (ιP child false (gL T L p)) =
        shiftC child (gL T L p).1 ((child (gL T L p).1).fC false (gL T L p).2.1) := rfl
    show (compose T child).turns (n₁ + n₂) (Patch.corner ((compose T child).bport (!false) (p, true))) =
      some (Patch.corner ((compose T child).bport (!false) (p, false)))
    rw [kids.bport_R p_lt, kids.bport_L p_lt, start_eq, end_eq, Patch.turns_add, to_L]
    exact kids.turns_lift cL_lt n₂ (Patch.sC_valid (kids.sig _ cL_lt) uL_lt).1 along
  · -- counter-clockwise children: from beside `L(p)` to beside `R(p)`, turning backwards about the vertex
    -- the edge before the vertex of `R(p)` is on the parent's rim
    have rim_R := kids.gR_rimL p_lt
    -- so turning backwards from the vertex of `L(p)` reaches it
    have back := turn.rotB wf rim_R.1 rim_R.2.1 _ (.stop rim_R.2.2)
    obtain ⟨a, path⟩ := rotB_bsteps back
    obtain ⟨n₁, _, to_R⟩ := kids.chain_path chains a cL_lt uL_lt path
    obtain ⟨n₂, along⟩ := chains _ cR_lt _ uR_lt
    refine ⟨n₁ + n₂, ?_⟩
    -- the parent's chain starts beside `L(p)`, at the start of the chain about its vertex
    have start_eq : Patch.corner (ιP child true (gL T L p)) =
        shiftC child (gL T L p).1 ((child (gL T L p).1).sC true (gL T L p).2.1) := rfl
    -- and ends beside `R(p)`, at the end of the chain about its vertex
    have end_eq : Patch.corner (ιP child true (gR T L d ω p)) =
        shiftC child (gR T L d ω p).1 ((child (gR T L d ω p).1).fC true (gR T L d ω p).2.1) := rfl
    show (compose T child).turns (n₁ + n₂) (Patch.corner ((compose T child).bport (!true) (p, false))) =
      some (Patch.corner ((compose T child).bport (!true) (p, true)))
    rw [kids.bport_R p_lt, kids.bport_L p_lt, start_eq, end_eq, Patch.turns_add, to_R]
    exact kids.turns_lift cR_lt n₂ (Patch.sC_valid (kids.sig _ cR_lt) uR_lt).1 along

end Kids

end SpectreKnot.Statement

/-
Two facts about gluings used to read the parent's signature off `Gluing.Sig`: a walk between rim ports can be
followed backwards (`FReach.reverse`), and turning about a vertex is injective on vertices reached along the rim
(`Rot.inj`).
-/
import SpectreKnot.Signature

namespace SpectreKnot.Gluing

variable {G : Gluing}

/-- In a well-formed gluing, `τ` (the children's signature pairing) undoes itself on the ports of actual children. -/
theorem tau_tau (wf : G.WF) {x : GPort} (valid : G.Valid x) : G.tau (G.tau x) = x := by
  obtain ⟨c, u, s⟩ := x
  -- the child's two corners differ
  have A_ne_B := wf.A_ne_B c valid.1
  by_cases at_A : u = G.A c
  · -- at corner `A`: to `B` and back
    -- `τ` sends `A` to `B`
    have to_B : G.tau (c, u, s) = (c, G.B c, s) := by simp [tau, at_A]
    -- and `B` back to `A`
    have to_A : G.tau (c, G.B c, s) = (c, G.A c, s) := by simp [tau, Ne.symm A_ne_B]
    rw [to_B, to_A, at_A]
  · by_cases at_B : u = G.B c
    · -- at corner `B`: to `A` and back
      -- `τ` sends `B` to `A`
      have to_A : G.tau (c, u, s) = (c, G.A c, s) := by simp [tau, at_A, at_B]
      -- and `A` back to `B`
      have to_B : G.tau (c, G.A c, s) = (c, G.B c, s) := by simp [tau]
      rw [to_A, to_B, at_B]
    · -- at a hook: `R` and `L` swap twice
      -- the first swap
      have swap : G.tau (c, u, s) = (c, u, !s) := by simp [tau, at_A, at_B]
      -- the second swap
      have swap_back : G.tau (c, u, !s) = (c, u, !!s) := by simp [tau, at_A, at_B]
      rw [swap, swap_back, Bool.not_not]

/-- In a well-formed gluing, `σ` (straight across a glued edge) is symmetric: if it takes `x` to `y`, it takes `y`
back to `x`. -/
theorem sigma_symm (wf : G.WF) {x y : GPort} (valid : G.Valid x) (across : G.sigma x = some y) :
    G.sigma y = some x := by
  obtain ⟨c, u, s⟩ := x
  obtain ⟨c_lt, u_lt⟩ := valid
  cases s with
  | true =>
    -- port `R(u)`, on edge `u`
    simp only [sigma] at across
    cases mate_eq : G.mate c u with
    | none => rw [mate_eq] at across; contradiction
    | some p =>
      obtain ⟨c', k'⟩ := p
      rw [mate_eq] at across
      simp only [Option.map_some, Option.some.injEq] at across
      subst across
      -- the edge is glued back
      obtain ⟨_, _, mate_back⟩ := wf.mate_valid c u c' k' c_lt u_lt mate_eq
      simp only [sigma, mate_back, Option.map_some]
  | false =>
    -- port `L(u)`, on edge `u - 1`
    simp only [sigma] at across
    cases mate_eq : G.mate c (prv (G.E c) u) with
    | none => rw [mate_eq] at across; contradiction
    | some p =>
      obtain ⟨c', k'⟩ := p
      rw [mate_eq] at across
      simp only [Option.map_some, Option.some.injEq] at across
      subst across
      -- the edge is glued back
      obtain ⟨_, k'_lt, mate_back⟩ := wf.mate_valid c _ c' k' c_lt (prv_lt u_lt) mate_eq
      simp only [sigma, prv_nxt k'_lt, mate_back, Option.map_some, nxt_prv u_lt]

/-- `Walk n a b`: `n` steps (`τ` then `σ`) lead from `a` to `b`. -/
inductive Walk (G : Gluing) : Nat → GPort → GPort → Prop
  | zero {a : GPort} : Walk G 0 a a
  | succ {n : Nat} {a a' b : GPort} : G.sigma (G.tau a) = some a' → Walk G n a' b → Walk G (n + 1) a b

/-- A walk extended by one more step at its end. -/
theorem Walk.snoc {n : Nat} {a b b' : GPort} (walk : G.Walk n a b) (last_step : G.sigma (G.tau b) = some b') :
    G.Walk (n + 1) a b' := by
  induction walk with
  | zero => exact .succ last_step .zero
  | succ first_step _ ih => exact .succ first_step (ih last_step)

/-- A walk read backwards, through the other ends of the same pieces and edges. -/
theorem Walk.reverse (wf : G.WF) {n : Nat} {a b : GPort} (walk : G.Walk n a b) (valid : G.Valid a) :
    G.Walk n (G.tau b) (G.tau a) := by
  induction walk with
  | zero => exact .zero
  | @succ n a a' b first_step _ ih =>
    -- the other end of the first piece is a port of an actual child
    have tau_valid_a := tau_valid wf valid
    -- and so is the port across from it
    have valid_a' := sigma_valid wf tau_valid_a first_step
    -- the rest of the walk, backwards
    have rest_back := ih valid_a'
    refine rest_back.snoc ?_
    rw [tau_tau wf valid_a']
    exact sigma_symm wf tau_valid_a first_step

/-- A full walk is a `Walk` to a port whose piece ends on the parent's rim. -/
theorem FReach.walk {k : Nat} {x r : GPort} (reach : G.FReach k x r) :
    ∃ y, G.Walk k x y ∧ G.sigma (G.tau y) = none ∧ r = G.tau y := by
  induction reach with
  | @stop x on_rim => exact ⟨x, .zero, on_rim, rfl⟩
  | step first_step _ ih =>
    obtain ⟨y, walk, on_rim, r_eq⟩ := ih
    exact ⟨y, .succ first_step walk, on_rim, r_eq⟩

/-- A `Walk` to a port whose piece ends on the parent's rim is a full walk. -/
theorem Walk.freach {k : Nat} {x y : GPort} (walk : G.Walk k x y) (on_rim : G.sigma (G.tau y) = none) :
    G.FReach k x (G.tau y) := by
  induction walk with
  | zero => exact .stop on_rim
  | succ first_step _ ih => exact .step first_step (ih on_rim)

/-- **Following backwards**: a walk from a rim port `x` to `r` gives a walk from `r` back to `x`. -/
theorem FReach.reverse (wf : G.WF) {k : Nat} {x r : GPort} (reach : G.FReach k x r) (valid : G.Valid x)
    (x_on_rim : G.sigma x = none) : G.FReach k r x := by
  obtain ⟨y, walk, _, rfl⟩ := reach.walk
  -- the walk backwards, ending where `x` leaves the parent
  have back := (walk.reverse wf valid).freach (by rw [tau_tau wf valid]; exact x_on_rim)
  rwa [tau_tau wf valid] at back

/-- `FReach.reverse` for the full walk with any number of crossings. -/
theorem FullReach.reverse (wf : G.WF) {x r : GPort} (reach : G.FullReach x r) (valid : G.Valid x)
    (x_on_rim : G.sigma x = none) : G.FullReach r x := by
  obtain ⟨k, reach_k⟩ := reach
  exact ⟨k, reach_k.reverse wf valid x_on_rim⟩

/-! ### Turning about a vertex, backwards -/

/-- Turning backwards about a vertex: across the edge before it, while that edge is glued. -/
inductive RotB (G : Gluing) : Nat × Nat → Nat × Nat → Prop
  | stop {c u : Nat} : G.mate c (prv (G.E c) u) = none → RotB G (c, u) (c, u)
  | step {c u c' k' : Nat} {r : Nat × Nat} : G.mate c (prv (G.E c) u) = some (c', k') → RotB G (c', k') r →
      RotB G (c, u) r

/-- Turning backwards about a vertex has one result. -/
theorem RotB.unique {x r r' : Nat × Nat} (turn : G.RotB x r) (turn' : G.RotB x r') : r = r' := by
  induction turn generalizing r' with
  | stop unglued =>
    cases turn' with
    | stop _ => rfl
    | step glued _ => rw [unglued] at glued; contradiction
  | step glued _ ih =>
    cases turn' with
    | stop unglued => rw [glued] at unglued; contradiction
    | step glued' rest' =>
      rw [glued] at glued'
      simp only [Option.some.injEq, Prod.mk.injEq] at glued'
      obtain ⟨rfl, rfl⟩ := glued'
      exact ih rest'

/-- Turning backwards undoes turning forwards: in a well-formed gluing, if turning about vertex `x` (of an actual
child) reaches `r`, then turning backwards from `r` reaches whatever turning backwards from `x` reaches. -/
theorem Rot.rotB (wf : G.WF) {x r : Nat × Nat} (turn : G.Rot x r) :
    x.1 < G.n → x.2 < G.E x.1 → ∀ y, G.RotB x y → G.RotB r y := by
  induction turn with
  | stop _ => intro _ _ y turn_back; exact turn_back
  | @step c u c' k' r glued _ ih =>
    intro c_lt u_lt y turn_back
    -- the edge is glued back, and `k'` is an actual edge of `c'`
    obtain ⟨c'_lt, k'_lt, glued_back⟩ := wf.mate_valid c u c' k' c_lt u_lt glued
    refine ih c'_lt (nxt_lt k'_lt) y (RotB.step (c' := c) (k' := u) ?_ turn_back)
    rw [prv_nxt k'_lt]; exact glued_back

/-- Two vertices reached along the parent's rim that turn to the same vertex are the same. -/
theorem Rot.inj (wf : G.WF) {x x' r : Nat × Nat} (rim_x : G.RimL x.1 x.2) (rim_x' : G.RimL x'.1 x'.2)
    (turn : G.Rot x r) (turn' : G.Rot x' r) : x = x' := by
  obtain ⟨c, u⟩ := x
  obtain ⟨c', u'⟩ := x'
  -- turning backwards from `r` stops at `x`, since the edge before `x` is on the rim
  have back := turn.rotB wf rim_x.1 rim_x.2.1 (c, u) (.stop rim_x.2.2)
  -- and likewise at `x'`
  have back' := turn'.rotB wf rim_x'.1 rim_x'.2.1 (c', u') (.stop rim_x'.2.2)
  exact back.unique back'

end SpectreKnot.Gluing

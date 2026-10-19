/-
Strands (paper §3.3, Def 3.3 and Lemma 3.4), in the "two involutions" model.

Instead of the strand multigraph of Def 3.3 we work with ports. Every port is an end of exactly one piece, and the
piece pairs it with the port at its other end (`inside`); every port is joined by the straight-through rule
(Def 3.2) to exactly one port of the neighbouring tile (`across`). Both are involutions without fixed points. A strand
is followed by alternating the two; Lemma 3.4 becomes a statement about the permutation `next = across ∘ inside`.
-/
import SpectreKnot.Basic

namespace SpectreKnot

/-- Ports with the two pairings of Def 3.1 (`inside`: the two ends of a piece) and Def 3.2 (`across`: the
straight-through rule). In a tiling of the plane both are defined everywhere and have no fixed points. -/
structure StrandSystem (P : Type) where
  inside : P → P
  across : P → P
  inside_inside : ∀ p, inside (inside p) = p
  across_across : ∀ p, across (across p) = p
  inside_ne : ∀ p, inside p ≠ p
  across_ne : ∀ p, across p ≠ p

namespace StrandSystem

variable {P : Type} (S : StrandSystem P)

/-- One step along a strand: from a port, through its piece to the other end, then across the edge. -/
def next (p : P) : P := S.across (S.inside p)

/-- One step back. -/
def prev (p : P) : P := S.inside (S.across p)

/-- A step back undoes a step forwards. -/
theorem prev_next (p : P) : S.prev (S.next p) = p := by
  simp [prev, next, S.across_across, S.inside_inside]

/-- A step forwards undoes a step back. -/
theorem next_prev (p : P) : S.next (S.prev p) = p := by
  simp [prev, next, S.across_across, S.inside_inside]

/-- The port reached after `k` steps. -/
def walk (p : P) (k : Nat) : P := iter S.next k p

/-- `k + 1` steps are `k` steps and one more. -/
theorem walk_succ (p : P) (k : Nat) : S.walk p (k + 1) = S.next (S.walk p k) := rfl

/-- Two ports that reach the same port after `n` steps are the same port (each step can be undone). -/
theorem iter_next_injective (n : Nat) {x y : P} (same_end : iter S.next n x = iter S.next n y) : x = y := by
  induction n with
  | zero => simpa using same_end
  | succ n ih =>
    apply ih
    -- one step back from the common end: the two walks already met after `n` steps
    have one_back := congrArg S.prev same_end
    simpa [iter_succ, prev_next] using one_back

/-- The strand through `p` is *closed* if following it returns to `p`. -/
def Closed (p : P) : Prop := ∃ n, 0 < n ∧ S.walk p n = p

/-- A strand never runs through a piece in both directions: no port reached from `p` is the other end of the piece
of another port reached from `p`. (In the multigraph language: a strand passes through each piece only once.) -/
theorem walk_ne_inside_walk (p : P) : ∀ i j, S.walk p j ≠ S.inside (S.walk p i) := by
  -- the claim for i and j = i + d, by two-step induction on d
  have key : ∀ d i, S.walk p (i + d) ≠ S.inside (S.walk p i) ∧
      S.walk p (i + (d + 1)) ≠ S.inside (S.walk p i) := by
    intro d
    induction d with
    | zero =>
      intro i
      refine ⟨fun same_piece => S.inside_ne _ same_piece.symm, fun next_is_inside => ?_⟩
      -- walk (i+1) = across (inside (walk i)) = across (walk (i+1)), but `across` has no fixed point
      have fixed_by_across : S.walk p (i + 1) = S.across (S.walk p (i + 1)) := by
        conv => lhs; rw [walk_succ, next, ← next_is_inside]
      exact S.across_ne _ fixed_by_across.symm
    | succ d ih =>
      intro i
      refine ⟨(ih i).2, fun far_is_inside => ?_⟩
      -- from walk (i + (d+2)) = inside (walk i) we get walk (i+1 + d) = inside (walk (i+1))
      apply (ih (i + 1)).1
      -- the step after `walk i`, written as `across` of the far port
      have after_start : S.walk p (i + 1) = S.across (S.walk p (i + (d + 1 + 1))) := by
        rw [far_is_inside, walk_succ, next]
      -- the far port is one step after `walk (i + 1 + d)`
      have far_step : S.walk p (i + (d + 1 + 1)) = S.next (S.walk p (i + 1 + d)) := by
        rw [← walk_succ]; congr 1; omega
      rw [after_start, far_step, next, S.across_across, S.inside_inside]
  intro i j is_inside
  by_cases i_le_j : i ≤ j
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    exact (key d i).1 is_inside
  · -- `j` comes first: swap the two ends of the piece
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    apply (key d j).1
    rw [is_inside, S.inside_inside]

/-- If a strand is not closed, the ports reached by following it are pairwise distinct. -/
theorem walk_injective_of_not_closed (p : P) (not_closed : ¬ S.Closed p) :
    ∀ i j, S.walk p i = S.walk p j → i = j := by
  -- if walk i = walk (i + d) with d > 0 then walk d = p
  have key : ∀ i d, S.walk p i = S.walk p (i + d) → d = 0 := by
    intro i d same_port
    apply Classical.byContradiction
    intro d_ne_zero
    apply not_closed
    refine ⟨d, by omega, ?_⟩
    apply S.iter_next_injective i
    show iter S.next i (iter S.next d p) = iter S.next i p
    rw [← iter_add]
    exact same_port.symm
  intro i j same_port
  by_cases i_le_j : i ≤ j
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    -- the gap between the two visits is zero
    have no_gap := key i d same_port
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    -- the gap between the two visits is zero
    have no_gap := key j d same_port.symm
    omega

/-- Following a strand that is not closed backwards never meets the ports reached forwards, except at `p`. -/
theorem back_ne_forward_of_not_closed (p : P) (not_closed : ¬ S.Closed p) :
    ∀ a b, iter S.prev a p = S.walk p b → a = 0 ∧ b = 0 := by
  -- `a` steps back, then `a` steps forwards, return to the start
  have back_then_forward : ∀ a x, iter S.next a (iter S.prev a x) = x := by
    intro a
    induction a with
    | zero => intro x; rfl
    | succ a ih => intro x; rw [iter_succ', iter_succ, next_prev, ih]
  intro a b meet
  -- going `a` steps forwards from the meeting point: `a + b` steps from `p` return to `p`
  have returns : p = S.walk p (a + b) := by
    -- the meeting point, moved `a` steps forwards on both sides
    have moved := congrArg (iter S.next a) meet
    rw [back_then_forward] at moved
    calc p = iter S.next a (iter S.next b p) := moved
      _ = iter S.next (a + b) p := (iter_add _ _ _ _).symm
  -- an open strand never returns to `p`, so `a + b = 0`
  have no_steps := S.walk_injective_of_not_closed p not_closed 0 (a + b) returns
  omega

/-- If a strand is not closed, the ports reached by following it backwards are pairwise distinct. -/
theorem prev_injective_of_not_closed (p : P) (not_closed : ¬ S.Closed p) :
    ∀ a a', iter S.prev a p = iter S.prev a' p → a = a' := by
  -- `a` steps back, then `a` steps forwards, return to the start
  have back_then_forward : ∀ a x, iter S.next a (iter S.prev a x) = x := by
    intro a
    induction a with
    | zero => intro x; rfl
    | succ a ih => intro x; rw [iter_succ', iter_succ, next_prev, ih]
  -- going back `d` steps never returns to the start, unless `d = 0`
  have back_ne : ∀ d, iter S.prev d p = p → d = 0 := fun d back_at_start =>
    (S.back_ne_forward_of_not_closed p not_closed d 0 back_at_start).1
  -- if `a` and `a + d` steps back meet, then `d` steps back return to the start
  have key : ∀ a d, iter S.prev a p = iter S.prev (a + d) p → d = 0 := by
    intro a d same
    rw [iter_add] at same
    -- go `a` steps forwards from both
    have undone := congrArg (iter S.next a) same
    rw [back_then_forward, back_then_forward] at undone
    exact back_ne d undone.symm
  intro a a' same
  rcases Nat.le_total a a' with le | le
  · obtain ⟨d, rfl⟩ : ∃ d, a' = a + d := ⟨a' - a, by omega⟩
    -- the gap between the two visits is zero
    have no_gap := key a d same
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, a = a' + d := ⟨a - a', by omega⟩
    -- the gap between the two visits is zero
    have no_gap := key a' d same.symm
    omega

/-- **Lemma 3.4** (in the port model). Every strand is either closed, or a two-way infinite path: following it
forwards from a port `p`, the ports met are distinct; so are those met backwards; the two walks meet only at `p`; and
no piece is passed twice (in either direction). -/
theorem closed_or_path (p : P) :
    S.Closed p ∨
      ((∀ i j, S.walk p i = S.walk p j → i = j) ∧
       (∀ a a', iter S.prev a p = iter S.prev a' p → a = a') ∧
       (∀ a b, iter S.prev a p = S.walk p b → a = 0 ∧ b = 0) ∧
       (∀ i j, S.walk p j ≠ S.inside (S.walk p i))) := by
  by_cases closed : S.Closed p
  · exact Or.inl closed
  · exact Or.inr ⟨S.walk_injective_of_not_closed p closed, S.prev_injective_of_not_closed p closed,
      S.back_ne_forward_of_not_closed p closed, S.walk_ne_inside_walk p⟩

end StrandSystem

end SpectreKnot

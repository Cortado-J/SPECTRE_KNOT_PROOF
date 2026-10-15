/-
Compositions with given side lengths (`Comp.ofLens`): positions, the side containing an edge, and the gluing formula.
Used by the parity lemma (`Parity.lean`).
-/
import SpectreKnot.Subdivide
import SpectreKnot.CompFull

namespace SpectreKnot.Compose

open Gluing Pattern

/-! ### Positions -/

/-- `pos f j = f 0 + … + f (j-1)`: where side `j` begins, for side lengths `f`. -/
def pos (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => pos f j + f j

/-- Side `j + 1` begins where side `j` begins, plus the length of side `j`. -/
theorem pos_succ (f : Nat → Nat) (j : Nat) : pos f (j + 1) = pos f j + f j := rfl

/-- Later sides begin later: `pos f` is monotone. -/
theorem pos_mono (f : Nat → Nat) {a b : Nat} (a_le_b : a ≤ b) : pos f a ≤ pos f b := by
  induction b with
  | zero =>
    -- only side 0 begins at or before side 0
    have a_zero : a = 0 := by omega
    subst a_zero; exact Nat.le_refl _
  | succ b ih =>
    by_cases a_eq : a = b + 1
    · subst a_eq; exact Nat.le_refl _
    · have := ih (by omega)  -- side `a` begins no later than side `b`, which begins before side `b + 1`
      rw [pos_succ]; omega

/-- Side `a` ends no later than any later side `b` begins. -/
theorem pos_lt_of_pos (f : Nat → Nat) (len_pos : ∀ i, i < 6 → 1 ≤ f i) {a b : Nat} (a_lt_b : a < b) (b_le : b ≤ 6) :
    pos f a + f a ≤ pos f b := by
  rw [← pos_succ]; exact pos_mono f a_lt_b

/-- The six side lengths, as an explicit list. -/
theorem range6_map (f : Nat → Nat) : (List.range 6).map f = [f 0, f 1, f 2, f 3, f 4, f 5] := rfl

/-- The prefix sums of the list of six side lengths, read at `j ≤ 6`, are `pos f j`: the list form of a child
(`mkKidL`) puts side `j` where `pos` does. -/
theorem prefixSums_getD (f : Nat → Nat) {j : Nat} (j_le : j ≤ 6) :
    (prefixSums ((List.range 6).map f) 0).getD j 0 = pos f j := by
  rw [range6_map]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Entry `j < 6` of the list of six side lengths is `f j`. -/
theorem len_getD (f : Nat → Nat) {j : Nat} (j_lt : j < 6) : ((List.range 6).map f).getD j 0 = f j := by
  rw [range6_map]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every position `k` of a rim with side lengths `f` (all positive) lies in exactly one side `j`, at offset `o`. -/
theorem decomp (f : Nat → Nat) : ∀ i, i ≤ 6 → ∀ k, k < pos f i → ∃ j o, j < i ∧ o < f j ∧ k = pos f j + o := by
  intro i
  induction i with
  | zero => intro _ k k_lt; simp [pos] at k_lt
  | succ i ih =>
    intro i_le k k_lt
    by_cases before : k < pos f i
    · obtain ⟨j, o, j_lt, o_lt, rfl⟩ := ih (by omega) k before
      exact ⟨j, o, by omega, o_lt, rfl⟩
    · rw [pos_succ] at k_lt
      exact ⟨i, k - pos f i, by omega, by omega, by omega⟩

/-- The side lookup `Comp.sideIdx` finds the side: at offset `o < f j` in side `j`, it returns `j`. -/
theorem sideIdx_eq (f : Nat → Nat) (len_pos : ∀ i, i < 6 → 1 ≤ f i) {j o : Nat} (j_lt : j < 6) (o_lt : o < f j) :
    Comp.sideIdx (prefixSums ((List.range 6).map f) 0) (pos f j + o) 5 = j := by
  -- searching down from any side `i ≥ j` finds side `j`
  have search : ∀ i, i ≤ 5 → j ≤ i →
      Comp.sideIdx (prefixSums ((List.range 6).map f) 0) (pos f j + o) i = j := by
    intro i
    induction i with
    | zero =>
      intro _ j_le
      -- only side 0 is left
      have j_zero : j = 0 := by omega
      subst j_zero; rfl
    | succ i ih =>
      intro i_le j_le
      simp only [Comp.sideIdx]
      rw [prefixSums_getD f (by omega)]
      by_cases at_j : j = i + 1
      · subst at_j; rw [ite_eq_left (by omega)]
      -- side `j` ends before side `i + 1` begins
      · have ends_before := pos_lt_of_pos f len_pos (show j < i + 1 by omega) (by omega)
        rw [ite_eq_right (by omega)]
        exact ih (by omega) (by omega)
  exact search 5 (by omega) (by omega)

/-! ### The children of `ofLens` -/

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- The number of children. -/
abbrev nk (T : Kind) : Nat := (Pattern.kids T).length

/-- The composition `ofLens` has the kind's children. -/
theorem ofLens_n : (Comp.ofLens T L d ω).toGluing.n = nk T := by
  simp [Comp.ofLens, Comp.toGluing]

/-- Child `c` of `ofLens` is the child built from its kind and its side lengths `L c`. -/
theorem ofLens_kid {c : Nat} (c_lt : c < nk T) :
    (Comp.ofLens T L d ω).kid c = mkKidL (kidAt T c) ((List.range 6).map (L c)) d ω := by
  simp [Comp.ofLens, Comp.kid, List.getD_eq_getElem?_getD, c_lt]

/-- The rim of child `c` has `pos (L c) 6` edges: the sum of its six side lengths. -/
theorem ofLens_E {c : Nat} (c_lt : c < nk T) : (Comp.ofLens T L d ω).toGluing.E c = pos (L c) 6 := by
  simp only [Comp.toGluing, ofLens_kid c_lt, mkKidL]; exact prefixSums_getD _ (by omega)

/-- Side `j` of child `c` begins at `pos (L c) j`. -/
theorem ofLens_U {c j : Nat} (c_lt : c < nk T) (j_le : j ≤ 6) :
    ((Comp.ofLens T L d ω).kid c).U.getD j 0 = pos (L c) j := by
  simp only [ofLens_kid c_lt, mkKidL]; exact prefixSums_getD _ j_le

/-- Side `j` of child `c` has length `L c j`. -/
theorem ofLens_len {c j : Nat} (c_lt : c < nk T) (j_lt : j < 6) :
    ((Comp.ofLens T L d ω).kid c).len.getD j 0 = L c j := by
  simp only [ofLens_kid c_lt, mkKidL]; exact len_getD _ j_lt

/-- The corner `A` of child `c`: vertex 0, or for the Σ child the point `d` along its side 5. -/
theorem ofLens_A {c : Nat} (c_lt : c < nk T) :
    (Comp.ofLens T L d ω).toGluing.A c = if kidAt T c = .Sigma then pos (L c) 5 + d else 0 := by
  simp only [Comp.toGluing, ofLens_kid c_lt, mkKidL, prefixSums_getD _ (show 5 ≤ 6 by omega)]

/-- The corner `B` of child `c`: the vertex after `A` if `ω`, the vertex before it otherwise. -/
theorem ofLens_B {c : Nat} (c_lt : c < nk T) :
    (Comp.ofLens T L d ω).toGluing.B c =
      if ω then nxt (pos (L c) 6) ((Comp.ofLens T L d ω).toGluing.A c)
      else prv (pos (L c) 6) ((Comp.ofLens T L d ω).toGluing.A c) := by
  rw [ofLens_A c_lt]
  simp only [Comp.toGluing, ofLens_kid c_lt, mkKidL, prefixSums_getD _ (show 5 ≤ 6 by omega),
    prefixSums_getD _ (show 6 ≤ 6 by omega)]

/-! ### The tables, as facts -/

/-- Table 2 entry `adj T c j`. -/
abbrev adjAt (T : Kind) (c j : Nat) : Option (Nat × Nat) := ((adj T).getD c []).getD j none

/-- Table 2 is consistent at `(c, j)`: a glued side is glued back, to a side of a different child. -/
def adjOk (T : Kind) (c j : Nat) : Bool :=
  match adjAt T c j with
  | none => true
  | some (c', j') => decide (c' < nk T) && decide (j' < 6) && c' != c && adjAt T c' j' == some (c, j)

/-- Table 2 is consistent at every side of every child of every kind (checked by `decide`). -/
theorem adj_ok : ∀ T : Kind, ∀ c, c < nk T → ∀ j, j < 6 → adjOk T c j = true := by
  intro T; cases T <;> decide

/-- A side glued by Table 2 is glued to a side of a different child, which is glued back to it. -/
theorem adj_valid {T : Kind} {c j c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6)
    (glued : adjAt T c j = some (c', j')) : c' < nk T ∧ j' < 6 ∧ c' ≠ c ∧ adjAt T c' j' = some (c, j) := by
  -- the table check at `(c, j)`
  have table := adj_ok T c c_lt j j_lt
  simp only [adjOk, glued, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at table
  exact ⟨table.1.1.1, table.1.1.2, table.1.2, table.2⟩

/-! ### The gluing formula -/

/-- Edge `pos j + o` of child `c` (offset `o` in side `j`) is glued as Table 2 says: to the edge of side `j'` of child
`c'` that is `o` edges from its end. -/
theorem ofLens_mate (len_pos : ∀ c, c < nk T → ∀ j, j < 6 → 1 ≤ L c j) {c j o : Nat} (c_lt : c < nk T) (j_lt : j < 6)
    (o_lt : o < L c j) :
    (Comp.ofLens T L d ω).mate c (pos (L c) j + o) =
      (adjAt T c j).map fun (c', j') => (c', pos (L c') j' + L c' j' - 1 - o) := by
  simp only [Comp.mate, Comp.sideOf]
  rw [ofLens_kid c_lt]
  simp only [mkKidL]
  rw [sideIdx_eq (L c) (len_pos c c_lt) j_lt o_lt, prefixSums_getD _ (by omega),
    show pos (L c) j + o - pos (L c) j = o by omega]
  show (match adjAt T c j with
    | none => none
    | some (c', j') =>
      some (c', ((Comp.ofLens T L d ω).kid c').U.getD j' 0 + ((Comp.ofLens T L d ω).kid c').len.getD j' 0 - 1 - o)) = _
  cases glued : adjAt T c j with
  | none => rfl
  | some p =>
    obtain ⟨c', j'⟩ := p
    obtain ⟨c'_lt, j'_lt, _, _⟩ := adj_valid c_lt j_lt glued
    simp only [Option.map_some, ofLens_U c'_lt (by omega : j' ≤ 6), ofLens_len c'_lt j'_lt]

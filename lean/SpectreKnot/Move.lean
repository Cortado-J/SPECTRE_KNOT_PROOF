/-
A *move*: lengthen side `j₀` of child `c₀` by 2, together with the side of the sibling glued to it (Table 2), or
alone if it lies on the parent's rim. The composition with the longer sides is (equivalent to) the old one with one
edge cut into three (`Move.OK.equiv`), so by `Subdivide` and `Signature` it has the signature if the old one has
(Lemma 7.1: `Move.OK.keep`, in `Parity.lean`).
-/
import SpectreKnot.Lens

namespace SpectreKnot.Compose

open Gluing Pattern

/-- A move: cut the edge at offset `r₀` of side `j₀` of child `c₀` (and the same edge seen from the sibling). -/
structure Move where
  c₀ : Nat
  j₀ : Nat
  r₀ : Nat

namespace Move

variable (T : Kind) (μ : Move)

/-- Is side `j₀` of child `c₀` glued to a sibling? -/
def two : Bool := (adjAt T μ.c₀ μ.j₀).isSome

/-- The sibling and its side (meaningful when `two`). -/
def c₁ : Nat := ((adjAt T μ.c₀ μ.j₀).getD (0, 0)).1
def j₁ : Nat := ((adjAt T μ.c₀ μ.j₀).getD (0, 0)).2

/-- Side `j` of child `c` is one of the sides lengthened. -/
def Hit (c j : Nat) : Prop := (c = μ.c₀ ∧ j = μ.j₀) ∨ (μ.two T = true ∧ c = μ.c₁ T ∧ j = μ.j₁ T)

instance (c j : Nat) : Decidable (μ.Hit T c j) := by unfold Hit; infer_instance

/-- The new side lengths. -/
def lens (L : Nat → Nat → Nat) (c j : Nat) : Nat := L c j + if μ.Hit T c j then 2 else 0

/-- The offset of the cut edge in the sibling's side. -/
def r₁ (L : Nat → Nat → Nat) : Nat := L μ.c₀ μ.j₀ - 1 - μ.r₀

/-- The cut, in the positions of the old composition. -/
def cut (L : Nat → Nat → Nat) : Cut :=
  ⟨μ.c₀, pos (L μ.c₀) μ.j₀ + μ.r₀, μ.c₁ T, pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L, μ.two T⟩

/-- The new Σ offset: the corner moves on by 2 if the edge cut lies before it on the Σ child's side 5. -/
def d' (L : Nat → Nat → Nat) (d : Nat) : Nat :=
  d + (if kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5 ∧ μ.r₀ + 2 ≤ d then 2 else 0)
    + (if μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5 ∧ μ.r₁ L + 2 ≤ d then 2 else 0)

/-- When a move can be made. -/
structure OK (L : Nat → Nat → Nat) (d : Nat) (ω : Bool) : Prop where
  /-- the old composition is well formed -/
  wf : (Comp.ofLens T L d ω).toGluing.WF
  /-- every side has an edge -/
  pos_len : ∀ c, c < nk T → ∀ j, j < 6 → 1 ≤ L c j
  /-- glued sides have the same length -/
  pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j
  /-- the child cut is a child -/
  c₀ : μ.c₀ < nk T
  /-- the side cut is one of its six sides -/
  j₀ : μ.j₀ < 6
  /-- the cut edge is not the first edge of its side -/
  r₀ : 1 ≤ μ.r₀
  /-- nor the last -/
  r₀' : μ.r₀ + 2 ≤ L μ.c₀ μ.j₀
  /-- the Σ corner and its neighbours lie inside side 5 of the Σ child -/
  sig : ∀ c, c < nk T → kidAt T c = .Sigma → 2 ≤ d ∧ d + 2 ≤ L c 5
  /-- there is only one Σ child -/
  sig1 : ∀ c c', c < nk T → c' < nk T → kidAt T c = .Sigma → kidAt T c' = .Sigma → c = c'
  /-- a cut on the Σ child's side 5 is clear of its corners -/
  cut₀ : kidAt T μ.c₀ = .Sigma → μ.j₀ = 5 → d + 1 ≤ μ.r₀ ∨ μ.r₀ + 2 ≤ d
  /-- the same, seen from the sibling -/
  cut₁ : μ.two T = true → kidAt T (μ.c₁ T) = .Sigma → μ.j₁ T = 5 → d + 1 ≤ μ.r₁ L ∨ μ.r₁ L + 2 ≤ d

variable {T} {μ} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- Side `j₀` of `c₀` is glued to side `j₁` of the sibling `c₁` if `two`, and lies on the parent's rim otherwise. -/
theorem adj₀ : adjAt T μ.c₀ μ.j₀ = if μ.two T = true then some (μ.c₁ T, μ.j₁ T) else none := by
  unfold two c₁ j₁
  cases adjAt T μ.c₀ μ.j₀ <;> rfl

/-! #### The new Σ offset -/

/-- If neither side lengthened is side 5 of the Σ child, the Σ offset does not change. -/
theorem d'_eq (not_sigma₀ : ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5))
    (not_sigma₁ : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5)) : μ.d' T L d = d := by
  unfold d'
  rw [ite_eq_right (show ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5 ∧ μ.r₀ + 2 ≤ d) from
      fun ⟨is_sigma, is_5, _⟩ => not_sigma₀ ⟨is_sigma, is_5⟩),
    ite_eq_right (show ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5 ∧ μ.r₁ L + 2 ≤ d) from
      fun ⟨side_glued, is_sigma, is_5, _⟩ => not_sigma₁ ⟨side_glued, is_sigma, is_5⟩)]
  rfl

/-- If side `j₀` of `c₀` is side 5 of the Σ child, the Σ offset moves on by 2 exactly when the cut lies before the
corner. -/
theorem d'_c₀ (is_sigma : kidAt T μ.c₀ = .Sigma) (is_5 : μ.j₀ = 5)
    (not_sigma₁ : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5)) :
    μ.d' T L d = d + if μ.r₀ + 2 ≤ d then 2 else 0 := by
  unfold d'
  rw [ite_eq_right (show ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5 ∧ μ.r₁ L + 2 ≤ d) from
      fun ⟨side_glued, sib_sigma, sib_5, _⟩ => not_sigma₁ ⟨side_glued, sib_sigma, sib_5⟩), Nat.add_zero]
  by_cases before : μ.r₀ + 2 ≤ d
  · rw [ite_eq_left ⟨is_sigma, is_5, before⟩, ite_eq_left before]
  · rw [ite_eq_right (fun ⟨_, _, before'⟩ => before before'), ite_eq_right before]

/-- If the sibling's side `j₁` is side 5 of the Σ child, the Σ offset moves on by 2 exactly when the cut lies before
the corner. -/
theorem d'_c₁ (side_glued : μ.two T = true) (is_sigma : kidAt T (μ.c₁ T) = .Sigma) (is_5 : μ.j₁ T = 5)
    (not_sigma₀ : ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5)) :
    μ.d' T L d = d + if μ.r₁ L + 2 ≤ d then 2 else 0 := by
  unfold d'
  rw [ite_eq_right (show ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5 ∧ μ.r₀ + 2 ≤ d) from
      fun ⟨c₀_sigma, c₀_5, _⟩ => not_sigma₀ ⟨c₀_sigma, c₀_5⟩), Nat.add_zero]
  by_cases before : μ.r₁ L + 2 ≤ d
  · rw [ite_eq_left ⟨side_glued, is_sigma, is_5, before⟩, ite_eq_left before]
  · rw [ite_eq_right (fun ⟨_, _, _, before'⟩ => before before'), ite_eq_right before]

namespace OK

variable (move_ok : μ.OK T L d ω)

include move_ok

set_option linter.unusedSectionVars false

/-- If side `j₀` of `c₀` is glued, the sibling `c₁` is a different child, and its side `j₁` is glued back. -/
theorem sib (side_glued : μ.two T = true) :
    μ.c₁ T < nk T ∧ μ.j₁ T < 6 ∧ μ.c₁ T ≠ μ.c₀ ∧ adjAt T (μ.c₁ T) (μ.j₁ T) = some (μ.c₀, μ.j₀) := by
  -- Table 2 glues side `j₀` of `c₀` to side `j₁` of `c₁`
  have glued := adj₀ (T := T) (μ := μ)
  rw [ite_eq_left side_glued] at glued
  exact adj_valid move_ok.c₀ move_ok.j₀ glued

/-- The sibling's side `j₁` is as long as side `j₀` of `c₀`. -/
theorem L₁ (side_glued : μ.two T = true) : L (μ.c₁ T) (μ.j₁ T) = L μ.c₀ μ.j₀ := by
  -- Table 2 glues side `j₀` of `c₀` to side `j₁` of `c₁`
  have glued := adj₀ (T := T) (μ := μ)
  rw [ite_eq_left side_glued] at glued
  exact move_ok.pair _ move_ok.c₀ _ move_ok.j₀ _ _ glued

/-- Only one side of each child is hit: of `c₀`, side `j₀`. -/
theorem hit_c₀ {j : Nat} : μ.Hit T μ.c₀ j ↔ j = μ.j₀ := by
  unfold Hit
  constructor
  · rintro (⟨_, is_j₀⟩ | ⟨side_glued, same, _⟩)
    · exact is_j₀
    · exact absurd same.symm (move_ok.sib side_glued).2.2.1
  · intro is_j₀; exact Or.inl ⟨rfl, is_j₀⟩

/-- Of the sibling `c₁`, only side `j₁` is hit. -/
theorem hit_c₁ (side_glued : μ.two T = true) {j : Nat} : μ.Hit T (μ.c₁ T) j ↔ j = μ.j₁ T := by
  unfold Hit
  constructor
  · rintro (⟨same, _⟩ | ⟨_, _, is_j₁⟩)
    · exact absurd same (move_ok.sib side_glued).2.2.1
    · exact is_j₁
  · intro is_j₁; exact Or.inr ⟨side_glued, rfl, is_j₁⟩

/-- No side of any other child is hit. -/
theorem hit_other {c j : Nat} (not_c₀ : c ≠ μ.c₀) (not_c₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T)) : ¬ μ.Hit T c j := by
  rintro (⟨is_c₀, _⟩ | ⟨side_glued, is_c₁, _⟩)
  · exact not_c₀ is_c₀
  · exact not_c₁ ⟨side_glued, is_c₁⟩

/-- Positions of the new composition, on `c₀`: the sides after `j₀` begin two edges later. -/
theorem pos_c₀ (j : Nat) : pos (μ.lens T L μ.c₀) j = pos (L μ.c₀) j + if μ.j₀ < j then 2 else 0 := by
  induction j with
  | zero => simp [pos]
  | succ j ih =>
    rw [pos_succ, pos_succ, ih]
    simp only [lens]
    by_cases is_j₀ : j = μ.j₀
    · rw [ite_eq_left (move_ok.hit_c₀.mpr is_j₀), ite_eq_right (by omega), ite_eq_left (by omega)]; omega
    · rw [ite_eq_right (fun hit => is_j₀ (move_ok.hit_c₀.mp hit))]
      by_cases after : μ.j₀ < j
      · rw [ite_eq_left after, ite_eq_left (by omega)]; omega
      · rw [ite_eq_right after, ite_eq_right (by omega)]; omega

/-- Positions of the new composition, on the sibling `c₁`: the sides after `j₁` begin two edges later. -/
theorem pos_c₁ (side_glued : μ.two T = true) (j : Nat) :
    pos (μ.lens T L (μ.c₁ T)) j = pos (L (μ.c₁ T)) j + if μ.j₁ T < j then 2 else 0 := by
  induction j with
  | zero => simp [pos]
  | succ j ih =>
    rw [pos_succ, pos_succ, ih]
    simp only [lens]
    by_cases is_j₁ : j = μ.j₁ T
    · rw [ite_eq_left ((move_ok.hit_c₁ side_glued).mpr is_j₁), ite_eq_right (by omega), ite_eq_left (by omega)]; omega
    · rw [ite_eq_right (fun hit => is_j₁ ((move_ok.hit_c₁ side_glued).mp hit))]
      by_cases after : μ.j₁ T < j
      · rw [ite_eq_left after, ite_eq_left (by omega)]; omega
      · rw [ite_eq_right after, ite_eq_right (by omega)]; omega

/-- Positions of the new composition, on every other child: unchanged. -/
theorem pos_other {c : Nat} (not_c₀ : c ≠ μ.c₀) (not_c₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T)) (j : Nat) :
    pos (μ.lens T L c) j = pos (L c) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pos_succ, pos_succ, ih]; simp only [lens]; rw [ite_eq_right (move_ok.hit_other not_c₀ not_c₁)]; omega

/-- After the move every side still has an edge. -/
theorem lens_pos_len : ∀ c, c < nk T → ∀ j, j < 6 → 1 ≤ μ.lens T L c j := by
  intro c c_lt j j_lt
  -- every side had an edge before
  have := move_ok.pos_len c c_lt j j_lt
  simp only [lens]; omega

/-- The cut can be made. -/
theorem cutOK : (μ.cut T L).OK (Comp.ofLens T L d ω).toGluing where
  wf := move_ok.wf
  c₀ := by simp only [cut]; rw [ofLens_n]; exact move_ok.c₀
  e₀ := by
    show pos (L μ.c₀) μ.j₀ + μ.r₀ + 1 < (Comp.ofLens T L d ω).toGluing.E μ.c₀
    rw [ofLens_E move_ok.c₀]
    -- side `j₀` is one of the six sides
    have j₀_lt := move_ok.j₀
    -- side `j₀` ends where side `j₀ + 1` begins
    have side_end := pos_lt_of_pos (L μ.c₀) (move_ok.pos_len _ move_ok.c₀) (show μ.j₀ < μ.j₀ + 1 by omega)
      (by omega)
    -- side `j₀ + 1` begins no later than the end of the rim
    have next_le := pos_mono (L μ.c₀) (show μ.j₀ + 1 ≤ 6 by omega)
    -- the cut edge is at least two edges from the end of side `j₀`
    have r₀_le := move_ok.r₀'
    rw [pos_succ] at next_le; omega
  mate := by
    show (Comp.ofLens T L d ω).mate μ.c₀ (pos (L μ.c₀) μ.j₀ + μ.r₀) =
      if μ.two T = true then some (μ.c₁ T, pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L) else none
    -- the cut edge lies inside side `j₀`
    have r₀_le := move_ok.r₀'
    rw [ofLens_mate move_ok.pos_len move_ok.c₀ move_ok.j₀ (by omega), adj₀]
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued, ite_eq_left side_glued]
      simp only [Option.map_some, move_ok.L₁ side_glued, r₁]
      congr 2; omega
    · rw [ite_eq_right side_glued, ite_eq_right side_glued]; rfl
  ne side_glued := (move_ok.sib side_glued).2.2.1
  e₁ side_glued := by
    obtain ⟨c₁_lt, j₁_lt, _, _⟩ := move_ok.sib side_glued
    show pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L + 1 < (Comp.ofLens T L d ω).toGluing.E (μ.c₁ T)
    rw [ofLens_E c₁_lt]
    -- side `j₁ + 1` begins no later than the end of the rim
    have next_le := pos_mono (L (μ.c₁ T)) (show μ.j₁ T + 1 ≤ 6 by omega)
    -- the cut edge is at least two edges from the end of side `j₀`
    have r₀_le := move_ok.r₀'
    -- and at least one edge from its start
    have r₀_ge := move_ok.r₀
    -- the two glued sides have the same length
    have same_len := move_ok.L₁ side_glued
    simp only [r₁]; rw [pos_succ] at next_le; omega

/-! #### Positions under the cut -/

/-- On `c₀`, positions up to the cut edge stay put. -/
theorem sh₀_le {p : Nat} (p_le : p ≤ pos (L μ.c₀) μ.j₀ + μ.r₀) : (μ.cut T L).sh μ.c₀ p = p :=
  move_ok.cutOK.sh_c₀_le (G := (Comp.ofLens T L d ω).toGluing) p_le

/-- On `c₀`, positions after the cut edge move on by 2. -/
theorem sh₀_gt {p : Nat} (p_gt : pos (L μ.c₀) μ.j₀ + μ.r₀ < p) : (μ.cut T L).sh μ.c₀ p = p + 2 :=
  move_ok.cutOK.sh_c₀_gt (G := (Comp.ofLens T L d ω).toGluing) p_gt

/-- On the sibling, positions up to its cut edge stay put. -/
theorem sh₁_le (side_glued : μ.two T = true) {p : Nat} (p_le : p ≤ pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L) :
    (μ.cut T L).sh (μ.c₁ T) p = p :=
  move_ok.cutOK.sh_c₁_le (G := (Comp.ofLens T L d ω).toGluing) side_glued p_le

/-- On the sibling, positions after its cut edge move on by 2. -/
theorem sh₁_gt (side_glued : μ.two T = true) {p : Nat} (p_gt : pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L < p) :
    (μ.cut T L).sh (μ.c₁ T) p = p + 2 :=
  move_ok.cutOK.sh_c₁_gt (G := (Comp.ofLens T L d ω).toGluing) side_glued p_gt

/-- On every other child, positions stay put. -/
theorem sh_oth {c p : Nat} (not_c₀ : c ≠ μ.c₀) (not_c₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T)) :
    (μ.cut T L).sh c p = p :=
  move_ok.cutOK.sh_other (G := (Comp.ofLens T L d ω).toGluing) not_c₀ not_c₁

/-- Positions in a side that is not lengthened move with the sides before it. -/
theorem sh_side {c j q : Nat} (c_lt : c < nk T) (j_lt : j < 6) (q_lt : q < L c j) (not_hit : ¬ μ.Hit T c j) :
    (μ.cut T L).sh c (pos (L c) j + q) = pos (μ.lens T L c) j + q := by
  -- the cut edge is at least two edges from the end of side `j₀`
  have r₀_le := move_ok.r₀'
  by_cases is_c₀ : c = μ.c₀
  · subst is_c₀
    -- side `j` is not the side cut
    have not_j₀ : j ≠ μ.j₀ := fun is_j₀ => not_hit (move_ok.hit_c₀.mpr is_j₀)
    rw [move_ok.pos_c₀]
    by_cases before : j < μ.j₀
    -- side `j` ends no later than side `j₀` begins
    · have side_ends := pos_mono (L μ.c₀) (show j + 1 ≤ μ.j₀ by omega)
      rw [pos_succ] at side_ends
      rw [move_ok.sh₀_le (by omega), ite_eq_right (by omega)]; omega
    -- side `j` begins no earlier than side `j₀` ends
    · have side_begins := pos_mono (L μ.c₀) (show μ.j₀ + 1 ≤ j by omega)
      rw [pos_succ] at side_begins
      rw [move_ok.sh₀_gt (by omega), ite_eq_left (by omega)]; omega
  · by_cases is_c₁ : μ.two T = true ∧ c = μ.c₁ T
    · obtain ⟨side_glued, rfl⟩ := is_c₁
      -- side `j` is not the sibling's side cut
      have not_j₁ : j ≠ μ.j₁ T := fun is_j₁ => not_hit ((move_ok.hit_c₁ side_glued).mpr is_j₁)
      -- the two glued sides have the same length
      have same_len := move_ok.L₁ side_glued
      rw [move_ok.pos_c₁ side_glued]
      by_cases before : j < μ.j₁ T
      -- side `j` ends no later than side `j₁` begins
      · have side_ends := pos_mono (L (μ.c₁ T)) (show j + 1 ≤ μ.j₁ T by omega)
        rw [pos_succ] at side_ends
        rw [move_ok.sh₁_le side_glued (by simp only [r₁]; omega), ite_eq_right (by omega)]; omega
      -- side `j` begins no earlier than side `j₁` ends
      · have side_begins := pos_mono (L (μ.c₁ T)) (show μ.j₁ T + 1 ≤ j by omega)
        rw [pos_succ] at side_begins
        rw [move_ok.sh₁_gt side_glued (by simp only [r₁]; omega), ite_eq_left (by omega)]; omega
    · rw [move_ok.sh_oth is_c₀ is_c₁, move_ok.pos_other is_c₀ is_c₁]

/-- A position determines its side and offset. -/
theorem side_unique {c j j' o o' : Nat} (c_lt : c < nk T) (j_lt : j < 6) (j'_lt : j' < 6) (o_lt : o < L c j)
    (o'_lt : o' < L c j') (same : pos (L c) j + o = pos (L c) j' + o') : j = j' := by
  -- the side lookup finds side `j` at the first position
  have finds_j := sideIdx_eq (L c) (move_ok.pos_len c c_lt) j_lt o_lt
  -- and side `j'` at the second
  have finds_j' := sideIdx_eq (L c) (move_ok.pos_len c c_lt) j'_lt o'_lt
  rw [same] at finds_j
  rw [finds_j] at finds_j'; exact finds_j'

/-- The partner of a side that is not lengthened is not lengthened either. -/
theorem not_hit_partner {c j c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6) (glued : adjAt T c j = some (c', j'))
    (not_hit : ¬ μ.Hit T c j) : ¬ μ.Hit T c' j' := by
  obtain ⟨c'_lt, j'_lt, c'_ne, glued_back⟩ := adj_valid c_lt j_lt glued
  rintro (⟨rfl, rfl⟩ | ⟨side_glued, rfl, rfl⟩)
  -- (c', j') = (c₀, j₀): then (c, j) is the partner of (c₀, j₀), which is hit
  · have partner := adj₀ (T := T) (μ := μ)
    rw [glued_back] at partner
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued] at partner
      simp only [Option.some.injEq, Prod.mk.injEq] at partner
      exact not_hit (Or.inr ⟨side_glued, partner.1, partner.2⟩)
    · rw [ite_eq_right side_glued] at partner; contradiction
  -- (c', j') = (c₁, j₁): then (c, j) is the partner of (c₁, j₁), that is (c₀, j₀)
  · have partner := (move_ok.sib side_glued).2.2.2
    rw [glued_back] at partner
    simp only [Option.some.injEq, Prod.mk.injEq] at partner
    exact not_hit (Or.inl ⟨partner.1, partner.2⟩)

/-! #### The subdivided gluing, in the move's terms -/

set_option quotPrecheck false
local notation "G₀" => (Comp.ofLens T L d ω).toGluing
local notation "G₁" => (Comp.ofLens T (μ.lens T L) (μ.d' T L d) ω).toGluing
local notation "Gs" => subdiv (Comp.ofLens T L d ω).toGluing (μ.cut T L)

/-- In the subdivided gluing, `c₀` has two more edges. -/
theorem sE₀ : (Gs).E μ.c₀ = (G₀).E μ.c₀ + 2 := move_ok.cutOK.E_c₀

/-- In the subdivided gluing, the sibling has two more edges. -/
theorem sE₁ (side_glued : μ.two T = true) : (Gs).E (μ.c₁ T) = (G₀).E (μ.c₁ T) + 2 := move_ok.cutOK.E_c₁ side_glued

/-- In the subdivided gluing, every other child keeps its rim length. -/
theorem sE_oth {c : Nat} (not_c₀ : c ≠ μ.c₀) (not_c₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T)) : (Gs).E c = (G₀).E c :=
  move_ok.cutOK.E_other not_c₀ not_c₁

/-- In the subdivided gluing, an edge that is not cut is glued as before (with positions moved on). -/
theorem smate_old {c k : Nat} (not_cut₀ : ¬ (c = μ.c₀ ∧ k = pos (L μ.c₀) μ.j₀ + μ.r₀))
    (not_cut₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T ∧ k = pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L)) :
    (Gs).mate c ((μ.cut T L).sh c k) = ((G₀).mate c k).map fun (c₂, k₂) => (c₂, (μ.cut T L).sh c₂ k₂) :=
  move_ok.cutOK.mate_old not_cut₀ not_cut₁

/-- In the subdivided gluing, the three new edges of `c₀` are glued, in reverse order, to the sibling's (or lie on the
rim). -/
theorem smate_new₀ {i : Nat} (i_le : i ≤ 2) :
    (Gs).mate μ.c₀ (pos (L μ.c₀) μ.j₀ + μ.r₀ + i) =
      if μ.two T = true then some (μ.c₁ T, pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L + 2 - i) else none :=
  move_ok.cutOK.mate_new₀ i_le

/-- In the subdivided gluing, the three new edges of the sibling are glued, in reverse order, to those of `c₀`. -/
theorem smate_new₁ (side_glued : μ.two T = true) {i : Nat} (i_le : i ≤ 2) :
    (Gs).mate (μ.c₁ T) (pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L + i) = some (μ.c₀, pos (L μ.c₀) μ.j₀ + μ.r₀ + 2 - i) :=
  move_ok.cutOK.mate_new₁ side_glued i_le

/-- Rim lengths agree. -/
theorem E_eq {c : Nat} (c_lt : c < nk T) : (G₁).E c = (Gs).E c := by
  rw [ofLens_E c_lt]
  -- side `j₀` is one of the six sides
  have j₀_lt := move_ok.j₀
  by_cases is_c₀ : c = μ.c₀
  · subst is_c₀; rw [move_ok.pos_c₀, ite_eq_left (by omega), move_ok.sE₀, ofLens_E c_lt]
  · by_cases is_c₁ : μ.two T = true ∧ c = μ.c₁ T
    · obtain ⟨side_glued, rfl⟩ := is_c₁
      rw [move_ok.pos_c₁ side_glued, ite_eq_left (move_ok.sib side_glued).2.1, move_ok.sE₁ side_glued, ofLens_E c_lt]
    · rw [move_ok.pos_other is_c₀ is_c₁, move_ok.sE_oth is_c₀ is_c₁, ofLens_E c_lt]

/-- Corners agree. -/
theorem A_eq {c : Nat} (c_lt : c < nk T) : (G₁).A c = (μ.cut T L).sh c ((G₀).A c) := by
  rw [ofLens_A c_lt, ofLens_A c_lt]
  -- the cut edge is at least two edges from the end of side `j₀`
  have r₀_le := move_ok.r₀'
  -- and at least one edge from its start
  have r₀_ge := move_ok.r₀
  -- side `j₀` is one of the six sides
  have j₀_lt := move_ok.j₀
  by_cases is_sigma : kidAt T c = .Sigma
  · rw [ite_eq_left is_sigma, ite_eq_left is_sigma]
    obtain ⟨d_ge, d_le⟩ := move_ok.sig c c_lt is_sigma
    by_cases is_c₀ : c = μ.c₀
    · subst is_c₀
      -- the sibling is not the Σ child as well
      have sib_not_sigma : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma) := fun ⟨side_glued, sib_sigma⟩ =>
        (move_ok.sib side_glued).2.2.1 (move_ok.sig1 _ _ (move_ok.sib side_glued).1 c_lt sib_sigma is_sigma)
      rw [move_ok.pos_c₀]
      by_cases is_5 : μ.j₀ = 5
      · rw [ite_eq_right (by omega)]
        -- side `j₀` is side 5
        have pos_5 : pos (L μ.c₀) μ.j₀ = pos (L μ.c₀) 5 := by rw [is_5]
        rw [d'_c₀ is_sigma is_5 (fun ⟨side_glued, sib_sigma, _⟩ => sib_not_sigma ⟨side_glued, sib_sigma⟩)]
        rcases move_ok.cut₀ is_sigma is_5 with cut_after | cut_before
        · rw [ite_eq_right (show ¬ μ.r₀ + 2 ≤ d by omega), move_ok.sh₀_le (by omega)]; omega
        · rw [ite_eq_left cut_before, move_ok.sh₀_gt (by omega)]; omega
      · rw [ite_eq_left (by omega), d'_eq (fun ⟨_, is_5'⟩ => is_5 is_5')
          (fun ⟨side_glued, sib_sigma, _⟩ => sib_not_sigma ⟨side_glued, sib_sigma⟩)]
        -- side `j₀` ends before side 5 begins
        have side_ends := pos_mono (L μ.c₀) (show μ.j₀ + 1 ≤ 5 by omega)
        rw [pos_succ] at side_ends
        rw [move_ok.sh₀_gt (by omega)]; omega
    · by_cases is_c₁ : μ.two T = true ∧ c = μ.c₁ T
      · obtain ⟨side_glued, rfl⟩ := is_c₁
        -- `c₀` is not the Σ child, since the sibling is
        have c₀_not_sigma : kidAt T μ.c₀ ≠ .Sigma :=
          fun c₀_sigma => is_c₀ (move_ok.sig1 _ _ c_lt move_ok.c₀ is_sigma c₀_sigma)
        -- the two glued sides have the same length
        have same_len := move_ok.L₁ side_glued
        rw [move_ok.pos_c₁ side_glued]
        by_cases is_5 : μ.j₁ T = 5
        · rw [ite_eq_right (by omega)]
          -- side `j₁` is side 5
          have pos_5 : pos (L (μ.c₁ T)) (μ.j₁ T) = pos (L (μ.c₁ T)) 5 := by rw [is_5]
          rw [d'_c₁ side_glued is_sigma is_5 (fun ⟨c₀_sigma, _⟩ => c₀_not_sigma c₀_sigma)]
          rcases move_ok.cut₁ side_glued is_sigma is_5 with cut_after | cut_before
          · rw [ite_eq_right (show ¬ μ.r₁ L + 2 ≤ d by omega), move_ok.sh₁_le side_glued (by omega)]; omega
          · rw [ite_eq_left cut_before, move_ok.sh₁_gt side_glued (by omega)]; omega
        -- side `j₁` is one of the six sides, and not side 5
        · have j₁_lt := (move_ok.sib side_glued).2.1
          rw [ite_eq_left (by omega)]
          rw [d'_eq (fun ⟨c₀_sigma, _⟩ => c₀_not_sigma c₀_sigma) (fun ⟨_, _, is_5'⟩ => is_5 is_5')]
          -- side `j₁` ends before side 5 begins
          have side_ends := pos_mono (L (μ.c₁ T)) (show μ.j₁ T + 1 ≤ 5 by omega)
          rw [pos_succ] at side_ends
          rw [move_ok.sh₁_gt side_glued (by simp only [r₁]; omega)]; omega
      -- the Σ child is neither `c₀` nor the sibling
      · have c₀_not_sigma : kidAt T μ.c₀ ≠ .Sigma :=
          fun c₀_sigma => is_c₀ (move_ok.sig1 _ _ c_lt move_ok.c₀ is_sigma c₀_sigma)
        -- the sibling is not the Σ child
        have sib_not_sigma : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma) := fun ⟨side_glued, sib_sigma⟩ =>
          is_c₁ ⟨side_glued, move_ok.sig1 _ _ c_lt (move_ok.sib side_glued).1 is_sigma sib_sigma⟩
        rw [move_ok.pos_other is_c₀ is_c₁, d'_eq (fun ⟨c₀_sigma, _⟩ => c₀_not_sigma c₀_sigma)
          (fun ⟨side_glued, sib_sigma, _⟩ => sib_not_sigma ⟨side_glued, sib_sigma⟩), move_ok.sh_oth is_c₀ is_c₁]
  · rw [ite_eq_right is_sigma, ite_eq_right is_sigma]
    by_cases is_c₀ : c = μ.c₀
    · subst is_c₀; rw [move_ok.sh₀_le (by omega)]
    · by_cases is_c₁ : μ.two T = true ∧ c = μ.c₁ T
      · obtain ⟨side_glued, rfl⟩ := is_c₁; rw [move_ok.sh₁_le side_glued (by omega)]
      · rw [move_ok.sh_oth is_c₀ is_c₁]

/-- The corner `A` is not at either end of a cut edge (cuts avoid the first and last edge of every side, and the Σ
corner). -/
theorem A_clear₀ {c : Nat} (c_lt : c < nk T) (is_c₀ : c = μ.c₀) :
    (G₀).A c ≠ pos (L μ.c₀) μ.j₀ + μ.r₀ ∧ (G₀).A c ≠ pos (L μ.c₀) μ.j₀ + μ.r₀ + 1 := by
  subst is_c₀
  rw [ofLens_A c_lt]
  -- the cut edge is at least two edges from the end of side `j₀`
  have r₀_le := move_ok.r₀'
  -- and at least one edge from its start
  have r₀_ge := move_ok.r₀
  -- side `j₀` is one of the six sides
  have j₀_lt := move_ok.j₀
  by_cases is_sigma : kidAt T μ.c₀ = .Sigma
  · rw [ite_eq_left is_sigma]
    obtain ⟨d_ge, d_le⟩ := move_ok.sig _ c_lt is_sigma
    by_cases is_5 : μ.j₀ = 5
    -- side `j₀` is side 5, and the cut is clear of the corner
    · have pos_5 : pos (L μ.c₀) μ.j₀ = pos (L μ.c₀) 5 := by rw [is_5]
      rcases move_ok.cut₀ is_sigma is_5 with cut_after | cut_before <;> omega
    -- side `j₀` ends before side 5 begins
    · have side_ends := pos_mono (L μ.c₀) (show μ.j₀ + 1 ≤ 5 by omega)
      rw [pos_succ] at side_ends; omega
  · rw [ite_eq_right is_sigma]; omega

/-- The cut edge is not the first edge of the sibling's side. -/
theorem r₁_ge : 1 ≤ μ.r₁ L := by
  -- the cut edge is not the last edge of side `j₀`
  have := move_ok.r₀'
  simp only [r₁]; omega

/-- Nor the last. -/
theorem r₁_le : μ.r₁ L + 2 ≤ L μ.c₀ μ.j₀ := by
  -- the cut edge is not the first edge of side `j₀`
  have := move_ok.r₀
  -- nor the last
  have := move_ok.r₀'
  simp only [r₁]; omega

/-- The sibling's corner `A` is not at either end of its cut edge. -/
theorem A_clear₁ (side_glued : μ.two T = true) {c : Nat} (c_lt : c < nk T) (is_c₁ : c = μ.c₁ T) :
    (G₀).A c ≠ pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L ∧ (G₀).A c ≠ pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L + 1 := by
  subst is_c₁
  rw [ofLens_A c_lt]
  -- the cut edge is not the last edge of the sibling's side
  have r₁_le := move_ok.r₁_le
  -- nor the first
  have r₁_ge := move_ok.r₁_ge
  -- the two glued sides have the same length
  have same_len := move_ok.L₁ side_glued
  -- side `j₁` is one of the six sides
  have j₁_lt := (move_ok.sib side_glued).2.1
  by_cases is_sigma : kidAt T (μ.c₁ T) = .Sigma
  · rw [ite_eq_left is_sigma]
    obtain ⟨d_ge, d_le⟩ := move_ok.sig _ c_lt is_sigma
    by_cases is_5 : μ.j₁ T = 5
    -- side `j₁` is side 5, and the cut is clear of the corner
    · have pos_5 : pos (L (μ.c₁ T)) (μ.j₁ T) = pos (L (μ.c₁ T)) 5 := by rw [is_5]
      rcases move_ok.cut₁ side_glued is_sigma is_5 with cut_after | cut_before <;> omega
    -- side `j₁` ends before side 5 begins
    · have side_ends := pos_mono (L (μ.c₁ T)) (show μ.j₁ T + 1 ≤ 5 by omega)
      rw [pos_succ] at side_ends; omega
  · rw [ite_eq_right is_sigma]; omega

/-- Second corners agree. -/
theorem B_eq {c : Nat} (c_lt : c < nk T) : (G₁).B c = (μ.cut T L).sh c ((G₀).B c) := by
  -- the corner `A` is a vertex of the child
  have A_lt := move_ok.wf.A_lt c (by rw [ofLens_n]; exact c_lt)
  rw [ofLens_B (L := μ.lens T L) (d := μ.d' T L d) c_lt, ofLens_B (L := L) (d := d) c_lt,
    ← ofLens_E (L := μ.lens T L) (d := μ.d' T L d) (ω := ω) c_lt, ← ofLens_E (L := L) (d := d) (ω := ω) c_lt,
    move_ok.E_eq c_lt, move_ok.A_eq c_lt]
  -- `A` is at neither end of the cut edge of `c₀`
  have not_cut₀ : ∀ i, i ≤ 1 → ¬ (c = (μ.cut T L).c₀ ∧ (G₀).A c = (μ.cut T L).e₀ + i) := by
    rintro i i_le ⟨is_c₀, at_cut⟩
    -- the corner is clear of both ends of the cut edge
    have clear := move_ok.A_clear₀ c_lt is_c₀
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact clear.1 at_cut
    · exact clear.2 at_cut
  -- nor at either end of the sibling's cut edge
  have not_cut₁ : ∀ i, i ≤ 1 →
      ¬ ((μ.cut T L).two = true ∧ c = (μ.cut T L).c₁ ∧ (G₀).A c = (μ.cut T L).e₁ + i) := by
    rintro i i_le ⟨side_glued, is_c₁, at_cut⟩
    -- the corner is clear of both ends of the cut edge
    have clear := move_ok.A_clear₁ side_glued c_lt is_c₁
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact clear.1 at_cut
    · exact clear.2 at_cut
  by_cases B_after_A : ω = true
  · rw [ite_eq_left B_after_A, ite_eq_left B_after_A]
    exact move_ok.cutOK.nxt_sh A_lt (not_cut₀ 0 (by omega)) (not_cut₁ 0 (by omega))
  · rw [ite_eq_right B_after_A, ite_eq_right B_after_A]
    exact move_ok.cutOK.prv_sh A_lt (not_cut₀ 1 (by omega)) (not_cut₁ 1 (by omega))

/-- The gluing along the lengthened side `j₀` of `c₀`. -/
theorem mate_hit₀ {o : Nat} (o_lt : o < L μ.c₀ μ.j₀ + 2) :
    (adjAt T μ.c₀ μ.j₀).map (fun (c', j') => (c', pos (μ.lens T L c') j' + μ.lens T L c' j' - 1 - o)) =
      (Gs).mate μ.c₀ (pos (μ.lens T L μ.c₀) μ.j₀ + o) := by
  -- the cut edge is at least two edges from the end of side `j₀`
  have r₀_le := move_ok.r₀'
  -- and at least one edge from its start
  have r₀_ge := move_ok.r₀
  rw [move_ok.pos_c₀, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero]
  -- `c₀` is not the sibling, so none of its edges is the sibling's cut edge
  have not_cut₁ : ∀ k, ¬ (μ.two T = true ∧ μ.c₀ = μ.c₁ T ∧ k = pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L) :=
    fun _ ⟨side_glued, same, _⟩ => (move_ok.sib side_glued).2.2.1 same.symm
  -- an old edge of side `j₀` other than the cut edge is glued as Table 2 says, with positions moved on
  have old : ∀ q, q < L μ.c₀ μ.j₀ → q ≠ μ.r₀ →
      (Gs).mate μ.c₀ ((μ.cut T L).sh μ.c₀ (pos (L μ.c₀) μ.j₀ + q)) =
        if μ.two T = true then
          some (μ.c₁ T, (μ.cut T L).sh (μ.c₁ T) (pos (L (μ.c₁ T)) (μ.j₁ T) + L μ.c₀ μ.j₀ - 1 - q))
        else none := by
    intro q q_lt not_r₀
    rw [move_ok.smate_old (fun ⟨_, same⟩ => not_r₀ (by omega)) (not_cut₁ _)]
    show ((Comp.ofLens T L d ω).mate μ.c₀ (pos (L μ.c₀) μ.j₀ + q)).map _ = _
    rw [ofLens_mate move_ok.pos_len move_ok.c₀ move_ok.j₀ q_lt, adj₀]
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued, ite_eq_left side_glued]; simp only [Option.map_some, move_ok.L₁ side_glued]
    · rw [ite_eq_right side_glued, ite_eq_right side_glued]; rfl
  rw [adj₀]
  rcases (show o < μ.r₀ ∨ (μ.r₀ ≤ o ∧ o ≤ μ.r₀ + 2) ∨ μ.r₀ + 2 < o by omega) with before | at_cut | after
  · rw [← move_ok.sh₀_le (p := pos (L μ.c₀) μ.j₀ + o) (by omega), old o (by omega) (by omega)]
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued, ite_eq_left side_glued]; simp only [Option.map_some]
      rw [move_ok.pos_c₁ side_glued, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero, lens,
        ite_eq_left ((move_ok.hit_c₁ side_glued).mpr rfl), move_ok.L₁ side_glued,
        move_ok.sh₁_gt side_glued (by simp only [r₁]; omega)]
      congr 2; omega
    · rw [ite_eq_right side_glued, ite_eq_right side_glued]; rfl
  · obtain ⟨i, i_le, rfl⟩ : ∃ i, i ≤ 2 ∧ o = μ.r₀ + i := ⟨o - μ.r₀, by omega, by omega⟩
    rw [show pos (L μ.c₀) μ.j₀ + (μ.r₀ + i) = pos (L μ.c₀) μ.j₀ + μ.r₀ + i by omega, move_ok.smate_new₀ i_le]
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued, ite_eq_left side_glued]; simp only [Option.map_some]
      rw [move_ok.pos_c₁ side_glued, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero, lens,
        ite_eq_left ((move_ok.hit_c₁ side_glued).mpr rfl), move_ok.L₁ side_glued]
      simp only [r₁]; congr 2; omega
    · rw [ite_eq_right side_glued, ite_eq_right side_glued]; rfl
  · rw [show pos (L μ.c₀) μ.j₀ + o = pos (L μ.c₀) μ.j₀ + (o - 2) + 2 by omega,
      ← move_ok.sh₀_gt (p := pos (L μ.c₀) μ.j₀ + (o - 2)) (by omega), old (o - 2) (by omega) (by omega)]
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued, ite_eq_left side_glued]; simp only [Option.map_some]
      rw [move_ok.pos_c₁ side_glued, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero, lens,
        ite_eq_left ((move_ok.hit_c₁ side_glued).mpr rfl), move_ok.L₁ side_glued,
        move_ok.sh₁_le side_glued (by simp only [r₁]; omega)]
      congr 2; omega
    · rw [ite_eq_right side_glued, ite_eq_right side_glued]; rfl

/-- The gluing along the lengthened side `j₁` of the sibling `c₁`. -/
theorem mate_hit₁ (side_glued : μ.two T = true) {o : Nat} (o_lt : o < L μ.c₀ μ.j₀ + 2) :
    (adjAt T (μ.c₁ T) (μ.j₁ T)).map (fun (c', j') => (c', pos (μ.lens T L c') j' + μ.lens T L c' j' - 1 - o)) =
      (Gs).mate (μ.c₁ T) (pos (μ.lens T L (μ.c₁ T)) (μ.j₁ T) + o) := by
  -- the cut edge is at least two edges from the end of side `j₀`
  have r₀_le := move_ok.r₀'
  -- and at least one edge from its start
  have r₀_ge := move_ok.r₀
  -- the two glued sides have the same length
  have same_len := move_ok.L₁ side_glued
  -- the offset of the cut edge in the sibling's side
  have r₁_eq : μ.r₁ L = L μ.c₀ μ.j₀ - 1 - μ.r₀ := rfl
  obtain ⟨c₁_lt, j₁_lt, c₁_ne, glued_back⟩ := move_ok.sib side_glued
  rw [move_ok.pos_c₁ side_glued, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero, glued_back]; simp only [Option.map_some]
  rw [move_ok.pos_c₀, ite_eq_right (Nat.lt_irrefl _), Nat.add_zero, lens, ite_eq_left (move_ok.hit_c₀.mpr rfl)]
  -- the sibling is not `c₀`, so none of its edges is the cut edge of `c₀`
  have not_cut₀ : ∀ k, ¬ (μ.c₁ T = μ.c₀ ∧ k = pos (L μ.c₀) μ.j₀ + μ.r₀) := fun _ ⟨same, _⟩ => c₁_ne same
  -- an old edge of side `j₁` other than the cut edge is glued as Table 2 says, with positions moved on
  have old : ∀ q, q < L μ.c₀ μ.j₀ → q ≠ μ.r₁ L →
      (Gs).mate (μ.c₁ T) ((μ.cut T L).sh (μ.c₁ T) (pos (L (μ.c₁ T)) (μ.j₁ T) + q)) =
        some (μ.c₀, (μ.cut T L).sh μ.c₀ (pos (L μ.c₀) μ.j₀ + L μ.c₀ μ.j₀ - 1 - q)) := by
    intro q q_lt not_r₁
    rw [move_ok.smate_old (not_cut₀ _) (fun ⟨_, _, same⟩ => not_r₁ (by omega))]
    show ((Comp.ofLens T L d ω).mate (μ.c₁ T) (pos (L (μ.c₁ T)) (μ.j₁ T) + q)).map _ = _
    rw [ofLens_mate move_ok.pos_len c₁_lt j₁_lt (by omega), glued_back]; simp only [Option.map_some]
  rcases (show o < μ.r₁ L ∨ (μ.r₁ L ≤ o ∧ o ≤ μ.r₁ L + 2) ∨ μ.r₁ L + 2 < o by omega) with before | at_cut | after
  · rw [← move_ok.sh₁_le side_glued (p := pos (L (μ.c₁ T)) (μ.j₁ T) + o) (by omega),
      old o (by simp only [r₁] at before; omega) (by omega), move_ok.sh₀_gt (by simp only [r₁] at before; omega)]
    congr 2; omega
  · obtain ⟨i, i_le, rfl⟩ : ∃ i, i ≤ 2 ∧ o = μ.r₁ L + i := ⟨o - μ.r₁ L, by omega, by omega⟩
    rw [show pos (L (μ.c₁ T)) (μ.j₁ T) + (μ.r₁ L + i) = pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L + i by omega,
      move_ok.smate_new₁ side_glued i_le]
    simp only [r₁]; congr 2; omega
  · rw [show pos (L (μ.c₁ T)) (μ.j₁ T) + o = pos (L (μ.c₁ T)) (μ.j₁ T) + (o - 2) + 2 by omega,
      ← move_ok.sh₁_gt side_glued (p := pos (L (μ.c₁ T)) (μ.j₁ T) + (o - 2)) (by omega),
      old (o - 2) (by simp only [r₁] at after; omega) (by omega),
      move_ok.sh₀_le (by simp only [r₁] at after; omega)]
    congr 2; omega

/-- The gluings agree. -/
theorem mate_eq {c k : Nat} (c_lt : c < nk T) (k_lt : k < (G₁).E c) : (G₁).mate c k = (Gs).mate c k := by
  rw [ofLens_E c_lt] at k_lt
  obtain ⟨j, o, j_lt, o_lt, rfl⟩ := decomp (μ.lens T L c) 6 (Nat.le_refl _) k k_lt
  show (Comp.ofLens T (μ.lens T L) (μ.d' T L d) ω).mate c (pos (μ.lens T L c) j + o) = _
  rw [ofLens_mate move_ok.lens_pos_len c_lt j_lt o_lt]
  by_cases side_hit : μ.Hit T c j
  -- a lengthened side: the offset, against the old length plus 2
  · have o_lt_old := o_lt
    simp only [lens, ite_eq_left side_hit] at o_lt_old
    rcases side_hit with ⟨rfl, rfl⟩ | ⟨side_glued, rfl, rfl⟩
    · exact move_ok.mate_hit₀ o_lt_old
    · rw [move_ok.L₁ side_glued] at o_lt_old; exact move_ok.mate_hit₁ side_glued o_lt_old
  -- a side that is not lengthened keeps its length
  · have unchanged : ∀ c j, ¬ μ.Hit T c j → μ.lens T L c j = L c j := fun c j not_hit => by
      simp only [lens]; rw [ite_eq_right not_hit, Nat.add_zero]
    rw [unchanged c j side_hit] at o_lt
    rw [← move_ok.sh_side c_lt j_lt o_lt side_hit]
    -- the edge is not the cut edge of `c₀`, which lies in a lengthened side
    have not_cut₀ : ¬ (c = μ.c₀ ∧ pos (L c) j + o = pos (L μ.c₀) μ.j₀ + μ.r₀) := by
      rintro ⟨rfl, same⟩
      -- the cut edge lies inside side `j₀`
      have r₀_le := move_ok.r₀'
      exact side_hit (Or.inl ⟨rfl, move_ok.side_unique c_lt j_lt move_ok.j₀ o_lt (by omega) same⟩)
    -- nor the sibling's cut edge
    have not_cut₁ : ¬ (μ.two T = true ∧ c = μ.c₁ T ∧ pos (L c) j + o = pos (L (μ.c₁ T)) (μ.j₁ T) + μ.r₁ L) := by
      rintro ⟨side_glued, rfl, same⟩
      -- the cut edge lies inside the sibling's side `j₁`
      have r₁_le := move_ok.r₁_le
      -- the two glued sides have the same length
      have same_len := move_ok.L₁ side_glued
      exact side_hit (Or.inr ⟨side_glued, rfl,
        move_ok.side_unique c_lt j_lt (move_ok.sib side_glued).2.1 o_lt (by omega) same⟩)
    rw [move_ok.smate_old not_cut₀ not_cut₁]
    show _ = ((Comp.ofLens T L d ω).mate c (pos (L c) j + o)).map _
    rw [ofLens_mate move_ok.pos_len c_lt j_lt o_lt]
    cases glued : adjAt T c j with
    | none => rfl
    | some p =>
      obtain ⟨c', j'⟩ := p
      obtain ⟨c'_lt, j'_lt, _, _⟩ := adj_valid c_lt j_lt glued
      -- the partner side is not lengthened either
      have partner_not_hit := move_ok.not_hit_partner c_lt j_lt glued side_hit
      -- and it has the same length
      have same_len := move_ok.pair c c_lt j j_lt c' j' glued
      simp only [Option.map_some]
      rw [unchanged c' j' partner_not_hit,
        show pos (L c') j' + L c' j' - 1 - o = pos (L c') j' + (L c' j' - 1 - o) by omega,
        move_ok.sh_side c'_lt j'_lt (by omega) partner_not_hit]
      congr 2; omega

/-- **Lengthening is subdividing**: the composition with the lengthened sides is equivalent to the old one with the
edge cut. -/
theorem equiv : Gluing.Equiv (G₁) (Gs) where
  n := by rw [ofLens_n]; show nk T = (Comp.ofLens T L d ω).toGluing.n; rw [ofLens_n]
  E c c_lt := move_ok.E_eq (by rwa [ofLens_n] at c_lt)
  A c c_lt := move_ok.A_eq (by rwa [ofLens_n] at c_lt)
  B c c_lt := move_ok.B_eq (by rwa [ofLens_n] at c_lt)
  mate c k c_lt k_lt := move_ok.mate_eq (by rwa [ofLens_n] at c_lt) k_lt

end OK

end Move

end SpectreKnot.Compose

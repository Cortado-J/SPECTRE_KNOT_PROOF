/-
**"A composition has the signature"**, as the paper's §7.1 words it, and Computation 7.3 in that form.

The composition `Comp.ofLens T L d ω` has Table 3's rim: its rim vertex at position `p` (in the parent's own order)
lies between the children's edges at positions `p - 1` and `p` (`ownGo`), with the ports `gR p` and `gL p`. The Γ
child's corners `A` and `B` are the rim vertices at the adjacent positions `cA` and `cB` (`corners_at`). `CompSig`
says that the composition has the signature: no closed strand, a hook at every other rim vertex, and the crossover at
`A` and `B`.

The kernel's check of Computation 7.3 (`Comp.check`) gives `Sig`, the form in which the proof of Lemma 7.1 carries the
signature through cuts (`sig_of_check`); and `Sig` gives `CompSig` (`compSig_of_sig`). So Computation 7.3 holds as the
paper words it (`Compose.comp_7_3`), and so, after the induction, does Prop 7.4 (`Compose.prop_7_4`, `Parity.lean`).
-/
import SpectreKnot.ParentRim
import SpectreKnot.Reverse

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- Stepping back one position round a rim of length `N` is one to one. -/
theorem prv_inj {N p p' : Nat} (p_lt : p < N) (p_lt' : p' < N) (same : prv N p = prv N p') : p = p' := by
  unfold prv at same; split at same <;> split at same <;> omega

/-! ### The corners of a composition -/

/-- The last child is the Γ child. -/
theorem kid_last : ∀ T : Kind, kidAt T (nk T - 1) = .Gamma := by intro T; cases T <;> rfl

/-- Every kind has a child. -/
theorem last_lt : ∀ T : Kind, 0 < nk T := by intro T; cases T <;> decide

/-- For every kind but Σ, the parent's rim begins with side 5 of the Γ child and ends with its side 0. -/
theorem pcs_nonSigma : ∀ T : Kind, T ≠ .Sigma →
    pcs T = (nk T - 1, 5) :: ((pcs T).drop 1).dropLast ++ [(nk T - 1, 0)] := by
  intro T not_sigma; cases T <;> first | exact absurd rfl not_sigma | decide

/-- The pieces of the Σ-supertile's rim before its crossover corner. -/
def preS : List (Nat × Nat) :=
  [(6, 3), (6, 2), (5, 4), (5, 3), (5, 2), (5, 1), (4, 2), (3, 4), (3, 3), (3, 2), (2, 4), (2, 3), (2, 2), (2, 1),
    (1, 2), (0, 4), (0, 3), (0, 2), (0, 1)]

/-- The Σ-supertile's rim: `preS`, then sides 0 and 5 of the Γ child (child 7), then side 4 of child 6. -/
theorem pcs_sigma : pcs .Sigma = preS ++ [(7, 0), (7, 5), (6, 4)] := by decide

/-- `preS` is the pieces of the Σ-supertile's sides 0–4, then the first two pieces of its side 5. -/
theorem preS_eq : preS = ((pside .Sigma).take 5).flatMap id ++ [(0, 2), (0, 1)] := by decide

section Corners

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- The Γ child's corner `A` is its vertex 0. -/
theorem gA_last (last_lt' : nk T - 1 < nk T) : (Comp.ofLens T L d ω).toGluing.A (nk T - 1) = 0 := by
  rw [ofLens_A last_lt', ite_eq_right (by rw [kid_last]; decide)]

/-- With positive side lengths, a child's rim has at least two edges, and ends after its side 5. -/
theorem pos6 (len_pos : ∀ c j, 1 ≤ L c j) (c : Nat) : 2 ≤ pos (L c) 6 ∧ pos (L c) 6 = pos (L c) 5 + L c 5 := by
  -- sides 0 … 4 come before vertex 5
  have before_5 := pos_lt_of_pos (L c) (fun i _ => len_pos c i) (show 0 < 5 by omega) (by omega)
  -- side 5 has an edge
  have len_5 := len_pos c 5
  -- the rim ends after side 5
  have pos_6 : pos (L c) 6 = pos (L c) 5 + L c 5 := pos_succ _ 5
  -- the rim starts at vertex 0
  have pos_0 : pos (L c) 0 = 0 := rfl
  -- side 0 has an edge
  have len_0 := len_pos c 0
  exact ⟨by omega, pos_6⟩

/-- The Γ child's corner `B` is its vertex 1 if `ω`, and its last rim vertex otherwise. -/
theorem gB_last (len_pos : ∀ c j, 1 ≤ L c j) (last_lt' : nk T - 1 < nk T) :
    (Comp.ofLens T L d ω).toGluing.B (nk T - 1) =
      if ω then 1 else pos (L (nk T - 1)) 6 - 1 := by
  -- the Γ child's rim has at least two edges
  have rim_ge_two := (pos6 len_pos (nk T - 1)).1
  rw [ofLens_B last_lt', gA_last last_lt']
  cases ω with
  | true => simp only [ite_true, nxt]; rw [ite_eq_right (by omega)]
  | false => rfl

/-- The corners of a non-Σ parent: `A` at its vertex 0, `B` next to it. -/
theorem corners_nonSigma (not_sigma : T ≠ .Sigma) (len_pos : ∀ c j, 1 ≤ L c j)
    (side0_ge_two : 2 ≤ L (nk T - 1) 0) :
    0 < rimN T L ∧ (if !ω then nxt (rimN T L) 0 else prv (rimN T L) 0) < rimN T L ∧
    0 ≠ (if !ω then nxt (rimN T L) 0 else prv (rimN T L) 0) ∧
    ownGo L (pcs T) (prv (rimN T L) 0) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.A (nk T - 1)) ∧
    ownGo L (pcs T) (prv (rimN T L) (if !ω then nxt (rimN T L) 0 else prv (rimN T L) 0)) =
      (nk T - 1, (Comp.ofLens T L d ω).toGluing.B (nk T - 1)) := by
  -- the Γ child is an actual child
  have last_lt' : nk T - 1 < nk T := by
    -- every kind has a child
    have := last_lt T
    omega
  -- the parent's rim begins with the Γ child's side 5 and ends with its side 0
  have pcs_shape := pcs_nonSigma T not_sigma
  generalize ((pcs T).drop 1).dropLast = mid at pcs_shape
  -- the last rim position is the Γ child's edge 0
  have at_last : ownGo L (pcs T) (rimN T L - 1) = (nk T - 1, 0) := by
    -- the last position of a list ending with side 0 of the Γ child
    have last := ownGo_last (L := L) (c := nk T - 1) (j := 0) (len_pos _ 0) ((nk T - 1, 5) :: mid)
    rw [← pcs_shape] at last
    exact last
  -- the first rim position is the Γ child's last edge
  have at_zero : ownGo L (pcs T) 0 = (nk T - 1, pos (L (nk T - 1)) 6 - 1) := by
    rw [pcs_shape, List.cons_append, ownGo_zero (len_pos _ 5), (pos6 len_pos _).2]
  -- the rim length, with the last piece split off
  have total : rimN T L = totL L ((nk T - 1, 5) :: mid) + L (nk T - 1) 0 := by
    show totL L (pcs T) = _
    rw [pcs_shape, totL_append]; simp only [totL]; omega
  -- the second-last rim position is the Γ child's edge 1
  have at_last2 : ownGo L (pcs T) (rimN T L - 2) = (nk T - 1, 1) := by
    rw [total, pcs_shape, ownGo_append, ite_eq_right (by omega), show totL L ((nk T - 1, 5) :: mid) + L (nk T - 1) 0 -
      2 - totL L ((nk T - 1, 5) :: mid) = L (nk T - 1) 0 - 2 by omega]
    simp only [ownGo]
    rw [ite_eq_left (by omega)]
    simp only [pos]
    congr 1; omega
  -- the rim has at least two edges
  have rim_ge_two : 2 ≤ rimN T L := by
    rw [total]; simp only [totL]
    -- the Γ child's side 5 has an edge
    have := len_pos (nk T - 1) 5
    omega
  rw [gA_last last_lt', gB_last len_pos last_lt']
  -- the step back from 0 wraps round to the last position
  have prv_zero : prv (rimN T L) 0 = rimN T L - 1 := by simp [prv]
  cases ω with
  | true =>
    -- two steps back from 0
    have prv_prv : prv (rimN T L) (prv (rimN T L) 0) = rimN T L - 2 := by
      rw [prv_zero]; simp only [prv]; rw [ite_eq_right (show ¬ (rimN T L - 1 = 0) by omega)]; omega
    simp only [Bool.not_true, ite_false, Bool.false_eq_true, ite_true]
    refine ⟨by omega, prv_lt (by omega), by rw [prv_zero]; omega, by rw [prv_zero, at_last], ?_⟩
    rw [prv_prv, at_last2]
  | false =>
    -- one step forwards from 0
    have nxt_zero : nxt (rimN T L) 0 = 1 := by simp only [nxt]; rw [ite_eq_right (show ¬ (0 + 1 = rimN T L) by omega)]
    -- and back again
    have prv_nxt_zero : prv (rimN T L) (nxt (rimN T L) 0) = 0 := by rw [nxt_zero]; rfl
    simp only [Bool.not_false, ite_true, ite_false, Bool.false_eq_true]
    refine ⟨by omega, by rw [nxt_zero]; omega, by rw [nxt_zero]; omega, by rw [prv_zero, at_last], ?_⟩
    rw [prv_nxt_zero, at_zero]

/-- The corners of a Σ parent: `A` on side 5, after the pieces `preS` and the Γ child's side 0. -/
theorem corners_sigma (len_pos : ∀ c j, 1 ≤ L c j) (side0_ge_two : 2 ≤ L 7 0) :
    totL L preS + L 7 0 < rimN .Sigma L ∧
    (if !ω then nxt (rimN .Sigma L) (totL L preS + L 7 0) else prv (rimN .Sigma L) (totL L preS + L 7 0)) <
      rimN .Sigma L ∧
    totL L preS + L 7 0 ≠
      (if !ω then nxt (rimN .Sigma L) (totL L preS + L 7 0) else prv (rimN .Sigma L) (totL L preS + L 7 0)) ∧
    ownGo L (pcs .Sigma) (prv (rimN .Sigma L) (totL L preS + L 7 0)) =
      (7, (Comp.ofLens .Sigma L d ω).toGluing.A 7) ∧
    ownGo L (pcs .Sigma) (prv (rimN .Sigma L)
      (if !ω then nxt (rimN .Sigma L) (totL L preS + L 7 0) else prv (rimN .Sigma L) (totL L preS + L 7 0))) =
      (7, (Comp.ofLens .Sigma L d ω).toGluing.B 7) := by
  -- the Γ child, child 7, is an actual child
  have last_lt' : nk .Sigma - 1 < nk .Sigma := by decide
  -- its corner `A` is its vertex 0
  have A_zero : (Comp.ofLens .Sigma L d ω).toGluing.A 7 = 0 := gA_last last_lt'
  -- and its corner `B` is vertex 1 or its last vertex
  have B_eq : (Comp.ofLens .Sigma L d ω).toGluing.B 7 = if ω then 1 else pos (L 7) 6 - 1 := gB_last len_pos last_lt'
  -- the rim length, piece by piece
  have total : rimN .Sigma L = totL L preS + L 7 0 + L 7 5 + L 6 4 := by
    show totL L (pcs .Sigma) = _
    rw [pcs_sigma, totL_append]; simp only [totL]; omega
  -- past `preS`, the rim is the last three pieces
  have after_preS : ∀ q, ownGo L (pcs .Sigma) (totL L preS + q) = ownGo L [(7, 0), (7, 5), (6, 4)] q := by
    intro q
    rw [pcs_sigma, ownGo_append, ite_eq_right (show ¬ (totL L preS + q < totL L preS) by omega),
      Nat.add_sub_cancel_left]
  -- the Γ child's rim starts at vertex 0
  have pos_zero : pos (L 7) 0 = 0 := rfl
  -- the last position in the Γ child's side 0 is its edge 0
  have at_edge0 : ownGo L (pcs .Sigma) (totL L preS + (L 7 0 - 1)) = (7, 0) := by
    rw [after_preS]; simp only [ownGo]; rw [ite_eq_left (show L 7 0 - 1 < L 7 0 by omega), pos_zero,
      show 0 + L 7 0 - 1 - (L 7 0 - 1) = 0 by omega]
  -- the one before it is its edge 1
  have at_edge1 : ownGo L (pcs .Sigma) (totL L preS + (L 7 0 - 2)) = (7, 1) := by
    rw [after_preS]; simp only [ownGo]; rw [ite_eq_left (show L 7 0 - 2 < L 7 0 by omega), pos_zero,
      show 0 + L 7 0 - 1 - (L 7 0 - 2) = 1 by omega]
  -- the next position, the first of the piece `(7, 5)`, is the Γ child's last edge
  have at_last : ownGo L (pcs .Sigma) (totL L preS + L 7 0) = (7, pos (L 7) 6 - 1) := by
    rw [after_preS]; simp only [ownGo]
    rw [ite_eq_right (show ¬ (L 7 0 < L 7 0) by omega), Nat.sub_self, ite_eq_left (show 0 < L 7 5 from len_pos 7 5),
      (pos6 len_pos 7).2, Nat.sub_zero]
  -- the Γ child's side 5 has an edge
  have len_75 := len_pos 7 5
  -- and so does child 6's side 4
  have len_64 := len_pos 6 4
  -- the step back from the corner position
  have prv_corner : prv (rimN .Sigma L) (totL L preS + L 7 0) = totL L preS + (L 7 0 - 1) := by
    simp only [prv]; rw [ite_eq_right (show ¬ (totL L preS + L 7 0 = 0) by omega)]; omega
  rw [A_zero, B_eq]
  cases ω with
  | true =>
    -- two steps back
    have prv_prv : prv (rimN .Sigma L) (totL L preS + (L 7 0 - 1)) = totL L preS + (L 7 0 - 2) := by
      simp only [prv]; rw [ite_eq_right (show ¬ (totL L preS + (L 7 0 - 1) = 0) by omega)]; omega
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by rw [prv_corner]; omega, by rw [prv_corner]; omega, by rw [prv_corner, at_edge0], ?_⟩
    rw [prv_corner, prv_prv, at_edge1]
  | false =>
    -- one step forwards from the corner position
    have nxt_corner : nxt (rimN .Sigma L) (totL L preS + L 7 0) = totL L preS + L 7 0 + 1 := by
      simp only [nxt]; rw [ite_eq_right (show ¬ (totL L preS + L 7 0 + 1 = rimN .Sigma L) by omega)]
    -- and back again
    have prv_nxt_corner : prv (rimN .Sigma L) (totL L preS + L 7 0 + 1) = totL L preS + L 7 0 := by
      simp only [prv]; rw [ite_eq_right (show ¬ (totL L preS + L 7 0 + 1 = 0) by omega)]; omega
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by rw [nxt_corner]; omega, by rw [nxt_corner]; omega, by rw [prv_corner, at_edge0], ?_⟩
    rw [nxt_corner, prv_nxt_corner, at_last]

end Corners

/-! ### The rim vertices of a composition -/

/-- The gluing's port at the parent's port `R(p)` (in the parent's orientation): the end of the child edge at rim
position `p`, in the children's sense. -/
def gR (T : Kind) (L : Nat → Nat → Nat) (d : Nat) (ω : Bool) (p : Nat) : GPort :=
  ((ownGo L (pcs T) p).1, nxt ((Comp.ofLens T L d ω).toGluing.E (ownGo L (pcs T) p).1) (ownGo L (pcs T) p).2, false)

/-- The gluing's port at the parent's port `L(p)`: the start of the child edge at rim position `p - 1`. -/
def gL (T : Kind) (L : Nat → Nat → Nat) (p : Nat) : GPort :=
  ((ownGo L (pcs T) (prv (rimN T L) p)).1, (ownGo L (pcs T) (prv (rimN T L) p)).2, true)

section Ports

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- The vertex of `gR p` is a parent rim vertex reached along the rim: the edge before it is unglued. -/
theorem gR_rimL (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.RimL (gR T L d ω p).1 (gR T L d ω p).2.1 := by
  obtain ⟨c_lt, k_lt, unglued⟩ := own_mate (d := d) (ω := ω) len_pos p_lt
  -- the edge is on the child's rim, in the composition's terms
  have k_lt' : (ownGo L (pcs T) p).2 < (Comp.ofLens T L d ω).toGluing.E (ownGo L (pcs T) p).1 := by
    rw [ofLens_E c_lt]; exact k_lt
  exact ⟨by rw [ofLens_n]; exact c_lt, nxt_lt k_lt', by simp only [gR]; rw [prv_nxt k_lt']; exact unglued⟩

/-- Turning about the vertex of `gR p` reaches the start of the child edge at position `p - 1`, the vertex of
`gL p`. -/
theorem gR_rot (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.Rot ((gR T L d ω p).1, (gR T L d ω p).2.1) (ownGo L (pcs T) (prv (rimN T L) p)) :=
  own_rot len_pos p_lt

/-- `gR p` is a port of an actual child, at an actual rim vertex. -/
theorem gR_valid (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.Valid (gR T L d ω p) :=
  ⟨(gR_rimL len_pos p_lt).1, (gR_rimL len_pos p_lt).2.1⟩

/-- `gL p` is a port of an actual child, at an actual rim vertex. -/
theorem gL_valid (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.Valid (gL T L p) := by
  obtain ⟨c_lt, k_lt, _⟩ := own_mate (d := d) (ω := ω) len_pos (prv_lt p_lt)
  refine ⟨?_, ?_⟩ <;> simp only [gL]
  · rw [ofLens_n]; exact c_lt
  · rw [ofLens_E c_lt]; exact k_lt

/-- `gR p` is on the parent's rim: nothing lies across it. -/
theorem gR_sigma (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.sigma (gR T L d ω p) = none := by
  -- the edge before the vertex is unglued
  have unglued := (gR_rimL (d := d) (ω := ω) len_pos p_lt).2.2
  simp only [gR, Gluing.sigma] at unglued ⊢
  rw [unglued]; rfl

/-- `gL p` is on the parent's rim: nothing lies across it. -/
theorem gL_sigma (len_pos : ∀ c j, 1 ≤ L c j) {p : Nat} (p_lt : p < rimN T L) :
    (Comp.ofLens T L d ω).toGluing.sigma (gL T L p) = none := by
  obtain ⟨_, _, unglued⟩ := own_mate (d := d) (ω := ω) len_pos (prv_lt p_lt)
  simp only [gL, Gluing.sigma]
  rw [unglued]; rfl

end Ports

/-! ### The corners of the composition, as rim positions -/

/-- The parent rim position of the Γ child's corner `A`: position 0, or for a Σ parent the position after the pieces
`preS` and the Γ child's side 0 (Table 3). -/
def cA (T : Kind) (L : Nat → Nat → Nat) : Nat := if T = .Sigma then totL L preS + L 7 0 else 0

/-- The parent rim position of the Γ child's corner `B`, next to `cA`: before it in the parent's own order if `ω`
(that is, after it in the children's order), after it otherwise. -/
def cB (T : Kind) (L : Nat → Nat → Nat) (ω : Bool) : Nat :=
  if !ω then nxt (rimN T L) (cA T L) else prv (rimN T L) (cA T L)

section CornersAt

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- **The Γ child's corners are adjacent rim vertices of the composition**, at the positions `cA` and `cB`: the
child edge before position `cA` starts at `A`, the one before `cB` at `B`. -/
theorem corners_at (len_pos : ∀ c j, 1 ≤ L c j) (side0_ge_two : 2 ≤ L (nk T - 1) 0) :
    cA T L < rimN T L ∧ cB T L ω < rimN T L ∧ cA T L ≠ cB T L ω ∧
    ownGo L (pcs T) (prv (rimN T L) (cA T L)) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.A (nk T - 1)) ∧
    ownGo L (pcs T) (prv (rimN T L) (cB T L ω)) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.B (nk T - 1)) := by
  by_cases is_sigma : T = .Sigma
  · subst is_sigma
    -- a Σ parent: `A` on its side 5
    exact corners_sigma len_pos side0_ge_two
  · -- any other parent: `A` at its vertex 0
    simp only [cA, cB, ite_eq_right is_sigma]
    exact corners_nonSigma is_sigma len_pos side0_ge_two

end CornersAt

/-! ### "Has the signature" -/

/-- **The composition `C_T(L, d, ω)` has the signature**, as §7.1 words it: it is well formed; it has no closed strand;
the Γ child's corners `A` and `B` are its rim vertices at the adjacent positions `cA` and `cB` of Table 3's rim; every
other rim vertex `p` is a hook, its port `gR p` joined to its port `gL p`; and `A` and `B` carry the crossover,
`R(A) ↔ R(B)` and `L(A) ↔ L(B)`. -/
structure CompSig (T : Kind) (L : Nat → Nat → Nat) (d : Nat) (ω : Bool) : Prop where
  wf : (Comp.ofLens T L d ω).toGluing.WF
  noLoops : ∀ x, (Comp.ofLens T L d ω).toGluing.Valid x → ∃ r, (Comp.ofLens T L d ω).toGluing.FullReach x r
  cA_lt : cA T L < rimN T L
  cB_lt : cB T L ω < rimN T L
  at_A : gL T L (cA T L) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.A (nk T - 1), true)
  at_B : gL T L (cB T L ω) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.B (nk T - 1), true)
  hooks : ∀ p, p < rimN T L → p ≠ cA T L → p ≠ cB T L ω →
    (Comp.ofLens T L d ω).toGluing.FullReach (gR T L d ω p) (gL T L p)
  crossR : (Comp.ofLens T L d ω).toGluing.FullReach (gL T L (cA T L)) (gL T L (cB T L ω))
  crossL : (Comp.ofLens T L d ω).toGluing.FullReach (gR T L d ω (cA T L)) (gR T L d ω (cB T L ω))

section FromSig

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- **`Sig` gives "has the signature"**: the turning form that the proof of Lemma 7.1 carries through cuts, read at
Table 3's rim positions. A rim vertex found by turning is the one at a position (`own_rot`); it is a corner only at
`cA` or `cB`, since different positions are different edges (`own_inj`); and the crossover walks start at the ports
`gR` of the corners, since turning about a vertex is one to one on rim vertices (`Rot.inj`). -/
theorem compSig_of_sig (len_pos : ∀ c j, 1 ≤ L c j) (side0_ge_two : 2 ≤ L (nk T - 1) 0)
    (has_sig : Sig (Comp.ofLens T L d ω).toGluing (nk T - 1)) : CompSig T L d ω := by
  obtain ⟨pA_lt, pB_lt, _, at_A, at_B⟩ := corners_at (d := d) (ω := ω) len_pos side0_ge_two
  -- the composition is well formed
  have wf := has_sig.wf
  -- turning about the vertex of `gR cA` reaches the Γ child's corner `A`
  have rot_A := gR_rot (d := d) (ω := ω) len_pos pA_lt
  rw [at_A] at rot_A
  -- and about that of `gR cB`, its corner `B`
  have rot_B := gR_rot (d := d) (ω := ω) len_pos pB_lt
  rw [at_B] at rot_B
  -- `gL cA` is the port `R` at the Γ child's corner `A`
  have gL_A : gL T L (cA T L) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.A (nk T - 1), true) := by
    simp only [gL, at_A]
  -- `gL cB` is the port `R` at its corner `B`
  have gL_B : gL T L (cB T L ω) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.B (nk T - 1), true) := by
    simp only [gL, at_B]
  refine ⟨wf, has_sig.noLoops, pA_lt, pB_lt, gL_A, gL_B, fun p p_lt ne_A ne_B => ?_, ?_, ?_⟩
  · -- a hook: turning about the vertex of `gR p` reaches that of `gL p`
    obtain ⟨c₂, u₂, turn, corner_or_hook⟩ := has_sig.hooks _ _ (gR_rimL len_pos p_lt)
    -- the vertex turned to is the start of the child edge at position `p - 1`
    have same_vtx := Rot.unique turn (gR_rot len_pos p_lt)
    -- it is not one of the Γ child's corners, since `p` is neither `cA` nor `cB`
    have not_corner : ¬ (c₂ = nk T - 1 ∧ (u₂ = (Comp.ofLens T L d ω).toGluing.A (nk T - 1) ∨
        u₂ = (Comp.ofLens T L d ω).toGluing.B (nk T - 1))) := by
      rintro ⟨rfl, at_cA | at_cB⟩
      · rw [at_cA, ← at_A] at same_vtx
        exact ne_A (prv_inj p_lt pA_lt (own_inj len_pos (prv_lt pA_lt) (prv_lt p_lt) same_vtx).symm)
      · rw [at_cB, ← at_B] at same_vtx
        exact ne_B (prv_inj p_lt pB_lt (own_inj len_pos (prv_lt pB_lt) (prv_lt p_lt) same_vtx).symm)
    rcases corner_or_hook with corner | hook
    · exact absurd corner not_corner
    · have gL_eq : gL T L p = (c₂, u₂, true) := by simp only [gL, ← same_vtx] -- `R` at the vertex turned to
      rw [gL_eq]; exact hook
  · -- `R(A) ↔ R(B)`: the crossover of `Sig`
    rw [gL_A, gL_B]; exact has_sig.crossR
  · -- `L(A) ↔ L(B)`: the vertices that turn to `A` and `B` are those of `gR cA` and `gR cB`
    obtain ⟨cA', uA', cB', uB', rim_A, turn_A, rim_B, turn_B, reach⟩ := has_sig.crossL
    -- the vertex turning to `A` is that of `gR cA`
    have vtx_A := Rot.inj wf rim_A (gR_rimL len_pos pA_lt) turn_A rot_A
    -- the vertex turning to `B` is that of `gR cB`
    have vtx_B := Rot.inj wf rim_B (gR_rimL len_pos pB_lt) turn_B rot_B
    -- so `gR cA` is the start of the crossover walk
    have gR_A : gR T L d ω (cA T L) = (cA', uA', false) := by
      rw [Prod.ext_iff] at vtx_A; exact Prod.ext vtx_A.1.symm (Prod.ext vtx_A.2.symm rfl)
    -- and `gR cB` its end
    have gR_B : gR T L d ω (cB T L ω) = (cB', uB', false) := by
      rw [Prod.ext_iff] at vtx_B; exact Prod.ext vtx_B.1.symm (Prod.ext vtx_B.2.symm rfl)
    rw [gR_A, gR_B]; exact reach

end FromSig

/-! ### Table 3's rim as `Comp.check` lists it -/

section CheckRim

/-- Table 3's rim as a list, in the parent's own order: the edges of each listed side, from its last edge to its
first (as `ownGo` reads them). -/
def ownList (L : Nat → Nat → Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.flatMap fun x => (List.range (L x.1 x.2)).map fun i => (x.1, pos (L x.1) x.2 + L x.1 x.2 - 1 - i)

/-- The list has the total length of its pieces. -/
theorem ownList_length (L : Nat → Nat → Nat) : ∀ l, (ownList L l).length = totL L l
  | [] => rfl
  | (c, j) :: rest => by
    simp only [ownList, List.flatMap_cons, List.length_append, List.length_map, List.length_range, totL]
    rw [← ownList_length L rest]; rfl

/-- Entry `p` of the list is the edge `ownGo` finds at position `p`. -/
theorem ownList_getElem? (L : Nat → Nat → Nat) : ∀ l p, p < totL L l → (ownList L l)[p]? = some (ownGo L l p)
  | [], p, p_lt => by simp [totL] at p_lt
  | (c, j) :: rest, p, p_lt => by
    simp only [totL] at p_lt
    simp only [ownList, List.flatMap_cons]
    by_cases in_head : p < L c j
    · -- in the first piece
      rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact in_head),
        List.getElem?_map, List.getElem?_range in_head]
      simp only [ownGo, ite_eq_left in_head, Option.map_some]
    · -- in a later piece: by induction
      rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range]
      rw [show (rest.flatMap fun x => (List.range (L x.1 x.2)).map fun i => (x.1, pos (L x.1) x.2 + L x.1 x.2 - 1 - i))
          = ownList L rest from rfl, ownList_getElem? L rest (p - L c j) (by omega)]
      simp only [ownGo, ite_eq_right in_head]

/-- Two functions that agree on a list give the same `flatMap` over it. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: rest, agree => by
    rw [List.flatMap_cons, List.flatMap_cons, agree x List.mem_cons_self,
      flatMap_congr_mem rest (fun y mem => agree y (List.mem_cons_of_mem _ mem))]

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- `Comp.check` lists Table 3's rim (`rimEdges`, in the children's sense) as `ownList` backwards. -/
theorem rimEdges_eq : (Comp.ofLens T L d ω).rimEdges = (ownList L (pcs T)).reverse := by
  show (((pside T).flatMap id).flatMap fun (x : Nat × Nat) =>
    (List.range (((Comp.ofLens T L d ω).kid x.1).len.getD x.2 0)).map fun i =>
      (x.1, ((Comp.ofLens T L d ω).kid x.1).U.getD x.2 0 + ((Comp.ofLens T L d ω).kid x.1).len.getD x.2 0 - 1 -
        i)).reverse = _
  congr 1
  apply flatMap_congr_mem
  intro x mem
  -- the piece is a side of an actual child
  obtain ⟨c_lt, j_lt, _⟩ := pcs_valid T x mem
  rw [ofLens_len c_lt j_lt, ofLens_U c_lt (by omega)]

/-- The rim that `Comp.check` reads has `rimN T L` vertices. -/
theorem rimVertexPorts_length : (Comp.ofLens T L d ω).rimVertexPorts.length = rimN T L := by
  simp only [Comp.rimVertexPorts, List.length_map, List.length_range, rimEdges_eq, List.length_reverse,
    ownList_length]

/-- **The rim vertex that `Comp.check` numbers `t` is the one at position `N - 1 - t`** (the check counts in the
children's sense, positions in the parent's own order): its ports are `gR` and `gL` there. -/
theorem vtx_eq {t : Nat} (t_lt : t < rimN T L) :
    (Comp.ofLens T L d ω).vtx t = (gR T L d ω (rimN T L - 1 - t), gL T L (rimN T L - 1 - t)) := by
  -- entry `t` of the rim list, read backwards
  have entry : ∀ s, s < rimN T L →
      (Comp.ofLens T L d ω).rimEdges.getD s (0, 0) = ownGo L (pcs T) (rimN T L - 1 - s) := by
    intro s s_lt
    rw [List.getD_eq_getElem?_getD, rimEdges_eq, List.getElem?_reverse (by rw [ownList_length]; exact s_lt),
      ownList_length, ownList_getElem? L _ _ (by show rimN T L - 1 - s < rimN T L; omega)]
    rfl
  -- the next entry, cyclically, is the edge at the position before
  have next : (Comp.ofLens T L d ω).rimEdges.getD ((t + 1) % rimN T L) (0, 0) =
      ownGo L (pcs T) (prv (rimN T L) (rimN T L - 1 - t)) := by
    rw [entry _ (Nat.mod_lt _ (by omega))]
    congr 1
    simp only [prv]
    by_cases at_end : t + 1 = rimN T L
    · rw [at_end, Nat.mod_self, ite_eq_left (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega)]; omega
  simp only [Comp.vtx, Comp.rimVertexPorts]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by
    rw [rimEdges_eq, List.length_reverse, ownList_length]; exact t_lt)]
  simp only [Option.map_some, Option.getD_some]
  rw [show (Comp.ofLens T L d ω).rimEdges.length = rimN T L by rw [rimEdges_eq, List.length_reverse, ownList_length],
    entry t t_lt, next]
  rfl

end CheckRim

/-! ### `Comp.check` gives `Sig` -/

section FromCheck

variable {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool}

/-- The composition has the kind's children. -/
theorem ofLens_kids_length : (Comp.ofLens T L d ω).kids.length = nk T := by
  simp [Comp.ofLens]

/-- What `Comp.check`'s search for a corner found: if the index it returns is a rim vertex, that vertex's port `R` is
the one searched for. -/
theorem found_corner {C : Comp} {u t : Nat}
    (t_eq : t = (C.rimVertexPorts.findIdx? fun (x : GPort × GPort) => x.2 == (C.kids.length - 1, u, true)).getD
      C.rimVertexPorts.length)
    (t_lt : t < C.rimVertexPorts.length) : (C.vtx t).2 = (C.kids.length - 1, u, true) := by
  cases found : C.rimVertexPorts.findIdx? (fun (x : GPort × GPort) => x.2 == (C.kids.length - 1, u, true)) with
  | none => rw [found, Option.getD_none] at t_eq; omega
  | some i =>
    rw [found, Option.getD_some] at t_eq
    subst t_eq
    obtain ⟨i_lt, pred_i, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    simp only [Comp.vtx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i_lt, Option.getD_some]
    simpa using pred_i

/-- **Computation 7.3's check gives `Sig`**, the form in which the proof of Lemma 7.1 carries the signature through
cuts: every rim vertex found by turning about a child's vertex is the check's rim vertex at some position
(`own_surj`, `own_rot`, `vtx_eq`), so the check's hooks, corners and crossover are `Sig`'s. -/
theorem sig_of_check (len_pos : ∀ c j, 1 ≤ L c j) (checked : (Comp.ofLens T L d ω).check ω = true) :
    Sig (Comp.ofLens T L d ω).toGluing (nk T - 1) := by
  obtain ⟨wf, no_loops, hooks, tA_lt, tB_lt, _, cross_R, cross_L⟩ := Comp.check_sound _ checked
  -- what the searches for the corners found, at the check's indices `tA` and `tB`
  have found_A := found_corner (C := Comp.ofLens T L d ω) (t := (Comp.ofLens T L d ω).tA) rfl tA_lt
  -- (and for `B`)
  have found_B := found_corner (C := Comp.ofLens T L d ω) (t := (Comp.ofLens T L d ω).tB) rfl tB_lt
  rw [rimVertexPorts_length] at tA_lt tB_lt hooks
  rw [ofLens_kids_length] at found_A found_B
  -- the check's vertices at `tA` and `tB` are the rim vertices at the positions `N - 1 - tA` and `N - 1 - tB`
  rw [vtx_eq tA_lt] at found_A cross_R cross_L
  rw [vtx_eq tB_lt] at found_B cross_R cross_L
  generalize pA_def : rimN T L - 1 - (Comp.ofLens T L d ω).tA = pA at found_A cross_R cross_L
  generalize pB_def : rimN T L - 1 - (Comp.ofLens T L d ω).tB = pB at found_B cross_R cross_L
  -- the positions are on the rim
  have pA_lt : pA < rimN T L := by omega
  -- (both of them)
  have pB_lt : pB < rimN T L := by omega
  -- the child edge before `pA` starts at the Γ child's corner `A`
  have own_A : ownGo L (pcs T) (prv (rimN T L) pA) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.A (nk T - 1)) := by
    simp only [gL, Prod.mk.injEq] at found_A
    exact Prod.ext found_A.1 found_A.2.1
  -- and the one before `pB` at its corner `B`
  have own_B : ownGo L (pcs T) (prv (rimN T L) pB) = (nk T - 1, (Comp.ofLens T L d ω).toGluing.B (nk T - 1)) := by
    simp only [gL, Prod.mk.injEq] at found_B
    exact Prod.ext found_B.1 found_B.2.1
  refine ⟨wf, no_loops, fun c u rim_L => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- a parent rim vertex: the check's rim vertex at some position `p`
    obtain ⟨c_lt_n, u_lt, unglued⟩ := rim_L
    -- `c` is a child
    have c_lt : c < nk T := by rwa [ofLens_n] at c_lt_n
    -- the edge before `u` is a parent rim edge, at some position `p`
    obtain ⟨p, p_lt, at_p⟩ := own_surj (d := d) (ω := ω) len_pos c_lt
      (by rw [← ofLens_E (d := d) (ω := ω) c_lt]; exact prv_lt u_lt) unglued
    -- `gR p` is the port `L` at `u`
    have gR_eq : gR T L d ω p = (c, u, false) := by
      simp only [gR, at_p]; rw [nxt_prv u_lt]
    -- turning about `u` reaches the start of the child edge at position `p - 1`
    have turn := gR_rot (d := d) (ω := ω) len_pos p_lt
    rw [gR_eq] at turn
    refine ⟨_, _, turn, ?_⟩
    -- the check's index of the vertex at position `p`
    have vtx_t := vtx_eq (d := d) (ω := ω) (show rimN T L - 1 - p < rimN T L by omega)
    rw [show rimN T L - 1 - (rimN T L - 1 - p) = p by omega] at vtx_t
    by_cases is_A : rimN T L - 1 - p = (Comp.ofLens T L d ω).tA
    · -- at the corner `A`
      have p_eq : p = pA := by omega
      subst p_eq
      exact Or.inl ⟨by rw [own_A], Or.inl (by rw [own_A])⟩
    · by_cases is_B : rimN T L - 1 - p = (Comp.ofLens T L d ω).tB
      · -- at the corner `B`
        have p_eq : p = pB := by omega
        subst p_eq
        exact Or.inl ⟨by rw [own_B], Or.inr (by rw [own_B])⟩
      · -- a hook, by the check
        have hook := hooks _ (by omega) is_A is_B
        rw [vtx_t, gR_eq] at hook
        exact Or.inr hook
  · -- the Γ child is a child
    rw [ofLens_n]
    -- every kind has a child
    have := last_lt T
    omega
  · -- the Γ child's edge at `A` is on the parent's rim
    have unglued := (own_mate (d := d) (ω := ω) len_pos (prv_lt pA_lt)).2.2
    rwa [own_A] at unglued
  · -- and so is its edge at `B`
    have unglued := (own_mate (d := d) (ω := ω) len_pos (prv_lt pB_lt)).2.2
    rwa [own_B] at unglued
  · -- `R(A) ↔ R(B)`
    rwa [found_A, found_B] at cross_R
  · -- `L(A) ↔ L(B)`, from the vertices of `gR pA` and `gR pB`
    -- turning about the vertex of `gR pA` reaches `A`
    have rot_A := gR_rot (d := d) (ω := ω) len_pos pA_lt
    rw [own_A] at rot_A
    -- and about that of `gR pB`, `B`
    have rot_B := gR_rot (d := d) (ω := ω) len_pos pB_lt
    rw [own_B] at rot_B
    exact ⟨_, _, _, _, gR_rimL len_pos pA_lt, rot_A, gR_rimL len_pos pB_lt, rot_B, cross_L⟩

end FromCheck

end SpectreKnot.Statement

namespace SpectreKnot.Compose

open Gluing Statement

/-- Every level-1 letter length is positive (each is at least 5). -/
theorem letterLen_one_pos : ∀ x, 1 ≤ letterLen 1 x := by intro x; cases x <;> decide

/-- The Γ child's side 0 has at least two edges at level 1 (it has 7). -/
theorem gamma_side0_one : ∀ T : Kind, 2 ≤ letterLen 1 (letterOf (kidAt T (nk T - 1)) 0) := by
  intro T; cases T <;> decide

/-- **The base case of the induction**: Computation 7.3, the kernel's check (`compositions_level1`), in the form
`Sig` that the proof of Lemma 7.1 carries through cuts. -/
theorem sig_base (T : Kind) (ω : Bool) : Sig (Comp.ofPattern T (letterLen 1) (dOff 1) ω).toGluing (nk T - 1) :=
  sig_of_check (L := fun c j => letterLen 1 (letterOf (kidAt T c) j)) (fun _ _ => letterLen_one_pos _)
    (compositions_level1 T ω)

/-- **Computation 7.3, as the paper words it**: for each of the nine kinds `T` and both signs `ω`, the composition
`C_T(ℓ₁, d₁, ω)` has the signature (`CompSig`). -/
theorem comp_7_3 (T : Kind) (ω : Bool) :
    CompSig T (fun c j => letterLen 1 (letterOf (kidAt T c) j)) (dOff 1) ω :=
  compSig_of_sig (fun _ _ => letterLen_one_pos _) (gamma_side0_one T) (sig_base T ω)

end SpectreKnot.Compose

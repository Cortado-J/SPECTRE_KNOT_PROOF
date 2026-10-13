/-
**Theorem A** (`theoremA`): no supertile of any level or kind contains a closed strand.

The induction of Thm 7.6, at tile level: every level-`m` supertile (`m ≥ 1`) has the signature, with its corners
`A`, `B` at the positions `aPos m K`, `bPos m K` and its vertices where the side lengths ℓ_m put them (`Good m K`).
Level 1 is the kernel's check of the nine clusters (`good_one`). From level `m` to `m + 1`: the children have the
signature, the composition has it by the parity lemma, so the parent has it (`Kids.parent_sig`), with its corners
where Table 3 puts the Γ child's corners (`corners_nonSigma`, `corners_sigma`).
-/
import SpectreKnot.ParentSig

namespace SpectreKnot.Statement

open Pattern Compose Gluing

/-- `pos f J` depends only on the side lengths before `J`. -/
theorem pos_congr {f g : Nat → Nat} : ∀ J, (∀ i, i < J → f i = g i) → pos f J = pos g J
  | 0, _ => rfl
  | J + 1, agree => by rw [pos_succ, pos_succ, pos_congr J (fun i i_lt => agree i (by omega)), agree J (by omega)]

/-- `totL` is the sum of the side lengths of the pieces. -/
theorem totL_eq (L : Nat → Nat → Nat) : ∀ l : List (Nat × Nat), totL L l = (l.map fun p => L p.1 p.2).sum
  | [] => rfl
  | (c, j) :: rest => by simp only [totL, List.map_cons, List.sum_cons, totL_eq L rest]

/-- The side lengths of the children in a composition of level-`m` supertiles. -/
abbrev Lk (m : Nat) (T : Kind) (c j : Nat) : Nat := letterLen m (letterOf (kidAt T c) j)

/-- The parent's sides have the lengths ℓ_{m+1} (Prop 2.4(c) with Prop 6.1). -/
theorem parentLen_eq {m : Nat} (m_pos : 1 ≤ m) (T : Kind) {J : Nat} (J_lt : J < 6) :
    parentLen T (Lk m T) J = lenAt (m + 1) T J := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [lenAt, ← sideLen_eq_letterLen (m' + 2) (by omega) T J J_lt]
  simp only [sideLen, parentLen, totL_eq]
  congr 1
  apply List.map_congr_left
  intro p mem
  rw [sideLen_eq_letterLen (m' + 1) (by omega) _ _ (pieces_valid T J J_lt p mem)]

/-- The parent's vertices sit where the lengths ℓ_{m+1} put them. -/
theorem vpos_eq {m : Nat} (m_pos : 1 ≤ m) (T : Kind) {J : Nat} (J_le : J ≤ 6) :
    vpos (m + 1) T J = pos (parentLen T (Lk m T)) J :=
  pos_congr J (fun i i_lt => (parentLen_eq m_pos T (by omega)).symm)

/-! ### The corners of the parent -/

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
  rw [ofLens_A last_lt', if_neg (by rw [kid_last]; decide)]

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
  | true => simp only [if_true, nxt]; rw [if_neg (by omega)]
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
    rw [total, pcs_shape, ownGo_append, if_neg (by omega), show totL L ((nk T - 1, 5) :: mid) + L (nk T - 1) 0 -
      2 - totL L ((nk T - 1, 5) :: mid) = L (nk T - 1) 0 - 2 by omega]
    simp only [ownGo]
    rw [if_pos (by omega)]
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
      rw [prv_zero]; simp only [prv]; rw [if_neg (show ¬ (rimN T L - 1 = 0) by omega)]; omega
    simp only [Bool.not_true, if_false, Bool.false_eq_true, if_true]
    refine ⟨by omega, prv_lt (by omega), by rw [prv_zero]; omega, by rw [prv_zero, at_last], ?_⟩
    rw [prv_prv, at_last2]
  | false =>
    -- one step forwards from 0
    have nxt_zero : nxt (rimN T L) 0 = 1 := by simp only [nxt]; rw [if_neg (show ¬ (0 + 1 = rimN T L) by omega)]
    -- and back again
    have prv_nxt_zero : prv (rimN T L) (nxt (rimN T L) 0) = 0 := by rw [nxt_zero]; rfl
    simp only [Bool.not_false, if_true, if_false, Bool.false_eq_true]
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
    rw [pcs_sigma, ownGo_append, if_neg (show ¬ (totL L preS + q < totL L preS) by omega), Nat.add_sub_cancel_left]
  -- the Γ child's rim starts at vertex 0
  have pos_zero : pos (L 7) 0 = 0 := rfl
  -- the last position in the Γ child's side 0 is its edge 0
  have at_edge0 : ownGo L (pcs .Sigma) (totL L preS + (L 7 0 - 1)) = (7, 0) := by
    rw [after_preS]; simp only [ownGo]; rw [if_pos (show L 7 0 - 1 < L 7 0 by omega), pos_zero,
      show 0 + L 7 0 - 1 - (L 7 0 - 1) = 0 by omega]
  -- the one before it is its edge 1
  have at_edge1 : ownGo L (pcs .Sigma) (totL L preS + (L 7 0 - 2)) = (7, 1) := by
    rw [after_preS]; simp only [ownGo]; rw [if_pos (show L 7 0 - 2 < L 7 0 by omega), pos_zero,
      show 0 + L 7 0 - 1 - (L 7 0 - 2) = 1 by omega]
  -- the next position, the first of the piece `(7, 5)`, is the Γ child's last edge
  have at_last : ownGo L (pcs .Sigma) (totL L preS + L 7 0) = (7, pos (L 7) 6 - 1) := by
    rw [after_preS]; simp only [ownGo]
    rw [if_neg (show ¬ (L 7 0 < L 7 0) by omega), Nat.sub_self, if_pos (show 0 < L 7 5 from len_pos 7 5),
      (pos6 len_pos 7).2, Nat.sub_zero]
  -- the Γ child's side 5 has an edge
  have len_75 := len_pos 7 5
  -- and so does child 6's side 4
  have len_64 := len_pos 6 4
  -- the step back from the corner position
  have prv_corner : prv (rimN .Sigma L) (totL L preS + L 7 0) = totL L preS + (L 7 0 - 1) := by
    simp only [prv]; rw [if_neg (show ¬ (totL L preS + L 7 0 = 0) by omega)]; omega
  rw [A_zero, B_eq]
  cases ω with
  | true =>
    -- two steps back
    have prv_prv : prv (rimN .Sigma L) (totL L preS + (L 7 0 - 1)) = totL L preS + (L 7 0 - 2) := by
      simp only [prv]; rw [if_neg (show ¬ (totL L preS + (L 7 0 - 1) = 0) by omega)]; omega
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by rw [prv_corner]; omega, by rw [prv_corner]; omega, by rw [prv_corner, at_edge0], ?_⟩
    rw [prv_corner, prv_prv, at_edge1]
  | false =>
    -- one step forwards from the corner position
    have nxt_corner : nxt (rimN .Sigma L) (totL L preS + L 7 0) = totL L preS + L 7 0 + 1 := by
      simp only [nxt]; rw [if_neg (show ¬ (totL L preS + L 7 0 + 1 = rimN .Sigma L) by omega)]
    -- and back again
    have prv_nxt_corner : prv (rimN .Sigma L) (totL L preS + L 7 0 + 1) = totL L preS + L 7 0 := by
      simp only [prv]; rw [if_neg (show ¬ (totL L preS + L 7 0 + 1 = 0) by omega)]; omega
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by rw [nxt_corner]; omega, by rw [nxt_corner]; omega, by rw [prv_corner, at_edge0], ?_⟩
    rw [nxt_corner, prv_nxt_corner, at_last]

end Corners

/-! ### The induction -/

/-- The children of a composition of level-`m` supertiles satisfy the bridge's hypotheses. -/
theorem kids_at {m : Nat} (m_pos : 1 ≤ m) (T : Kind) (good_m : ∀ K, Good m K) :
    Kids T (fun c => super m (kidAt T c)) (Lk m T) (dOff m) (ori m) (ori m) where
  len_pos c j := by
    -- every side is at least 5 long (Lemma 6.5)
    have := (bounds m m_pos).1 (letterOf (kidAt T c) j)
    simp only [Lk]; omega
  pair c c_lt j j_lt c' j' adj_eq := by simp only [Lk, pair_letter c_lt j_lt adj_eq]
  shape c _ := ⟨(good_m (kidAt T c)).vtx, (good_m (kidAt T c)).len⟩
  sig c c_lt := by
    -- the child has the signature at `aPos`, `bPos`
    have has_sig := (good_m (kidAt T c)).sig
    -- which is where the composition puts its corner `A`
    have A_eq : (Comp.ofLens T (Lk m T) (dOff m) (ori m)).toGluing.A c = aPos m (kidAt T c) := by
      rw [ofLens_A c_lt]; rfl
    -- and its corner `B`
    have B_eq : (Comp.ofLens T (Lk m T) (dOff m) (ori m)).toGluing.B c = bPos m (kidAt T c) := by
      rw [ofLens_B c_lt, A_eq]; rfl
    rw [A_eq, B_eq]; exact has_sig
  gsig := parity_lemma m m_pos T (ori m)

/-- The orientation flips from each level to the next. -/
theorem ori_succ (m : Nat) : ori (m + 1) = !ori m := by
  simp only [ori]
  rcases Nat.mod_two_eq_zero_or_one m with even | odd
  · have succ_odd : (m + 1) % 2 = 1 := by omega -- `m` even, so `m + 1` odd
    simp [even, succ_odd]
  · have succ_even : (m + 1) % 2 = 0 := by omega -- `m` odd, so `m + 1` even
    simp [odd, succ_even]

/-- **The induction step**: if every level-`m` supertile has the signature, so does every level-`(m+1)` one. -/
theorem good_succ {m : Nat} (m_pos : 1 ≤ m) (good_m : ∀ K, Good m K) (T : Kind) : Good (m + 1) T := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- the children satisfy the bridge's hypotheses
  have kids := kids_at m_pos T good_m
  -- the parent is the composition of its children
  have super_eq : super (m' + 1 + 1) T = compose T fun c => super (m' + 1) (kidAt T c) := rfl
  -- the children's sides have positive lengths
  have len_pos := kids.len_pos
  -- the Γ child's side 0 has at least two edges
  have side0_ge_two : 2 ≤ Lk (m' + 1) T (nk T - 1) 0 := by
    -- every side is at least 5 long (Lemma 6.5)
    have := (bounds (m' + 1) m_pos).1 (letterOf (kidAt T (nk T - 1)) 0)
    simp only [Lk]; omega
  -- the parent's rim length is where its vertex 6 sits
  have rim_len : rimN T (Lk (m' + 1) T) = vpos (m' + 1 + 1) T 6 := by
    rw [rimN_eq, vpos_eq m_pos T (Nat.le_refl _)]
  -- the parent's vertices sit where the lengths ℓ_{m+1} put them
  have vtx_eq :
      (compose T fun c => super (m' + 1) (kidAt T c)).vtx = (List.range 7).map (vpos (m' + 1 + 1) T) := by
    rw [parent_vtx kids.shape]
    apply List.map_congr_left
    intro J J_mem
    rw [vpos_eq m_pos T (by rw [List.mem_range] at J_mem; omega)]
  -- the parent's rim length
  have len_eq : (compose T fun c => super (m' + 1) (kidAt T c)).E = vpos (m' + 1 + 1) T 6 := by
    rw [compose_E kids.shape, rim_len]
  refine ⟨?_, by rw [super_eq]; exact vtx_eq, by rw [super_eq]; exact len_eq⟩
  rw [super_eq, ori_succ]
  by_cases is_sigma : T = .Sigma
  · -- a Σ parent: `A` on side 5
    subst is_sigma
    obtain ⟨pA_lt, pB_lt, pA_ne_pB, at_A, at_B⟩ :=
      corners_sigma (d := dOff (m' + 1)) (ω := ori (m' + 1)) len_pos side0_ge_two
    -- `aPos` is where `corners_sigma` puts `A`
    have aPos_eq : aPos (m' + 1 + 1) .Sigma = totL (Lk (m' + 1) .Sigma) preS + Lk (m' + 1) .Sigma 7 0 := by
      -- `d_{m+1}` is the length of the first three pieces of side 5
      have dOff_eq :
          dOff (m' + 2) = Lk (m' + 1) .Sigma 0 2 + Lk (m' + 1) .Sigma 0 1 + Lk (m' + 1) .Sigma 7 0 := by
        simp only [dOff, sigma_side5_start.1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Lk]
        rw [sideLen_eq_letterLen _ (by omega) _ 2 (by omega), sideLen_eq_letterLen _ (by omega) _ 1 (by omega),
          sideLen_eq_letterLen _ (by omega) _ 0 (by omega)]
        omega
      simp only [aPos, if_pos rfl]
      rw [vpos_eq m_pos _ (by omega), ← totL_take _ _ 5 (by omega), preS_eq, totL_append, dOff_eq]
      simp [totL]; omega
    -- `bPos` is where `corners_sigma` puts `B`
    have bPos_eq : bPos (m' + 1 + 1) .Sigma = if !ori (m' + 1) then nxt (rimN .Sigma (Lk (m' + 1) .Sigma))
        (totL (Lk (m' + 1) .Sigma) preS + Lk (m' + 1) .Sigma 7 0) else prv (rimN .Sigma (Lk (m' + 1) .Sigma))
        (totL (Lk (m' + 1) .Sigma) preS + Lk (m' + 1) .Sigma 7 0) := by
      simp only [bPos, aPos_eq, rim_len, ori_succ]
    rw [aPos_eq, bPos_eq]
    exact kids.parent_sig pA_lt pB_lt pA_ne_pB at_A at_B
  · -- any other parent: `A` at vertex 0
    obtain ⟨pA_lt, pB_lt, pA_ne_pB, at_A, at_B⟩ :=
      corners_nonSigma (d := dOff (m' + 1)) (ω := ori (m' + 1)) is_sigma len_pos side0_ge_two
    -- `aPos` is vertex 0
    have aPos_eq : aPos (m' + 1 + 1) T = 0 := by simp only [aPos, if_neg is_sigma]
    -- `bPos` is where `corners_nonSigma` puts `B`
    have bPos_eq : bPos (m' + 1 + 1) T = if !ori (m' + 1) then nxt (rimN T (Lk (m' + 1) T)) 0
        else prv (rimN T (Lk (m' + 1) T)) 0 := by
      simp only [bPos, aPos_eq, rim_len, ori_succ]
    rw [aPos_eq, bPos_eq]
    exact kids.parent_sig pA_lt pB_lt pA_ne_pB at_A at_B

/-- **Thm 7.6, at tile level**: every supertile of level `m ≥ 1` has the signature. -/
theorem good : ∀ m K, 1 ≤ m → Good m K := by
  intro m
  induction m with
  | zero => intro K one_le_zero; omega
  | succ m ih =>
    intro K _
    rcases Nat.eq_zero_or_pos m with rfl | m_pos
    · exact good_one K
    · exact good_succ m_pos (fun K' => ih K' m_pos) K

/-- **Theorem A** (as stated in `Statement.lean`): for every level `m` and every kind `K`, the supertile
`super m K` contains no closed strand. -/
theorem theoremA : TheoremA := by
  intro m K
  rcases Nat.eq_zero_or_pos m with rfl | m_pos
  · exact tile_noClosed
  · exact (good m K m_pos).sig.noClosed

/-! ### A negative control -/

/-- A one-tile patch with a made-up gluing (not a real one) that traps a ribbon: edges `e_5` and `e_3` are both glued
to `e_4`. -/
def loopPatch : Patch := ⟨1, fun _ i => if i = 5 ∨ i = 3 then some (0, 4) else none, [], []⟩

/-- **Negative control**: `NoClosedStrand` can fail, so `TheoremA` is not true by definition. In `loopPatch` the ribbon
from `L(v_5)` goes round `v_5` to `R(v_5)`, across `e_5` to `R(v_4)`, round `v_4` to `L(v_4)`, and across `e_3` back to
`L(v_5)`, for ever. -/
theorem loopPatch_closed : ¬ loopPatch.NoClosedStrand := by
  intro no_closed
  obtain ⟨r, follow⟩ := no_closed (0, 5, false) ⟨by decide, by decide⟩
  -- no finite walk starts at `L(v_5)` or `R(v_4)`: each only leads on to the other
  have key : ∀ p r, loopPatch.Follow p r → p ≠ (0, 5, false) ∧ p ≠ (0, 4, true) := by
    intro p r follow_pr
    induction follow_pr with
    | @leave p leaves =>
      constructor <;> rintro rfl <;> simp [loopPatch, Patch.across, pieceEnd] at leaves
    | @next p q r crosses _ ih =>
      constructor <;> rintro rfl
      · have q_eq : q = (0, 4, true) := by -- from `L(v_5)` the walk goes on to `R(v_4)`
          simp [loopPatch, Patch.across, pieceEnd] at crosses; exact crosses.symm
        exact ih.2 q_eq
      · have q_eq : q = (0, 5, false) := by -- from `R(v_4)` the walk goes on to `L(v_5)`
          simp [loopPatch, Patch.across, pieceEnd] at crosses; exact crosses.symm
        exact ih.1 q_eq
  exact (key _ _ follow).1 rfl

end SpectreKnot.Statement

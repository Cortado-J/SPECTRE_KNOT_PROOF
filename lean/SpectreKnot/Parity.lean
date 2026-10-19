/-
**The parity lemma** (the paper's Prop 7.4, by Lemmas 7.1 and 7.2). For every level `m ≥ 1`, every kind and both signs, the composition with the level-`m` lengths
`(ℓ_m, d_m)`, its children carrying the signature, has the signature itself (`parity_lemma`).

Proof. The lengths `ℓ_m` only grow with `m` and keep their parities (Cor 6.3), and so do `d_m` and the rest of the Σ
child's side 5. So `(ℓ_m, d_m)` is reached from `(ℓ₁, d₁)` by *moves*: each adds two edges to a pair of glued sides
(or to one side on the parent's rim), and two to `d` if it adds them before the Σ corner. A move is the same as cutting
one edge into three (`Move.OK.equiv`), and cutting keeps the signature (`Cut.OK.sig`). The base case `(ℓ₁, d₁)` is
the kernel's computation (`sig_base`). The induction runs backwards: from any admissible lengths `(L, d)` other than
`(ℓ₁, d₁)`, undo one move (`back_step`).
-/
import SpectreKnot.Move
import SpectreKnot.SigCheck

namespace SpectreKnot.Compose

open Gluing Pattern

/-! ### Facts from the tables -/

/-- The Σ child of each kind. -/
def sigIdx : Kind → Nat
  | .Gamma => 3
  | _ => 4

/-- `sigIdx T` is a child of kind `T`, and it is the Σ child (checked by `decide`). -/
theorem sigIdx_spec : ∀ T : Kind, sigIdx T < nk T ∧ kidAt T (sigIdx T) = .Sigma := by
  intro T; cases T <;> decide

/-- Each kind has only one Σ child. -/
theorem sigma_unique : ∀ T : Kind, ∀ c, c < nk T → ∀ c', c' < nk T → kidAt T c = .Sigma → kidAt T c' = .Sigma →
    c = c' := by
  intro T; cases T <;> decide

/-- Table 2 glues sides with the same letter. -/
def pairOk (T : Kind) (c j : Nat) : Bool :=
  match adjAt T c j with
  | none => true
  | some (c', j') => letterOf (kidAt T c') j' == letterOf (kidAt T c) j

/-- Table 2 glues sides with the same letter, at every side of every child of every kind (checked by `decide`). -/
theorem pair_ok : ∀ T : Kind, ∀ c, c < nk T → ∀ j, j < 6 → pairOk T c j = true := by
  intro T; cases T <;> decide

/-- Sides glued by Table 2 carry the same letter. -/
theorem pair_letter {T : Kind} {c j c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6)
    (glued : adjAt T c j = some (c', j')) : letterOf (kidAt T c') j' = letterOf (kidAt T c) j := by
  -- the table check at `(c, j)`
  have table := pair_ok T c c_lt j j_lt
  simp only [pairOk, glued, beq_iff_eq] at table
  exact table

/-! ### Sums -/

/-- `tot n f = f 0 + … + f (n-1)`. -/
def tot : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => tot n f + f n

/-- Sums are monotone: if `f ≤ g` term by term, then `tot n f ≤ tot n g`. -/
theorem tot_le {n : Nat} {f g : Nat → Nat} (le_termwise : ∀ i, i < n → f i ≤ g i) : tot n f ≤ tot n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [tot]
    -- the first `n` terms
    have := ih (fun i i_lt => le_termwise i (by omega))
    -- the last term
    have := le_termwise n (by omega)
    omega

/-- If `f ≤ g` term by term, and strictly at one term, then `tot n f < tot n g`. -/
theorem tot_lt {n : Nat} {f g : Nat → Nat} (le_termwise : ∀ i, i < n → f i ≤ g i) {i : Nat} (i_lt : i < n)
    (lt_at_i : f i < g i) : tot n f < tot n g := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [tot]
    by_cases is_last : i = n
    · subst is_last
      -- the terms before the strict one
      have := tot_le (n := i) (fun k k_lt => le_termwise k (by omega))
      omega
    -- the strict term is among the first `n`
    · have := ih (fun k k_lt => le_termwise k (by omega)) (by omega)
      -- the last term
      have := le_termwise n (by omega)
      omega

/-- A sum that is not zero has a term that is not zero. -/
theorem tot_ne_zero {n : Nat} {f : Nat → Nat} (ne_zero : tot n f ≠ 0) : ∃ i, i < n ∧ f i ≠ 0 := by
  induction n with
  | zero => exact absurd rfl ne_zero
  | succ n ih =>
    simp only [tot] at ne_zero
    by_cases last_zero : f n = 0
    · obtain ⟨i, i_lt, term_ne⟩ := ih (by omega)
      exact ⟨i, by omega, term_ne⟩
    · exact ⟨n, by omega, last_zero⟩

/-- A sum that is zero has only zero terms. -/
theorem tot_eq_zero {n : Nat} {f : Nat → Nat} (eq_zero : tot n f = 0) : ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => intro i i_lt; omega
  | succ n ih =>
    simp only [tot] at eq_zero
    intro i i_lt
    by_cases is_last : i = n
    · subst is_last; omega
    · exact ih (by omega) i (by omega)

/-! ### Admissible lengths -/

/-- The level-1 side lengths ℓ₁. -/
abbrev L₁ (T : Kind) (c j : Nat) : Nat := letterLen 1 (letterOf (kidAt T c) j)

/-- Side lengths `L` and Σ offset `d` reachable from `(ℓ₁, d₁)` by moves: every side at least as long as at level 1
and of the same parity, glued sides equally long, `d ≥ d₁` of the same parity, and the rest of the Σ child's side 5
past its corner at least as long as at level 1. -/
structure Adm (T : Kind) (L : Nat → Nat → Nat) (d : Nat) : Prop where
  len : ∀ c, c < nk T → ∀ j, j < 6 → L₁ T c j ≤ L c j ∧ (L c j - L₁ T c j) % 2 = 0
  pair : ∀ c, c < nk T → ∀ j, j < 6 → ∀ c' j', adjAt T c j = some (c', j') → L c' j' = L c j
  d_ge : dOff 1 ≤ d
  d_par : (d - dOff 1) % 2 = 0
  sig : ∀ c, c < nk T → kidAt T c = .Sigma → d + L₁ T c 5 ≤ L c 5 + dOff 1

/-- How far `L` is from `ℓ₁`. -/
def excess (T : Kind) (L : Nat → Nat → Nat) : Nat := tot (nk T) fun c => tot 6 fun j => L c j - L₁ T c j

/-- Every level-1 side has at least 5 edges (Lemma 6.5). -/
theorem L₁_ge (T : Kind) (c j : Nat) : 5 ≤ L₁ T c j := (bounds 1 (by omega)).1 _

/-- At level 1, side 5 of the Σ child has 10 edges. -/
theorem L₁_sig {T : Kind} {c : Nat} (is_sigma : kidAt T c = .Sigma) : L₁ T c 5 = 10 := by
  show letterLen 1 (letterOf (kidAt T c) 5) = 10; rw [is_sigma]; rfl

/-- The level-1 Σ offset is `d₁ = 6`. -/
theorem dOff_one : dOff 1 = 6 := rfl

/-- A composition depends only on the lengths of actual sides (and on `d` only through its Σ child). -/
theorem ofLens_congr {T : Kind} {L L' : Nat → Nat → Nat} {d d' : Nat} {ω : Bool}
    (same_len : ∀ c, c < nk T → ∀ j, j < 6 → L c j = L' c j)
    (same_d : ∀ c, c < nk T → kidAt T c = .Sigma → d = d') :
    Comp.ofLens T L d ω = Comp.ofLens T L' d' ω := by
  unfold Comp.ofLens
  congr 1
  apply List.map_congr_left
  intro c c_lt
  rw [List.mem_range] at c_lt
  -- the six side lengths of child `c` agree
  have same_sides : (List.range 6).map (L c) = (List.range 6).map (L' c) :=
    List.map_congr_left (fun j j_mem => same_len c c_lt j (List.mem_range.mp j_mem))
  rw [same_sides]
  by_cases is_sigma : kidAt T c = .Sigma
  · rw [same_d c c_lt is_sigma]
  · simp only [mkKidL, is_sigma, ite_false]

/-! ### Undoing a move -/

namespace Move

variable {T : Kind} {μ : Move}

/-- The side lengths before the move. -/
def shorten (T : Kind) (μ : Move) (L : Nat → Nat → Nat) (c j : Nat) : Nat := L c j - if μ.Hit T c j then 2 else 0

/-- If a side is lengthened, so is the side glued to it. -/
theorem hit_partner_mp (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6) {c j c' j' : Nat}
    (glued : adjAt T c j = some (c', j')) (hit : μ.Hit T c j) : μ.Hit T c' j' := by
  rcases hit with ⟨rfl, rfl⟩ | ⟨side_glued, rfl, rfl⟩
  -- (c, j) = (c₀, j₀): Table 2 glues it to the sibling's side, which is hit
  · have partner := adj₀ (T := T) (μ := μ)
    rw [glued] at partner
    by_cases side_glued : μ.two T = true
    · rw [ite_eq_left side_glued] at partner
      simp only [Option.some.injEq, Prod.mk.injEq] at partner
      exact Or.inr ⟨side_glued, partner.1, partner.2⟩
    · rw [ite_eq_right side_glued] at partner; contradiction
  -- (c, j) = (c₁, j₁): Table 2 glues side `j₀` of `c₀` to it
  · have sib_glued := adj₀ (T := T) (μ := μ)
    rw [ite_eq_left side_glued] at sib_glued
    -- so the sibling's side is glued back to side `j₀` of `c₀`
    have glued_back := (adj_valid c₀_lt j₀_lt sib_glued).2.2.2
    rw [glued] at glued_back
    simp only [Option.some.injEq, Prod.mk.injEq] at glued_back
    exact Or.inl ⟨glued_back.1, glued_back.2⟩

/-- Glued sides are both lengthened or both not. -/
theorem hit_partner (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6) {c j c' j' : Nat} (c_lt : c < nk T) (j_lt : j < 6)
    (glued : adjAt T c j = some (c', j')) : μ.Hit T c j ↔ μ.Hit T c' j' :=
  ⟨hit_partner_mp c₀_lt j₀_lt glued, hit_partner_mp c₀_lt j₀_lt (adj_valid c_lt j_lt glued).2.2.2⟩

variable {L : Nat → Nat → Nat} {d : Nat}

/-- The sides lengthened are at least two edges longer than at level 1. -/
theorem hit_big (adm : Adm T L d) (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6) (long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀)
    {c j : Nat} (hit : μ.Hit T c j) : L₁ T c j + 2 ≤ L c j := by
  rcases hit with ⟨rfl, rfl⟩ | ⟨side_glued, rfl, rfl⟩
  · exact long₀
  -- the sibling's side: Table 2 glues side `j₀` of `c₀` to it
  · have glued := adj₀ (T := T) (μ := μ)
    rw [ite_eq_left side_glued] at glued
    rw [adm.pair _ c₀_lt _ j₀_lt _ _ glued]
    show letterLen 1 (letterOf (kidAt T (μ.c₁ T)) (μ.j₁ T)) + 2 ≤ _
    rw [pair_letter c₀_lt j₀_lt glued]
    exact long₀

/-- Undoing a move and then making it gives back `L`. -/
theorem lens_shorten (adm : Adm T L d) (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6)
    (long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀) : μ.lens T (μ.shorten T L) = L := by
  funext c j
  simp only [lens, shorten]
  by_cases hit : μ.Hit T c j
  -- a side lengthened has at least two edges to spare
  · have := hit_big adm c₀_lt j₀_lt long₀ hit
    rw [ite_eq_left hit]; omega
  · rw [ite_eq_right hit]; omega

/-- Undoing a move from admissible lengths gives admissible lengths, with any Σ offset `d₀` that suits them. -/
theorem adm_shorten (adm : Adm T L d) (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6)
    (long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀) {d₀ : Nat} (d₀_ge : dOff 1 ≤ d₀) (d₀_par : (d₀ - dOff 1) % 2 = 0)
    (sig_room : ∀ c, c < nk T → kidAt T c = .Sigma → d₀ + L₁ T c 5 ≤ μ.shorten T L c 5 + dOff 1) :
    Adm T (μ.shorten T L) d₀ where
  len c c_lt j j_lt := by
    -- the side is as long as at level 1 or longer, by an even number of edges
    have := adm.len c c_lt j j_lt
    simp only [shorten]
    by_cases hit : μ.Hit T c j
    -- a side lengthened is at least two edges longer than at level 1
    · have := hit_big adm c₀_lt j₀_lt long₀ hit
      rw [ite_eq_left hit]; omega
    · rw [ite_eq_right hit]; omega
  pair c c_lt j j_lt c' j' glued := by
    simp only [shorten]
    rw [adm.pair c c_lt j j_lt c' j' glued]
    by_cases hit : μ.Hit T c j
    · rw [ite_eq_left hit, ite_eq_left ((hit_partner c₀_lt j₀_lt c_lt j_lt glued).mp hit)]
    · rw [ite_eq_right hit,
        ite_eq_right (fun partner_hit => hit ((hit_partner c₀_lt j₀_lt c_lt j_lt glued).mpr partner_hit))]
  d_ge := d₀_ge
  d_par := d₀_par
  sig := sig_room

/-- Undoing a move lowers the excess over the level-1 lengths. -/
theorem excess_shorten (adm : Adm T L d) (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6)
    (long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀) : excess T (μ.shorten T L) < excess T L := by
  unfold excess
  -- no side's excess grows
  have no_growth : ∀ c j, μ.shorten T L c j - L₁ T c j ≤ L c j - L₁ T c j := fun c j => by
    simp only [shorten]; omega
  refine tot_lt (fun c _ => tot_le (fun j _ => no_growth c j)) c₀_lt (tot_lt (fun j _ => no_growth _ j) j₀_lt ?_)
  simp only [shorten]
  rw [ite_eq_left (show μ.Hit T μ.c₀ μ.j₀ from Or.inl ⟨rfl, rfl⟩)]
  omega

/-- A move keeps the signature. -/
theorem OK.keep {ω : Bool} (move_ok : μ.OK T L d ω) (has_sig : Sig (Comp.ofLens T L d ω).toGluing (nk T - 1)) :
    Sig (Comp.ofLens T (μ.lens T L) (μ.d' T L d) ω).toGluing (nk T - 1) :=
  move_ok.equiv.symm.sig (move_ok.cutOK.sig has_sig)

/-- **One step back**: if undoing the move `μ` from `(L, d)` gives admissible lengths `(L₀, d₀)` with the
signature, then `(L, d)` has the signature. -/
theorem back_step {ω : Bool} (adm : Adm T L d) (c₀_lt : μ.c₀ < nk T) (j₀_lt : μ.j₀ < 6)
    (long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀) (r₀_ge : 1 ≤ μ.r₀) (r₀_le : μ.r₀ + 4 ≤ L μ.c₀ μ.j₀) {d₀ : Nat}
    (adm₀ : Adm T (μ.shorten T L) d₀)
    (cut₀ : kidAt T μ.c₀ = .Sigma → μ.j₀ = 5 → d₀ + 1 ≤ μ.r₀ ∨ μ.r₀ + 2 ≤ d₀)
    (cut₁ : μ.two T = true → kidAt T (μ.c₁ T) ≠ .Sigma ∨ μ.j₁ T ≠ 5)
    (d_eq : μ.d' T (μ.shorten T L) d₀ = d)
    (has_sig₀ : Sig (Comp.ofLens T (μ.shorten T L) d₀ ω).toGluing (nk T - 1)) :
    Sig (Comp.ofLens T L d ω).toGluing (nk T - 1) := by
  -- the move can be made from the shorter lengths
  have move_ok : μ.OK T (μ.shorten T L) d₀ ω :=
    { wf := has_sig₀.wf
      pos_len := fun c c_lt j j_lt => by
        -- the shorter side is at least as long as at level 1
        have := (adm₀.len c c_lt j j_lt).1
        -- which is at least 5 edges
        have := L₁_ge T c j
        omega
      pair := adm₀.pair
      c₀ := c₀_lt
      j₀ := j₀_lt
      r₀ := r₀_ge
      r₀' := by simp only [shorten]; rw [ite_eq_left (show μ.Hit T μ.c₀ μ.j₀ from Or.inl ⟨rfl, rfl⟩)]; omega
      sig := fun c c_lt is_sigma => by
        -- the shorter side 5 has room for the corner
        have := adm₀.sig c c_lt is_sigma
        -- and the offset `d₀` is at least `d₁`
        have := adm₀.d_ge
        rw [L₁_sig is_sigma, dOff_one] at *; omega
      sig1 := fun c c' c_lt c'_lt is_sigma is_sigma' => sigma_unique T c c_lt c' c'_lt is_sigma is_sigma'
      cut₀ := cut₀
      cut₁ := fun side_glued is_sigma is_5 => by rcases cut₁ side_glued with not_sigma | not_5 <;> contradiction }
  -- the signature after the move
  have after := move_ok.keep has_sig₀
  rwa [lens_shorten adm c₀_lt j₀_lt long₀, d_eq] at after

end Move

/-! ### The induction -/

/-- Every admissible `(L, d)` has the signature. -/
theorem adm_sig (T : Kind) (ω : Bool) :
    ∀ N L d, excess T L < N → Adm T L d → Sig (Comp.ofLens T L d ω).toGluing (nk T - 1) := by
  intro N
  induction N with
  | zero => intro L d excess_lt; omega
  | succ N ih =>
    intro L d excess_lt adm
    obtain ⟨sig_lt, sig_is_sigma⟩ := sigIdx_spec T
    -- `d₁ = 6`
    have d₁_eq := dOff_one
    by_cases zero_excess : excess T L = 0
    -- the base case: `(L, d) = (ℓ₁, d₁)`; first, every side is as at level 1
    · have at_level_1 : ∀ c, c < nk T → ∀ j, j < 6 → L c j = L₁ T c j := fun c c_lt j j_lt => by
        -- side `j` of child `c` has no excess
        have := tot_eq_zero (tot_eq_zero zero_excess c c_lt) j j_lt
        -- and is at least as long as at level 1
        have := (adm.len c c_lt j j_lt).1
        omega
      -- second, `d = d₁`
      have d_eq : d = dOff 1 := by
        -- side 5 of the Σ child has room for the corner
        have := adm.sig _ sig_lt sig_is_sigma
        -- and is as at level 1
        have := at_level_1 _ sig_lt 5 (by omega)
        -- and `d ≥ d₁`
        have := adm.d_ge
        omega
      rw [ofLens_congr (L' := L₁ T) (d' := dOff 1) at_level_1 (fun _ _ _ => d_eq)]
      exact sig_base T ω
    · -- a side longer than at level 1
      obtain ⟨c, c_lt, c_excess⟩ := tot_ne_zero zero_excess
      obtain ⟨j, j_lt, j_excess⟩ := tot_ne_zero c_excess
      -- side `j` of child `c` is at least two edges longer than at level 1
      have long : L₁ T c j + 2 ≤ L c j := by
        -- it is longer by an even number of edges
        have := adm.len c c_lt j j_lt
        omega
      -- the induction hypothesis, at the lengths before a move that lengthened a long side
      have ih_shorter : ∀ μ : Move, μ.c₀ < nk T → μ.j₀ < 6 → L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ → ∀ d₀,
          Adm T (μ.shorten T L) d₀ → Sig (Comp.ofLens T (μ.shorten T L) d₀ ω).toGluing (nk T - 1) :=
        fun μ c₀_lt j₀_lt long₀ d₀ adm₀ => by
          -- undoing the move lowers the excess
          have := Move.excess_shorten adm c₀_lt j₀_lt long₀
          exact ih _ _ (by omega) adm₀
      -- the sibling glued to side `5` of the Σ child is not the Σ child
      have sib_not_sig : ∀ μ : Move, μ.c₀ = sigIdx T → μ.j₀ = 5 → μ.two T = true → kidAt T (μ.c₁ T) ≠ .Sigma := by
        intro μ c₀_sig j₀_5 side_glued sib_sigma
        -- Table 2 glues side 5 of the Σ child to the sibling's side
        have glued := Move.adj₀ (T := T) (μ := μ)
        rw [ite_eq_left side_glued] at glued
        -- so the sibling is a child, different from the Σ child
        have valid := adj_valid (c₀_sig ▸ sig_lt) (by omega) glued
        exact valid.2.2.1 (sigma_unique T _ valid.1 _ (c₀_sig ▸ sig_lt) sib_sigma (c₀_sig ▸ sig_is_sigma))
      by_cases on_sigma_5 : (c = sigIdx T ∧ j = 5) ∨ adjAt T c j = some (sigIdx T, 5)
      -- a move on the Σ child's side 5, which is long
      · have long_5 : L₁ T (sigIdx T) 5 + 2 ≤ L (sigIdx T) 5 := by
          rcases on_sigma_5 with ⟨rfl, rfl⟩ | glued
          · exact long
          · rw [adm.pair c c_lt j j_lt _ _ glued]
            show letterLen 1 (letterOf (kidAt T (sigIdx T)) 5) + 2 ≤ _
            rw [pair_letter c_lt j_lt glued]; exact long
        -- at level 1 that side has 10 edges
        have L₁_5 := L₁_sig sig_is_sigma
        -- it has room for the corner
        have room := adm.sig _ sig_lt sig_is_sigma
        -- `d ≥ d₁`
        have d_ge := adm.d_ge
        -- `d - d₁` is even
        have d_par := adm.d_par
        by_cases d_big : dOff 1 + 2 ≤ d
        · -- before the corner
          obtain ⟨μ, c₀_sig, j₀_5, r₀_eq⟩ : ∃ μ : Move, μ.c₀ = sigIdx T ∧ μ.j₀ = 5 ∧ μ.r₀ = 1 :=
            ⟨⟨_, 5, 1⟩, rfl, rfl, rfl⟩
          -- the child cut is a child
          have c₀_lt : μ.c₀ < nk T := c₀_sig ▸ sig_lt
          -- the side cut is one of its six sides
          have j₀_lt : μ.j₀ < 6 := by omega
          -- the side cut is long
          have long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ := by rw [c₀_sig, j₀_5]; exact long_5
          -- undoing the move shortens side 5 of the Σ child by 2
          have shortened : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 - 2 := by
            simp only [Move.shorten]
            rw [ite_eq_left (show μ.Hit T (sigIdx T) 5 from Or.inl ⟨c₀_sig.symm, j₀_5.symm⟩)]
          -- the shorter lengths, with `d - 2`, are admissible
          have adm₀ : Adm T (μ.shorten T L) (d - 2) :=
            Move.adm_shorten adm c₀_lt j₀_lt long₀ (by omega) (by omega) (fun c' c'_lt is_sigma' => by
              rw [sigma_unique T _ c'_lt _ sig_lt is_sigma' sig_is_sigma, shortened, L₁_5]; omega)
          refine Move.back_step adm c₀_lt j₀_lt long₀ (by omega) (by rw [c₀_sig, j₀_5, r₀_eq]; omega) adm₀
            (fun _ _ => Or.inr (by omega)) (fun side_glued => Or.inl (sib_not_sig μ c₀_sig j₀_5 side_glued)) ?_
            (ih_shorter μ c₀_lt j₀_lt long₀ _ adm₀)
          -- the Σ offset after the move: `d - 2 + 2`
          have d_after := Move.d'_c₀ (L := μ.shorten T L) (d := d - 2) (by rw [c₀_sig]; exact sig_is_sigma) j₀_5
            (fun ⟨side_glued, sib_sigma, _⟩ => sib_not_sig μ c₀_sig j₀_5 side_glued sib_sigma)
          rw [ite_eq_left (by omega)] at d_after; omega
        -- after the corner, where `d = d₁`
        · have d_eq : d = dOff 1 := by omega
          obtain ⟨μ, c₀_sig, j₀_5, r₀_eq⟩ : ∃ μ : Move, μ.c₀ = sigIdx T ∧ μ.j₀ = 5 ∧ μ.r₀ = d + 1 :=
            ⟨⟨_, 5, d + 1⟩, rfl, rfl, rfl⟩
          -- the child cut is a child
          have c₀_lt : μ.c₀ < nk T := c₀_sig ▸ sig_lt
          -- the side cut is one of its six sides
          have j₀_lt : μ.j₀ < 6 := by omega
          -- the side cut is long
          have long₀ : L₁ T μ.c₀ μ.j₀ + 2 ≤ L μ.c₀ μ.j₀ := by rw [c₀_sig, j₀_5]; exact long_5
          -- undoing the move shortens side 5 of the Σ child by 2
          have shortened : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 - 2 := by
            simp only [Move.shorten]
            rw [ite_eq_left (show μ.Hit T (sigIdx T) 5 from Or.inl ⟨c₀_sig.symm, j₀_5.symm⟩)]
          -- the shorter lengths, with the same `d`, are admissible
          have adm₀ : Adm T (μ.shorten T L) d :=
            Move.adm_shorten adm c₀_lt j₀_lt long₀ d_ge d_par (fun c' c'_lt is_sigma' => by
              rw [sigma_unique T _ c'_lt _ sig_lt is_sigma' sig_is_sigma, shortened, L₁_5]; omega)
          refine Move.back_step adm c₀_lt j₀_lt long₀ (by omega) (by rw [c₀_sig, j₀_5, r₀_eq]; omega) adm₀
            (fun _ _ => Or.inl (by omega)) (fun side_glued => Or.inl (sib_not_sig μ c₀_sig j₀_5 side_glued)) ?_
            (ih_shorter μ c₀_lt j₀_lt long₀ _ adm₀)
          -- the Σ offset after the move: still `d`
          have d_after := Move.d'_c₀ (L := μ.shorten T L) (d := d) (by rw [c₀_sig]; exact sig_is_sigma) j₀_5
            (fun ⟨side_glued, sib_sigma, _⟩ => sib_not_sig μ c₀_sig j₀_5 side_glued sib_sigma)
          rw [ite_eq_right (by omega)] at d_after; omega
      · -- a move elsewhere, cutting the third edge of the side (the paper's choice, Lemma 7.2(b))
        obtain ⟨μ, c₀_eq, j₀_eq, r₀_eq⟩ : ∃ μ : Move, μ.c₀ = c ∧ μ.j₀ = j ∧ μ.r₀ = 2 := ⟨⟨c, j, 2⟩, rfl, rfl, rfl⟩
        subst c₀_eq j₀_eq
        -- the side cut is not side 5 of the Σ child
        have not_sigma₀ : ¬ (kidAt T μ.c₀ = .Sigma ∧ μ.j₀ = 5) := fun ⟨is_sigma, is_5⟩ =>
          on_sigma_5 (Or.inl ⟨sigma_unique T _ c_lt _ sig_lt is_sigma sig_is_sigma, is_5⟩)
        -- nor is the sibling's side
        have not_sigma₁ : ¬ (μ.two T = true ∧ kidAt T (μ.c₁ T) = .Sigma ∧ μ.j₁ T = 5) := by
          rintro ⟨side_glued, sib_sigma, sib_5⟩
          -- Table 2 glues the side cut to the sibling's side
          have glued := Move.adj₀ (T := T) (μ := μ)
          rw [ite_eq_left side_glued] at glued
          -- the sibling is a child
          have valid := adj_valid c_lt j_lt glued
          rw [sigma_unique T _ valid.1 _ sig_lt sib_sigma sig_is_sigma, sib_5] at glued
          exact on_sigma_5 (Or.inr glued)
        -- so side 5 of the Σ child is not lengthened
        have not_hit_5 : ¬ μ.Hit T (sigIdx T) 5 := by
          rintro (⟨is_c₀, is_j₀⟩ | ⟨side_glued, is_c₁, is_j₁⟩)
          · exact not_sigma₀ ⟨is_c₀ ▸ sig_is_sigma, is_j₀.symm⟩
          · exact not_sigma₁ ⟨side_glued, is_c₁ ▸ sig_is_sigma, is_j₁.symm⟩
        -- and undoing the move leaves it as it is
        have unshortened : μ.shorten T L (sigIdx T) 5 = L (sigIdx T) 5 := by
          simp only [Move.shorten]; rw [ite_eq_right not_hit_5]; omega
        -- the shorter lengths, with the same `d`, are admissible
        have adm₀ : Adm T (μ.shorten T L) d :=
          Move.adm_shorten adm c_lt j_lt long adm.d_ge adm.d_par (fun c' c'_lt is_sigma' => by
            rw [sigma_unique T _ c'_lt _ sig_lt is_sigma' sig_is_sigma, unshortened]
            exact adm.sig _ sig_lt sig_is_sigma)
        -- every level-1 side has at least 5 edges
        have L₁_ge_5 := L₁_ge T μ.c₀ μ.j₀
        refine Move.back_step adm c_lt j_lt long (by omega) (by rw [r₀_eq]; omega) adm₀
          (fun is_sigma is_5 => absurd ⟨is_sigma, is_5⟩ not_sigma₀) (fun side_glued => ?_)
          (Move.d'_eq not_sigma₀ not_sigma₁) (ih_shorter μ c_lt j_lt long _ adm₀)
        by_cases sib_sigma : kidAt T (μ.c₁ T) = .Sigma
        · exact Or.inr (fun sib_5 => not_sigma₁ ⟨side_glued, sib_sigma, sib_5⟩)
        · exact Or.inl sib_sigma

/-! ### The level-`m` lengths are admissible -/

/-- Each Fibonacci number is at most the next. -/
theorem fib_le_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  cases n with
  | zero => decide
  | succ n => rw [fib_add_two]; omega

/-- The Fibonacci numbers are monotone. -/
theorem fib_mono {a b : Nat} (a_le_b : a ≤ b) : fib a ≤ fib b := by
  induction b with
  | zero =>
    -- only `a = 0` is at most 0
    have a_zero : a = 0 := by omega
    subst a_zero; exact Nat.le_refl _
  | succ b ih =>
    by_cases a_eq : a = b + 1
    · subst a_eq; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (fib_le_succ b)

/-- Letter lengths only grow, and keep their parities. -/
theorem letterLen_ge (m : Nat) (m_pos : 1 ≤ m) (x : Letter) :
    letterLen 1 x ≤ letterLen m x ∧ (letterLen m x - letterLen 1 x) % 2 = 0 := by
  -- the closed forms of the eight letter lengths (Prop 6.2)
  obtain ⟨len_a, len_b, len_g, len_d, len_e, len_z, len_h, len_t⟩ := letterLen_fib m m_pos
  -- and their parities (Cor 6.3)
  obtain ⟨par_a, par_b, par_g, par_d, par_e, par_z, par_h, par_t⟩ := letterLen_parity m m_pos
  -- `F(3m+1) ≥ F(4)`
  have fib_3m1 := fib_mono (show 4 ≤ 3 * m + 1 by omega)
  -- `F(3m+2) ≥ F(5)`
  have fib_3m2 := fib_mono (show 5 ≤ 3 * m + 2 by omega)
  -- `F(3m+3) ≥ F(6)`
  have fib_3m3 := fib_mono (show 6 ≤ 3 * m + 3 by omega)
  -- `F(3m+4) ≥ F(7)`
  have fib_3m4 := fib_mono (show 7 ≤ 3 * m + 4 by omega)
  -- `F(4) = 3`
  have fib4_eq : fib 4 = 3 := rfl
  -- `F(5) = 5`
  have fib5_eq : fib 5 = 5 := rfl
  -- `F(6) = 8`
  have fib6_eq : fib 6 = 8 := rfl
  -- `F(7) = 13`
  have fib7_eq : fib 7 = 13 := rfl
  cases x <;> simp only [letterLen, letterLen1] <;> omega

/-- The level-`m` lengths `(ℓ_m, d_m)` are admissible. -/
theorem adm_level (T : Kind) (m : Nat) (m_pos : 1 ≤ m) :
    Adm T (fun c j => letterLen m (letterOf (kidAt T c) j)) (dOff m) where
  len c _ j _ := letterLen_ge m m_pos _
  pair c c_lt j j_lt c' j' glued := by simp only [pair_letter c_lt j_lt glued]
  d_ge := by
    rw [(dOff_fib m m_pos).1, dOff_one]
    -- `F(3m+1) ≥ F(4)`
    have := fib_mono (show 4 ≤ 3 * m + 1 by omega)
    -- `F(4) = 3`
    have fib4_eq : fib 4 = 3 := rfl
    omega
  d_par := by rw [(dOff_fib m m_pos).1, dOff_one]; omega
  sig c _ is_sigma := by
    show dOff m + L₁ T c 5 ≤ letterLen m (letterOf (kidAt T c) 5) + dOff 1
    rw [L₁_sig is_sigma, is_sigma, dOff_one, show letterOf .Sigma 5 = .delta from rfl, (dOff_fib m m_pos).2]
    -- `F(3m) ≥ F(3)`
    have := fib_mono (show 3 ≤ 3 * m by omega)
    -- `F(3) = 2`
    have fib3_eq : fib 3 = 2 := rfl
    omega

/-! ### The parity lemma -/

/-- **The parity lemma** (the paper's Prop 7.4: Computation 7.3 at every level). For every level `m ≥ 1`, every kind `T` and both signs
`ω`: the composition of §7.1 with the level-`m` lengths `(ℓ_m, d_m)`, its children carrying the signature, has the
signature (`Sig`): it is well formed, no strand closes up, every parent rim vertex is a hook except the Γ child's
corners `A` and `B`, which lie on the parent's rim and carry the crossover. -/
theorem parity_lemma (m : Nat) (m_pos : 1 ≤ m) (T : Kind) (ω : Bool) :
    Sig (Comp.ofPattern T (letterLen m) (dOff m) ω).toGluing (nk T - 1) :=
  adm_sig T ω _ _ _ (Nat.lt_succ_self _) (adm_level T m m_pos)

/-- The corner `B` of child `c`, in terms of the composition's own rim length and corner `A`: the vertex after `A` if
`ω`, the vertex before it otherwise. -/
theorem ofLens_B' {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} {c : Nat} (c_lt : c < nk T) :
    (Comp.ofLens T L d ω).toGluing.B c =
      if ω then nxt ((Comp.ofLens T L d ω).toGluing.E c) ((Comp.ofLens T L d ω).toGluing.A c)
      else prv ((Comp.ofLens T L d ω).toGluing.E c) ((Comp.ofLens T L d ω).toGluing.A c) := by
  rw [ofLens_B c_lt, ofLens_E c_lt]

/-- In a composition with the signature, `A` and `B` are adjacent parent rim vertices: `B` comes right after `A`
along the parent's rim (in the children's sense) if `ω`, right before it otherwise. -/
theorem sig_adj {T : Kind} {L : Nat → Nat → Nat} {d : Nat} {ω : Bool} {G : Gluing}
    (G_eq : G = (Comp.ofLens T L d ω).toGluing) (has_sig : Sig G (nk T - 1)) :
    if ω then G.Rot (nk T - 1, nxt (G.E (nk T - 1)) (G.A (nk T - 1))) (nk T - 1, G.B (nk T - 1))
    else G.Rot (nk T - 1, nxt (G.E (nk T - 1)) (G.B (nk T - 1))) (nk T - 1, G.A (nk T - 1)) := by
  -- the crossover child is a child of the composition
  have g_lt : nk T - 1 < nk T := by
    -- the signature says it is a child of `G`
    have g_lt_G := has_sig.g_lt
    rw [G_eq, ofLens_n] at g_lt_G; exact g_lt_G
  -- `B` is the vertex after `A` if `ω`, the vertex before it otherwise
  have B_eq : G.B (nk T - 1) = if ω then nxt (G.E (nk T - 1)) (G.A (nk T - 1))
      else prv (G.E (nk T - 1)) (G.A (nk T - 1)) := by subst G_eq; exact ofLens_B' g_lt
  cases ω with
  | true =>
    rw [ite_eq_left rfl] at B_eq ⊢
    rw [← B_eq]; exact .stop has_sig.rimB
  | false =>
    rw [ite_eq_right (by decide)] at B_eq ⊢
    rw [B_eq, nxt_prv (has_sig.wf.A_lt _ has_sig.g_lt)]; exact .stop has_sig.rimA

/-- **The parity lemma, adjacency**: `A` and `B` are adjacent parent rim vertices, `B` right after `A` along the
parent's rim (in the children's sense) if `ω`, right before it otherwise. -/
theorem parity_lemma_adj (m : Nat) (m_pos : 1 ≤ m) (T : Kind) (ω : Bool) :
    let G := (Comp.ofPattern T (letterLen m) (dOff m) ω).toGluing
    let g := nk T - 1
    if ω then G.Rot (g, nxt (G.E g) (G.A g)) (g, G.B g) else G.Rot (g, nxt (G.E g) (G.B g)) (g, G.A g) :=
  sig_adj rfl (parity_lemma m m_pos T ω)

end SpectreKnot.Compose

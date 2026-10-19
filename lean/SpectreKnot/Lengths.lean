/-
Side lengths (paper §6): Prop 6.1 (lengths by letter), Prop 6.2 (Fibonacci side lengths), Cor 6.3 (parities are
constant), Lemma 6.4 (position of A on the Σ side), Lemma 6.5 (lower bounds).

The side lengths are *defined* here from the level-1 counts and Prop 2.4(c) (a parent side is the concatenation of
the children's sides of Table 3). Prop 2.4 itself rests on the cited spectre theorems and is not formalised.
-/
import SpectreKnot.Basic
import SpectreKnot.Data.Pattern

namespace SpectreKnot

open Pattern Kind Letter

/-- Child `c` of a `T`-supertile (Table 1). -/
def kidAt (T : Kind) (c : Nat) : Kind := (kids T).getD c .Gamma

/-- The letter of side `j` of a `K`-supertile (Table 4). -/
def letterOf (K : Kind) (j : Nat) : Letter := (letters K).getD j .alpha

/-- The children's sides `(c, j)` that make up side `J` of a `T`-supertile (Table 3). -/
def pieces (T : Kind) (J : Nat) : List (Nat × Nat) := (pside T).getD J []

/-- `sideLen m K j` = ℓ_m(K, j), the number of edges of side `j` of a level-`m` `K`-supertile (`m ≥ 1`): the level-1
counts, and then Prop 2.4(c). (Level 0 is not a hexagon level; the value 0 there is a placeholder.) -/
def sideLen : Nat → Kind → Nat → Nat
  | 0, _, _ => 0
  | 1, K, j => (len1 K).getD j 0
  | m + 2, T, J => ((pieces T J).map (fun p => sideLen (m + 1) (kidAt T p.1) p.2)).sum

/-- The letters on the right-hand side of the recurrence (6.1), with multiplicity. -/
def recLetters : Letter → List Letter
  | .alpha => [.beta, .epsilon, .eta]
  | .beta => [.alpha, .epsilon]
  | .gamma => [.beta, .epsilon, .epsilon, .eta, .theta]
  | .delta => [.alpha, .beta, .epsilon, .theta, .theta]
  | .epsilon => [.epsilon, .epsilon, .epsilon, .eta]
  | .zeta => [.alpha, .epsilon, .theta]
  | .eta => [.epsilon, .epsilon, .epsilon, .epsilon, .eta]
  | .theta => [.epsilon, .epsilon, .epsilon, .epsilon, .eta, .theta]

/-- The level-1 letter lengths (α₁, …, θ₁) = (7, 5, 10, 10, 8, 6, 10, 11). -/
def letterLen1 : Letter → Nat
  | .alpha => 7 | .beta => 5 | .gamma => 10 | .delta => 10
  | .epsilon => 8 | .zeta => 6 | .eta => 10 | .theta => 11

/-- `letterLen m x` = x_m, the common length of the sides with letter `x` at level `m ≥ 1`, by the recurrence (6.1). -/
def letterLen : Nat → Letter → Nat
  | 0, _ => 0
  | 1, x => letterLen1 x
  | m + 2, x => ((recLetters x).map (letterLen (m + 1))).sum

/-! ### Prop 6.1: lengths by letter -/

/-- The level-1 counts depend only on the letter. -/
theorem len1_by_letter : ∀ K : Kind, ∀ j, j < 6 → (len1 K).getD j 0 = letterLen1 (letterOf K j) := by
  intro K; cases K <;> decide

/-- Every piece listed in Table 3 is a side `0..5` of a child. -/
theorem pieces_valid : ∀ T : Kind, ∀ J, J < 6 → ∀ p ∈ pieces T J, p.2 < 6 := by
  intro T; cases T <;> decide

/-- "Inspection of Tables 1, 3, 4" in the proof of Prop 6.1: the letters of the pieces of side `J` of `T` are, up to
order, the letters of the recurrence for the letter of side `J`. -/
theorem pieces_perm : ∀ T : Kind, ∀ J, J < 6 →
    ((pieces T J).map (fun p => letterOf (kidAt T p.1) p.2)).Perm (recLetters (letterOf T J)) := by
  intro T; cases T <;> decide

/-- **Prop 6.1.** For every `m ≥ 1`, ℓ_m(K, j) depends only on the letter of side `j` of `K`, and the letter lengths
satisfy (6.1). -/
theorem sideLen_eq_letterLen (m : Nat) (level_pos : 1 ≤ m) (K : Kind) (j : Nat) (side_lt : j < 6) :
    sideLen m K j = letterLen m (letterOf K j) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  clear level_pos
  induction m generalizing K j with
  | zero => exact len1_by_letter K j side_lt
  | succ m ih =>
    show ((pieces K j).map (fun p => sideLen (m + 1) (kidAt K p.1) p.2)).sum
      = ((recLetters (letterOf K j)).map (letterLen (m + 1))).sum
    -- each piece's length is the length of its letter one level down (by induction)
    have by_letter : (pieces K j).map (fun p => sideLen (m + 1) (kidAt K p.1) p.2)
        = ((pieces K j).map (fun p => letterOf (kidAt K p.1) p.2)).map (letterLen (m + 1)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p piece_mem
      exact ih _ _ (pieces_valid K j side_lt p piece_mem)
    rw [by_letter]
    exact ((pieces_perm K j side_lt).map _).sum_nat

/-- The recurrence (6.1) written out. -/
theorem letterLen_succ (m : Nat) :
    letterLen (m + 2) .alpha = letterLen (m + 1) .beta + letterLen (m + 1) .epsilon + letterLen (m + 1) .eta ∧
    letterLen (m + 2) .beta = letterLen (m + 1) .alpha + letterLen (m + 1) .epsilon ∧
    letterLen (m + 2) .gamma = letterLen (m + 1) .beta + 2 * letterLen (m + 1) .epsilon
      + letterLen (m + 1) .eta + letterLen (m + 1) .theta ∧
    letterLen (m + 2) .delta = letterLen (m + 1) .alpha + letterLen (m + 1) .beta
      + letterLen (m + 1) .epsilon + 2 * letterLen (m + 1) .theta ∧
    letterLen (m + 2) .epsilon = 3 * letterLen (m + 1) .epsilon + letterLen (m + 1) .eta ∧
    letterLen (m + 2) .zeta = letterLen (m + 1) .alpha + letterLen (m + 1) .epsilon + letterLen (m + 1) .theta ∧
    letterLen (m + 2) .eta = 4 * letterLen (m + 1) .epsilon + letterLen (m + 1) .eta ∧
    letterLen (m + 2) .theta = 4 * letterLen (m + 1) .epsilon + letterLen (m + 1) .eta
      + letterLen (m + 1) .theta := by
  simp only [letterLen, recLetters, List.map, List.sum_cons, List.sum_nil]
  omega

/-! ### Prop 6.2: Fibonacci side lengths -/

-- The Fibonacci numbers `fib`, with `fib 1 = fib 2 = 1`, are in `Basic.lean`.

/-- The Fibonacci recurrence. -/
theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Prop 6.2 at level `k + 1`, with the Fibonacci indices written out (3(k+1)+1 = 3k+4, …). -/
theorem letterLen_fib_aux (k : Nat) :
    letterLen (k + 1) .alpha = fib (3 * k + 5) + 2 ∧
    letterLen (k + 1) .beta = fib (3 * k + 4) + 2 ∧
    letterLen (k + 1) .gamma = 2 * fib (3 * k + 5) ∧
    letterLen (k + 1) .delta = 2 * fib (3 * k + 5) ∧
    letterLen (k + 1) .epsilon = fib (3 * k + 6) ∧
    letterLen (k + 1) .zeta = 2 * fib (3 * k + 4) ∧
    letterLen (k + 1) .eta = 2 * fib (3 * k + 5) ∧
    letterLen (k + 1) .theta + 2 = fib (3 * k + 7) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl]
    -- the closed forms at level `k + 1`, and the recurrence (6.1) from level `k + 1` to `k + 2`
    obtain ⟨alpha_k, beta_k, gamma_k, delta_k, epsilon_k, zeta_k, eta_k, theta_k⟩ := ih
    obtain ⟨alpha_rec, beta_rec, gamma_rec, delta_rec, epsilon_rec, zeta_rec, eta_rec, theta_rec⟩ := letterLen_succ k
    -- the Fibonacci recurrence up to F_{3k+10}, so that `omega` can write everything in F_{3k+4} and F_{3k+5}
    have fib6 : fib (3 * k + 6) = fib (3 * k + 4) + fib (3 * k + 5) := fib_add_two _
    have fib7 : fib (3 * k + 7) = fib (3 * k + 5) + fib (3 * k + 6) := fib_add_two _  -- likewise for F_{3k+7}
    have fib8 : fib (3 * k + 8) = fib (3 * k + 6) + fib (3 * k + 7) := fib_add_two _  -- likewise for F_{3k+8}
    have fib9 : fib (3 * k + 9) = fib (3 * k + 7) + fib (3 * k + 8) := fib_add_two _  -- likewise for F_{3k+9}
    have fib10 : fib (3 * k + 10) = fib (3 * k + 8) + fib (3 * k + 9) := fib_add_two _  -- likewise for F_{3k+10}
    -- the indices at level `k + 2` in the form of those above: 3k + 7 for β and ζ
    have idx4 : 3 * (k + 1) + 4 = 3 * k + 7 := by omega
    have idx5 : 3 * (k + 1) + 5 = 3 * k + 8 := by omega  -- for α, γ, δ and η
    have idx6 : 3 * (k + 1) + 6 = 3 * k + 9 := by omega  -- for ε
    have idx7 : 3 * (k + 1) + 7 = 3 * k + 10 := by omega  -- for θ
    rw [idx4, idx5, idx6, idx7]
    omega

/-- **Prop 6.2.** For every `m ≥ 1`: α_m = F_{3m+2} + 2, β_m = F_{3m+1} + 2, γ_m = δ_m = η_m = 2F_{3m+2},
ε_m = F_{3m+3}, ζ_m = 2F_{3m+1}, θ_m = F_{3m+4} − 2. -/
theorem letterLen_fib (m : Nat) (level_pos : 1 ≤ m) :
    letterLen m .alpha = fib (3 * m + 2) + 2 ∧
    letterLen m .beta = fib (3 * m + 1) + 2 ∧
    letterLen m .gamma = 2 * fib (3 * m + 2) ∧
    letterLen m .delta = 2 * fib (3 * m + 2) ∧
    letterLen m .epsilon = fib (3 * m + 3) ∧
    letterLen m .zeta = 2 * fib (3 * m + 1) ∧
    letterLen m .eta = 2 * fib (3 * m + 2) ∧
    letterLen m .theta = fib (3 * m + 4) - 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the indices at level `k + 1` in the form of `letterLen_fib_aux`: 3k + 4 for β and ζ
  have idx1 : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
  have idx2 : 3 * (k + 1) + 2 = 3 * k + 5 := by omega  -- for α, γ, δ and η
  have idx3 : 3 * (k + 1) + 3 = 3 * k + 6 := by omega  -- for ε
  have idx4 : 3 * (k + 1) + 4 = 3 * k + 7 := by omega  -- for θ
  rw [idx1, idx2, idx3, idx4]
  -- the closed forms, with the indices written out
  have closed_forms := letterLen_fib_aux k
  omega

/-! ### Cor 6.3: parities are constant -/

/-- **Cor 6.3.** For every `m ≥ 1`, α_m, β_m, θ_m are odd and γ_m, δ_m, ε_m, ζ_m, η_m are even. (Proved from the
recurrence: the parity vector is a fixed point of (6.1) mod 2.) -/
theorem letterLen_parity (m : Nat) (level_pos : 1 ≤ m) :
    letterLen m .alpha % 2 = 1 ∧ letterLen m .beta % 2 = 1 ∧ letterLen m .gamma % 2 = 0 ∧
    letterLen m .delta % 2 = 0 ∧ letterLen m .epsilon % 2 = 0 ∧ letterLen m .zeta % 2 = 0 ∧
    letterLen m .eta % 2 = 0 ∧ letterLen m .theta % 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl]
    -- the recurrence (6.1) keeps the parities
    have recurrence := letterLen_succ k
    omega

/-- Cor 6.3 for sides: the parity of ℓ_m(K, j) does not depend on `m ≥ 1`. -/
theorem sideLen_parity (m m' : Nat) (level_pos : 1 ≤ m) (level_pos' : 1 ≤ m') (K : Kind) (j : Nat) (side_lt : j < 6) :
    sideLen m K j % 2 = sideLen m' K j % 2 := by
  rw [sideLen_eq_letterLen m level_pos K j side_lt, sideLen_eq_letterLen m' level_pos' K j side_lt]
  -- the parities of the letter lengths at level `m`
  have parity := letterLen_parity m level_pos
  -- and the same parities at level `m'`
  have parity' := letterLen_parity m' level_pos'
  cases letterOf K j <;> omega

/-! ### Lemma 6.4: the position of A on the Σ side -/

/-- In a Σ-supertile of level ≥ 2, side 5 begins with the pieces 0.2, 0.1, 7.0, and child 7 is the Γ child, whose
vertex 0 (the end of piece 7.0) is the crossover corner (Prop 2.4(d)). -/
theorem sigma_side5_start :
    (pieces .Sigma 5).take 3 = [(0, 2), (0, 1), (7, 0)] ∧ kidAt .Sigma 0 = .Xi ∧ kidAt .Sigma 7 = .Gamma := by
  decide

/-- `dOff m` = d_m, the distance along side 5 of a level-`m` Σ-supertile from its vertex 5 to its crossover corner:
measured on the level-1 supertile for `m = 1`, and the length of the pieces before the Γ child's vertex 0 above. -/
def dOff : Nat → Nat
  | 0 => 0
  | 1 => d1
  | m + 2 => (((pieces .Sigma 5).take 3).map (fun p => sideLen (m + 1) (kidAt .Sigma p.1) p.2)).sum

/-- d_{m+2} is the sum of the lengths of the pieces 0.2, 0.1 and 7.0 at level `m + 1`: θ + ε + α. -/
theorem dOff_succ (m : Nat) :
    dOff (m + 2) = letterLen (m + 1) .theta + letterLen (m + 1) .epsilon + letterLen (m + 1) .alpha := by
  -- the length of piece 0.2, side 2 of the Ξ child 0, by its letter
  have piece_0_2 := sideLen_eq_letterLen (m + 1) (by omega) .Xi 2 (by omega)
  -- the length of piece 0.1, side 1 of the Ξ child 0, by its letter
  have piece_0_1 := sideLen_eq_letterLen (m + 1) (by omega) .Xi 1 (by omega)
  -- the length of piece 7.0, side 0 of the Γ child 7, by its letter
  have piece_7_0 := sideLen_eq_letterLen (m + 1) (by omega) .Gamma 0 (by omega)
  simp only [dOff, sigma_side5_start.1, List.map, List.sum_cons, List.sum_nil, sigma_side5_start.2.1,
    sigma_side5_start.2.2, piece_0_2, piece_0_1, piece_7_0]
  rw [show letterOf .Xi 2 = .theta from rfl, show letterOf .Xi 1 = .epsilon from rfl,
    show letterOf .Gamma 0 = .alpha from rfl]
  omega

/-- **Lemma 6.4.** d_m = 2F_{3m+1}, and the crossover corner is at distance δ_m − d_m = 2F_{3m} from vertex 0. -/
theorem dOff_fib (m : Nat) (level_pos : 1 ≤ m) :
    dOff m = 2 * fib (3 * m + 1) ∧ letterLen m .delta = dOff m + 2 * fib (3 * m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  cases k with
  | zero => decide
  | succ k =>
    rw [show k + 1 + 1 = k + 2 from rfl, dOff_succ, (letterLen_succ k).2.2.2.1]
    rw [show 3 * (k + 2) + 1 = 3 * k + 7 by omega, show 3 * (k + 2) = 3 * k + 6 by omega]
    -- the closed forms of Prop 6.2 at level `k + 1`
    have closed_forms := letterLen_fib_aux k
    -- the Fibonacci recurrence at F_{3k+6} and F_{3k+7}, for `omega`
    have fib6 : fib (3 * k + 6) = fib (3 * k + 4) + fib (3 * k + 5) := fib_add_two _
    have fib7 : fib (3 * k + 7) = fib (3 * k + 5) + fib (3 * k + 6) := fib_add_two _  -- likewise for F_{3k+7}
    omega

/-! ### Lemma 6.5: lower bounds -/

/-- **Lemma 6.5.** For every `m ≥ 1`: every side has length at least 5; d_m ≥ 6; and δ_m − d_m ≥ 4. -/
theorem bounds (m : Nat) (level_pos : 1 ≤ m) :
    (∀ x, 5 ≤ letterLen m x) ∧ 6 ≤ dOff m ∧ dOff m + 4 ≤ letterLen m .delta := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- every side has length at least 5, at every level
  have five : ∀ k x, 5 ≤ letterLen (k + 1) x := by
    intro k
    induction k with
    | zero => intro x; cases x <;> decide
    | succ k ih =>
      rw [show k + 1 + 1 = k + 2 from rfl]
      -- the recurrence (6.1): each letter at level `k + 2` is a sum of letters at level `k + 1`
      have recurrence := letterLen_succ k
      -- the bound one level down, letter by letter
      have alpha5 := ih .alpha
      have beta5 := ih .beta  -- likewise for β
      have gamma5 := ih .gamma  -- likewise for γ
      have delta5 := ih .delta  -- likewise for δ
      have epsilon5 := ih .epsilon  -- likewise for ε
      have zeta5 := ih .zeta  -- likewise for ζ
      have eta5 := ih .eta  -- likewise for η
      have theta5 := ih .theta  -- likewise for θ
      intro x; cases x <;> omega
  refine ⟨five k, ?_, ?_⟩
  · cases k with
    | zero => decide
    | succ k =>
      rw [show k + 1 + 1 = k + 2 from rfl, dOff_succ]
      -- d_{k+2} = θ + ε + α, each at least 5
      have theta5 := five k .theta
      have epsilon5 := five k .epsilon  -- likewise for ε
      have alpha5 := five k .alpha  -- likewise for α
      omega
  · cases k with
    | zero => decide
    | succ k =>
      rw [show k + 1 + 1 = k + 2 from rfl, dOff_succ]
      -- δ_{k+2} = α + β + ε + 2θ, so δ − d = β + θ
      have delta_rec := (letterLen_succ k).2.2.2.1
      have beta5 := five k .beta  -- β is at least 5
      have theta5 := five k .theta  -- θ is at least 5
      omega

end SpectreKnot

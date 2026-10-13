/-
The base case of the parity lemma: the signature (`Gluing.Sig`) of the 18 compositions at the level-1 lengths
`(ℓ₁, d₁)`, checked by the kernel. Well-formedness and the absence of closed strands come from `compositions_level1_signature`;
`sigCheck` checks the rest (the hooks at every parent rim vertex found by turning about it, and the crossover).
-/
import SpectreKnot.Signature
import SpectreKnot.CompFull
import SpectreKnot.Lens

namespace SpectreKnot.Compose

open Gluing

/-- Turning about a vertex, as a computation with fuel. -/
def rotWalk (G : Gluing) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, (c, u) =>
    match G.mate c u with
    | none => some (c, u)
    | some (c', k') => rotWalk G f (c', nxt (G.E c') k')

/-- If the computed turn about a vertex ends at `r`, then `Rot x r`. -/
theorem rotWalk_sound (G : Gluing) : ∀ f x r, rotWalk G f x = some r → G.Rot x r := by
  intro f
  induction f with
  | zero => intro x r walk_eq; simp [rotWalk] at walk_eq
  | succ f ih =>
    rintro ⟨c, u⟩ r walk_eq
    simp only [rotWalk] at walk_eq
    cases glued : G.mate c u with
    | none =>
      -- edge `u` of `c` is on the parent's rim: the turn stops here
      rw [glued] at walk_eq; simp only [Option.some.injEq] at walk_eq; subst walk_eq; exact .stop glued
    | some p =>
      -- edge `u` is glued to edge `k'` of `c'`: turn on to the vertex `k' + 1` of `c'`
      obtain ⟨c', k'⟩ := p
      rw [glued] at walk_eq
      exact .step glued (ih _ _ walk_eq)

namespace Comp

variable (C : Comp)

/-- The crossover child: the Γ child, listed last. -/
abbrev gc : Nat := C.kids.length - 1

/-- The hook at the parent rim vertex reached along the rim at the port `x = L_c(u)` (if it is one). -/
def hookOK : GPort → Bool
  | (c, u, false) =>
    match C.toGluing.mate c (prv (C.toGluing.E c) u) with
    | some _ => true
    | none =>
      match rotWalk C.toGluing C.fuel (c, u) with
      | none => false
      | some (c₂, u₂) =>
        (c₂ == C.gc && (u₂ == C.toGluing.A C.gc || u₂ == C.toGluing.B C.gc)) ||
          C.toGluing.fullWalk C.fuel (c, u, false) == some (c₂, u₂, true)
  | (_, _, true) => true

/-- The port `L` at the parent rim vertex `v` (reached along the rim). -/
def findL (v : Nat × Nat) : Option GPort :=
  C.ports.find? fun x =>
    x.2.2 == false && C.toGluing.mate x.1 (prv (C.toGluing.E x.1) x.2.1) == none &&
      rotWalk C.toGluing C.fuel (x.1, x.2.1) == some v

/-- The checks of `Sig` beyond `check`. -/
def sigCheck : Bool :=
  let G := C.toGluing
  (C.ports.all C.hookOK) && decide (C.gc < G.n) && G.mate C.gc (G.A C.gc) == none &&
  G.mate C.gc (G.B C.gc) == none &&
  G.fullWalk C.fuel (C.gc, G.A C.gc, true) == some (C.gc, G.B C.gc, true) &&
  match C.findL (C.gc, G.A C.gc), C.findL (C.gc, G.B C.gc) with
  | some a, some b => G.fullWalk C.fuel a == some b
  | _, _ => false

/-- Every port in the list `ports` is a port of an actual child. -/
theorem valid_of_mem_ports {x : GPort} (mem : x ∈ C.ports) : C.toGluing.Valid x := by
  simp only [ports, List.mem_flatMap, List.mem_range] at mem
  obtain ⟨c, c_lt, u, u_lt, one_of_two⟩ := mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at one_of_two
  rcases one_of_two with rfl | rfl <;> exact ⟨c_lt, u_lt⟩

/-- What `hookOK` establishes at a port `L_c(u)` on the parent's rim: turning about the vertex reaches a parent rim
vertex `(c₂, u₂)`, which is one of the Γ child's corners or carries a hook from `L_c(u)` to `R_{c₂}(u₂)`. -/
theorem hookOK_sound {c u : Nat} (ok : C.hookOK (c, u, false) = true)
    (on_rim : C.toGluing.mate c (prv (C.toGluing.E c) u) = none) :
    ∃ c₂ u₂, C.toGluing.Rot (c, u) (c₂, u₂) ∧
      ((c₂ = C.gc ∧ (u₂ = C.toGluing.A C.gc ∨ u₂ = C.toGluing.B C.gc)) ∨
        C.toGluing.FullReach (c, u, false) (c₂, u₂, true)) := by
  simp only [hookOK, on_rim] at ok
  cases turn_eq : rotWalk C.toGluing C.fuel (c, u) with
  | none => rw [turn_eq] at ok; contradiction
  | some p =>
    obtain ⟨c₂, u₂⟩ := p
    rw [turn_eq] at ok
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
    refine ⟨c₂, u₂, rotWalk_sound _ _ _ _ turn_eq, ?_⟩
    rcases ok with ⟨is_gc, is_corner⟩ | hook
    · exact Or.inl ⟨is_gc, is_corner⟩
    · exact Or.inr (fullWalk_sound _ hook)

/-- What `findL v` establishes: the port it finds is `L_c(u)` at a vertex `u` of a child `c` on the parent's rim, from
which turning about the vertex reaches `v`. -/
theorem findL_sound {v : Nat × Nat} {x : GPort} (found : C.findL v = some x) :
    ∃ c u, x = (c, u, false) ∧ C.toGluing.RimL c u ∧ C.toGluing.Rot (c, u) v := by
  -- the port found passes the search's test
  have passes := List.find?_some found
  -- and it is a port of an actual child
  have x_valid := C.valid_of_mem_ports (List.mem_of_find?_eq_some found)
  obtain ⟨c, u, s⟩ := x
  simp only [Bool.and_eq_true, beq_iff_eq] at passes
  obtain ⟨⟨is_L, on_rim⟩, turn_eq⟩ := passes
  subst is_L
  exact ⟨c, u, rfl, ⟨x_valid.1, x_valid.2, on_rim⟩, rotWalk_sound _ _ _ _ turn_eq⟩

/-- What `check` and `sigCheck` together establish. -/
theorem sig_of_checks {ω : Bool} (checked : C.check ω = true) (sig_checked : C.sigCheck = true) :
    Sig C.toGluing C.gc := by
  obtain ⟨wf, no_loops, -⟩ := C.check_sound checked
  simp only [sigCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at sig_checked
  obtain ⟨⟨⟨⟨⟨hooks_ok, gc_lt⟩, A_on_rim⟩, B_on_rim⟩, cross_R⟩, cross_L⟩ := sig_checked
  refine ⟨wf, no_loops, fun c u rim_L => ?_, gc_lt, A_on_rim, B_on_rim, fullWalk_sound _ cross_R, ?_⟩
  · exact C.hookOK_sound (hooks_ok _ (C.mem_ports ⟨rim_L.1, rim_L.2.1⟩)) rim_L.2.2
  · cases found_A : C.findL (C.gc, C.toGluing.A C.gc) with
    | none => rw [found_A] at cross_L; contradiction
    | some a =>
      cases found_B : C.findL (C.gc, C.toGluing.B C.gc) with
      | none => rw [found_A, found_B] at cross_L; contradiction
      | some b =>
        rw [found_A, found_B] at cross_L
        simp only [beq_iff_eq] at cross_L
        obtain ⟨cA, uA, rfl, rim_A, turn_A⟩ := C.findL_sound found_A
        obtain ⟨cB, uB, rfl, rim_B, turn_B⟩ := C.findL_sound found_B
        exact ⟨cA, uA, cB, uB, rim_A, turn_A, rim_B, turn_B, fullWalk_sound _ cross_L⟩

end Comp

/-! ### The kernel's runs at the level-1 lengths -/

/-- Γ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Gamma_plus : (Comp.ofPattern .Gamma (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Γ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Gamma_minus : (Comp.ofPattern .Gamma (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Δ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Delta_plus : (Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Δ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Delta_minus : (Comp.ofPattern .Delta (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Θ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Theta_plus : (Comp.ofPattern .Theta (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Θ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Theta_minus : (Comp.ofPattern .Theta (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Λ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Lambda_plus : (Comp.ofPattern .Lambda (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Λ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Lambda_minus : (Comp.ofPattern .Lambda (letterLen 1) (dOff 1) false).sigCheck = true := by
  decide +kernel
/-- Ξ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Xi_plus : (Comp.ofPattern .Xi (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Ξ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Xi_minus : (Comp.ofPattern .Xi (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Π, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Pi_plus : (Comp.ofPattern .Pi (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Π, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Pi_minus : (Comp.ofPattern .Pi (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Σ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Sigma_plus : (Comp.ofPattern .Sigma (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Σ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Sigma_minus : (Comp.ofPattern .Sigma (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Φ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Phi_plus : (Comp.ofPattern .Phi (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Φ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Phi_minus : (Comp.ofPattern .Phi (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel
/-- Ψ, `ω = +1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Psi_plus : (Comp.ofPattern .Psi (letterLen 1) (dOff 1) true).sigCheck = true := by decide +kernel
/-- Ψ, `ω = −1`: the level-1 composition passes `sigCheck`. -/
theorem sigCheck_Psi_minus : (Comp.ofPattern .Psi (letterLen 1) (dOff 1) false).sigCheck = true := by decide +kernel

/-- The kernel's runs, collected: at the level-1 lengths, every composition passes `sigCheck`. -/
theorem sigCheck_all : ∀ (T : Kind) (ω : Bool), (Comp.ofPattern T (letterLen 1) (dOff 1) ω).sigCheck = true
  | .Gamma, true => sigCheck_Gamma_plus
  | .Gamma, false => sigCheck_Gamma_minus
  | .Delta, true => sigCheck_Delta_plus
  | .Delta, false => sigCheck_Delta_minus
  | .Theta, true => sigCheck_Theta_plus
  | .Theta, false => sigCheck_Theta_minus
  | .Lambda, true => sigCheck_Lambda_plus
  | .Lambda, false => sigCheck_Lambda_minus
  | .Xi, true => sigCheck_Xi_plus
  | .Xi, false => sigCheck_Xi_minus
  | .Pi, true => sigCheck_Pi_plus
  | .Pi, false => sigCheck_Pi_minus
  | .Sigma, true => sigCheck_Sigma_plus
  | .Sigma, false => sigCheck_Sigma_minus
  | .Phi, true => sigCheck_Phi_plus
  | .Phi, false => sigCheck_Phi_minus
  | .Psi, true => sigCheck_Psi_plus
  | .Psi, false => sigCheck_Psi_minus

/-- **The base case**: at the level-1 lengths `(ℓ₁, d₁)`, every composition has the signature. -/
theorem sig_base (T : Kind) (ω : Bool) : Sig (Comp.ofPattern T (letterLen 1) (dOff 1) ω).toGluing (nk T - 1) := by
  -- the signature at the crossover child `gc`, from the two kernel checks
  have sig_gc := Comp.sig_of_checks _ (compositions_level1 T ω) (sigCheck_all T ω)
  -- the crossover child is the last of the `nk T` children
  have gc_eq : (Comp.ofPattern T (letterLen 1) (dOff 1) ω).gc = nk T - 1 := by
    show (Comp.ofLens T _ _ ω).toGluing.n - 1 = _; rw [ofLens_n]
  rwa [gc_eq] at sig_gc

end SpectreKnot.Compose

/-
Computation 7.3, from the tables alone: the unreduced abstract compositions of §7.1, glued port by port in the
Lean kernel. This does not use the reduced walk, the skeletons exported from JavaScript, or the zigzag lemma.
`compositions_level1_signature` states the result as theorems about the glued compositions (via `Comp.check_sound`).
-/
import SpectreKnot.Compose

namespace SpectreKnot.Compose

/-- The nine kinds. -/
def allKinds : List Kind := [.Gamma, .Delta, .Theta, .Lambda, .Xi, .Pi, .Sigma, .Phi, .Psi]

/-! The kernel's runs, one composition per theorem (one run needs about 1.5 GB). -/

/-- Γ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Gamma_plus : (Comp.ofPattern .Gamma (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Γ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Gamma_minus : (Comp.ofPattern .Gamma (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Δ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Delta_plus : (Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Δ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Delta_minus : (Comp.ofPattern .Delta (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Θ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Theta_plus : (Comp.ofPattern .Theta (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Θ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Theta_minus : (Comp.ofPattern .Theta (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Λ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Lambda_plus : (Comp.ofPattern .Lambda (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Λ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Lambda_minus : (Comp.ofPattern .Lambda (letterLen 1) (dOff 1) false).check false = true := by
  decide +kernel
/-- Ξ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Xi_plus : (Comp.ofPattern .Xi (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Ξ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Xi_minus : (Comp.ofPattern .Xi (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Π, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Pi_plus : (Comp.ofPattern .Pi (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Π, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Pi_minus : (Comp.ofPattern .Pi (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Σ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Sigma_plus : (Comp.ofPattern .Sigma (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Σ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Sigma_minus : (Comp.ofPattern .Sigma (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Φ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Phi_plus : (Comp.ofPattern .Phi (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Φ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Phi_minus : (Comp.ofPattern .Phi (letterLen 1) (dOff 1) false).check false = true := by decide +kernel
/-- Ψ, `ω = +1`: the level-1 composition passes `check`. -/
theorem check_Psi_plus : (Comp.ofPattern .Psi (letterLen 1) (dOff 1) true).check true = true := by decide +kernel
/-- Ψ, `ω = −1`: the level-1 composition passes `check`. -/
theorem check_Psi_minus : (Comp.ofPattern .Psi (letterLen 1) (dOff 1) false).check false = true := by decide +kernel

/-- **Computation 7.3** (the kernel's runs, collected). -/
theorem compositions_level1 : ∀ (T : Kind) (ω : Bool), (Comp.ofPattern T (letterLen 1) (dOff 1) ω).check ω = true
  | .Gamma, true => check_Gamma_plus
  | .Gamma, false => check_Gamma_minus
  | .Delta, true => check_Delta_plus
  | .Delta, false => check_Delta_minus
  | .Theta, true => check_Theta_plus
  | .Theta, false => check_Theta_minus
  | .Lambda, true => check_Lambda_plus
  | .Lambda, false => check_Lambda_minus
  | .Xi, true => check_Xi_plus
  | .Xi, false => check_Xi_minus
  | .Pi, true => check_Pi_plus
  | .Pi, false => check_Pi_minus
  | .Sigma, true => check_Sigma_plus
  | .Sigma, false => check_Sigma_minus
  | .Phi, true => check_Phi_plus
  | .Phi, false => check_Phi_minus
  | .Psi, true => check_Psi_plus
  | .Psi, false => check_Psi_minus

/-- **Computation 7.3**, as theorems. For every kind `T` and both signs `ω`, in the composition of §7.1 with
the level-1 lengths `(ℓ₁, d₁)`, its children carrying the signature: the gluing is well formed; the walk from every
port ends on the parent's rim (no closed strand); every parent rim vertex is a hook except the Γ child's corners `A`
and `B`; these are adjacent in the right order; and they carry the crossover. -/
theorem compositions_level1_signature (T : Kind) (ω : Bool) :
    let C := Comp.ofPattern T (letterLen 1) (dOff 1) ω
    let G := C.toGluing
    let n := C.rimVertexPorts.length
    G.WF ∧
    (∀ x, G.Valid x → ∃ r, G.FullReach x r) ∧
    (∀ t, t < n → t ≠ C.tA → t ≠ C.tB → G.FullReach (C.vtx t).1 (C.vtx t).2) ∧
    C.tA < n ∧ C.tB < n ∧ C.tB = (if ω then (C.tA + 1) % n else (C.tA + n - 1) % n) ∧
    G.FullReach (C.vtx C.tA).2 (C.vtx C.tB).2 ∧ G.FullReach (C.vtx C.tA).1 (C.vtx C.tB).1 := by
  exact Comp.check_sound _ (compositions_level1 T ω)

/-- For the negative control: give child `c` a crossover at two non-adjacent corners (`B = A + 2`). -/
def Comp.spreadCorners (C : Comp) (c : Nat) : Comp :=
  { C with kids := C.kids.modify c fun k => { k with B := (k.A + 2) % k.E } }

/-- Negative control: if one child's crossover corners are not adjacent (for the first child and for the Γ child of a
Δ), the parent fails the check. -/
theorem negative_control :
    ([0, 7].all fun c => !((Comp.ofPattern .Delta (letterLen 1) (dOff 1) true).spreadCorners c).check true) = true := by
  decide +kernel

end SpectreKnot.Compose

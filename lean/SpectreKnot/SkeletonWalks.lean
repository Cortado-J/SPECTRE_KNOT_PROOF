/-
The skeleton walks of the paper's Remark 7.8 (corroboration; the main proofs do not use them), re-run by the Lean
kernel (`decide +kernel`: the kernel evaluates the checker itself; no compiled
code is trusted).
-/
import SpectreKnot.Data.Skeletons

namespace SpectreKnot.Skeletons

open Skeleton

/-- **The skeleton walks** (Remark 7.8). For all nine kinds `T` and both signs `ω`, the reduced walk on `S_T(ℓ₁, d₁, ω)` closes no
loop and gives the parent the signature at the Γ child's crossover corners. -/
theorem skeleton_walks : all.all Skel.check = true := by decide +kernel

/-- The Lean walk finds the same non-hooks as the JavaScript walk (`core/reduce.js`, `rcompose`). -/
theorem agrees_with_js : all.map Skel.nonHooks = allJsNonHooks := by decide +kernel

/-- Negative control: the check is not vacuous. Flipping the parity of one shared run of `S_Δ(ℓ₁, d₁, +1)` together
with its partner keeps the skeleton consistent, and for these seven runs it breaks the signature (the walk then finds
four non-hooks), so the check fails. (For the other shared runs the signature survives the flip: it is fairly robust,
which is why a control has to be chosen with care.) -/
theorem negative_control :
    ([(0, 3), (1, 1), (1, 3), (1, 8), (4, 1), (4, 3), (4, 5)].all fun (c, i) =>
      (deltaPlus.flipShared c i).involutionsOK && !(deltaPlus.flipShared c i).check) = true := by
  decide +kernel

end SpectreKnot.Skeletons

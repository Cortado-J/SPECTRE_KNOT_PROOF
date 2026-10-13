/-
Basic types and helpers. No Mathlib: everything here is core Lean.
-/

namespace SpectreKnot

/-- The nine kinds of supertile (paper §2.2). -/
inductive Kind where
  | Gamma | Delta | Theta | Lambda | Xi | Pi | Sigma | Phi | Psi
  deriving DecidableEq, Repr

/-- The eight letters of the edge labels of [SMKGS-spectre, Fig. 4.2], signs ignored (paper §6.1). -/
inductive Letter where
  | alpha | beta | gamma | delta | epsilon | zeta | eta | theta
  deriving DecidableEq, Repr

/-- `iter f n x = f (f (... (f x)))`, `n` times. (Core Lean has no `f^[n]`.) -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- Zero steps leave `x` where it is. -/
@[simp] theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

/-- `n + 1` steps are `n` steps, then one more application of `f`. -/
theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) : iter f (n + 1) x = f (iter f n x) := rfl

/-- The extra step can also be taken first: `n + 1` steps from `x` are `n` steps from `f x`. -/
theorem iter_succ' {α : Type} (f : α → α) (n : Nat) (x : α) : iter f (n + 1) x = iter f n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, iter_succ]

/-- `m + n` steps are `n` steps followed by `m` steps. -/
theorem iter_add {α : Type} (f : α → α) (m n : Nat) (x : α) : iter f (m + n) x = iter f m (iter f n x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_right_comm, iter_succ, ih, iter_succ]

end SpectreKnot

/-
Rim ports, boxes and the signature (paper §4.1–4.2: Def 4.3, Lemma 4.4 for the tile), and the decoration (Def 3.1).
-/
import SpectreKnot.Basic

namespace SpectreKnot

/-- The two ports at a rim vertex `u`: `R` on the rim edge after `u`, near `u`; `L` on the rim edge before `u`,
near `u` (in a chosen orientation of the rim; reversing it exchanges `L` and `R`). -/
inductive Hand where
  | L | R
  deriving DecidableEq, Repr

/-- A rim port of a patch with `E` rim vertices `u_0, …, u_{E-1}`. -/
abbrev RimPort (E : Nat) := Fin E × Hand

/-- A claim about every rim port can be decided vertex by vertex, both hands at each. -/
instance {E : Nat} (q : RimPort E → Prop) [DecidablePred q] : Decidable (∀ p : RimPort E, q p) :=
  decidable_of_iff (∀ i : Fin E, q (i, .L) ∧ q (i, .R))
    ⟨fun both_hands p => by rcases p with ⟨i, _ | _⟩ <;> simp [both_hands i],
     fun every_port i => ⟨every_port _, every_port _⟩⟩

/-- The box of a patch (Lemma 4.1): the pairing of its rim ports by its arcs, and its number `κ` of closed
strands. -/
structure Box (E : Nat) where
  pair : RimPort E → RimPort E
  closed : Nat

/-- A box is *proper* if its pairing is an involution without fixed points (Lemma 4.1). -/
def Box.Proper {E : Nat} (b : Box E) : Prop :=
  ∀ p, b.pair (b.pair p) = p ∧ b.pair p ≠ p

instance {E : Nat} (b : Box E) : Decidable b.Proper := by unfold Box.Proper; infer_instance

/-- **Def 4.3.** The box has the *signature at* `(A, B)`: a hook at every rim vertex other than `A` and `B`, the
crossover `R(A) ↔ R(B)`, `L(A) ↔ L(B)`, and no closed strand. -/
def Box.Signature {E : Nat} (b : Box E) (A B : Fin E) : Prop :=
  (∀ u : Fin E, u ≠ A → u ≠ B → b.pair (u, .L) = (u, .R)) ∧
  b.pair (A, .R) = (B, .R) ∧ b.pair (A, .L) = (B, .L) ∧ b.closed = 0

instance {E : Nat} (b : Box E) (A B : Fin E) : Decidable (b.Signature A B) := by
  unfold Box.Signature; infer_instance

/-! ### The tile -/

/-- **Def 3.1.** The decoration of the tile, as a pairing of its 28 ports `R(v_i)`, `L(v_i)` (vertices counted
counter-clockwise from `v_0`): twelve hooks `L(v_i) ↔ R(v_i)` for `2 ≤ i ≤ 13`, and the crossover
`R(v_0) ↔ R(v_1)`, `L(v_0) ↔ L(v_1)`. -/
def tilePiece : RimPort 14 → RimPort 14
  | (⟨0, _⟩, hand) => (1, hand)
  | (⟨1, _⟩, hand) => (0, hand)
  | (i, .L) => (i, .R)
  | (i, .R) => (i, .L)

/-- The tile seen as a patch: its pieces are its arcs, and it has no closed strand. -/
def tileBox : Box 14 := ⟨tilePiece, 0⟩

/-- The tile's pairing is a proper box: every port is paired with another port, which is paired back. -/
theorem tileBox_proper : tileBox.Proper := by decide

/-- **Lemma 4.4** (tile). A tile has the signature at `(v_0, v_1)`. -/
theorem tile_signature : tileBox.Signature 0 1 := by decide

end SpectreKnot

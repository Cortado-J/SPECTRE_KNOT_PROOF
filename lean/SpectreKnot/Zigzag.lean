/-
The zigzag lemma (paper Lemma 5.1), for every length `n`.

Setting: a path `u_0 u_1 … u_n` of `n ≥ 1` edges lies on the rims of two children `X_c` and `X_{c'}`; `X_c` traverses
it from `u_0` to `u_n`, and `X_{c'}` (oriented in the same rotational sense) from `u_n` to `u_0`. None of
`u_1, …, u_{n-1}` is a crossover corner of either child, so both children have hooks there.

The ports involved are named by `Strip`: `c h k` is the port `h(u_k)` of `X_c` and `d h k` the port `h(u_k)` of
`X_{c'}`, each in its own orientation. They live in some type `P` of ports (`ι : Strip → P`), on which `σ` is the
straight-through rule (Def 3.2) and `τ` is the pairing inside the children (their boxes). The lemma follows the
alternation `σ, τ, σ, τ, …, σ` along the path.
-/
import SpectreKnot.Basic
import SpectreKnot.Box

namespace SpectreKnot

/-- Ports along the shared path: `c h k` = `h_c(u_k)`, `d h k` = `h_{c'}(u_k)`. -/
inductive Strip where
  | c (h : Hand) (k : Nat)
  | d (h : Hand) (k : Nat)
  deriving DecidableEq, Repr

namespace Zigzag

variable {P : Type} (σ τ : P → P) (ι : Strip → P) (n : Nat)

/-- One step of the alternation: across an edge, then through a hook. -/
def zz (p : P) : P := τ (σ p)

/-- The core computation, with the four local rules the walk uses. The walk from `R_c(u_0)`: after `k` steps it is at
`R_c(u_k)` (`k` even) or `L_{c'}(u_k)` (`k` odd), and crossing edge `k` takes it to `R_{c'}(u_{k+1})` or
`L_c(u_{k+1})`. The four rules: across edge `k` from `R_c(u_k)` (`across_R`) and from `L_{c'}(u_k)` (`across_L`),
and the hooks of `X_{c'}` (`hook_d`) and of `X_c` (`hook_c`) at the inner vertices. -/
theorem walk_core
    (across_R : ∀ k, k < n → σ (ι (.c .R k)) = ι (.d .R (k + 1)))
    (hook_d : ∀ k, 0 < k → k < n → τ (ι (.d .R k)) = ι (.d .L k))
    (across_L : ∀ k, k < n → σ (ι (.d .L k)) = ι (.c .L (k + 1)))
    (hook_c : ∀ k, 0 < k → k < n → τ (ι (.c .L k)) = ι (.c .R k)) :
    ∀ k, k < n →
      iter (zz σ τ) k (ι (.c .R 0)) = (if k % 2 = 0 then ι (.c .R k) else ι (.d .L k)) ∧
      σ (iter (zz σ τ) k (ι (.c .R 0))) = (if k % 2 = 0 then ι (.d .R (k + 1)) else ι (.c .L (k + 1))) := by
  intro k k_lt
  induction k with
  | zero => simp [across_R 0 (by omega)]
  | succ k ih =>
    obtain ⟨_, crossed⟩ := ih (by omega)
    -- after `k + 1` steps: the hook at `u_{k+1}` of the child the crossing reached
    have at_next : iter (zz σ τ) (k + 1) (ι (.c .R 0))
        = (if (k + 1) % 2 = 0 then ι (.c .R (k + 1)) else ι (.d .L (k + 1))) := by
      rw [iter_succ, zz, crossed]
      by_cases k_even : k % 2 = 0
      · rw [ite_eq_left k_even, ite_eq_right (by omega), hook_d (k + 1) (by omega) k_lt]
      · rw [ite_eq_right k_even, ite_eq_left (by omega), hook_c (k + 1) (by omega) k_lt]
    refine ⟨at_next, ?_⟩
    rw [at_next]
    by_cases next_even : (k + 1) % 2 = 0
    · rw [ite_eq_left next_even, ite_eq_left next_even, across_R (k + 1) k_lt]
    · rw [ite_eq_right next_even, ite_eq_right next_even, across_L (k + 1) k_lt]

/-- The relabelling that exchanges the two children and `L` with `R`. It turns the walk from `L_{c'}(u_0)` into a
walk from `R_c(u_0)`, so `walk_core` also describes the second connection. -/
def swap : Strip → Strip
  | .c .R k => .d .L k
  | .c .L k => .d .R k
  | .d .R k => .c .L k
  | .d .L k => .c .R k

/-- **Lemma 5.1 (zigzag lemma).** Let `σ` and `τ` be involutions, `σ` the straight-through rule across the edges
`u_k u_{k+1}` of the path and `τ` the hooks of both children at `u_1, …, u_{n-1}`. Then the alternation joins the
ports at the ends of the path as follows:

* `n` even: `R_c(u_0) ↔ L_c(u_n)` and `L_{c'}(u_0) ↔ R_{c'}(u_n)`;
* `n` odd: `R_c(u_0) ↔ R_{c'}(u_n)` and `L_{c'}(u_0) ↔ L_c(u_n)`.

(Each connection is `σ ∘ (τ ∘ σ)^(n-1)`, read from the port at `u_0`.) Moreover, for `0 < k < n`, the hook of `X_c`
at `u_k` lies on the connection through `R_c(u_0)` if `k` is even and on the one through `L_{c'}(u_0)` if `k` is
odd; and the two connections together cross every edge of the path at all four of its ports. -/
theorem zigzag (len_pos : 1 ≤ n)
    (σ_invol : ∀ p, σ (σ p) = p) (τ_invol : ∀ p, τ (τ p) = p)
    (across_R : ∀ k, k < n → σ (ι (.c .R k)) = ι (.d .R (k + 1)))
    (across_L : ∀ k, k < n → σ (ι (.c .L (k + 1))) = ι (.d .L k))
    (hook_c : ∀ k, 0 < k → k < n → τ (ι (.c .L k)) = ι (.c .R k))
    (hook_d : ∀ k, 0 < k → k < n → τ (ι (.d .L k)) = ι (.d .R k)) :
    -- the connection through R_c(u_0)
    σ (iter (zz σ τ) (n - 1) (ι (.c .R 0))) = (if n % 2 = 0 then ι (.c .L n) else ι (.d .R n)) ∧
    -- the connection through L_{c'}(u_0)
    σ (iter (zz σ τ) (n - 1) (ι (.d .L 0))) = (if n % 2 = 0 then ι (.d .R n) else ι (.c .L n)) ∧
    -- where the hooks of X_c go
    (∀ k, 0 < k → k < n →
      σ (iter (zz σ τ) (k - 1) (ι (if k % 2 = 0 then .c .R 0 else .d .L 0))) = ι (.c .L k)) ∧
    -- every port on the edges of the path is used
    (∀ k, k < n →
      (iter (zz σ τ) k (ι (.c .R 0)) = ι (.c .R k) ∨ iter (zz σ τ) k (ι (.d .L 0)) = ι (.c .R k)) ∧
      (iter (zz σ τ) k (ι (.c .R 0)) = ι (.d .L k) ∨ iter (zz σ τ) k (ι (.d .L 0)) = ι (.d .L k))) := by
  -- the hook of `X_{c'}` from `R` to `L`: the given rule read backwards, as `τ` is an involution
  have hook_d_RL : ∀ k, 0 < k → k < n → τ (ι (.d .R k)) = ι (.d .L k) := by
    intro k k_pos k_lt; rw [← hook_d k k_pos k_lt, τ_invol]
  -- the crossing from `L_{c'}(u_k)` to `L_c(u_{k+1})`: the given rule read backwards, as `σ` is an involution
  have across_L_fwd : ∀ k, k < n → σ (ι (.d .L k)) = ι (.c .L (k + 1)) := by
    intro k k_lt; rw [← across_L k k_lt, σ_invol]
  -- the walk from `R_c(u_0)`
  have from_R := walk_core σ τ ι n across_R hook_d_RL across_L_fwd hook_c
  -- the walk from `L_{c'}(u_0)`: the same rules for the relabelled strip
  have from_L := walk_core σ τ (fun s => ι (swap s)) n
    (fun k k_lt => by simp only [swap]; exact across_L_fwd k k_lt)
    (fun k k_pos k_lt => by simp only [swap]; exact hook_c k k_pos k_lt)
    (fun k k_lt => by simp only [swap]; exact across_R k k_lt)
    (fun k k_pos k_lt => by simp only [swap]; exact hook_d_RL k k_pos k_lt)
  simp only [swap] at from_L
  refine ⟨?_, ?_, ?_, ?_⟩
  · have last := (from_R (n - 1) (by omega)).2  -- the last crossing of the walk from `R_c(u_0)`
    rw [show n - 1 + 1 = n by omega] at last
    rw [last]; by_cases n_even : n % 2 = 0
    · rw [ite_eq_right (by omega), ite_eq_left n_even]
    · rw [ite_eq_left (by omega), ite_eq_right n_even]
  · have last := (from_L (n - 1) (by omega)).2  -- the last crossing of the walk from `L_{c'}(u_0)`
    rw [show n - 1 + 1 = n by omega] at last
    rw [last]; by_cases n_even : n % 2 = 0
    · rw [ite_eq_right (by omega), ite_eq_left n_even]
    · rw [ite_eq_left (by omega), ite_eq_right n_even]
  · intro k k_pos k_lt
    by_cases k_even : k % 2 = 0
    · rw [ite_eq_left k_even, (from_R (k - 1) (by omega)).2, ite_eq_right (by omega), show k - 1 + 1 = k by omega]
    · rw [ite_eq_right k_even, (from_L (k - 1) (by omega)).2, ite_eq_left (by omega), show k - 1 + 1 = k by omega]
  · intro k k_lt
    by_cases k_even : k % 2 = 0
    · rw [(from_R k k_lt).1, (from_L k k_lt).1, ite_eq_left k_even, ite_eq_left k_even]; simp
    · rw [(from_R k k_lt).1, (from_L k k_lt).1, ite_eq_right k_even, ite_eq_right k_even]; simp

end Zigzag

end SpectreKnot

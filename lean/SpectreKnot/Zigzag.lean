/-
The zigzag lemma (paper Lemma 5.1), for every length `n`.

Setting: a path `u_0 u_1 … u_n` of `n ≥ 1` edges lies on the rims of two children `X_c` and `X_{c'}`; `X_c` traverses
it from `u_0` to `u_n`, and `X_{c'}` (oriented in the same rotational sense) from `u_n` to `u_0`. None of
`u_1, …, u_{n-1}` is a crossover corner of either child, so both children have hooks there.

The ports involved are named by `Strip`: `c h k` is the port `h(u_k)` of `X_c` and `d h k` the port `h(u_k)` of
`X_{c'}`, each in its own orientation. They live in some type `P` of ports (`ι : Strip → P`), on which `σ` is the
straight-through rule (Def 3.2), undefined where nothing is glued, and `τ` is the pairing inside the children (their
boxes). The lemma follows the alternation `σ, τ, σ, τ, …, σ` along the path (`Chain`). The lengthening (Lemma 7.1)
uses it with `n = 3`, along an edge cut into three (`Gluing.Cut.OK.cross_cut`).
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

/-- **A connection**: `Chain σ τ p q` says that from `p`, crossing an edge (`σ`, defined there) and then, until `q` is
reached, going through a piece (`τ`) and crossing again, leads to `q`. -/
inductive Chain {P : Type} (σ : P → Option P) (τ : P → P) : P → P → Prop
  | one {p q : P} : σ p = some q → Chain σ τ p q
  | more {p p₁ q : P} : σ p = some p₁ → Chain σ τ (τ p₁) q → Chain σ τ p q

/-- A chain goes on through one more piece and crossing at its end. -/
theorem Chain.snoc {P : Type} {σ : P → Option P} {τ : P → P} {p q q' : P} (chain : Chain σ τ p q)
    (next : σ (τ q) = some q') : Chain σ τ p q' := by
  induction chain with
  | one crosses => exact .more crosses (.one next)
  | more crosses _ ih => exact .more crosses (ih next)

section Chains

variable {P : Type} (σ : P → Option P) (τ : P → P) (ι : Strip → P) (n : Nat)

/-- The connection through `R_c(u_0)`, crossing by crossing: after its `k + 1`-th crossing (`k < n`) it has arrived at
`R_{c'}(u_{k+1})` (`k` even) or `L_c(u_{k+1})` (`k` odd). The four rules: across edge `k` from `R_c(u_k)` (`across_R`)
and from `L_{c'}(u_k)` (`across_L`), and the hooks of `X_{c'}` (`hook_d`) and of `X_c` (`hook_c`) at the inner
vertices. -/
theorem walk_chain
    (across_R : ∀ k, k < n → σ (ι (.c .R k)) = some (ι (.d .R (k + 1))))
    (hook_d : ∀ k, 0 < k → k < n → τ (ι (.d .R k)) = ι (.d .L k))
    (across_L : ∀ k, k < n → σ (ι (.d .L k)) = some (ι (.c .L (k + 1))))
    (hook_c : ∀ k, 0 < k → k < n → τ (ι (.c .L k)) = ι (.c .R k)) :
    ∀ k, k < n → Chain σ τ (ι (.c .R 0)) (if k % 2 = 0 then ι (.d .R (k + 1)) else ι (.c .L (k + 1))) := by
  intro k k_lt
  induction k with
  | zero => exact .one (across_R 0 k_lt)
  | succ k ih =>
    -- the first `k + 1` crossings
    have before := ih (by omega)
    by_cases k_even : k % 2 = 0
    · -- arrived at `R_{c'}(u_{k+1})`: the hook of `X_{c'}` there, then across edge `k + 1` from `L_{c'}(u_{k+1})`
      rw [ite_eq_left k_even] at before
      rw [ite_eq_right (show ¬ ((k + 1) % 2 = 0) by omega)]
      exact before.snoc (by rw [hook_d (k + 1) (by omega) k_lt]; exact across_L (k + 1) k_lt)
    · -- arrived at `L_c(u_{k+1})`: the hook of `X_c` there, then across edge `k + 1` from `R_c(u_{k+1})`
      rw [ite_eq_right k_even] at before
      rw [ite_eq_left (show (k + 1) % 2 = 0 by omega)]
      exact before.snoc (by rw [hook_c (k + 1) (by omega) k_lt]; exact across_R (k + 1) k_lt)

/-- The relabelling that exchanges the two children and `L` with `R`. It turns the connection through `L_{c'}(u_0)`
into a connection through `R_c(u_0)`, so `walk_chain` also describes the second connection. -/
def swap : Strip → Strip
  | .c .R k => .d .L k
  | .c .L k => .d .R k
  | .d .R k => .c .L k
  | .d .L k => .c .R k

/-- **Lemma 5.1 (the Zigzag Lemma).** Let `σ` be the straight-through rule across the edges `u_k u_{k+1}` of the path,
and `τ` the hooks of both children at `u_1, …, u_{n-1}`. Alternately applying them joins the ports at the ends of the
path as follows:

* `n` even: `R_c(u_0) ↔ L_c(u_n)` and `L_{c'}(u_0) ↔ R_{c'}(u_n)`;
* `n` odd: `R_c(u_0) ↔ R_{c'}(u_n)` and `L_{c'}(u_0) ↔ L_c(u_n)`.

These two connections use every port on the edges of the path: after `k + 1` crossings they have arrived at the two
ports `R_{c'}(u_{k+1})` and `L_c(u_{k+1})` of edge `k`, one each, so each crosses every edge once, and between them they
leave from its other two ports, `R_c(u_k)` and `L_{c'}(u_k)`. -/
theorem zigzag (len_pos : 1 ≤ n)
    (across_R : ∀ k, k < n → σ (ι (.c .R k)) = some (ι (.d .R (k + 1))))
    (across_L : ∀ k, k < n → σ (ι (.d .L k)) = some (ι (.c .L (k + 1))))
    (hook_c : ∀ k, 0 < k → k < n → τ (ι (.c .L k)) = ι (.c .R k))
    (hook_d : ∀ k, 0 < k → k < n → τ (ι (.d .R k)) = ι (.d .L k)) :
    -- the connection through R_c(u_0)
    Chain σ τ (ι (.c .R 0)) (if n % 2 = 0 then ι (.c .L n) else ι (.d .R n)) ∧
    -- the connection through L_{c'}(u_0)
    Chain σ τ (ι (.d .L 0)) (if n % 2 = 0 then ι (.d .R n) else ι (.c .L n)) ∧
    -- every port on the edges of the path is used
    (∀ k, k < n →
      Chain σ τ (ι (.c .R 0)) (if k % 2 = 0 then ι (.d .R (k + 1)) else ι (.c .L (k + 1))) ∧
      Chain σ τ (ι (.d .L 0)) (if k % 2 = 0 then ι (.c .L (k + 1)) else ι (.d .R (k + 1)))) := by
  -- the connection through `R_c(u_0)`, crossing by crossing
  have from_R := walk_chain σ τ ι n across_R hook_d across_L hook_c
  -- the connection through `L_{c'}(u_0)`: the same rules for the relabelled strip
  have from_L := walk_chain σ τ (fun s => ι (swap s)) n
    (fun k k_lt => by simp only [swap]; exact across_L k k_lt)
    (fun k k_pos k_lt => by simp only [swap]; exact hook_c k k_pos k_lt)
    (fun k k_lt => by simp only [swap]; exact across_R k k_lt)
    (fun k k_pos k_lt => by simp only [swap]; exact hook_d k k_pos k_lt)
  simp only [swap] at from_L
  refine ⟨?_, ?_, fun k k_lt => ⟨from_R k k_lt, from_L k k_lt⟩⟩
  · have last := from_R (n - 1) (by omega)  -- the last crossing of the connection through `R_c(u_0)`
    rw [show n - 1 + 1 = n by omega] at last
    by_cases n_even : n % 2 = 0
    · rw [ite_eq_right (show ¬ ((n - 1) % 2 = 0) by omega)] at last; rw [ite_eq_left n_even]; exact last
    · rw [ite_eq_left (show (n - 1) % 2 = 0 by omega)] at last; rw [ite_eq_right n_even]; exact last
  · have last := from_L (n - 1) (by omega)  -- the last crossing of the connection through `L_{c'}(u_0)`
    rw [show n - 1 + 1 = n by omega] at last
    by_cases n_even : n % 2 = 0
    · rw [ite_eq_right (show ¬ ((n - 1) % 2 = 0) by omega)] at last; rw [ite_eq_left n_even]; exact last
    · rw [ite_eq_left (show (n - 1) % 2 = 0 by omega)] at last; rw [ite_eq_right n_even]; exact last

end Chains

end Zigzag

end SpectreKnot

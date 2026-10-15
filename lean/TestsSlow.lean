/-
Slower tests: the level-5 entries of the paper's Table 5 and of Remark 10.1 (about 6 minutes), and the conclusion of
the parity lemma (the paper's Prop 7.4) at level 2, computed directly.
Run with `./build.sh --slow`.
-/
import Tests

open SpectreKnot Compose StatementTests

-- N_1 and N_2 lie on a single strand of N_5 (Table 5: k = 4 for b = 1, k = 3 for b = 2)
#guard [nestCount 1 4, nestCount 2 3] == [1, 1]

-- along the chain of Remark 10.1, X_1 still lies on three strands of X_5
#guard chainCount 1 4 == 3

-- the parity lemma (Prop 7.4) at level 2, computed directly (it is proved for every level `m ≥ 1`)
#guard allKinds.all fun T => [true, false].all fun ω =>
  let C := Comp.ofPattern T (letterLen 2) (dOff 2) ω
  C.check ω && C.sigCheck

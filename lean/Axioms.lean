/-
Prints the axioms each main theorem depends on. `build.sh` fails unless they are among Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`): no `sorryAx`, no `Lean.ofReduceBool` (which `native_decide` would add);
and unless every `#print axioms` below has printed its answer. At the end, each main theorem is pinned to its claim in
`Statement.lean`.
-/
import SpectreKnot

open SpectreKnot

-- §3: strands (Lemma 3.4), the decoration and the tile's signature (Def 3.1, Lemma 4.4)
#print axioms StrandSystem.closed_or_path
#print axioms tileBox_proper
#print axioms tile_signature
-- §5: the zigzag lemma (Lemma 5.1)
#print axioms Zigzag.zigzag
-- §5: Prop 5.4, for every well-formed gluing
#print axioms Gluing.prop_5_4_a
#print axioms Gluing.prop_5_4_b
#print axioms Gluing.prop_5_4_c
#print axioms Gluing.fullReach_unique
-- §6: side lengths (Prop 6.1, Prop 6.2, Cor 6.3, Lemma 6.4, Lemma 6.5)
#print axioms sideLen_eq_letterLen
#print axioms letterLen_fib
#print axioms letterLen_parity
#print axioms sideLen_parity
#print axioms dOff_fib
#print axioms bounds
-- §7: the skeleton walks of Remark 7.8 in the kernel, agreement with the JavaScript walk, negative control
#print axioms Skeletons.skeleton_walks
#print axioms Skeletons.agrees_with_js
#print axioms Skeletons.negative_control
-- §7: Computation 7.3, the 18 compositions at the level-1 lengths, from the tables alone; negative control
#print axioms Compose.compositions_level1
#print axioms Compose.compositions_level1_signature
#print axioms Compose.negative_control
-- §7: the lengthening lemma (Lemma 7.1) and the parity lemma (Prop 7.4: Computation 7.3 at every level m ≥ 1)
#print axioms Gluing.Cut.OK.sim
#print axioms Gluing.Cut.OK.sig
#print axioms Gluing.Equiv.sig
#print axioms Compose.Move.OK.equiv
#print axioms Compose.sig_base
#print axioms Compose.parity_lemma
#print axioms Compose.parity_lemma_adj
-- Theorem A (the statement file's `TheoremA`): Thm 7.6 at tile level, by induction from the level-1 clusters
#print axioms Statement.good_one
#print axioms Statement.Kids.follow_of_reach
#print axioms Statement.Kids.noClosed
#print axioms Statement.Kids.parent_sig
#print axioms Statement.own_rot
#print axioms Statement.good
#print axioms Statement.theoremA
#print axioms Statement.loopPatch_closed
-- Theorem B (the statement file's `TheoremB`, `TheoremB_sharp`): the junction map (Computation 9.2, Lemma 9.3) at every
-- level, then the nest
#print axioms Statement.step_base
#print axioms Statement.StepOK.move
#print axioms Compose.adm_induct
#print axioms Statement.step_level
#print axioms Statement.super_glueSymm
#print axioms Statement.linked_symm
#print axioms Statement.step_tile
#print axioms Statement.stretch_eq
#print axioms Statement.chain_even
#print axioms Statement.chain_odd
#print axioms Statement.no_boundary
#print axioms Statement.theoremB_sharp
#print axioms Statement.theoremB
-- The bound is exact (the statement file's `TheoremB_exact`, the last two rows of Table 5): hooks at different
-- vertices lie on different strands, and each of the two strands is reached
#print axioms Statement.Patch.Linked.ends
#print axioms Statement.hooks_apart
#print axioms Statement.theoremB_exact
-- The Grandparent Lemma (the statement file's `Grandparent`, Lemma 8.3(a) at tile vertices): every supertile is a disc
-- at its rim, and the tables make every vertex of N_b surrounded in N_{b+2}; negative control
#print axioms Statement.Patch.surrounded_or_chain
#print axioms Statement.Kids.rimChains
#print axioms Statement.level1Chains
#print axioms Statement.chains_super
#print axioms Statement.delta_cycles
#print axioms Statement.grandparent
#print axioms Statement.rim_not_surrounded
-- Theorem B, final form (the statement file's `NestModel`, `TheoremB_strand`): the nest tiling as one patch, and
-- Lemma 3.4 applied to it
#print axioms Statement.super_noSelf
#print axioms Statement.nestModel
#print axioms Statement.not_closed
#print axioms Statement.all_same
#print axioms Statement.theoremB_strand
-- Theorem A in strand form (the statement file's `ChainModel`, `TheoremA_strand`): the union of any chain of
-- supertiles that covers, and Lemma 3.4 applied to it; and a chain that covers exists (`NestCovers`)
#print axioms Statement.chainModel
#print axioms Statement.Chain.all_glued_at
#print axioms Statement.Chain.not_closed
#print axioms Statement.theoremA_strand
#print axioms Statement.nestCovers

/-! The main theorems prove exactly the claims of `Statement.lean`: each `example` states one claim, as written there,
and gives the main theorem as its proof, so this file fails to build if a main theorem's statement is changed. -/
example : SpectreKnot.Statement.TheoremA := SpectreKnot.Statement.theoremA
example : SpectreKnot.Statement.TheoremB := SpectreKnot.Statement.theoremB
example : SpectreKnot.Statement.TheoremB_sharp := SpectreKnot.Statement.theoremB_sharp
example : SpectreKnot.Statement.TheoremB_exact := SpectreKnot.Statement.theoremB_exact
example : SpectreKnot.Statement.Grandparent := SpectreKnot.Statement.grandparent
example : SpectreKnot.Statement.NestModel := SpectreKnot.Statement.nestModel
example : SpectreKnot.Statement.TheoremB_strand := SpectreKnot.Statement.theoremB_strand
example : SpectreKnot.Statement.ChainModel := SpectreKnot.Statement.chainModel
example : SpectreKnot.Statement.TheoremA_strand := SpectreKnot.Statement.theoremA_strand
example : SpectreKnot.Statement.NestCovers := SpectreKnot.Statement.nestCovers

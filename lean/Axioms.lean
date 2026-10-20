/-
Prints the axioms each main theorem depends on. `build.sh` fails unless they are among Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`): no `sorryAx`, no `Lean.ofReduceBool` (which `native_decide` would add);
and unless every `#print axioms` below has printed its answer. At the end, each main theorem is pinned to its claim in
`Statement.lean`.
-/
import SpectreKnot

open SpectreKnot

-- §3: strands (Lemma 3.4); §4: the box of a patch with the signature (Lemma 4.1), and a tile has the signature
-- (Lemma 4.4)
#print axioms StrandSystem.closed_or_path
#print axioms Statement.Patch.HasSig.box
#print axioms Statement.tile_hasSig
-- The pilot's model of the tile, its 14 pieces as a pairing of its 28 ports (`Box.lean`, not used by the main results)
#print axioms tileBox_proper
#print axioms tile_signature
-- §5: the Zigzag Lemma (Lemma 5.1), for every length
#print axioms Zigzag.zigzag
-- §6: side lengths (Prop 6.1, Prop 6.2, Cor 6.3, Lemma 6.4, Lemma 6.5), and Prop 6.1 for the supertiles themselves
#print axioms sideLen_eq_letterLen
#print axioms letterLen_fib
#print axioms letterLen_parity
#print axioms sideLen_parity
#print axioms dOff_fib
#print axioms bounds
#print axioms Statement.super_side_length
-- §7: Computation 7.3, the 18 compositions at the level-1 lengths, from the tables alone, as the kernel checks it and
-- as the paper words it; negative control
#print axioms Compose.compositions_level1
#print axioms Compose.compositions_level1_signature
#print axioms Compose.sig_base
#print axioms Compose.comp_7_3
#print axioms Compose.negative_control
-- §7: the lengthening (Lemma 7.1): a move is a cut, and a cut keeps the signature, the new path by the Zigzag Lemma
-- with n = 3 (`cross_three`), the new ports by the old ones (`Cut.OK.noLoops`)
#print axioms Gluing.cross_three
#print axioms Gluing.Cut.OK.sim
#print axioms Gluing.Cut.OK.noLoops
#print axioms Gluing.Cut.OK.sig
#print axioms Gluing.Equiv.sig
#print axioms Compose.Move.OK.equiv
#print axioms Compose.Move.OK.keep
-- §7: reachability (Lemma 7.2, an induction principle), and Prop 7.4 (Computation 7.3 at every level m ≥ 1), as the
-- induction uses it and as the paper words it
#print axioms Compose.adm_level
#print axioms Compose.adm_induct
#print axioms Compose.adm_sig
#print axioms Compose.parity_lemma
#print axioms Compose.parity_lemma_adj
#print axioms Statement.sig_of_check
#print axioms Statement.compSig_of_sig
#print axioms Compose.prop_7_4
-- Theorem A (the statement file's `TheoremA`): Thm 7.6 at tile level, by induction from the level-1 clusters
-- (Computation 7.5), the parent's corners where Table 3 puts its Γ child's; and the corner A of a supertile is that of
-- its Γ child (§2.3)
#print axioms Statement.good_one
#print axioms Statement.Kids.follow_of_reach
#print axioms Statement.Kids.noClosed
#print axioms Statement.Kids.parent_sig
#print axioms Statement.own_rot
#print axioms Statement.aPos_succ
#print axioms Statement.good
#print axioms Statement.cornerA_succ
#print axioms Statement.theoremA
#print axioms Statement.loopPatch_closed
#print axioms Statement.compose_no_default
-- Theorem B (the statement file's `TheoremB`, `TheoremB_sharp`): the junction map (Computation 9.2, Lemma 9.3) at every
-- level, then the nest
#print axioms Statement.step_base
#print axioms Statement.StepOK.move
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
-- The Signature Theorem (the statement file's `SignatureTheorem`, Thm 7.6): the conclusion of the induction, with the
-- corners written out (Lemma 6.4), and every supertile a disc at its rim
#print axioms Statement.cornerA_eq_aPos
#print axioms Statement.signatureTheorem
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
example : SpectreKnot.Statement.SignatureTheorem := SpectreKnot.Statement.signatureTheorem
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

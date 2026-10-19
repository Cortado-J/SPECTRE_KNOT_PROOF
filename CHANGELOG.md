# Changes

What changed each time this site was published, newest first: in the paper, the Lean, the code and the pages
themselves. Dates are UK dates.

## 19 October 2026

- **Lean:** the statement changed: a new claim, `SignatureTheorem`, states the paper's Signature Theorem (Thm 7.6) in
  the statement file. Every supertile of level 1 or more is a disc at its rim and has the signature at its crossover
  corners A and B = A + ω_m, with A placed as in Lemma 6.4. The definitions it uses (the rim ports, the
  signature itself, and what it means to be a disc at the rim) moved into the statement file unchanged. The ten
  earlier claims say what they said before. Assumption (M) is worded more exactly: (M1) covers levels 1 and above and
  says how the tiles are numbered, and (M2) gives the step from a tiling to a chain in which every edge is glued.
- **Lean:** Lemma 9.4 is also proved as the paper states it, five edges from the ends of a side. Lemma 3.4 now says
  that the ports met going backwards along a strand are distinct. The induction behind Prop 7.4 makes the same moves
  as the paper's proof. The paper's two negative controls (corners two apart in Computation 7.3; junctions 12 and 16
  exchanged in Computation 9.2) run as tests. Several comments are corrected. None of this changes what the claims
  say.
- **Paper:** the account of the formal verification (§1) lists the differences between the paper's proofs and the
  Lean's more fully. Small corrections in the proofs of Lemma 3.4, the Zigzag Lemma, Lemma 7.2 and Theorem A, in
  Definition 5.2, Proposition 5.4(c) and §7.1 (why §5 applies to the compositions), and in Appendix A.
- **Site:** the guide to the statement file explains the new claim and the definitions it uses. Proposition 5.4 and
  Remark 7.8 are marked as formalised in part. The table of how each Lean statement differs from the paper's is
  brought up to date.

## 15 October 2026

- **Code:** a new check runs Kaplan’s implementation of the spectre’s substitution, the program of the spectre
  authors’ interactive application, and finds the paper’s Table 1 and, tile for tile, the same supertiles up to
  level 4; and, from its tiles alone, the same vertices and side lengths of the level-1 supertiles. Two altered copies
  of that program are rejected. It downloads the program when run (`./run_all.sh --kaplan`): the program is
  published without a licence, so it is not included.
- **Paper:** §2 and the table *What was computed* mention this comparison.
- **Lean:** comparator, the Lean developers’ tool for judging whether proofs prove exactly the statements of a
  trusted file, confirms that the ten main theorems prove exactly the claims of the statement file, using only Lean’s
  standard axioms; the public repository’s checks now run it (`lean/tools/comparator.sh`). A new theorem says that the
  construction of the supertiles never falls back on a default value, at any level. A new test shows that the same
  definitions do find closed strands when the decoration is changed: with the crossing moved to another corner, or
  with no crossing at all. The proofs no longer use lemma names that Lean has deprecated. What is proved is unchanged.
- **Lean:** the statement changed: the link with actual tilings, assumption (M), is written out in its three parts,
  each with where the paper argues it; whole tilings have a type of their own, so that notions meant for finite
  patches cannot be applied to them; and a new claim, proved, says that the nest is a chain of supertiles in which
  every edge is eventually glued, so the final form of Theorem A applies to at least one tiling. The theorems say what
  they said before. The public repository’s checks now also run the slower tests.
- **Paper:** the account of the formal verification (§1) brought up to date: Lean also proves that the bound of
  Theorem 9.1 is exact, and Lemma 8.3(a) at the vertices of tiles; the assumption linking the formal statements to
  tilings has three parts.
- **Site:** each result’s Lean section, and the table on the Lean page, say how the Lean statement differs from the
  paper’s: the same, stronger, weaker, part of it, another form, or not in the paper. The pages of results that are not
  formalised say which part of assumption (M) they belong to.
- **Site:** a drawing beside the overview’s title: the block $N_2$ of the nest with its ribbons in fine lines, and the
  two strands through the first tile picked out.
- **Lean:** the build checks more. Each main theorem is pinned to its claim in the statement file; the statement file
  and the files it imports are recorded by their SHA-256, so a change to what is proved cannot pass unnoticed; names
  must be declared; more ways round Lean’s kernel are refused; and Lean’s `leanchecker` replays every declaration
  through the kernel. What is proved is unchanged.
- **Code:** a new check, run whenever the paper’s programs or the Lean’s data change, confirms that the Lean’s data
  files are exactly what the programs generate.
- **Lean:** now also proves that the bound of Theorem 9.1 cannot be improved: the pieces of $N_b$ lie on exactly two
  strands of $N_{b+2}$, and, if $b$ is odd, of $N_{b+3}$ (the last two rows of Table 5). And Lemma 8.3(a), the
  Grandparent Lemma, at the vertices of tiles: every vertex of every tile of $N_b$ is surrounded by tiles of
  $N_{b+2}$.
- **Site:** five ways in on the overview; the paper’s contents, with the page of every section and result in the PDF;
  a page for every Lean file; a page for the code; a search box on every page.
- **Site:** this list of changes, linked at the foot of every page.

## 14 October 2026

- **Site:** a favicon: the tile, in the site’s green.

## 13 October 2026

- First publication: the paper, with every program its proof uses and their logs; the Lean formalisation of its
  combinatorial part; and this site.
- **Site:** an internal note removed from the source of the overview page.

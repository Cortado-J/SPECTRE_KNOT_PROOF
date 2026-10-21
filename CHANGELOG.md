# Changes

What changed each time this site was published, newest first: in the paper, the Lean, the code and the pages
themselves. Dates are UK dates. From 21 October 2026, each publication that changes the paper, its code or the Lean is
tagged in the repository with its date, so that every published version of them can be found again.

## 21 October 2026

- **Paper:** Appendix A gives the addresses of the public repository and of this site, in place of the ancillary files
  of a paper not on arXiv. Appendix B says that the AI system also searched the literature for related work, and that
  an AI system can reproduce published ideas without naming their source, so the paper may use an idea whose source it
  does not cite; its tool disclosure points to the run log for the versions of the software. Three references are made
  exact: the spectre paper's theorem, figure, section and page numbers refer to its published version; Tatham's paper
  is cited as arXiv version 2; the bohemian-miser project is cited at the commit read. The paper is dated 21 October
  2026 and still has 22 pages.
- **Code:** every run of `run_all.sh` first records its date, system and tool versions, in `logs/A00_environment.log`.
  The logs are those of a new full run (`./run_all.sh --all`), with the same results.
- **Lean:** the README and the note on the `Statement.lean` guide name Justin Roughley instead of "the owner". The
  statement is unchanged.
- **Site:** the overview's title is "The Spectre Knot theorems and their proof". The page description says which
  tilings each theorem covers, and that the proof is a draft, not peer reviewed. About says how to cite the paper, and
  who wrote the parts of this site that are not generated; What has been checked no longer says that the paper gives
  the version of every tool. The repository has a `CITATION.cff`, for GitHub's *Cite this repository*, and each
  publication from today is tagged with its date.
- **Site:** a workflow in the repository, `.github/workflows/tag.yml`, tags each publication; today's first is tagged
  `2026-10-21`.
- **Site:** the README says that Justin Roughley is the author and is responsible for the work, and that the AI is not
  an author.
- **Site:** the overview's five cards are buttons: a click or tap anywhere on a card opens what its title names. The
  links inside a card still go to their own places; "contents" and "every file", which went where their cards go, are
  dropped.
- **Site:** only a publication that changes the paper, its code or the Lean is now tagged, so that each tag is a new
  version of them; the three tags given earlier today to publications that changed only the site are removed.

## 20 October 2026

- **Paper:** shortened from 33 pages to 21, with the argument kept complete and every result on the path to Theorems A
  and B kept under the same number. Dropped: §5.2 (marks, skeletons, Proposition 5.4, Corollary 5.5), which only the
  second routes used; Remarks 3.5, 3.6, 7.7, 7.8, 9.5 and 10.1, cut to a sentence or two in §1, §10 or Appendix A; the
  outline, five illustrations, and the table of what was computed (Appendix A now points to `paper/code/README.md`).
  New: a figure of the route of the proof (Fig. 2) and §3.3, *Strands*.
- **Paper:** the paper and the Lean now take the same route, result by result. Lemma 7.2 ends as an induction
  principle; §7.1 states the finite check that Tables 2 and 3 agree; the Signature Theorem is stated from level 1;
  Theorem A's proof is in two steps, the second the one the Lean checks; Lemma 8.3 is proved from the tables; Lemma 9.4
  says two edges; Theorem 9.1 includes its exactness (Table 5). Appendix B lists the differences that remain, all of
  them bookkeeping.
- **Paper:** the account of how the work was done with AI, and of what the Lean formalisation checks, moves from
  §1 to a new Appendix B, with a new *Tool and computational resource disclosure* listing the AI system, the proof
  assistant, the other software and the computing the checks need; §1 keeps a short note. The abstract and §1 say
  that the paper has not been peer reviewed, and §1 that the author is responsible for the paper, including its
  citations, and that the AI system is not an author. Appendix B says that no human has checked that the Lean's
  formal statements say what the paper's theorems say. Four references are corrected or completed.
- **Lean:** the statement changed, in its opening comment only: assumption (M1) also names step (ii) of §7.1
  (children meet only in the sides they share), as the paper's Appendix B does. No definition or claim changes.
- **Lean:** the proofs follow the paper's. Lemma 7.1 crosses the new path of a cut by the Zigzag Lemma with n = 3, and
  shows directly that a cut creates no closed strand, so Proposition 5.4, dropped from the paper, is no longer needed
  here either: it is removed, with its reduced walk, and so are the skeleton walks, which only checked an earlier route
  again. Lemma 7.2 is one induction principle, used for both the signature and the junction map. Computation 7.3 and
  Proposition 7.4 are stated as the paper words them, and the induction step uses that form; a second kernel check of
  the 18 compositions is no longer needed. New statements in the paper's terms: Proposition 6.1 for the supertiles
  themselves, Lemma 4.4 for a tile, Lemma 4.1 for patches with the signature, and the corner A of a supertile as that
  of its Γ child. None of this touches `Statement.lean`.
- **Site:** every page says, under the menu, that this is a draft proof, not peer reviewed; so do the overview's
  opening paragraph and its line about AI.
- **Site:** the pages follow the shortened paper: the computations each result's page lists come from
  `paper/code/README.md`, step 1 shows the new route figure, and step 10 shows §10 in full.
- **Site:** a new page, What has been checked: what has been checked by Lean, by computer, by the AI and by a
  human, and what has not. The line under the menu on every page links to it, instead of to the public site's Made
  with AI page; so do the overview's line about AI, About and the search box. The public site now links here for
  everything about checking.
- **Paper:** the proof of the Signature Theorem (Theorem 7.6) cites Lemma 4.2 where it uses it, to read the box of
  a supertile off its composition; two phrases in the same proof are shorter, so the paper keeps its 21 pages.
- **Site:** the graph joins Lemmas 4.1 and 4.2 to the rest of the argument again, and fits the page without
  scrolling sideways.
- **Paper:** the contact address at the end of the paper is now cortado.just@gmail.com.
- **Paper:** the related work is wider, with eleven new references: Hooper on a family of Truchet tilings whose
  curves a renormalisation shows to be almost all closed; Gerdes on mirror curves; Gardner on the Conway–Penrose
  arcs; a second paper by Cline, and one by Gaenshirt, on girih interlace on Penrose tilings; Liu, Choi and Mahadevan
  on Hamiltonian cycles through every tile of finite patches; and Gross and Tucker on Celtic knotwork as alternating
  diagrams. §1 mentions knot mosaics (Lomonaco and Kauffman) and the Socolar–Taylor tile, and Appendix B cites
  `leanchecker` and `comparator`. The paper is dated 20 October 2026 and has 22 pages.
- **Paper:** two statements about earlier work are corrected: on Penrose tiles, at most two Conway–Penrose curves
  *of each colour* fail to close (it said at most two in all); and the Hamiltonian cycles of Singh, Lloyd and Flicker
  go through every vertex of arbitrarily large regions of Ammann–Beenker tilings (it said every tile).

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

# Changes

What changed each time this site was published, newest first: in the paper, the Lean, the code and the pages
themselves. Dates are UK dates.

## 15 October 2026

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

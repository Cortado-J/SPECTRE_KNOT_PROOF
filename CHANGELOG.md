# Changes

What changed each time this site was published, newest first: in the paper, the Lean, the code and the pages
themselves. Dates are UK dates.

## 15 October 2026

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

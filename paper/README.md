# A Goldbach theorem for the Liouville function

An authorless paper accompanying the complete Lean proof.

The title is followed by "The problem and its background", with no abstract. The opening credits the MathOverflow user Pablo for the August 2018 question and notes Mangerel's attribution to Shusterman. The paper begins with the Goldbach analogy and the previous literature, explains why positive-positive pairs at twice primes suffice, and then proves the result through commuting defects, short coset representatives, and quadratic reciprocity. The appendix identifies the formal theorem and its verified dependencies.

## Files

- `liouville-goldbach.pdf`: the finished paper, with linked citations and cross-references.
- `liouville-goldbach.tex`: the editable LaTeX source, including the bibliography.
- `verification.json`: document checks, source hashes, and the accompanying Lean verification status.

## Rebuild the paper

Use a current TeX Live or MiKTeX installation with the standard packages listed in the source, including `newtx`, `microtype`, `booktabs`, and `hyperref`. Run from this directory:

```text
pdflatex -interaction=nonstopmode -halt-on-error liouville-goldbach.tex
pdflatex -interaction=nonstopmode -halt-on-error liouville-goldbach.tex
```

The bibliography is embedded in the source; no separate BibTeX run is required. The PDF has no author byline or author name in its metadata.

## Rebuild the formal proof

The combined paper-and-proof archive includes the Lean project in its `lean/` directory. Its README gives the complete build and audit commands. The final theorem is `LiouvilleGoldbach.liouville_goldbach`, using mathlib's actual Liouville function. The versions are pinned to Lean `v4.34.0-rc2` and mathlib revision `de2ef68216c6074f338c8e61890ee0a379ddfb9b`.

The formal code is unchanged from the verified polished proof. Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The paper presents the short-representative argument using cosets; the Lean proof establishes a more general invariant-set formulation and derives the same extension theorem.

## References

The eleven references distinguish published results, preprints, a preliminary repository manuscript, and standard mathematical sources. In particular, the exact nonextremality theorem is cited from Mangerel's published IMRN article, whose conclusion is stronger than the earlier arXiv version. The proof credits Bloom's scaling observation and Mangerel's rigidity and commuting-defect ideas.

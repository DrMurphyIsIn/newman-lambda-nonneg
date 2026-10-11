# arXiv submission sheet

Everything the arXiv form asks for, ready to paste. The source package is `paper/arxiv.tar.gz`
(one file, `paper.tex`, with `\pdfoutput=1` on line 1 and an inline bibliography; no figures, no
.bbl). Rebuild with `paper/make_arxiv.sh`; the page count below is from that build.

## Upload

- **File:** `paper/arxiv.tar.gz`.
- **Processing:** pdflatex (arXiv autodetects from `\pdfoutput=1`).

## Metadata

- **Title:** Newman's conjecture, kernel-checked: Lambda >= 0 for the de Bruijn-Newman constant in Lean 4 along Dobner's proof
  (TeX form: `Newman's conjecture, kernel-checked: $\Lambda \ge 0$ for the de Bruijn--Newman constant in Lean 4 along Dobner's proof`)
- **Authors:** Peter W. Murphy
- **Primary category:** math.NT (Number Theory)
- **Cross-list:** cs.LO (Logic in Computer Science)
- **MSC classes:** 11M26 (primary); 03B35, 11M06, 33B15 (secondary)
- **ACM classes:** F.4.1
- **Comments:** 15 pages. Lean 4 sources, verification records and Comparator transcripts at
  https://github.com/DrMurphyIsIn/newman-lambda-nonneg (v1.1.0), archived at Zenodo, doi:10.5281/zenodo.23292885
  (concept doi:10.5281/zenodo.23287832). The theorem is Rodgers-Tao's (2018) and the proof formalized is Dobner's
  (arXiv:2005.05142), including his extension to the whole extended Selberg class; the contribution is the formalization. Not a proof of the Riemann Hypothesis.
- **License:** CC BY 4.0 (matches `paper/`'s licence in `LICENSING.md`).
- **Report number / journal ref / DOI fields:** leave blank (the Zenodo DOI is the dataset, not the paper).

## Abstract (plain text with light TeX, as arXiv renders it)

Newman's conjecture states that the de Bruijn-Newman constant $\Lambda$ is non-negative; Rodgers and Tao proved it in 2018. We report a formalization in Lean 4, on the Arda project's dbn island, of the theorem in the form Dobner gave it in 2020: for every real $t < 0$ the heat-flowed Riemann $\xi$ function $H_t$ has a zero off the real axis. The proof term depends only on propext, Classical.choice and Quot.sound. Dobner's argument uses no information about the zeros of $\zeta$: it exhibits zeros of $H_t$ directly, by comparing $\xi_t$ at large height with an everywhere absolutely convergent Dirichlet series whose zeros are forced by Hadamard's factorization theorem and moved to every height by Bohr's almost periodicity. The formalization follows that route and departs from it in three places that make it shorter than the paper proof: Rouch\'e is replaced by the zero-free form of Hurwitz's theorem; the Dirichlet expansion of $H_t$ is obtained from the Polymath15 series rather than from $\xi = \gamma\zeta$; and the saddle-point analysis of Dobner's Theorem 4 is carried out with a fixed base point and contours in $\mathrm{Re}\, v \ge 2$, so that no pole of the Gamma factor is crossed and a single pointwise estimate covers every term. Along the way the development acquires kernel-checked infrastructure that Mathlib lacks: Stirling's formula for the complex Gamma function with an explicit remainder on the right half-plane, the digamma asymptotic, Bohr almost periodicity for everywhere convergent Dirichlet series, and the Gaussian-convolution representation of $H_t$. The registry node for the theorem was read back by an independent operator, granted through the registry's gate, and replayed by two kernels (Lean and nanoda) through openai/ten-proofs Comparator against a challenge whose type is the registered statement. Version 1.1 adds Dobner's theorem in full: Newman's conjecture for every element of the extended Selberg class, stated as a Lean structure carrying the class's axioms, with the completed function proved entire and bounded on vertical strips by Phragm\'en-Lindel\"of, and with $\zeta$ as the control instance. Together with the kernel-checked $\Lambda \le 9/32$, the machine-checked range for the constant is $0 \le \Lambda \le 9/32$. The Riemann Hypothesis is $\Lambda = 0$ and is not proved. The mathematics is Rodgers and Tao's theorem by Dobner's proof; the contribution is the formalization, and this paper is its record.

## After the identifier is assigned

1. Add `arXiv:XXXX.XXXXX` to `README.md` (paper section), `CITATION.cff` (an `identifiers` entry of type
   `other` with value `arXiv:XXXX.XXXXX`), `.zenodo.json` (`related_identifiers`: `arxiv:XXXX.XXXXX`,
   relation `isSupplementTo`), and the `\date` line of `paper/paper.tex`.
2. Rebuild (`paper/make_arxiv.sh`), commit, tag `v1.0.1`, and publish a new Zenodo version (new version on
   the v1.0.0 deposition, replace the two files, PUT metadata with `related_identifiers` written explicitly, publish).

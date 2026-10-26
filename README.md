# Conditional parity hashing

**An almost-entropic Ingleton score below −0.09738: Conditional hashing of a binary parity structure**

**Søren Riis — creator and coordinator.**

[Read the paper](https://sr123.github.io/conditional-parity-hashing/) · [PDF](paper/conditional_parity_hashing.pdf) · [DOI: 10.5281/zenodo.23662511](https://doi.org/10.5281/zenodo.23662511) · [Lean source](lean_proof/lean/CertifiedMain.lean)

## Result and construction

Conditional parity hashing improves the known lower bound on the largest normalised Ingleton violation for four-variable almost-entropic vectors to **0.097387436922**. The limiting signed score is enclosed rigorously in

```
[-0.097387436923, -0.097387436922].
```

The construction combines local binary parity labels, one common linear hash, simultaneous conditional privacy amplification and joint conditioning. Applied to a rational 24-atom specialisation of Matúš and Csirmaz’s published source, it subtracts a multiple of the uniform-matroid rank function U(3,4) from all fifteen entropy coordinates. Previously reported constructions reach approximately 0.0925, used as a rounded benchmark; the paper cites the best published universal upper bound, 19/124 ≈ 0.15322581.

The endpoint is proved almost entropic, and finite-alphabet distributions with signed score below −0.09738 exist. The original 24-atom source itself has the weaker signed score of approximately −0.0836547. No practical successful block length, hash matrix or conditioning fibre is supplied. Exact finite realisability of the endpoint, global optimality and extremality remain open.

## Contents

- `paper/`: PDF and all LaTeX manuscript sources.
- `lean_proof/lean/`: 27 proof modules and the verification module.
- `lean_proof/evidence/`: the successful fresh kernel rebuild report and per-module axiom reports.
- `checks/`: two independent exact numerical checkers using only the Python standard library.
- `docs/`: the public reader page and the same PDF.

## Formal verification

`ConditionalParityHashing.certified_main` proves the complete closed rate interval, positive denominator, exact rational score enclosure and existence of a finite law with signed score below −0.09738. The general six-test reduction and finite-coordinate closure/source bridges are also formalised.

A fresh local rebuild on 26 October 2026 checked **28 modules and audited 281 declarations**. The main theorem uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The report is [here](lean_proof/evidence/latest_verification.json). The finite sampling recipe and fixed-path optimality argument are written proofs rather than separate Lean declarations.

### Rebuild Lean

Install the official [elan toolchain manager](https://github.com/leanprover/elan), then run:

```sh
cd lean_proof
lake update
lake exe cache get
lake build
lake env python3 build_verify.py
```

Lean is pinned to **4.35.0-rc2** and Mathlib to commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The final script compiles the research sources in a fresh directory, verifies source hashes and audits their axioms. See [the detailed instructions and statement map](lean_proof/README.txt). Dependency downloads require internet access. Dependencies and compiled research objects are not distributed.

### Check the finite data

Python 3.10 or newer; no external packages:

```sh
python3 checks/verify_paper.py
python3 checks/independent_source_audit.py
```

The checkers verify all fifteen source marginal entropies, the privacy thresholds, the rational score enclosure and the strict subcritical finite-score margin. They do not replace the almost-entropic membership proof.

### Build the paper

With a standard TeX distribution including TikZ and Latin Modern:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Keep the included TeX files beside `main.tex`.

## Credit and provenance

Søren Riis directed and coordinated the research. Astra/Codex and Claude contributed mathematical development, computation and verification; Claude contributed the Lean formalisation and adversarial review, and Astra/Codex checked the formal statements and rebuilt the proof package. These AI-assisted checks do not constitute independent human peer review.

The finite source is due to **František Matúš and László Csirmaz**, *Entropy region and convolution*, IEEE Transactions on Information Theory 62(11), 6007–6018 (2016), [doi:10.1109/TIT.2016.2601598](https://doi.org/10.1109/TIT.2016.2601598). The paper credits the earlier entropy-region, information-inequality, convolution, tightening and privacy-amplification work in full. No researcher named in those references is claimed as a coauthor or endorser of this preprint.

## Citation and licences

Use the paper’s DOI **[10.5281/zenodo.23662511](https://doi.org/10.5281/zenodo.23662511)** to cite this version of the paper-and-proof package. GitHub also provides citation metadata through [CITATION.cff](CITATION.cff).

- Paper PDF, LaTeX sources and original paper figures: **CC BY 4.0**, as described in [LICENSE-PAPER.txt](LICENSE-PAPER.txt).
- Lean source, numerical checkers, build scripts and other code: **Apache-2.0**, in [LICENSE](LICENSE).
- Third-party dependencies retain their original licences.

This is a research preprint, version **1.0.0**, dated **26 October 2026**. No journal publication or acceptance is implied.

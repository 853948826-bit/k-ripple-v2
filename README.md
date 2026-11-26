# k-ripple-v2

Code, machine-checked proofs and analysis materials for the preprint

> **Saturated Signed Ripple Dynamics on Directed Networks: Machine-Checked Theory and a Preregistered Empirical Test** (v0.1, November 2026)

The model is `r(t+1) = D(t) r(t) + W(t) tanh r(t) + s(t)`. Here `r` is a signed, unbounded state, `D` is retention, and `W` is a signed, unnormalised influence matrix. The paper proves boundedness, contraction certificates, a scalar regime map indexed by the signed gain `K = d + w`, a frustration-attenuation inequality, identifiability criteria and a global input–response gain formula. All proofs are in Lean 4 with Mathlib. The paper also reports two lightweight-preregistered fits on the Bitcoin OTC signed network, which mostly gave negative results.

DOI: *assigned by Zenodo at the first release; it will be added here.*

## Contents

| Path | What it is |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | Preprint (CC BY 4.0). Compile with XeLaTeX, for example `tectonic main.tex`. |
| `paper/gen_lean_appendix.py` | Regenerates `paper/lean_statements.tex` (Appendix A) verbatim from `lean/KRippleV2.lean`. |
| `lean/KRippleV2.lean` | The formal development: 1,907 lines, 50 theorems, 63 lemmas, no `sorry`, axioms limited to `propext`, `Classical.choice`, `Quot.sound`. SHA-256 `b9f8fa17691531c0625648de6530cfd6859c3fdf108b0a8c0a038879cbe37ce3`. |
| `numerics/analyze.py` → `RESULTS.json` | Synthetic checks of the propositions (Section 5 of the paper), seed 20261118. |
| `numerics/numeric_checks.py` → `numeric_checks.json` | Standard-library-only checks of the critical rate (Theorem 5) and the signed-gain example (Section 3.5). |
| `empirical/bitcoin_otc/` | Preregistered plans (`PLAN*.md`) with their recorded hashes (`PLAN*.sha256`), analysis scripts, outputs and reports for the two Bitcoin OTC rounds (Section 6). |

The `REPORT*.md` files and the plans are written in Chinese, the language the analyses were conducted in. The paper is the English summary of record.

Some files mention paths in the authors' private working repository, such as `01_THEORY_CORE/...` or `07_EXPERIMENTS/...`. These files are published byte-for-byte unchanged, so that the recorded SHA-256 hashes still verify. The draft they point to is superseded by the paper.

## Verifying the Lean proofs

```
cd lean
lake exe cache get   # downloads prebuilt Mathlib
lake build
```

The development was built with Lean `v4.34.1` against Mathlib tag `v4.34.1` (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`), using a local checkout of that exact commit. The build had zero warnings and took about 40 seconds with a cached Mathlib. The git-based `lakefile.toml` in this repository points to the same tag. It has not been re-tested from a clean clone.

## Reproducing the numbers

- `python3 numerics/numeric_checks.py` uses the standard library only.
- `python3 numerics/analyze.py` needs numpy and scipy (see `requirements.txt`) and takes about 15 seconds.
- Empirical scripts:
  1. Download the data (it is not redistributed here): https://snap.stanford.edu/data/soc-sign-bitcoinotc.csv.gz. The expected SHA-256 is `6424ac981dad3a019f697fc1b9fcd85c19d8d9f039797758e9ffb6fea100c373`, and the scripts check it.
  2. Run:
     ```
     python3 empirical/bitcoin_otc/fit.py soc-sign-bitcoinotc.csv.gz
     python3 empirical/bitcoin_otc/fit_v2.py soc-sign-bitcoinotc.csv.gz OTC
     ```

The reported outputs were produced on 2026-11-18 with the versions in `requirements.txt`. They have not been re-run in a clean environment for this release.

## Provenance and limits of the preregistration

Before each round of fitting, its analysis plan was written and hashed on 2026-11-18, at 03:46:20Z and 04:07:57Z respectively. The hashes were recorded in the authors' private working repository. **They were not externally timestamped.** This public repository was created on 2026-11-27. The hashes show that the plans in this repository are the ones the scripts implement. They cannot by themselves prove that the plans preceded the analyses. The paper states this explicitly. Future confirmatory runs will be preregistered publicly first.

## AI-use statement

The formal proofs, analysis scripts and the drafting of the manuscript were done with the assistance of an AI coding agent (Claude Code, Anthropic). Every theorem labelled as verified is checked by the Lean kernel, and every reported number is produced by a script in this repository. Responsibility for the content rests with the author.

## Licence

- Code and Lean proofs: MIT (`LICENSE`).
- Manuscript: CC BY 4.0 (`paper/LICENSE.md`).
- Bitcoin OTC data: please cite Kumar et al., ICDM 2016, and the SNAP collection.

## Citation

See `CITATION.cff`. The Zenodo DOI will be added after the first release.

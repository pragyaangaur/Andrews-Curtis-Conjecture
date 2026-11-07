# Third-party inputs of the audit

All fetched 2026-11-05 from the URLs below. The two large AC-19 files are not
duplicated in this directory; run `../fetch_sources.sh` to download them and to
print every hash.

| file | source | sha256 |
|---|---|---|
| `twohump/classification_table.tex` | arXiv:2606.21611v1 e-print, Table 2 | `e4a6b2a9270d039ca160758adb792c1603b56364975081d2a1e4e5899f94ab72` |
| `twohump/counterexamples_table.tex` | arXiv:2606.21611v1 e-print, Table 3 | `49f622603fdbed86a6093194e8e43b79e66531758bed8ffb2daac59179d434a1` |
| `ac19/1190MS.txt` | `https://raw.githubusercontent.com/Math-AI-Caltech/ACSolverX/main/data/1190MS.txt` | `81323166e956b35e3c816fccdcad3507e7978d6291da13bfda6a45de5763cdf2` |
| `ac19/AC19.txt` (fetch) | `.../data/AC19.txt` | `f72df134e4deca4cb9c040099b6e09b2b45516f9aa460fc460a120669f1f1e19` |
| `ac19/AC19_extended.txt` (fetch) | `.../data/AC19_extended.txt` | `d028cd4d54f9204be8b2d811f9b6d428bc2920fa83a0e2143a32ad52f55660c0` |
| `audited/manuscript.tex` (fetch) | arXiv:2607.23611v1 e-print | `12bddfacfae57d5a6b014da5a65d64a3db7ba9b20f9b24e378efcf5cd47d8e5f` |

The two e-prints are fetched as `https://arxiv.org/src/2606.21611` and
`https://arxiv.org/src/2607.23611`, both gzip tarballs.

The AC-19 data files are released by the ACSolverX repository under its own data
licence (`LICENSE-DATA` in that repository). They are third-party data, cited
here and not redistributed.

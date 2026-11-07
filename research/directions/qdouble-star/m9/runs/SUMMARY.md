# The search runs behind Section 7 of `round4-m9.md`

One line per instance is in the log files below. Every run is deterministic:
seeded at 20261104, and the score is total relator length. "canonical" is
`cfsearch.py`, the canonical-form engine; "round 3" is `../qstar.py`, unmodified,
driven by `runpush.py`. No run found a path.

| log | target | engine | cap | rank | budget per instance | instances | outcome |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `cf_ak3.txt` | AK(3) | canonical | 24 | 3 | 20,000 | 1 | no path, 512,260 states pushed, best length 13, 618 MB peak |
| `m10_ak3_rank4.txt` | AK(3) | round 3 | 26 | 4 | 25,000 | 1 | no path, best length 13, 26 s |
| `cf96.txt` | the 96 Q*-open resisters of `../table_open.md` | canonical | 24 | 3 | 10,000 | 96 | no path, 96 of 96, 315 MB peak |
| `m10_96_rank4.txt` | the same 96 | round 3 | 26 | 4 | 20,000 | 96 | no path, 96 of 96 |
| `m10_l13_cap26.txt` | the six length-13 resisters | round 3 | 26 | 3 | 50,000 | 6 | no path, 6 of 6 |
| `m10_l13_rank4.txt` | the same six | round 3 | 26 | 4 | 20,000 | 6 | no path, 6 of 6 |
| `cf_metzler.txt` | Metzler's pair, first to second | canonical | 30 | 3 | 20,000 | 1 | no path, 647,837 states pushed, 881 MB peak |
| `pos.txt` | Metzler's pair, first attempt | canonical | 30 | 3 | 150,000 | 0 | cut off by the caller's time limit after 43 minutes; no line written |

The last row is kept because it is a measurement: at 150,000 expansions the
canonical engine needs about 4.5 GB, so the run was killed by the caller before
it wrote its line. It is the reason every other canonical run stays at or below
20,000 expansions.

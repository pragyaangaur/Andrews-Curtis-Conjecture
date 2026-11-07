# directions/cap25 -- round 7, member m9, direction J3

The report is `cap25-round7.md`. Everything in it reruns from this directory.

Headlines: class C is AC-trivial at peak exactly 18 and all sixteen states of its length-13
PU level set are AC-trivial (so class C is AK(3)-equivalent if and only if AK(3) is
AC-trivial, and the whitehead Section 9 caution is withdrawn); the six other length-13
resisters are AK(3)-equivalent at peak exactly 19; the closed boxes nest exactly and are not
layer-stable, with the additions tabulated per total length for caps 21 to 24; bounded-shape
detour probes are a recorded dead end; the closed cap-25 box is out of reach this round and
T = 17 at cap 25 stays open.

Files:
  stdball.c    my in-RAM twelve-move box search, standard pair or explicit target
  box.c        streaming exact per-stratum histogram and k-way merge join of two boxes
  keytool.c    sample reader: count, min, max, sortedness, key-layout test
  probe.c      the bounded-shape detour probe of the report's Section 6
  accheck.py   my own replayer for the campaign's certificate lines
  RESULTS.txt  the raw output of every table in the report
  diff_2*.txt  the four merge joins of Section 5
  punf_*.txt   the PU canonical forms of the length-13 rows (directions/cap24/punf.py)
  cc8.txt cc8b.txt cc8c.txt ak6.txt  the row lists used for the replays

Build and run:

    gcc -O3 -march=native -o stdball stdball.c && ./stdball 15 "abaBAB,aaaBBBB"
    gcc -O2 -o box box.c && gcc -O2 -o keytool keytool.c
    gcc -O3 -march=native -o probe probe.c
    python3 accheck.py <certificate file> <start-pair list>

The box key files are not copied here (they are 40 GB); their locations are named in the
report's Section 8.

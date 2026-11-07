"""Check that the 800 presentations missed at relator length 5 are reached at 6.

Run from the repository root:

    python3 toolkit/runs/gap_check.py
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import bfs as B

def main():
    five = B.bfs_from_standard(2, 5, 2)
    gap5 = B.box_gap(five, 2, 5)
    print("rank 2, relator length 5, conjugator length 2")
    print("  component %d, filtered box %d, missed %d"
          % (len(five["dist"]), gap5["passing"], len(gap5["missing"])))
    six = B.bfs_from_standard(2, 6, 2)
    print("rank 2, relator length 6, conjugator length 2")
    print("  component %d, largest radius %d"
          % (len(six["dist"]), len(six["layer_sizes"]) - 1))
    still = [v for v in gap5["missing"] if v not in six["dist"]]
    print("  presentations missed at length 5 and still missed at length 6: %d" % len(still))
    print("  the component at length 6 contains the whole length 5 filtered box: %s"
          % (len(still) == 0))
    print("  layer sizes at length 6: %s" % (six["layer_sizes"],))

if __name__ == "__main__":
    main()

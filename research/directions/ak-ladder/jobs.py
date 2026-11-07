"""Job driver: run ball searches and store certificates and statistics.

Usage: python3 jobs.py JOB [JOB...]

Each job is a name understood by start_target(); on success the certificate
(the list of forward-move tags) is written to certs/<job>.json together with
the start and target tuples, and replayed from scratch by verify_cert.py.
"""

import json
import os
import sys
import time
import acx
import ball


def start_target(job):
    if job.startswith("ms") and "_to_n11" in job:
        n = int(job[2])
        k = int(job.split("_w")[1].split("_")[0])
        return job, acx.ms(n, acx.w_word(k)), acx.n11(n)
    if job.startswith("ms") and "_to_w" in job:
        n = int(job[2])
        k0 = int(job.split("_w")[1].split("_")[0])
        k1 = int(job.split("_to_w")[1])
        return job, acx.ms(n, acx.w_word(k0)), acx.ms(n, acx.w_word(k1))
    if job.startswith("ak") and "_to_n11" in job:
        n = int(job[2])
        return job, acx.ak(n), acx.n11(n)
    if job.startswith("ak") and "_to_ms" in job:
        n = int(job[2])
        k = int(job.split("_w")[1])
        return job, acx.ak(n), acx.ms(n, acx.w_word(k))
    raise SystemExit("unknown job %r" % job)


JOBS = {
    # job name            : (total length cap, depth, conj_len)
    "ms3_w3_to_n11":   (17, 20, 2),
    "ms4_w3_to_n11":   (20, 20, 2),
    "ms5_w4_to_n11":   (23, 20, 2),
    "ms6_w5_to_n11":   (26, 20, 2),
    "ms7_w6_to_n11":   (29, 20, 2),
    "ms8_w7_to_n11":   (32, 20, 2),
    "ms3_w1_to_w2":    (19, 24, 2),
    "ms3_w2_to_w3":    (19, 24, 2),
    "ms4_w1_to_w2":    (22, 24, 2),
    "ms4_w2_to_w3":    (22, 24, 2),
    "ak3_to_n11":      (16, 22, 2),
    "ak4_to_n11":      (18, 22, 2),
    "ak3_to_ms3_w1":   (16, 22, 2),
}


def main():
    os.makedirs("certs", exist_ok=True)
    for job in sys.argv[1:]:
        cap, depth, conj_len = JOBS[job]
        name, start, target = start_target(job)
        t0 = time.time()
        print("=== job %s  start total %d  target total %d  cap %d  depth %d"
              % (name, acx.total_length(start), acx.total_length(target),
                 cap, depth), flush=True)
        moves = ball.ball(start, target, cap, depth, conj_len, max_states=3000000)
        secs = round(time.time() - t0, 1)
        if moves is None:
            print("NOT FOUND  %s  (%.1f s)" % (name, secs), flush=True)
            with open("certs/%s.fail.txt" % name, "w") as f:
                f.write("no certificate: total length cap %d, depth %d, "
                        "conjugator length %d, %.1f s\n"
                        % (cap, depth, conj_len, secs))
            continue
        ok = acx.verify(start, moves, target, len(start))
        print("FOUND %s: %d forward moves, replay %s, %.1f s"
              % (name, len(moves), ok, secs), flush=True)
        with open("certs/%s.json" % name, "w") as f:
            json.dump({"job": name,
                       "start": [list(r) for r in start],
                       "target": [list(r) for r in target],
                       "moves": [list(m) for m in moves],
                       "length": acx.total_length(start),
                       "target_length": acx.total_length(target),
                       "cap": cap, "depth": depth, "conj_len": conj_len,
                       "seconds": secs, "replay_ok": ok}, f, indent=1)


if __name__ == "__main__":
    main()

# Windows smux diagnostic exceeds the enforced compile RSS cap

Status: OPEN. No smux executable, runtime feature pass or compiler admission
follows from these attempts. Bug database registration awaits its canonical
checksummed writer.

Producer is the Hello-tested but unadmitted diagnostic compiler SHA-256
`bad4c7fced5d4c945a24a3deb8f601685446a76dbbe2ace5938feeccaea1b04a9`, derived
from frozen f612. Source is a private capsule of 3636b716 with the exact sleep
owner selected directly and a reviewed temporary local socket receiver.
Canonical source retains its original nested receiver for the compiler fix.

Evidence root:
`D:/dev/simple-smux-upstream-20261017/build/smux-diagnostic-capsule/`.
The first real capsule build cleared HIR/MIR 92/92, then failed because its
SPL-only snapshot omitted a backend C ABI header. The exact frozen header was
copied, with equality/hash recorded; no C implementation was invented.

| Retained attempt | Configuration | Terminal Job result |
| --- | --- | --- |
| `smux-build-attempt3` | Default optimization; exact missing header supplied | RSS exceeded; 5,865,220 KiB peak against 5,859,375 KiB; exit 88, quiescent 1 |
| `smux-build-attempt4` | Supported `--opt-level=none`, private cache/output | RSS exceeded; 5,862,400 KiB peak against the same cap; exit 88, quiescent 1 |

Both receipts record complete measurement budgets. No output executable exists.
The helper's root_exit_raw=0 is not a successful build verdict when the owned
Job fails its RSS policy. Both peaks are constrained by termination near the
cap and cannot establish an optimization memory improvement.

No resource check was disabled or raised. The old-producer diagnostic lane
stops after this changed-configuration comparison. Retain all source hashes,
cache entries, object artifacts, stdout/stderr and receipts. The canonical
3636b716 rebuild remains a separate live owner with its normal checks.

Next evidence must use the new exact producer, preserve original-form compiler
regressions, and measure process-tree RSS plus elapsed time. This evidence does
not yet attribute the peak to retained parent AST/MIR state, child compilation
or native C/LLVM optimization; do not claim a memory-owner fix without that
attribution and a comparable regression.

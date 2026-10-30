# Windows outer wall can lose buffered worker diagnostics

The pure-Simple P2 compiler built from fa967a99dcb captures its native worker's
stdout/stderr through anonymous Windows pipes in `runtime_process.c`. The parent
drains into heap buffers and returns the strings only after the child terminates.
The outer finite Job guard can terminate both before the coordinator publishes
those strings. A small outer log therefore does not prove an idle worker.

The first private attempt to preserve output also exposed malformed SDN: a UTC
timestamp was written on the line after its key. The strict parser now rejects
that form; fractional UTC timestamps retain all seven CIM digits.

`scripts/bootstrap/owned_worker_wall_drain_windows.py` provides an explicit
diagnostic child-only cutoff. It requires a reviewed, hash-bound plan, actual
immutable workload spec/launch argv pins, matching finite guard/collector walls,
an 8 MiB collector and monitor-only resource policy. It retains native process
handles for guard, parent, worker and ancestry intermediates; validates creation
times, image hashes and parent edges; rejects worker descendants; and grants
termination rights only to the worker handle. UTC and monotonic checks preserve
at least 25 seconds parent grace after a target configured at least 30 seconds
before the unchanged outer wall. The original Job remains the cleanup owner.

The helper reserves an exclusive durable action receipt with exact plan/helper
and process identities before the action. A deliberate cutoff never becomes a
natural compile failure or successful compile. Capture completeness requires
independent coordinator/collector terminal receipts, matching log size/hash,
absence of overflow and actual Job quiescence. A child can spawn between the
last snapshot and termination: that residual race remains visible, and the
finite outer Job remains mandatory. No policy packet is synthesized or replayed.

Private focused Windows fixtures verified exact 2,097,194-byte capture, deadline
and ownership negatives, and subsequently held four-process ancestry with
exact 102,400-byte capture. Astra independently reviewed helper 700fb69905b8.
A further reviewed integration used the actual campaign Perl watchdog, native
Job helper fc62219b and collector 17f0935e: 60-second outer/collector wall, 12-second
drain, 24 requested jobs, monitor-only memory and 8 MiB logging. Worker/parent/outer
all retained 124; the full 2,097,194-byte stderr was captured and the Job was
quiescent. The workload stayed explicitly incomplete. This is harness FIXTURE
evidence, not compiler, Phase3 or whole-suite qualification.

The repository helper additionally enforces workload/argv hashes and reviewed
CLI plan/helper hashes. Its focused authority-binding regression is
`python scripts/check/check-owned-worker-drain-binding-windows.py --output <new-dir>`.
Concrete launcher integration still requires independent review and its own
actual terminal evidence. No full bootstrap was launched for this change.

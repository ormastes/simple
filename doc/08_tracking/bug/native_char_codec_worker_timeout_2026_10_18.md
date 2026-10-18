# Native CharLit codec qualification exceeds its 600-second worker budget

Canonical ID: `native_char_codec_worker_timeout_2026_10_18`.
Status: OPEN; authoritative bug DB reconciliation pending a qualified full CLI.
Owner: native-build worker startup and phase-progress lane, currently unassigned.

The third and final focused character-codec attempt used immutable compiler
`b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab`, source
`ebd27e64134103786f3f7f0c27866f73ed4d0260`, and the actual generated-codec
fixture `test/fixtures/repro/compiler/char_wire_codec/main.spl`.
The fixture SHA-256 was
`aae77504d858b316db26f721e05a06df5dedc2d3ccb3913157bae91754fa1f01`.

The public native-build command selected Windows MSVC, LLVM, all of
`src/compiler`, `src/lib`, and `src/os` under `--entry-closure`, four jobs,
`--timeout 480 --keep-going --keep-intermediates`, one-binary mode, the genuine
`core-c-bootstrap` runtime bundle, and `SIMPLE_NO_STUB_FALLBACK=1`.
The separate entry-bound cache is `C:/dev/p4char3/cache`; the earlier scalar
entry cache at `C:/dev/p4char/cache` was preserved untouched. No cache identity
stamps, producer bytes, runtime providers, or source snapshots were forged.

The external reproduction script and launch log are
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/char-wire-codec-probe-cycle3.shs`
and its sibling `.launch.log`. Evidence is retained at `C:/dev/p4char3`:
`admission.env`, `input-pins.env`, `compile.stdout.log`, `compile.stderr.log`,
`guard.env`, and the complete cache. A fresh 74 GiB availability gate passed
with 81,717,702,656 physical bytes and 116,023,943,168 commit bytes available.
The process-tree cap was 8 GiB with a 600-second outer deadline.

Observed progress was HIR **100/100 succeeded, zero failed, zero cached** at
profile elapsed 46,219 ms. This is HIR evidence, not MIR or executable evidence.
The controller PID was 38856. Earlier child 43572 exited; subsequent child
31236 ran the genuine compiler's `run src/app/cli/native_build_worker.spl`
entry with the requested build arguments. At 14:20:18 KST it had consumed
at least 329.62 CPU seconds, with an earlier sampled RSS of 888 MiB. The last
phase record remained HIR completion. The exact internal stage after that
record is unknown; no MIR completion or module-specific MIR failure was
observed. This does not prove a new source regression or identify the worker's
internal bottleneck.

The authoritative guard receipt is terminal: `status=timeout`,
`exit_status=124`, `root_pid=33180`, `peak_rss_kib=2974508`,
`quiescent=1`, `session_helper_integrity=verified`, and
`timeout_signal=job-terminate`. The outer command session 66114 drained with
exit 1. There is no `result.env` or fixture execution result. The cache retained
106 `.fpc` files, 100 queue terminal records, and zero `.o`/`.obj` files. A
`CACHE_STORED` queue record and a 95-entry warm-candidate receipt are present;
neither establishes a successful subsequent cache hit or persisted reusable HIR.

Qualification remains BLOCKED. No fourth native attempt was started. The
earlier scalar-cast prerequisite PASS is recorded separately in
`native_text_scalar_validation_failure_2026_10_18.md`; it does not qualify the
full generated codec. Follow-up should inspect worker startup/phase progress
using the retained evidence and preserve the entry-bound cache. Broader tests,
MIR/link/runtime qualification, full compiler linking, deployment, and release
admission remain pending.

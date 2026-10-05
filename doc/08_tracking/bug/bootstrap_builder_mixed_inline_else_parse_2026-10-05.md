# Bootstrap builder mixed block and inline else parse failure

Status: OPEN; source workaround implemented, native verification pending.

The actual new Phase 2 producer (3bd45885) failed the Cranelift buildrunner
entry before HIR/MIR/linking. Its frozen source 916be6 reported unexpected
colon tokens at worker.spl:259:60 and grouped_native_run.spl:555:42.
Evidence is the buildrunner row in the executable-batch20-review packet's
batch-state.json under runtime/windows-restart-20261004.

Four expressions begin a multiline if body, then append `else:` to that
body's expression on the next line. The current parser rejects this mixed
form. The workaround gives else its own aligned branch in the crash-exit
selection and memory/disk/commit minimum selections. Values, evaluation
order, failure propagation and memory admission policy are unchanged.

The native fixture test/fixtures/compiler/bootstrap_multiline_if/main.spl
covers positive signal, absent signal, zero exit, both minimum orderings,
and equal zero capacities. It must compile and execute with exit zero and
exactly `bootstrap multiline if: 6 checks, 0 failures` before claiming PASS.
The full buildrunner entry must also get beyond the reported parse errors.
Both native checks remain UNRUN; this change does not fix later link errors.

Do not silently treat the rejected mixed form as supported. If that syntax
is intended to be accepted, add a separate parser regression retaining the
original form before retiring this source workaround. Frozen active sources
and cached successful artifacts are not modified by this patch.

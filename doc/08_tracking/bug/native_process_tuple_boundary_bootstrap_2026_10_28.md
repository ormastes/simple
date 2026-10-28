# Native process tuple boundary in the bootstrap compiler

Status: OPEN — source repair has bootstrap diagnostic evidence only; the
self-hosted compiler and release gates remain unverified. Owner: native process
capture / bootstrap continuation.

The native process tuple providers return a raw three-word block. In the
seed-produced Stage 2 compiler, a language-level caller destructures the
adapter result using `rt_tuple_get`, which expects a managed tuple. A macOS
Stage 2 identity query therefore received nil output and a failure code even
though its `ps` child exited zero and printed the executable path.

On 2026-10-28, the focused bootstrap fixture
`test/fixtures/native_process_tuple_boundary_probe.spl` was built with the
retained Phase 1 seed and core-C runtime. Before the source repair, it exited
1 with an invalid array-handle error and `FAIL destructure status=3`. After
the repair, it exited 0 and printed `PASS native process tuple boundary`; the
fixture checks direct and public calls, destructuring and field access, UTF-8,
stderr, exit 7, empty output, and a missing command. The existing
`check-native-process-capture.shs` also passed its 11 cases against a newly
seed-built diagnostic executable. These are bootstrap diagnostic results,
not self-hosted CLI, release, or SPipe admission evidence.

The repair reads the provider's raw fields and reconstructs a language tuple
outside the unsafe call. The block's existing allocation ownership is not
changed. The output strings are copied, so peak memory can include both the
provider's output and the copies.

The seed-built retention probe
`test/fixtures/native_process_capture_retention_probe.spl` completed 32 bounded
256 KiB captures with correct output. `/usr/bin/time -l` reported a maximum
resident set of 56,016,896 bytes for the timed wrapper invocation. This is a
single bounded diagnostic, not a no-leak proof or self-hosted performance
qualification; the unbounded capture path still needs representative repeated
capture and lifetime evidence.

The first repair attempt used multiline conditional expressions around the
unsafe string copies; the seed native build failed with `llvm global load
referenced undeclared symbol stderr`. Replacing those expressions with explicit
assignments built successfully. The failing adapter assigned `stdout` and
`stderr` using `val stdout = if stdout_len == 0: "" else:` followed by an
indented `unsafe(...): rt_string_new(...)` expression, and the analogous
`stderr` expression. The retained output is
`/tmp/native-tuple-repair-build-20261028.log`. This is a separate compiler
syntax/codegen defect; its exact minimal grammar reproducer is not yet isolated.

Next: verify the adapter with a qualified self-hosted backend and runner,
rebuild and admit Stage 2 with unmodified normal gates, and run lint, SPipe,
and applicable release checks. Preserve the failed original Stage 2 and the
diagnostic logs; do not promote seed-built fixture results to release evidence.

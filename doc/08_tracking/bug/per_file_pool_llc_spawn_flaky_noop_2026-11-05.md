# Per-file pool: llc subprocess intermittently never runs (process facade returns success with no child) (2026-11-05)

Status: symptom hardened with a retry in
`src/compiler/70.backend/backend/llvm_backend_tools.spl`
(`compile_ir_to_object` re-runs the identical llc invocation when the object
file is missing, up to 2 attempts). ROOT CAUSE NOT FIXED: the runtime
process facade intermittently reports success without spawning the child.

## Related campaign blocker found the same night (stage2 test matrix)

The stage-2 compiler test campaign (mandatory before any Stage 3 resume)
could not be driven to green on 2026-11-05 (12 lane attempts). After the
RSS-cap and AOP-closure blockers below were fixed, the remaining failure is
in the ADMITTED stage2 binary's parse fanout: parse shards either SIGSEGV
(exit -139, attempt 11) or spin at 100% CPU for 25+ minutes with flat RSS
(attempt 12, `parse_shard_main.spl` child). This is a pre-existing compiler
defect in the current tree (not in the file-based-default changes: those
touch routing, env reads, and codegen retry only) and needs a dedicated
debug session (see .claude/rules/bootstrap.md T0/T1 probes) before the next
bootstrap campaign. Phase 3 was NOT resumed (rejection.env policy: do not
resume until the test failure is understood).

## Symptom

Per-file worker pool builds (default route since the `env_get_nullable`
fix today) intermittently fail a module with:

```
[llvm-tools] write-at:done
[llvm-tools] llc-done
[llvm-tools] read-bytes
[llvm-tools] bytes-nil
[ERROR] MIR shard error: AOT compile error in <module>: Compile error in
backend (llvm): Failed to read compiled object file: <tmp>/simple_llvm_<pid>.o
```

`llc` exits "success" but never creates the object. Process observation
during a failing run: NO `llc` and NO `/bin/sh -c` processes ever appear --
`process_run("/bin/sh", ["-c", cmd])` (backend/io_compat.spl) returned
`("", "", 0)` without a child.

## Reproduction (admitted stage2 from the 2026-11-05 lane, aarch64 host)

UPDATE (same day, later lane): a retry hardening in `compile_ir_to_object`
(llc-retry when the object is missing) did NOT save the build -- the log shows
`llc-retry 1`, `llc-retry 2`, then `llc-no-object`. The facade is inert for
the AFFECTED CHILD'S ENTIRE LIFETIME (every spawn in that process no-ops), not
per-spawn. Until the runtime is fixed, the planner receipt build and the
phase-C campaign tool builds pin `SIMPLE_FILE_WORKERS=0` (the documented
per-invocation phase-route opt-out); the file-based default remains for the
stage lanes and ordinary builds (the 1567-module Stage 2 pool build passed
repeatedly).

## Original reproduction

```
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BOOTSTRAP=1 \
SIMPLE_RUNTIME_PATH=<stage2-runtime-authority> \
<stage2-admitted>/simple native-build --backend=llvm \
  --source src/app/cli --source src/lib \
  --runtime-path <stage2-runtime-authority> --runtime-bundle core-c-bootstrap \
  --cache-dir /tmp/pc --entry-closure \
  --entry src/app/cli/bootstrap_reason_planner.spl -o /tmp/out
```

FLAKY: identical invocations failed (2026-11-05 21:18, 21:13) and passed
(21:22 via `SIMPLE_FILE_WORKERS=0` phase route; 21:25 pool route). Roughly
1-in-2 under the 7-worker pool on this host. The phase route
(two-pass shards) does not show the failure -- llc runs inside the MIR shard
child directly rather than inside a per-file pool unit child
(`--file-worker=i/n` claim loop spawning `--hir-shard=` unit children).

## Suspected layer

Runtime process-spawn facade silently no-op'ing (or the child dying before
exec without an error propagation) specifically in the per-file pool unit
child context (a spawned child of a spawned child, often marked
`+fork-m0`). Hello-world single-module pool builds usually pass, so the
race needs pool concurrency. `find_llc()` resolves the same absolute llc
on success and failure, so PATH is not the differentiator.

## Follow-ups

1. Runtime: make the process facade fail LOUDLY instead of returning
   success-without-child (or fix the spawn in the pool unit child context).
2. Once fixed, remove or keep the llvm-tools retry (it is cheap and
   idempotent: same argv, pid-unique tmp names).

# Stage2 progress helper traps when the optional event sink is absent

Date: 2026-09-22. Base: `2fe76eb26177b0ed539bbbaf0cae7e0723a555ea`.
Status: targeted source fix and native regression PASS; rebuilt Stage2 admission pending.

## Observed failure and cause

The macOS Stage2 build compiled and linked 899 units with zero failures, then
failed the positional hello-world admission probe with SIGILL/132. The rejected
candidate SHA-256 is
`a245740bb2bf90e354974ea05f10fedd7d3c0126614ddab1cdb9bff1eb691015`.
Its original file is preserved under
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage2/aarch64-apple-darwin/simple.rejected`.

The crash report `simple-2026-09-22-214141.ips` identifies
`compiler__driver__driver_log_helpers__log_build_progress+2828`.
Disassembly establishes the exact path: after stdout flush,
`rt_string_eq(path, "")` leads to `b.ne` at +1424 targeting +2828,
`udf #0xc11f`. This is the early bare `return`; no file append is attempted.
The enabled-sink path instead calls `file_append`, boxes its boolean using
`rt_value_bool`, and returns it.

The bootstrap producer's lowering explains the mismatch:

1. `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` lowers a wildcard
   binding (`val _ = expr`) to `HirStmt::Expr(expr)`.
2. `hir/lower/module_lowering/function.rs` treats a terminal nonvoid expression
   as value-producing and selects `TypeId::ANY` for the unannotated function.
3. `codegen/instr/body.rs` intentionally emits a trap for `Return(None)` in a
   function with a nonvoid return type.

Thus the discarded terminal `file_append` boolean incorrectly makes this
procedural helper value-returning. The fix declares `log_build_progress` as
`-> ()`, matching its side-effect-only API and early return. It changes neither
stdout ordering nor optional event, snapshot, or metric behavior.

**Remaining compiler defect:** wildcard-discard lowering loses the distinction
between a discarded initializer and a value-producing expression during return
inference. This change does not repair that general seed inference defect or
prove other unannotated functions safe. Keep this follow-up open; do not remove
the backend fail-fast trap or replace it with fabricated return values.

## Native reproduction and verification

Worktree: `/Users/ormastes/simple-tmp/macos-stage2-progress-sigill`.
Evidence directory: `build/native_probe/progress_sigill` in that worktree.
Fixture: `test/fixtures/native/build_progress_optional_sink.spl` imports the real
driver helper and emits running/complete transitions, then a completion marker.
The compiled fixture includes 36 modules; there is no replacement logging stub.

The immutable rejected candidate was also replayed with the admission ownership
pins (`SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and
`SIMPLE_FRONTEND_DELEGATE` all naming that candidate),
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_EXECUTION_MODE=`,
`SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, `SIMPLE_BOOTSTRAP=0`,
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and local
`SIMPLE_LIB`. Its positional command was:

```sh
"$candidate" native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry-closure --cache-dir build/native_probe/progress_sigill/candidate-cache \
  --mode one-binary scripts/check/cert/redeploy_gate/fixtures/hello_world.spl \
  --output build/native_probe/progress_sigill/hw-red
```

`candidate-red.log` and `candidate-red.rss.env` record exit 132 after the first
progress line, 56,352 KiB peak tree RSS, zero observer errors, and quiescence.

The fixture uses the same frozen bootstrap producer/runtime as the failed
Stage2 build. This is **bootstrap-only mini-build evidence**, not a substituted
production compiler or proof of Stage2/Stage3/full-CLI admission.
Producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Its authority directory is:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.

Build invocation (set `probe_name` to `red` on the base source or `green` with
the explicit unit signature; preserve the same private cache):

```sh
authority=/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority
probe_dir=build/native_probe/progress_sigill
probe_name=green
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
  --receipt="$probe_dir/$probe_name-native-build.rss.env" -- \
  env SIMPLE_BINARY="$authority/simple" SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB="$PWD/src" \
    SIMPLE_LLVM_BIN=/opt/homebrew/Cellar/llvm/23.1.1_1/bin \
    /usr/bin/time -l "$authority/simple" native-build \
    --backend cranelift --runtime-bundle core-c-bootstrap \
    --runtime-path "$authority" --source src/compiler --source src/lib \
    --entry-closure --threads 2 --cache-dir "$probe_dir/cache" \
    --mode one-binary --entry test/fixtures/native/build_progress_optional_sink.spl \
    --output "$probe_dir/$probe_name" >"$probe_dir/$probe_name-native-build.log" 2>&1
sh test/01_unit/compiler/driver/build_progress_optional_sink_native_test.shs \
  "$probe_dir/$probe_name" "$probe_dir/$probe_name-cases"
```

The actual red execution predates the harness: `red-empty.log` records SIGILL
132 after the running line; red writable/unwritable logs both contain the two
progress lines and completion marker with exit 0. The green harness passed all
four subprocess cases (unset, empty, writable, unwritable), asserting exit 0,
both stdout transitions with counts, completion, and exactly two correct
durable events. Evidence is under `green-cases/progress-sink.Rd7coeaw`.
`green.disasm` shows a normal epilogue and return for the absent-sink branch,
with no `udf` in the helper.

| Measurement | Red fixture | Green fixture |
|---|---:|---:|
| Compiled modules / failures | 36 / 0 | 36 / 0 |
| Build wall time | 5.24 s | 5.00 s |
| Peak sampled process-tree RSS | 293,168 KiB | 280,368 KiB |
| Writable-sink process max RSS | 9,093,120 bytes | 9,093,120 bytes |
| Writable-sink wall time, coarse timer | 0.00 s | 0.00 s |
| Watchdog observer errors / restarts | 0 / 0 | 0 / 0 |
| Watchdog quiescent | 1 | 1 |

Both builds are below the unchanged 5,859,375 KiB guard and the ordinary
976,562 KiB target. No speedup claim follows from these single short samples.
The green binary's first unset-sink launch took 0.51 s; subsequent launches
reported 0.00 s at the timer's resolution. The annotation adds no allocations,
loops, I/O, or hot-path work; the helper no longer boxes a discarded bool.

Native fixture SHA-256 values:

- Red: `35e00db6fdd326c2d4a80f17d6b6b42f7e671bd509a3a1bd240233a483aa5d2e`.
- Green: `15e8be9899912b12c251d874997a0e9c5d616af7c7dd10df3c3b552ea1f8d955`.

Independent Astra review: PASS for the scoped source fix and native regression,
with no blocking findings. Review explicitly excludes full Stage2 admission.
Shell syntax, whitespace, direct-env runtime guard, and the zero-executable-spec
layout gate pass. No unrelated dirty worktree files were incorporated.

## Remaining admission boundary

The immutable rejected Stage2 binary is unchanged. Rebuild Stage2 from the
reviewed source through the canonical bootstrap flow and rerun all admission
probes, including positional hello world, under the existing resource observer,
cap and ownership pins. Full runtime/tree checks and MCP native smoke require
the rebuilt admitted self-hosted runtime; this worktree has no deployed
`bin/release/<triple>/simple`. They were not replaced with seed tests. No full
bootstrap, release, push or deployment was performed in this lane.

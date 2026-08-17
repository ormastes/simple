# BUG: LLM Caret compiled carrier cannot be produced within bounded build time

- **ID:** `llm_caret_compiled_carrier_build_latency`
- **Severity:** P1 (blocks production compiled database/plugin carriers)
- **Found:** 2026-08-02
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Owner:** Codex LLM Caret messaging integration lane (2026-08-09)

## Symptom

The focused messaging source checks and interpreter-mode SSpecs converge, but a
native entry-closure build for `messaging/hook_worker.spl` does not complete
within the repository's 120-second bounded verification window. The same class
of timeout affects the larger database and MCP carriers. No executable artifact
is produced under `build/database/`.

Standalone SMF is not currently an alternative: the compiler correctly rejects
the PureDatabase closure because 57 reachable functions still require
interpreter-only `PatternMatch`, `TryOperator`, collection operations, or
collection literals.

## Reproduction

```sh
SIMPLE_TIMEOUT_SECONDS=120 bin/simple native-build \
  --source src/app --source src/lib --entry-closure \
  --entry src/app/llm_caret/messaging/hook_worker.spl \
  --strip --output build/database/llm_caret_messaging_hook
```

The watchdog terminates the build at 120 seconds without an artifact.

## Required resolution

- Profile frontend/module loading and entry-closure construction for this
  realistic PureDatabase application.
- Cache compiler/module analysis across the four messaging carrier builds.
- Meet a cold build target below 120 seconds and provide a materially faster
  warm rebuild.
- Alternatively, lower the remaining PureDatabase closure constructs for
  standalone SMF without interpreter fallback.

Until resolved, production startup must fail closed when the cached compiled
carrier is missing or stale. Interpreter execution is diagnostic-only.

## 2026-08-09 source-matched Phase-2 probe

The retained Phase-2-derived native-build capsule compiled a six-module,
strict-no-stub tokenizer probe in 2.7 seconds, so build latency is no longer the
first blocker for this reduced closure.  Replacing deprecated text slices with
`substring` did not repair native tokenization: `CREATE TABLE
messaging_events` became 28 one-character tokens (`C`, `R`, `E`, ...), while
the same outer-loop `_is_alpha` branch recognized each character.  Capturing
the substring in a local and calling `_is_alpha`/`_is_digit` directly inside
the identifier loop produced the same result.

The exact retained reproducer is
`test/fixtures/compiler/native_sql_tokenizer_substring_probe.spl`; cycle 3 is
`build/native_probe/sql_tokenizer_substring/native_sql_tokenizer_substring_probe`.
Its incremental receipt was 2 compiled / 4 cached / 0 failed, followed by exit
1 and the 28-token diagnostic.  The next owner is native text-value
classification or lifetime across the loop/helper-call boundary, not another
messaging carrier retry.  No database carrier or performance PASS is claimed.

## 2026-08-09 root cause and bounded repair

The apparent loop/lifetime failure was a backend contract mismatch. `_is_alpha`
casts a one-codepoint `text` with `c as i64`. LLVM passed STRING values through
as tagged handles, while Cranelift routed them to decimal parsing. Both results
were wrong for nonnumeric characters, so the identifier loop stopped after one
character. Both native backends now route ANY/STRING integer casts through
`rt_value_as_int`: one codepoint decodes to its Unicode scalar value and longer
numeric text retains the existing lenient parse. Cranelift's referenced-call
scan now also declares that helper for STRING casts in reused modules.

The focused Rust contracts pass 2/2 for the LLVM/Cranelift cast decision and
1/1 for the reused-module helper declaration. A targeted `libsimple_native_all`
rebuild and cached Phase-2-derived capsule relink reused 792 modules and rebuilt
3; no full bootstrap ran. The fresh six-module native tokenizer probe then
completed in 2.6 seconds and printed `PASS native_sql_tokenizer_substring`.

The subsequent 95-module database carrier compile reached its final link, so
the tokenizer and previous build-latency blockers are closed. It is still not
admitted: entry-closure emission left bare built-in method symbols (`len`,
`trim`, `starts_with`, `unwrap_err`, and siblings) unresolved at link time.
That is a separate closure/call-target owner and no carrier PASS is claimed.

## Additional backend evidence

A bounded build of the smallest hook carrier with `--backend cranelift` and a
dedicated cache also completed without producing an executable artifact. The
failure is therefore not demonstrated to be LLVM-only; frontend closure
construction/lowering remains part of the investigation scope.

The smaller `src/app/postgres_mimic_server/main.spl` native entry closure also
produced no artifact. Its standalone SMF diagnostic reports 36 unsupported
functions, primarily `TryOperator` and `PatternMatch` in PureDatabase plus CLI
helpers. This is the current finite lowering target for a reusable compiled
database process.

The newest available self-hosted `simple-bootstrap` bypasses that Rust-seed
gate and reaches HIR lowering, but its focused compile command bulk-loads
`nogc_async_mut/async/future.spl`. Passing `--entry-closure` does not alter that
behavior, and compilation stops on missing generic monomorphization before an
artifact can be emitted.

Closure transport was audited after the self-hosted failure. Its initial `0`
state is intentional: the driver uses it to walk the entry import graph, then
sets the state to `1` before suppressing whole-project loading. Pre-setting `1`
would skip closure discovery, so no such change is retained. The unexpected
generic async module must instead be removed from the database entrypoint's
reachable dependency graph or supported by native monomorphization.

Removing `std.cli.cli_util` from the PostgreSQL-mimic entry eliminated the
generic-async failure. The third bounded self-hosted attempt reached MIR, where
imported database methods were unresolved, lowered to const-zero placeholders,
and caused a nil-receiver crash (exit 132, Task #145). Owner-module free
façades now replace open/startup/query/close plus map/join rendering. Their
closure contract test exits 0; the three-cycle guard prevented another compile.

## Re-verification 2026-08-17 (app-rest lane) — UNVERIFIABLE (build-latency record)

`src/app/llm_caret/messaging/hook_worker.spl` is 526 bytes and contains no
statically visible defect. The claim is a >120 s native-build timeout plus 57
functions requiring interpreter-only features — a build-lane property, not a
source defect, and not reproducible without a native build. Classify as
blocked-on-deploy rather than a silent-wrong-result bug.

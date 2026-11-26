# Native doctest route rejects declaration-only and `main`-defining examples that the interpreter route passes (2026-11-12)

Status: fix-implemented-verification-pending (2026-11-27, W2-3). Severity P2 (the only doctest route a Stage 2 producer can serve
— `--sdoctest --native-backend=<b>` — turns 10 of 13 examples in `doc/07_guide/quick_reference`
into errors before any compiler runs; the interpreter route needs the full CLI).

## Symptom
`<stage2-built runner> doc/07_guide/quick_reference --sdoctest --native-backend=cranelift ...`
(producer = Stage 2, run 15 `bfe789dd411` and run 16 `c7431e08861` alike):
`SDoctest Results: 13 total, 0 passed, 0 failed, 3 skipped, 10 errors`, rc=1 in 0 s —
3x `native-plain: no executable body`, 7x
`native-plain: completion entry wrapper unavailable: native-spec: source defines main`.
Seed interpreter route on the same directory: `13 total, 6 passed, 4 failed, 3 skipped, 0 errors`.

## Minimal repro (scratch `s2runner/doctest_repro/`, one block each; seed route: 3/3 pass)
```
decl_only.md     -> fn add(a: i64, b: i64) -> i64: a + b          # native: "no executable body"
defines_main.md  -> fn main() -> i64: print "hello"; 0           # native: "source defines main"
plain_body.md    -> val x = 1 + 2; print "x={x}"                   # native: compiles (control)
```

## Cause
`src/lib/common/test_runner/native_framework_wrapper.spl`:
- `native_plain_wrapper_source` (line ~358) refuses a partition without an executable body —
  deliberate since `42f057fa6a6` ("require invocation-bound native completion evidence"): a
  declaration-only example yields no executed evidence. The interpreter route counts the same
  example as passed, so the two routes disagree on what a doc example is.
- `spipe_partition_source` (line ~186, `native_source_defines_main_v1`) refuses any source that
  defines `main` because the generated completion call is appended at top level and would compete
  with the entry.

## Proposed fix
1. Declaration-only example: emit the wrapper anyway (compile + completion evidence proves the
   declarations compile) and report it as a distinct `compiled, no body` verdict (skipped with
   reason, or passed, matching the interpreter route) — never an error.
2. `main`-defining example: rename `main` to a generated symbol in the wrapper and call it from
   the generated body before the completion call (the interpreter route runs `main` for such a
   script), so the completion evidence stays invocation-bound.
Both need a spec over `native_plain_wrapper_source` with the three repro sources (red on the
first two today) and a native run through a Stage 2-built runner as the green evidence.

## Fix & Verification 2026-11-27 (Windows host, W2-3)

- `src/lib/common/test_runner/native_framework_wrapper.spl`: added `allow_authored_main: bool = false` to `spipe_partition_source` and `native_plain_main_param_kind_v1` so `native_framework_wrapper_source` continues rejecting `fn main`, while `native_plain_wrapper_source` accepts declaration-only examples (non-empty `declarations`/`imports`) and single top-level `fn main` definitions (`()` or `(args: [text])`, renaming top-level `fn main` to `{prefix}user_main` and generating `fn main() -> i64:` with `plain` completion evidence, while rejecting non-empty unsupported `main` param lists), and updated `native_rewrite_infix_expect_line` to use `.byte_len()` for UTF-8-safe lexical matcher boundary slicing.
- `test/01_unit/lib/test_runner/native_framework_wrapper_spec.spl`: 22/22 PASS (escaped `\{ScenarioOmissionStatus}` in test assertions and added `fn main(args: [text])` + rejected `fn main(a: i64, b: i64)` coverage).
- `test/01_unit/lib/nogc_sync_mut/test_runner/wrapper_filename_owners_spec.spl`: 7/7 PASS.
- `test/01_unit/app/test_runner/doctest_child_execution_spec.spl`: 7/7 PASS.
- `test/01_unit/lib/test_runner/test_runner_doctest_scope_path_spec.spl`: 3/3 PASS.
- Stage 2 native `--sdoctest --native-backend=<backend>` compilation/execution verification remains pending outside this Windows seed host.

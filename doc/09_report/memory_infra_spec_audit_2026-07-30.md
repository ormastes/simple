# Memory-Infra Spec Audit — 2026-07-30

Independent, read-only audit. No source files were changed. Every command
below was run to completion (no timeouts hit; 600s budget per spec was never
needed — longest run was `mem_infra_flag_spec.spl` at ~111s).

## Method

1. Located specs by grepping `test/` for the literal tokens named in the task
   (`mem_attr_report`, `mem_cli`, `mem_top_tui`, `mem_dump`, `gen_arena`,
   `mem_profile`, `memstat`, `mem_infra`, `ast_arena_harden`) plus a name-scan
   for `*mem*`. The name-scan alone returned ~150 hits, but the overwhelming
   majority (OS memory-leveling, CUDA/GC memory, Wine kernel32 memory, VHDL
   memory templates, RISC-V mem-stage, memleak baselines, etc.) belong to
   unrelated features that happen to use the word "memory". I scoped the run
   to the 15 specs that are actually the memory-infra project's own directory
   cluster (`test/01_unit/lib/mem/`, `test/01_unit/lib/mem_infra/`,
   `test/01_unit/lib/gpu/mem_profile_spec.spl`, `test/01_unit/runtime/mem_*`,
   `test/01_unit/compiler/ast_arena_harden_spec.spl`,
   `test/01_unit/compiler/interp/mem_guard_rate_spec.spl` /
   `mem_harden_spec.spl`, `test/03_system/app/mem_cli_spec.spl` /
   `mem_top_tui_spec.spl`, `test/03_system/check/mem_attr_report_spec.spl` /
   `mem_infra_flag_spec.spl` / `stage4_memory_gate_spec.spl`, which is also
   what the task's own keyword list maps to 1:1). This scoping is itself a
   finding — flag it if the true intended set is broader.
2. Ran each with `timeout 600 bin/simple test <path>`, captured full stdout+
   stderr, then grepped the **entire** log (not just the summary) for
   `unknown extern`, `panic:`, `FAILED`, `error[`, `assertion failed`
   (excluding source-code identifiers like `STATICS_FAILED_KEY` that are
   lint-warning noise, not test output).
3. For every FAIL, read the full failing-scenario block, not just the
   Results line, and traced the root cause in source.
4. Pre-existing vs. dirty-WC attribution: for each file relevant to a
   failure, ran `git fetch -q origin main` then
   `git diff FETCH_HEAD -- <path>`. Empty diff = working-copy content is
   byte-identical to `origin/main` (even if local `git status` shows `M`
   because this session's HEAD hasn't been fast-forwarded — colocated-jj
   artifact, not a real divergence). Non-empty diff = genuinely dirty,
   uncommitted local change.
5. `cargo test -p simple-runtime` was run from `src/compiler_rust/` per the
   task, read-only.

## Results table

| Spec | Results line | Verdict | Pre-existing? |
|---|---|---|---|
| `test/01_unit/compiler/ast_arena_harden_spec.spl` | `Results: 4 total, 4 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/01_unit/lib/gpu/mem_profile_spec.spl` | `Results: 5 total, 5 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/01_unit/lib/mem/gen_arena_report_spec.spl` | `Results: 4 total, 4 passed, 0 failed` | PASS | n/a — new file (`git status: A`), not on origin |
| `test/01_unit/lib/mem/gen_arena_spec.spl` | `Results: 5 total, 5 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/01_unit/lib/mem_infra/config_spec.spl` | `Results: 12 total, 12 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/01_unit/lib/mem/mem_dump_spec.spl` | `Results: 3 total, 3 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/01_unit/runtime/mem_attr_gate_spec.spl` | `Results: 3 total, 3 passed, 0 failed` | PASS | n/a — new file (`A`), not on origin |
| `test/01_unit/runtime/mem_extern_parity_spec.spl` | `Results: 7 total, 7 passed, 0 failed` | PASS | n/a — new file (`A`), not on origin |
| `test/03_system/app/mem_cli_spec.spl` | `Results: 7 total, 7 passed, 0 failed` | PASS | n/a — `git status` shows `M` but `git diff FETCH_HEAD` is empty (content already landed on origin) |
| `test/03_system/app/mem_top_tui_spec.spl` | `Results: 6 total, 6 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/03_system/check/mem_attr_report_spec.spl` | `Results: 2 total, 2 passed, 0 failed` | PASS | n/a — file clean vs origin |
| `test/03_system/check/mem_infra_flag_spec.spl` | `Results: 3 total, 2 passed, 1 failed` | **FAIL** | New file (`A`), not on origin — see below |
| `test/03_system/check/stage4_memory_gate_spec.spl` | `Results: 4 total, 4 passed, 0 failed` | PASS | n/a — `git status` shows `M` but `git diff FETCH_HEAD` is empty (already landed on origin) |
| `test/01_unit/compiler/interp/mem_guard_rate_spec.spl` | `Results: 3 total, 3 passed, 0 failed` | PASS | n/a — new file (`A`), not on origin |
| `test/01_unit/compiler/interp/mem_harden_spec.spl` | `Results: 3 total, 3 passed, 0 failed` | PASS | n/a — new file (`A`), not on origin |

**No spec hung; no 600s timeout was needed for any spec.**

### `cargo test -p simple-runtime` (src/compiler_rust, read-only)

Verbatim summary line:
```
test result: FAILED. 1074 passed; 8 failed; 10 ignored; 0 measured; 0 filtered out; finished in 9.73s
```
Failing tests:
```
executor::tests::test_isolated_thread_spawn_with_args_and_join
executor::tests::test_isolated_thread_spawn_with_args_and_join_direct_function_record
loader::package::format::tests::test_manifest_section_rejects_partial_runtime_variants_trailer
loader::settlement::native::tests::test_native_lib_manager
value::collections::tests::test_dict_invalid_value
value::collections::tests::test_low_heap_tagged_values_do_not_crash_collection_runtime
value::heap::attr_tests::owner_attribution_orders_by_live_bytes_and_frees_settle
value::heap::attr_tests::owner_attribution_survives_concurrent_alloc_free_across_threads
```
Attribution:
- `executor::tests::*`, `loader::package::format::*`, `loader::settlement::native::*`,
  `value::collections::tests::*` (6 of 8): source files
  (`executor.rs`, `executor_tests.rs`, `loader/package/format.rs`,
  `loader/settlement/native.rs`, `value/collections.rs`,
  `value/collection_tests.rs`) all show **empty** `git diff FETCH_HEAD`
  — byte-identical to `origin/main`. **PRE-EXISTING** on a clean origin
  checkout, unrelated to the memory-infra work (thread-spawn join, package
  manifest trailer parsing, native-lib manager, dict-corruption guards).
- `value::heap::attr_tests::owner_attribution_orders_by_live_bytes_and_frees_settle`
  and `..._survives_concurrent_alloc_free_across_threads` (2 of 8): these
  **are** memory-infra-relevant (owner-attribution accounting, tracked under
  task M2/M3 "sampled guard pages + hardened debug allocator" /
  "`--mem-infra=` interface"). `value/heap.rs` has a 447-line diff vs
  `origin/main` — genuinely dirty, in-progress local work. The
  `_orders_by_live_bytes_and_frees_settle` test name exists verbatim on
  origin too (so it may or may not pass there — not independently verified,
  a full origin-tree cargo build was out of scope for this audit's time
  budget); `..._survives_concurrent_alloc_free_across_threads` does **not**
  exist on origin at all — it is a new test added by the in-flight dirty
  change and its failure (`assertion left != right failed: left: 0 right: 0`,
  i.e. attribution never differentiates two owners) reflects incomplete
  in-progress work, not a landed regression.

## Untrustworthy-green check

Grepped every log's full output (not just the Results banner) for
`unknown extern`, `panic:`, `error[`, `assertion failed`. **One spec's FAIL
was the false-green pattern flagged in the task brief**, caught because it
already shows as FAIL in its own Results line (so no "green banner hiding a
red assertion" case was found in this set) — but the mechanism matches
memory's known "unknown extern → silent 0" pattern:

- **`test/03_system/check/mem_infra_flag_spec.spl`** — scenario "enables
  SIMPLE_MEM_ATTR before the target program runs on the default (cranelift)
  engine" fails with:
  ```
  [STDERR] ... ERROR ... rt_interp_call error: SemanticWithContext(ContextualError {
    message: "unknown extern function: rt_mem_attr_enabled", ... })
  expected attr_enabled_probe: enabled=0 ... to contain enabled=1
  ```
  Root cause traced: `rt_mem_attr_enabled` **is** registered in source
  (`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:220`,
  `mod.rs:307`, impl in `src/compiler_rust/runtime/src/value/heap.rs:807`),
  and that registration is a genuinely dirty, uncommitted change (`memory.rs`
  and `mod.rs` both show `M` vs local HEAD). But the compiled seed binary
  being exercised (`src/compiler_rust/target/debug/simple`) was built
  **2026-07-29 16:42**, while `memory.rs` was last touched **2026-07-30
  07:53** — i.e. the extern exists in source but the seed binary predates it
  and was never rebuilt. This is a **stale-seed-binary** failure, not a logic
  bug and not something visible from the origin source tree at all (the spec
  file itself is new, `git status: A`, not present on origin). It will very
  likely self-resolve once the seed is rebuilt (`cargo build` picking up the
  M2/M3 in-flight extern registration) — but as measured right now, on this
  working copy, it is a real, reproducible FAIL, not a false green.

No spec showed a PASS banner while its body logged `unknown extern`,
`panic:`, or `assertion failed` — every log where those strings appeared
also reported the failure honestly in its own Results line.

## Totals

- **13 green** (`bin/simple test` specs, PASS)
- **1 red** (`mem_infra_flag_spec.spl`, 1 of 3 examples failed — stale-seed
  attribution above)
- **1 hung: 0** (none of the 15 specs needed the 600s timeout)
- Separately, `cargo test -p simple-runtime`: 1074 passed / **8 failed**
  (6 pre-existing/unrelated, 2 memory-infra-relevant and tied to in-flight
  dirty `heap.rs` work) / 10 ignored.

## Dirty files found but not authored by this session

All of `src/compiler_rust/**`, `test/01_unit/runtime/**`, and the other
excluded paths per the task's ownership list were read-only touched (tests
run, source read for attribution) and never edited. Specifically read/relied
on but not modified:
- `src/compiler_rust/compiler/src/interpreter_extern/memory.rs`,
  `mod.rs` (M, dirty — rt_mem_attr_enabled registration)
- `src/compiler_rust/runtime/src/value/heap.rs` (M, dirty, 447-line diff —
  owner-attribution work)
- `test/01_unit/runtime/mem_attr_gate_spec.spl`,
  `test/01_unit/runtime/mem_extern_parity_spec.spl` (both `A`, new, owned by
  another lane per the task's exclusion list — run read-only only)
- `test/03_system/app/mem_cli_spec.spl`,
  `test/03_system/check/stage4_memory_gate_spec.spl` (both show local `M`
  but are byte-identical to `origin/main` — already landed elsewhere, this
  session's local HEAD is just behind)
- `test/03_system/check/mem_infra_flag_spec.spl`,
  `test/01_unit/lib/mem/gen_arena_report_spec.spl`,
  `test/01_unit/compiler/interp/mem_guard_rate_spec.spl`,
  `test/01_unit/compiler/interp/mem_harden_spec.spl` (all `A`, new, not
  authored by this session)

This report is the only file this audit created.

# JIT cannot resolve the native socket externs — every "JIT mode" networking run is silently an interpreter run

- **Filed:** 2026-08-09
- Status: **FIXED 2026-08-17** (was OPEN P2)
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** 47 manifest entries and both tests present in `runtime_symbols.rs`, but end-to-end JIT socket EXECUTION is unproven — the deployed seed predates the change. `bug_db.sdn` row is `fix-implemented-verification-pending`.
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  (Rust-seed-only fix, see "Root cause" below)

## Resolution (2026-08-17)

**Root cause, confirmed by content:** `register_runtime_symbols_from_provider`
(`src/compiler_rust/compiler/src/codegen/jit.rs:387-395`) iterates **only**
`RUNTIME_SYMBOL_NAMES`, and that manifest
(`src/compiler_rust/common/src/runtime_symbols.rs:385`) contained **zero**
`native_*` entries — `grep '"native_'` on the file returned three hits, all of
them `starts_with` prefix arms inside `symbol_tier_of`, none inside the array.
So the classifier already called the family `Sys`
(`runtime_symbols.rs:307-309`) and the native linker already stubbed all 39 of
them (`compiler/src/linker/native_binary/stubs.rs:87-125`), while the one list
the JIT actually reads had never heard of them. A name absent there is never
passed to `JITBuilder::symbol`, so Cranelift saw an unresolved import and the
whole module was demoted to the tree-walk interpreter.

**Fix:** added all 39 `native_tcp_* / native_udp_* / native_http_*` names to
`RUNTIME_SYMBOL_NAMES`. All are `#[no_mangle] pub extern "C"` in
`simple_runtime` (e.g. `runtime/src/value/net_tcp.rs:118`), so both provider
lookup and the `elf_utils::resolve_runtime_symbol` fallback can resolve them.

**Evidence (RED then GREEN, same tree, same isolated `CARGO_TARGET_DIR`):**

RED — with the 39 manifest entries stripped and the tests kept:
```
test runtime_symbols::tests::every_classified_native_extern_family_has_manifest_coverage ... FAILED
test runtime_symbols::tests::native_socket_externs_are_registered_for_the_jit ... FAILED
test result: FAILED. 7 passed; 4 failed; 0 ignored; 0 measured; 1 filtered out
```
GREEN — with the fix:
```
test runtime_symbols::tests::every_classified_native_extern_family_has_manifest_coverage ... ok
test runtime_symbols::tests::native_socket_externs_are_registered_for_the_jit ... ok
test result: FAILED. 9 passed; 2 failed; 0 ignored; 0 measured; 1 filtered out
```
The 2 residual failures (`realloc_is_exactly_once_and_adjacent_to_alloc_in_full_manifest`,
`struct_allocator_pair_is_present_in_core_and_full_manifests`) are **pre-existing
and unrelated** — they fail identically in both states, and this change only
*appends* names, which cannot cause a "symbol missing from the manifest"
assertion to start failing. They are not claimed as fixed here.

**Specs added** (both in `src/compiler_rust/common/src/runtime_symbols.rs`,
`mod tests`):
1. *reproducing* — `native_socket_externs_are_registered_for_the_jit`: asserts
   the four names the bug report measured are in the manifest.
2. *similar-problem detection* — `every_classified_native_extern_family_has_manifest_coverage`:
   generalises to the defect **class**, an extern family the tier table claims
   to know about while the JIT's registration manifest has never heard of it.
   For every prefix family `symbol_tier_of` special-cases it requires at least
   one manifest entry, and conversely requires every `native_*` manifest entry
   to classify as `Sys`, so the two tables cannot drift apart silently again.

**Not proven here:** end-to-end JIT execution of a socket program. The deployed
`bin/simple` is a Rust seed (mtime 2026-08-16 22:59) that predates this change,
and on it the doc's original reproduction no longer prints the `[jit-fallback]`
line at all — a control run with a deliberately bogus extern showed the run
going through `interpreter_sffi::rt_interp_call`, i.e. the JIT was never
entered for that program shape on that binary. Confirming the runtime effect
needs a rebuilt seed.
- **Severity:** Medium (correctness of engine claims; performance cliff)
- **Component:** `RUNTIME_SYMBOL_NAMES` manifest (`src/compiler_rust/common/src/runtime_symbols.rs`)
  → Cranelift JIT external-symbol registration
- **Binary measured:** `bin/release/x86_64-unknown-linux-gnu/simple`
  (`readlink -f bin/simple`)

## Summary

`native_tcp_bind`, `native_tcp_close`, `native_udp_bind` and `native_udp_close`
are not registered with the Cranelift JIT module. Any program that declares one
of them fails JIT compilation with an unresolved-external-symbol error and the
**whole module** is dropped back to the tree-walking interpreter. So
`SIMPLE_EXECUTION_MODE=jit` on networking code does not select the JIT at all —
it selects the interpreter with an extra compile attempt in front of it.

This was found while retrofitting `test/03_system/feature/usage/networking_spec.spl`
onto a real out-of-process engine probe
(`scripts/check/check-engine-claiming-specs-use-probe.shs` debt retirement).
That spec has a describe block literally titled **"JIT Compilation Mode"** with
examples named *"tcp bind compiles in JIT mode"* and *"udp bind compiles in JIT
mode"*. The title is false: tcp bind does not compile in JIT mode.

## Reproduction

```
$ cat /tmp/net.spl
extern fn native_tcp_bind(addr: text) -> (i64, i64)
fn main() -> void:
    val (h, e) = native_tcp_bind("127.0.0.1:0")
    print("TCP ok=" + (h > 0).to_text())

$ SIMPLE_EXECUTION_MODE=jit bin/simple run /tmp/net.spl
[jit-fallback] unresolved external symbol 'native_tcp_bind': whole module
dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1
to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: unresolved external symbol 'native_tcp_bind' would
NULL-jump in JIT; deferring to interpreter
TCP ok=true
```

Strict mode confirms it is a real resolution failure, not a heuristic demotion:

```
$ SIMPLE_JIT_STRICT=1 SIMPLE_EXECUTION_MODE=jit bin/simple run /tmp/net.spl
error: Cranelift JIT compile: Module error: SIMPLE_JIT_STRICT: unresolved
external symbol 'native_tcp_bind' would NULL-jump in JIT; refusing to fall back
to the interpreter
```

`native_udp_bind` reproduces identically in a file of its own, so this is not
one bad symbol contaminating a module — each socket extern is independently
unresolved.

## Why it matters

1. **Every engine claim about networking is unfalsifiable today.** A probe run
   under `"jit"` and one run under `"interpret"` execute the same interpreter,
   so an A/B looks like agreement no matter what the JIT would have done. Any
   future JIT-only networking defect is invisible.
2. **Silent 100-1000x performance cliff** for any server-shaped program: one
   socket extern demotes the entire module, including all the hot code that had
   nothing to do with sockets (this is the documented
   whole-module-demotion behaviour, see
   `.claude/rules/testing.md` — "One unsupported operation silently demotes the
   WHOLE program to the interpreter").
3. The fallback notice goes to **stderr**, so a caller scoring stdout — the
   documented and correct way to score a probe — cannot see it.

## Current pin

`test/03_system/feature/usage/networking_jit_probe.spl` binds real TCP/UDP
sockets on port 0 and self-scores, and
`test/03_system/feature/usage/networking_spec.spl` asserts BOTH the probe's
`PROBE VERDICT: PASS` and the presence of the `[jit-fallback] unresolved
external symbol 'native_tcp_bind'` line on stderr under `"jit"`. That fallback
assertion is a pin on measured reality, **not approval**: when the externs are
registered with the JIT it will go RED and must then be replaced by an
assertion of a genuinely compiled run.

## Root cause (2026-08-09, confirmed)

**One missing list, and it is a Rust-seed list — there is no `.spl`-side
registration list at all.** The chain:

1. `src/compiler_rust/compiler/src/codegen/jit.rs:387`
   `register_runtime_symbols_from_provider()` iterates **only**
   `RUNTIME_SYMBOL_NAMES` and calls `JITBuilder::symbol(name, ptr)` for each.
   A symbol not in that list is never handed to Cranelift.
2. `jit_import_resolves()` (`jit.rs:405`) then falls back to
   `elf_utils::resolve_runtime_symbol` and `dlsym(RTLD_DEFAULT, ..)`. Neither
   finds `native_tcp_bind`: the runtime is statically linked into the driver
   and the symbol is not in the dynamic symbol table, so `dlsym` misses.
   Result: unresolved import → whole-module demotion.
3. `RUNTIME_SYMBOL_NAMES` is `src/compiler_rust/common/src/runtime_symbols.rs:381`.
   **It contains zero `native_tcp_*` / `native_udp_*` / `native_http_*`
   entries** (the only `native` hits in the whole 1,800-line list are
   `rt_native_eq`, `rt_native_cmp`, `rt_compile_to_native_with_opt`,
   `rt_native_profile_*` — unrelated).
4. The omission is clearly an oversight, not a policy: the *tier classifier*
   in the same file (`symbol_tier_of`, lines 303-305) already has explicit
   `native_tcp_` / `native_udp_` / `native_http_` prefix arms assigning them
   Tier-`Sys`. Something classifies these symbols that the name list never
   emits.
5. The implementations **do exist and are correctly exported**:
   `src/compiler_rust/runtime/src/value/net_tcp.rs:118`
   `#[no_mangle] pub unsafe extern "C" fn native_tcp_bind(...) -> (i64, i64)`,
   plus `native_tcp_accept/flush/shutdown/close/set_backlog/set_nodelay`, and
   the UDP peers in `net.rs`. `nm -g --defined-only libsimple_runtime.a`
   confirms `native_tcp_bind` is a defined global. So this is purely a
   registration gap, not a missing implementation.
6. The static provider table is **generated** from that same list:
   `src/compiler_rust/runtime/build.rs:40-75` textually parses
   `../common/src/runtime_symbols.rs` for `pub const RUNTIME_SYMBOL_NAMES`,
   intersects it with `collect_defined_runtime_symbols()`, and emits
   `OUT_DIR/runtime_symbol_entries.rs` (`RUNTIME_SYMBOL_ENTRIES`), which
   `StaticSymbolProvider::get_symbol` serves. So adding the names to the one
   const propagates to both the static provider and the JIT builder.

### Scope ruling: Rust-seed only — deliberately NOT fixed here

Per CLAUDE.md "fix `.spl` not Rust": every artifact on this path is Rust seed
(`src/compiler_rust/**`). Searched `src/compiler/**` for an analogous
`.spl`-side "externs available to JIT" list — **none exists**; the pure-Simple
JIT files (`70.backend/backend/jit_interpreter.spl`,
`10.frontend/core/interpreter/jit.spl`, `95.interp/execution/tiered_jit_manager.spl`)
carry no runtime-symbol manifest. There is nothing to fix in `.spl` scope.

### Exact work a seed lane needs

- **File:** `src/compiler_rust/common/src/runtime_symbols.rs`, inside the
  `pub const RUNTIME_SYMBOL_NAMES: &[&str] = &[` literal (starts line 381).
- **Change:** add one `"name",` entry per socket extern actually defined in
  `src/compiler_rust/runtime/src/value/net_tcp.rs` and `net.rs` — at minimum
  `native_tcp_bind`, `native_tcp_accept`, `native_tcp_close`,
  `native_tcp_flush`, `native_tcp_shutdown`, `native_tcp_set_backlog`,
  `native_tcp_set_nodelay`, and the `native_udp_*` peers. Enumerate the family
  with `nm -g --defined-only` rather than adding only the two symbols this bug
  names — a partial add leaves siblings broken.
- **No other call site needs editing.** `build.rs` regenerates
  `RUNTIME_SYMBOL_ENTRIES`, `StaticSymbolProvider` picks them up, and
  `register_runtime_symbols_from_provider` registers them with `JITBuilder`
  automatically. `symbol_tier_of` already handles the tiering.
- **Watch:** `native_tcp_bind`/`native_tcp_accept` return Rust tuples
  (`-> (i64, i64)`), which is not a stable C ABI. Registration only takes the
  address so the list add is safe, but the seed lane should confirm the
  Cranelift-side signature the JIT synthesises for these matches what the
  interpreter/AOT lanes already assume before declaring the lane green.
- **Gate:** requires a `--full-bootstrap` (cargo seed + runtime rebuild), so
  this cannot ride an incremental pure-Simple bootstrap.

## Unblock condition

Land the `RUNTIME_SYMBOL_NAMES` additions above in a seed lane, then flip the
`networking_spec.spl` fallback assertion to a real compiled-lane assertion
(and add a regression check that `SIMPLE_JIT_STRICT=1
SIMPLE_EXECUTION_MODE=jit` on a `native_tcp_bind` program exits 0 — strict mode
is the sharpest available oracle for "the extern is genuinely resolvable") and
re-run both engines.

The current spec pin stays RED-on-fix by design and is **unchanged** by this
investigation: measured behaviour has not moved, so flipping the assertion now
would assert a fiction.

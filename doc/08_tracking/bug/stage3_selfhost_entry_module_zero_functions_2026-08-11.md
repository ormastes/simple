# Stage 3 self-host fails: entry module lowers 0 functions (ret-0 stub)

- **Date:** 2026-08-11
- **Status:** LIKELY FIXED IN CURRENT SOURCE — awaiting a stage-3 run to confirm.
  Re-checked 2026-08-17 (W1) by reading current source, not SHA ancestry. Both
  candidate faults named below are addressed at the sole call site:
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1928` now reads
  `val flat_functions: [HirFunction] = lowered_module.functions.values()` — taken
  from the freshly returned `HirModule`, with an in-source comment stating that
  reconstructing this array through the global bootstrap accumulator "loses the
  entry's functions under the bootstrap ABI", i.e. exactly this row's symptom;
  and `:1936-1938` now derives the registry name for the entry from
  `hir_module_logical_name_from_path(self.module_filename)` rather than
  `module.name`, which is the sibling row
  `stage3_selfhost_reaches_mir_entry_module_not_captured_2026-08-10`.
  NOT re-reproduced: this row needs a full `--full-bootstrap` stage-3 run
  (~35 min) and a live bootstrap was already occupying the box, so no
  before/after `Results:`/verdict line was captured. Leave OPEN until a stage-3
  run prints a non-zero `[bootstrap-flat-entry] ... functions=`.
  Residual, unfixed and separate: `_bootstrap_hir_entry_index` is still
  last-flag-wins (`lowering_helpers.spl:68-69`) with no "already flagged" guard —
  harmless while exactly one module is flagged, silent misdirection if ever two are.
- **Status (historical):** RED — reproduced end-to-end, root cause localized, not yet fixed
- **Severity:** BLOCKER — Stage 4 (full CLI) is unreachable; no genuine self-hosted `bin/simple` can be produced
- **Repro commit:** `7731b4c1394` (last commit whose Rust seed builds; see "Seed buildability" below)

## Verdict line

```
[bootstrap-flat-entry] index=0 modules=573 functions=0
error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)
```

Stage 2 produces a real compiler and passes its sanity + native-build capability
gates. Stage 3 (that stage2 binary recompiling `bootstrap_main.spl`) loads all
**573** HIR modules but the module flagged as the **entry** carries an **empty
function list**, so the entry lowers to zero MIR instructions. The guard in
`bootstrap_globals.spl` correctly refuses to emit a ret-0 stub and exits 1.

This is a fail-closed guard doing its job — the defect is upstream, in what gets
registered as the entry module.

## Reproduction

```bash
# real git worktree required (see "Trap 1")
git worktree add --detach /mnt/data/bs2/w3 7731b4c1394
cd /mnt/data/bs2/w3
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --jobs=min
# ~6 min Rust seed, ~9 min Stage 2, ~35 min Stage 3, then the error above
tail -5 build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log
```

## Root cause localization

- Guard: `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:365-377`
  ```
  val entry_index = bootstrap_hir_entry_index()
  val entry_function_count = bootstrap_hir_module_functions_at(entry_index).len()   # == 0
  ```
- Registry: `src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:60-73`
  `bootstrap_hir_modules_add(name, is_entry, symbols, functions, ...)`.
  `_bootstrap_hir_entry_index` is assigned on every `is_entry` call, so the
  **last** module flagged wins; it is never cleared.
- Sole caller: `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1877`
  passes `flat_functions` — the flat-AST bridge's function list.

`index=0` with `modules=573` means only module **0** was ever flagged `is_entry`,
and that module's `flat_functions` is empty. Two candidate faults, both to be
checked at the call site:

1. The entry module is registered **before** its functions are flattened, so
   `flat_functions` is `[]` at registration time; the real entry body is later
   registered as a different (unflagged) module.
2. `is_entry` is computed against a module identity that does not match the
   actual entry (`bootstrap_main`), flagging a leading stub/prelude module.

Discriminator: print `registry_module_name` alongside the existing
`[bootstrap-flat-entry]` line, and print `flat_functions.len()` for every module
whose name contains `bootstrap_main`. If a later module has a non-empty function
list and the right name, it is fault (2); if no module has one, it is fault (1).

**Note:** `module_lowering.spl` is under concurrent edit by another session (it is
`M` in the shared working copy). Coordinate before patching.

## What is PROVEN (with artifact identity)

| Stage | Result | Identity |
|-------|--------|----------|
| Rust seed | builds clean at `7731b4c1394`, 6m06s | md5 `6fd1d8e6fcf5c89973e25bf53696ed9f`, 59,147,824 B, prints the seed WARNING banner |
| Stage 2 | **PASS** — genuine, built by the seed from `bootstrap_main.spl`; passed bootstrap compiler sanity and native-build capability gates | 130,188,344 B at `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` |
| Stage 3 | **FAIL** — the error above; no binary emitted | n/a |
| Stage 4 | unreachable | n/a |

So Stage 2 self-hosting is real and working. The break is precisely at Stage 3.

## Correction to the prior baseline claim

The committed `bootstrap/stage{1,2,3}/simple` are byte-identical to each other
(md5 `2244f18ce2e694fb7ca395e9916404c3`, 3,464,072 B) but they are **NOT copies
of the Rust seed** — the seed is 59 MB and prints a seed warning, while these
print `simple-bootstrap 1.0.0-beta` / "Simple Bootstrap Compiler ... Built from
Simple source via the staged bootstrap". They are genuine (if stale, mtime
Aug 10 12:09) stage artifacts of the right shape.

They are, however, **broken**: `bootstrap/stage3/simple native-build` on a
one-line `print("hi")` program **segfaults** (SIGSEGV, core dumped, rc 139).
Filed separately below.

Also note: answering only `compile`/`native-build` and lacking `test`/`lint` is
**expected** for a Stage-3 artifact per `.claude/rules/bootstrap.md` — Stage 4 is
what produces the full CLI. That is not the "toolchain-shaped stage3" defect.

## Secondary defects found

1. **Committed stage3 binary SEGVs on hello-world.**
   `bootstrap/stage3/simple native-build t.spl` where `t.spl` is `print("hi")`
   → SIGSEGV rc 139. With `fun main()` it instead reports
   `HIR lowering error: unresolved name: fun`, and **exits 0** despite printing
   `[ERROR] phase 3 FAILED` (the known exit-0-after-fatal trap).

2. **Bootstrap fails closed on a `git archive` tree.**
   `error: could not bind Stage 3 git HEAD/dirty state`. The flow requires real
   git metadata; an extracted tarball is not enough. Use `git worktree add`.

3. **Stage 3 needs ~21 GB RSS and gets OOM-killed under load.**
   First attempt died with `exit 143`, which reads as a compiler failure but was
   **earlyoom**: `sending SIGTERM to process 2090765 uid 1000 "simple": badness
   1066, VmRSS 19352 MiB` at 08:12:50, host at 9.9% memory free with ~10 other
   agent sessions running. The retry survived to 20.9 GB once memory freed and
   reached the real defect. **A `143` from Stage 3 is an infrastructure kill, not
   a compiler verdict** — always check `journalctl | grep earlyoom` before
   believing it. `--jobs=min` does not reduce this; the RSS is a single process.

## Seed buildability (context)

`origin/main` (`bb8d6e6059a`) does **not** build: `6e2f613d302` truncated
`runtime/src/value/collections.rs` 5998→4211 lines and `sffi/value_ops.rs`,
dropping 8 functions still exported by `lib.rs` (E0432: `rt_array_each`,
`rt_array_map`, `rt_array_reduce`, `rt_map`, `rt_value_unbox_int`, 3 TLS timeout
fns) plus `HeapObjectType::WideInt` → `UInt` leaving a stale consumer in
`sffi/io_print.rs` (E0599). `ad2b5d5307f` ("revert: restore tree wiped...") did
**not** restore them. Six files lost net content vs `7731b4c1394`:
`collections.rs`, `sffi/value_ops.rs`, `core.rs`, `sffi/equality.rs`, `mod.rs`,
`heap.rs`. Repair is owned by a concurrent session and is **not** attempted here;
this lane worked at `7731b4c1394` instead. Note the shared working copy's
`runtime/` is *behind* origin (pre-u64), so it is not a drop-in fix — origin's
compiler crate requires the u64 API (`rt_value_u64`, `HeapObjectType::UInt`,
`RuntimeValue::from_u64`, `as_heap_u64`).

## Next step

Add the `registry_module_name` / per-module `flat_functions.len()` probe at
`module_lowering.spl:1877`, rerun Stage 3, and determine which of the two
candidate faults holds. Everything up to and including Stage 2 is green and
cached, so the loop is Stage 3 only (~35 min).

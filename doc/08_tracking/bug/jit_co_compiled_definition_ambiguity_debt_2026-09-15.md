# JIT co-compiled definition ambiguity debt — native-build blocker chain

Date: 2026-09-15
Status: open — `native-build` on Windows blocked; one symbol fixed, systematic
debt remains
Host: Windows 11, seed rebuilt + deployed 2026-09-15 21:15 (39,274,496 bytes)

## Symptom

`simple native-build <app> --backend=llvm` worker dies with:

```
error: semantic: method `len` not found on type `i64` (receiver value: 0)
```

The worker's own diagnostics name the cause:

```
warning: public function `env_vars` has 2 co-compiled definitions with 2
differing signatures (... vs ...); JIT call sites resolve by exact arg-type
match (mangled `$dupN` variants), falling back to the last definition when
types are ambiguous — a fallback hit may still dispatch to the wrong one.
Rename the conflicting helper(s) to a unique name.
[compiler_cross_module_private_symbol_collision]
```

~24 public symbols currently carry this warning in the native-build closure
(env_get, dir_create, dir_list, file_read_text, file_size, join, shell,
spawn, process_wait, token_new, ...). Any call site whose assumed return
type differs from the JIT's fallback pick fails the semantic check — the
receiver-value-0 pattern (an Optional nil compiled as i64) reaching a
method call like `.len()`.

## Fixed in this entry (2026-09-15)

- `env_vars` — the non-nilable `env_vars() -> [(text, text)]` in
  `src/lib/nogc_sync_mut/sffi/system.spl` renamed to `env_vars_or_empty`
  (definition + `nogc_sync_mut/sffi/__init__.spl` export +
  `nogc_async_mut/sffi/system.spl` + `nogc_async_mut/sffi/__init__.spl`
  re-exports). The nilable variant already had a unique name
  (`env_vars_nilable`).

## Current understanding (2026-09-15, updated)

The blocker chain is NOT primarily the stdlib renames — it is a seed-runtime
defect in the native-build worker's interpreted driver lane:

**`bool`/`i64` `.to_text()` and `str(x)` return the receiver unchanged**
(raw `false`/`0` stay non-text), so any `[text]` literal holding a converted
scalar smuggles an `i64`/`bool` in, and the next `.len()` dies with
`method 'len' not found on type 'i64' (receiver value: 0)`.
F-string interpolation (`"{x}"`) DOES stringify correctly — that is the only
reliable scalar→text conversion in this lane.

Located with `SIMPLE_INTERP_OOB_DEBUG=1 SIMPLE_DEBUG_FIELD_ACCESS=1`
(which prints `[mnf-debug-spl]` — the interpreted call stack): first hit was
`native_noop_normalized_invocation_v1 -> native_noop_frame_v1`
(`src/compiler/80.driver/cache/native_noop_admission.spl`); the ~35-element
invocation frame was reframed into smaller groups and all scalar elements
switched to interpolation, which is more robust regardless, but other driver
call sites keep hitting the same defect — this needs the seed-side fix, not
per-site workarounds.

`src/compiler/common/driver_compile_options.spl` was also reworked to build
`CompileOptions` field-by-field (no bulk aggregate copy) — the historical
corruption class the file's own comments document; harmless and more robust.

## Recommended lane (updated)

0. **Seed-side (first)**: fix scalar `.to_text()`/`str()` in the
   worker-lane method table (return tagged text), and attach the call span
   to the `method not found` semantic error so future hits are locatable
   without the env-gated debug. Rebuild + redeploy the seed.
1. Then the stdlib rename lane below (still real debt: `env_vars` fixed;
   `dir_list` — 5 definitions, ~129 mixed call sites — remains).
2. Gate on `native-build src/app/power/main.spl --backend=llvm`.

## Historical notes

- `env_vars` — fixed 2026-09-15 by renaming the non-nilable
  `env_vars() -> [(text, text)]` in `src/lib/nogc_sync_mut/sffi/system.spl`
  to `env_vars_or_empty` (+3 facade re-export sites). The nilable variant
  already had a unique name (`env_vars_nilable`).
- `src/compiler/80.driver/cache/cas_batch_transaction.spl` got explicit
  `val objects: [text] = dir_list(...)` annotations — did not guide the
  JIT's overload pick; kept as documentation of intent only.
- The `CompileOptions` bulk-copy corruption hypothesis was disproven by
  probes (`raw.input_files.len()` = 1 with the parameter AND the
  normalize() return both healthy); the large-LIST-literal hypothesis was
  also disproven (11-element groups still failed before the str/to_text
   root cause was found).

## Impact until closed

- All Windows `native-build` lanes (blocks the linker Gate 0 real-corpus
  baseline — see doc/01_research/domain/simple_linker_mold_mdsocpp.md §17).
- Any other JIT/AOT lane compiling the full driver closure.

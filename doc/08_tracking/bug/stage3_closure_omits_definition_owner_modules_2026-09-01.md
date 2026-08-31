# Stage 3: the entry closure omits definition-owner modules, so 764 of 1064 hir-fatals are "unresolved type" for types whose owner was never loaded

- **Status:** OPEN — root cause not yet established
- **Filed:** 2026-09-01
- **Blocks:** Stage 3 self-host (`--stop-after-stage3` → `stage3_rc=2`), and therefore Stage 4 / Stage 5
- **Evidence log:** `build/bootstrap/stage3/aarch64-apple-darwin/stage3-tmp/native-build-stderr-69741.log` (10,127 lines)

## Signature

Stage 3 fails with 1,064 `[hir-fatal] ... unresolved type: <T>` across **200 distinct
files**, then `error: native-build failed without diagnostics`.

The fatals are NOT spread evenly over types. They concentrate on types whose
**defining module is absent from the build entirely**:

| unresolved type | count | owner module | owner in closure? |
|---|---|---|---|
| `HirBinOp` | 162 | `compiler.hir.hir_operators` | **no** |
| `HirUnaryOp` | 148 | `compiler.hir.hir_operators` | **no** |
| `HirAssignOp` | 126 | `compiler.hir.hir_operators` | **no** |
| `TargetCapsKind` | 32 | `compiler.backend.feature_caps_arch32` | **no** |
| `X86Caps` | 31 | `compiler.backend.feature_caps_types` | **no** |
| `CompileError` | 20 | `compiler.common.error` | **no** |
| `BlockValue` | 18 | `compiler.blocks.value` | **no** |
| `CacheCheckResult` | 12 | `compiler.driver.cache.cache_types` | **no** |
| `ConcreteType` | 20 | `compiler.mono.monomorphize.types` | yes |
| `BackendKind` | 18 | `compiler.backend.backend_types` | yes |

Roughly **764 of 1,064** fatals are attributable to a missing owner module. The
remainder have owners that ARE loaded and are a separate question.

`compiler.hir.hir_operators` is the clearest case and was verified by hand:

```
$ grep -c 'hir_definitions' <log>   # 22
$ grep -c 'hir_types'       <log>   # 18
$ grep -c 'hir_codec'       <log>   # 21
$ grep -c 'hir_operators'   <log>   # 0     <-- never loaded, never lowered
$ grep -c 'module=compiler.hir.hir_operators' <log>   # 0 of 377 loaded modules
```

Both of its importers ARE in the build:
- `src/compiler/20.hir/hir_definitions.spl:39` — `export use compiler.hir.hir_operators.{HirBinOp, HirUnaryOp, HirAssignOp}`
- `src/compiler/20.hir/generated/hir_codec.spl:11` — plain `use compiler.hir.hir_operators.{...}`

The second matters: a **plain** `use` also failed to pull the module in, so this
is not simply "the walker does not follow `export use` edges".

## What is ruled out (each checked against source, not inferred)

1. **Module-name collision** — only one `hir_operators.spl` exists in the tree.
2. **Import extraction** — `_driver_entry_import_module_paths_text_fallback`
   (`80.driver/driver_source_loading.spl:504`) accepts `use `, `pub use `,
   `export use `, `import `, and cuts the module path at the first of
   `" " { ( * #`, then strips a trailing `.`. Line 39 yields exactly
   `compiler.hir.hir_operators`. No docstring toggle precedes it.
3. **Unbraced member imports** (`use a.b.C` extracting `a.b.C` as the module
   path) — `_driver_resolve_entry_import_untimed:1139` walks up parent paths
   until one resolves, and the `closure_has_exact` branch aliases the file under
   the requested name. This form works.
4. **Declaration visibility style** — `hir_operators.spl` declares
   `enum HirBinOp:` with no `pub`, identical to `hir_types.spl`, which resolves.

## Vacuous evidence — do not repeat this mistake

An earlier pass eliminated "resolver returned empty" on the grounds that the log
contained **0** lines matching `unresolved import`. That elimination was void:
the same log contains **0** occurrences of `no source file found`,
`empty or excluded from compilation`, and `phase 1 FAILED` as well. Phase-1
`add_error` output is not captured on this channel at all — which is exactly what
the trailing `error: native-build failed without diagnostics` is reporting.
**Absence of an error line in this log is not evidence the error did not occur.**

Likewise, `source-inputs-after.txt` stores **hex-encoded** paths
(`file-hex:<len>:<hex>:...`), so a plaintext `grep` against it always returns 0
and proves nothing.

## Live hypotheses

- **A — closure walk drops it.** Two silent `continue`s in the closure loop
  (`80.driver/driver_source_pipeline_loading.spl:317` `closure_seen_mods`,
  `:320` `closure_loaded_mods`) skip a module with no diagnostic.
- **B — loaded, then pruned before lowering.** The phase counters are
  `logical=741` → `scanned=538` → **377** modules reaching phase-3 lowering.
  364 logical sources are dropped somewhere after loading; the owner modules may
  be among them.

A and B are distinguishable by making the two `continue`s loud, gated on a module
name, and running only as far as `phase1:load_sources:closure:done` (+225 s in
the failing run — a ~4 minute probe, not a full Stage 3).

## Discriminator run: hypothesis B REFUTED (2026-09-01)

`hir_definitions.spl:39` was temporarily given a plain
`use compiler.hir.hir_operators.{HirBinOp, HirUnaryOp, HirAssignOp}` alongside the
existing `export use`, mirroring two prior fixes in that file (lines 24 and 37)
whose comments record that a name reachable only via a glob or re-export hop is
invisible to the cross-module materialization walk.

Stage 2 rebuilt cleanly with the change (`stage2_rc=0`, binary sha
`8afbb714…` -> `7090b58c…`, so a genuinely different compiler ran). Stage 3 then
produced a **byte-identical** failure:

| | before | after |
|---|---|---|
| log lines | 10,127 | 10,127 |
| `unresolved type` fatals | 1,064 | 1,064 |
| `HirBinOp` / `HirUnaryOp` / `HirAssignOp` | 162 / 148 / 126 | 162 / 148 / 126 |
| `module=compiler.hir.hir_operators` | 0 | 0 |

**Hypothesis B (loaded, then pruned before lowering) is refuted for this module.**
An import that the materialization walk could act on changes nothing, because the
module never enters the build in the first place. The change was reverted rather
than left in: it is provably inert, and `.claude/rules/code-style.md` forbids
keeping unused code.

By elimination this leaves **hypothesis A**. Within A, the `closure_seen_mods`
branch cannot be the whole story either (it only suppresses a *retry*; the first
importer would still have loaded the module), so the live candidate is that
`_driver_resolve_entry_import` returned empty and the resulting `add_error` was
swallowed by the invisible-diagnostics channel described above.

Note this is elimination, not direct observation. It is recorded as the leading
hypothesis, not as the cause.

## Fix landed: make the closure drop observable

The reason this took three full bootstrap cycles to narrow is that **both** exits
from the closure loop are silent from a staged bootstrap's point of view:
`add_error` output is not forwarded by the Stage-3 native-build worker, so a
dropped module produced no signal at all until 10,000 lines later.

`80.driver/driver_source_pipeline_loading.spl` now emits a `log_phase` line on
both branches — `phase1:load_sources:closure:unresolved` (with module, importing
file, and search dir) and `phase1:load_sources:closure:already-loaded`.
`[BOOTSTRAP-PHASE]` lines ARE captured in the Stage-3 stderr log, so the next run
names the dropped module directly instead of requiring it to be inferred.

This does not fix the drop. It makes the drop self-reporting, which is the
precondition for fixing it — and for noticing the next one.


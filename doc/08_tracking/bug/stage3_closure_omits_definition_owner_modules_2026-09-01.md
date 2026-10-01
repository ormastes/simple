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
| `CacheCheckResult` | 12 | `compiler.driver.cache.cache_types` | **no** |
| `BlockValue` | 18 | `compiler.blocks.blocks.value` | yes — see correction |
| `ConcreteType` | 20 | `compiler.mono.monomorphize.types` | yes |
| `BackendKind` | 18 | `compiler.backend.backend_types` | yes |

Roughly **730 of 1,064** fatals are attributable to a missing owner module. The
remainder have owners that ARE loaded and are a separate question.

### Correction (2026-09-01, after the tracing run)

The first version of this table was partly wrong. Module names in this tree
**double the layer segment** — `src/compiler/70.backend/backend/codegen_types.spl`
is `compiler.backend.backend.codegen_types`, not `compiler.backend.codegen_types`
— and the script that built the table collapsed repeated segments, so it looked
up names that never existed and scored them "missing". Re-checked against the
real names from the closure trace:

- `compiler.blocks.blocks.value` — **loaded** (2 hits). `BlockValue`, 18 fatals.
- `compiler.backend.backend.codegen_types` — **loaded** (2 hits).
  `CodegenOutput`/`CodegenOutputKind`, 15 fatals.

Those ~33 fatals are NOT missing-owner cases and belong with the residue.
`compiler.hir.hir_operators`, `compiler.backend.feature_caps_types`,
`compiler.backend.feature_caps_arch32`, `compiler.common.error` and
`compiler.driver.cache.cache_types` were re-checked under both the doubled and
undoubled spellings and are genuinely absent.

The `Option` / `Dict` / `Result` rows (225 fatals) come from the same
first-match heuristic and are **not** established — those are builtins and their
attribution is almost certainly wrong. They are excluded from every count here.

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


## Tracing run 1: both closure-skip hypotheses refuted, real cause relocated (2026-09-01)

With the two skip branches traced, the run produced 17 `already-loaded` lines and
3 `unresolved` lines (all three prose false-positives: `this`, `ast`, `of`), so
the trace is live and non-vacuous. **`compiler.hir.hir_operators` appears on
neither branch** — it is never attempted. The third exit added afterwards
(`closure:excluded`) fired **zero** times in the following run, so that branch is
ruled out too.

Both remaining forms of hypothesis A are therefore refuted alongside B.

### Where the defect actually is

The per-file scan trace shows the importers ARE scanned, but their import lists
come back short:

| file | `use` lines in source | extracted by the running compiler |
|---|---|---|
| `20.hir/generated/hir_codec.spl` | 12 | **1** |
| `20.hir/hir_definitions.spl` | 9 | **6** |

A faithful line-by-line simulation of
`_driver_entry_import_module_paths_text_fallback` (including the docstring
toggle, the comment strip, the `lazy` handling, the delimiter cut, and
`_driver_import_path_is_valid`, which accepts alnum/`_`/`.` and so rejects
none of these) returns **12** and **9** — the algorithm as written is correct.

So the compiled extractor does not do what its source says, and every module
missing from the closure is missing because its importer's import list was
silently truncated. `hir_operators` is at line 11 of `hir_codec.spl` and line 39
of `hir_definitions.spl` — both past the truncation point.

Note `hir_codec.spl` is a 230 KB generated file whose line 9 ends at byte 486 and
line 10 at byte 515, so `imports=1` is consistent with the content being cut near
a 512-byte boundary. That is a numeric coincidence worth testing, **not** an
established cause: no size cap was found in `rt_file_read_text`
(`src/runtime/runtime.c:1728`), though its `rt_string_new(content, strlen(content))`
would truncate at any embedded NUL.

### Next step

The trace now also prints `content_len` per scanned file and one line per
extracted module path. That distinguishes a short READ (content_len far below the
real file size) from a short PARSE (full content, truncated list), and shows
whether the survivors are a prefix or a scattered subset.

### Method note

Three root-cause stories have been adopted and two discarded in this
investigation. Each was discarded by a measurement, not by argument, and each
discard is recorded above rather than edited away.

## ROOT CAUSE (2026-09-01) — `char_code_at` is char-indexed, `len()`/slicing are byte-indexed

`_driver_line_end` (`80.driver/driver_source_loading.spl:492`) walked source lines with

```
while end < content.len() and content.char_code_at(end) != 10:
```

`rt_string_char_code_at` (`src/runtime/runtime_native.c:2882`) is **character**-indexed —
it decodes UTF-8 — while `text.len()` returns the **byte** length (`s->len`) and text
slicing is byte-based (`_driver_text_index_of` derives its index from
`split(needle)[0].len()`, so it agrees with slicing, not with `char_code_at`).

Inside an ASCII prefix a character index IS a byte index, so the mix is invisible.
At the first multi-byte character the two diverge, `_driver_line_end` returns an
offset in the wrong unit, and every line after that point is sliced from the wrong
place and silently dropped by the import scanner.

### Evidence

Contingency over all 538 files scanned in one Stage-3 closure:

|  | imports LOST | imports COMPLETE |
|---|---|---|
| file contains non-ASCII | **90** | 120 |
| file is pure ASCII | **1** | 248 |

`hir_definitions.spl` extracted exactly the 6 imports on lines <= 28 and dropped the
3 on lines 37-39 — a clean split at **line 34, byte 2009**, the file's first
non-ASCII byte (an em dash `\xe2\x80\x94` in a comment). Line 39 is
`export use compiler.hir.hir_operators.{...}`, which is why that module never
entered the closure and 200 files then failed on `HirBinOp`/`HirUnaryOp`/`HirAssignOp`.

The 120 non-ASCII-but-complete files are consistent with the mechanism: their first
non-ASCII byte falls after their last import line.

### Fix

`content.byte_at(end)` instead of `content.char_code_at(end)` — the byte-indexed
accessor that pairs with `len()` (canonical pairing at
`src/app/compiler_schema/fold_gen.spl:426`). `_driver_import_path_is_valid` carried
the identical mix (`char_code_at` under a `len()` bound) and was fixed with it.

### Correction: the "compiled extractor" claim above was WRONG

The previous section concluded that `hir_codec.spl` has 12 `use` lines but the
compiler extracted 1, and inferred that the compiled extractor did not match its
source. That inference was false, and no codegen defect exists. There are **two**
files:

- `src/compiler/20.hir/hir_codec.spl` — 4,641 bytes, a facade with 4 imports
- `src/compiler/20.hir/generated/hir_codec.spl` — 230,011 bytes, the generated codec

The trace's `content_len=4641` matches the facade **exactly**; the closure loaded the
facade, which is correct, and nothing was truncated. The comparison was against the
wrong file. The 512-byte-boundary coincidence noted earlier was likewise a red
herring and is withdrawn.

Only `hir_definitions.spl` (`content_len=29609`, the full file, 9 use lines, 6
extracted) was ever real evidence, and that is fully explained by the em dash.

### Method note

Four root-cause stories were adopted in this investigation and three discarded, each
by a measurement rather than an argument. The step that resolved it was printing
`content_len` next to the import count — the one datum that separates a short READ
from a short PARSE. All discarded stories are retained above rather than edited away.

## Fix VERIFIED, but Stage 3 is NOT green (2026-09-01)

Measured with the fixed Stage-2 compiler, `compile --format=smf` on
`src/app/cli/bootstrap_main.spl` with the entry closure enabled:

| | before | after |
|---|---|---|
| entry-closure modules | 741 | **763** |
| `hir_operators.spl` in the build | absent | **parsed as source 354/763** |
| `HirBinOp` + `HirUnaryOp` + `HirAssignOp` fatals | 436 | **0** |
| `unresolved type` occurrences | 1,064 | 910 |
| distinct files with hir-fatals | 200 | 172 |

The targeted family is eliminated and the closure recovered the 22 modules it had
been dropping. **The build still fails** (`phase 3 FAILED`), now dominated by a
different set whose top entries are `LocalId` (65), `MirModule` (64),
`MirFunction` (40), `MirType` (39), `BlockValue` (27), `PrimitiveType` (25).

Two cautions on reading the after-column:

- It comes from a `compile` invocation, not the Stage-3 native-build, so the
  totals are indicative rather than strictly comparable. The `436 -> 0` is safe
  either way: those symbols cannot resolve if their owner is absent, and the
  owner is now demonstrably present.
- `Option` / `Result` / `Dict` still appear in the raw `unresolved type` count but
  are **not** `[hir-fatal]` lines — they come from the advisory
  `[hir-callable-dep-origin-unresolved]` channel. They are excluded from the
  per-type table above, which counts only true `^[hir-fatal]` lines.

Whether the remaining MIR-type failures are the same defect class (owners reachable
only through a glob or re-export hop) or something else is **not yet established**.
More code now reaches lowering than before, so some of these may be newly exposed
rather than newly broken.

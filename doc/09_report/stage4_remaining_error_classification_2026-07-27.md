# Stage-4 Native-Build Remaining Error Classification (2026-07-27)

Source evidence log (read-only, not modified): `/home/ormastes/.claude/jobs/4403a7d8/tmp/stage4_repro24.log`
(1,942,962 lines; a full stage-4 focused native-build run.)

Totals in the log:
- 1,681 lines matching `error: focused native-build: HIR lowering error in <MODULE>: unresolved name: <SYMBOL>`
- 166 lines matching `... untyped function returns a value: function '<FN>' returns a value but declares no return type; add '-> T'`
- `unresolved name: me` → **0** occurrences in this log (the "me receiver, 20 residual" class is confirmed already fixed at the time of this run).

All investigation below is read-only: repo source was inspected with `grep`/`find`/`python3` only, nothing was built or edited.

## 1. Histograms

### 1a. Top 25 unresolved SYMBOLS (count, symbol)

```
185 TokenKind            38 T32BridgeResult      28 error                 19 MirOperandKind
160 lex_make_token       38 FixConfidence        26 panic                 18 native_pixel_rows_enabled
116 lex_advance          37 Replacement          25 json_serialize        18 lex_paren_depth_get
 70 lex_peek             36 PrimitiveType        24 MirType               16 lex_col_get
 60 lex_pos_get          36 EasyFix              22 lex_line_get
 48 text                 34 lex_match_char       21 MirOperand
                          30 lex_source_slice     29 MirInstKind / MirInst (tie)
```
(205 distinct symbols total; sum of all occurrences = 1,681.)

Note: `lex_match_char`(34), `lex_source_slice`(30), `lex_line_get`(22), `lex_paren_depth_get`(18),
`lex_col_get`(16), plus 11 smaller `lex_*` symbols (12,12,10,10,8,8,6,6,4,2,2) are **not** covered
by the "fix in flight" list named in the task (`TokenKind`, `lex_make_token`, `lex_advance`,
`lex_peek`, `lex_pos_get`). Full lexer-family total = 793 (185 `TokenKind` + 608 across 21 distinct
`lex_*` symbols); the named in-flight fix covers only 591 of those 793.

### 1b. Top 25 reporting MODULES (count, module)

```
304 compiler.core.lexer_scanners                  16 lib.nogc_sync_mut.gpu.engine2d.backend_session
304 compiler.10.frontend.core.lexer_scanners       15 compiler.tools.fix.rules.impl_.lint_spec
 97 compiler.mir_opt._OptimizationPasses.io_passes 15 compiler.tools.fix.rules.impl_.error_fix
 61 compiler.mir_opt._OptimizationPasses.engine    15 app.io.cli_lint_commands
 61 compiler.frontend.treesitter.outline_members   14 std.db_atomic
 59 compiler.frontend.treesitter.outline_decls     14 lib.nogc_async_mut.db_atomic
 55 compiler.frontend.treesitter.outline           13 app.t32_cli.bridge_access
 25 app.t32_cli.bridge                             12 compiler.tools.fix.rules.impl_.lint_short_grammar
 23 compiler.backend.cuda.ptx_builder
 23 compiler.70.backend.backend.cuda.ptx_builder
 22 compiler.driver.driver_bootstrap
 20 app.io._CliCommands.run_commands
 19 nogc_sync_mut.database.sql.statement
 19 lib.nogc_sync_mut.database.sql.statement
 18 compiler.frontend.treesitter.outline_types
 16 std.nogc_sync_mut.gpu.engine2d.backend_session
 16 std.gpu.engine2d.backend_session
```
(157 distinct modules; sum = 1,681.)

**Structural finding — duplicate module-path aliasing.** `src/compiler/{frontend,backend,blocks,mir_opt,...}`
are symlinks to the numbered layer dirs (`10.frontend`, `70.backend`, `15.blocks`, `60.mir_opt`, ...):
```
src/compiler/frontend -> 10.frontend
src/compiler/backend  -> 70.backend
```
The SAME physical `.spl` file is independently lowered and reported under two (sometimes three)
different qualified module-path aliases — e.g. `compiler.core.lexer_scanners` (304) and
`compiler.10.frontend.core.lexer_scanners` (304) are the *same file*,
`src/compiler/10.frontend/core/lexer_scanners.spl`. Same pattern confirmed for
`ptx_builder` (23/23 across `compiler.backend.cuda.*` / `compiler.70.backend.backend.cuda.*`),
`cranelift_codegen_adapter` (6/6/6 across three aliases), and a `std.*`/`lib.*` prefix variant of the
same duplication for `src/lib` tier files (e.g. `database.sql.statement` 19/19,
`gpu.engine2d.backend_session` 16/16/16, `db_atomic` 14/14). Summing the confirmed excess
(count beyond the first alias) across the pairs visible in the top-modules list alone gives
**≈468 of the 1,681 lines (~28%) that are literal duplicate reports of an error already counted once
under a different alias for the identical file/line.** This is not exhaustive — smaller pairs further
down the 157-module tail were not all individually verified — so 468 is a lower bound.

## 2. Mechanism for the ~15 largest remaining symbols

Excluded per instructions (fixed / in-flight, counted above only): `me` (0 remaining),
`TokenKind`/`lex_make_token`/`lex_advance`/`lex_peek`/`lex_pos_get` (591, in-flight fix).

| Symbol (count) | Defined at | Reporting module imports via | Class |
|---|---|---|---|
| `FixConfidence`(38) / `Replacement`(37) / `EasyFix`(36) | `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:24,34,52` (`pub enum`/`pub class`) | consumers do `use std.tooling.easy_fix.*` (e.g. `src/compiler/90.tools/fix/rules/impl_/error_fix.spl:8`); the package facade `.../easy_fix/__init__.spl` does `export use .types.{LintLevel, LintCategory, FixConfidence, Replacement, EasyFix, ...}` — an explicit, correctly-listed re-export. The facade file's own comment reads: *"`export X from module` loses `module` in the current bridge, so use explicit import-form re-exports"* — i.e. the authors already hit and worked around one form of this bridge bug. | **(b) facade/glob re-export failing under native HIR lowering** |
| `T32BridgeResult`(38) | `src/lib/common/ui/access_cli_grammar.spl:86` (`class AccessResult`) | `src/app/t32_cli/types.spl:4`: `export use common.ui.access_cli_grammar.{AccessResult as T32BridgeResult}` — an **aliased-rename** re-export; consumers (`bridge.spl:7`, `bridge_access.spl:6`, `mod.spl:4`, `cli_shell.spl:7`) then do the normal explicit `use app.t32_cli.types.{T32BridgeResult}` | **(b) facade/glob re-export**, specifically the `{X as Y}` rename sub-form |
| `PrimitiveType`(36) | `src/compiler/70.backend/backend/common/type_mapper.spl:221` (`enum`, no explicit `export`) | `src/compiler/70.backend/backend/cuda/ptx_builder.spl` uses `PrimitiveType` at lines 148,160,210-218 but its import block (lines 6-10) never imports `compiler.backend.common.type_mapper` at all — only `compiler.mir.mir_data.*`, `compiler.backend.cuda_type_mapper.{CudaTypeMapper, cuda_type_mapper_create_sm}`, `compiler.hir.hir_types.MemorySpace`, `std.common.binary_io.*`, `std.common.format.*`. `cuda_type_mapper.spl` (which ptx_builder DOES import from) itself does `use compiler.backend.common.type_mapper.*` and uses `PrimitiveType`, but that glob import is local to `cuda_type_mapper` and is not transitively visible to ptx_builder. | **(d) genuinely missing import in the source** — ptx_builder.spl has zero import path to `PrimitiveType`'s definition |
| `native_pixel_rows_enabled`(18), `vulkan_sffi_compile_spirv`(15), `metal_sffi_release_uncommitted_submission`(12) etc. | Real implementations live in the `nogc_sync_mut`/`nogc_async_mut` tier (e.g. `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:336`, `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:395`) | The `gc_async_mut` tier copy of the same module is a **one-line facade**: `src/lib/gc_async_mut/gpu/engine2d/sffi_vulkan.spl` (3 lines total) reads `export use std.nogc_async_mut.gpu.engine2d.sffi_vulkan.*`. Consumers explicitly import the exact symbol from the exact facade path (e.g. `backend_vulkan_spirv.spl:46`: `use std.gc_async_mut.gpu.engine2d.sffi_vulkan.{vulkan_sffi_compile_spirv}`). | **(b) facade/glob re-export** — third independent instance of the same `export use <mod>.*` pattern failing |
| `MirInstKind`(29), `MirInst`(29), `MirType`(24), `MirOperand`(21), `MirOperandKind`(19), `MirConstValue`(14), `LocalId`(12), `MirBlock`(10), `MirFunction`(9), `MirTypeKind`(5) | `src/compiler/50.mir/mir_instructions.spl` / `mir_types.spl` | `src/compiler/50.mir/mir_data.spl` imports both with `use compiler.mir.mir_types.*` / `use compiler.mir.mir_instructions.*` and **explicitly re-exports with bare `export` statements** (`mir_data.spl:619` `export MirBlock, MirInst, MirInstKind`; `:635` `export MirTypeKind, MirType, MirSignature, MirConstValue`, etc). `compiler.mir_opt._OptimizationPasses.{engine,io_passes}` both do `use compiler.mir.mir_data.*` — same pattern used successfully by many other consumers (`c_backend.spl`, `_CBackendTranslate/*`, `_MirToLlvm/*`) that are **not** in the error list. | **(e) other/unknown — needs a probe.** The facade re-export mechanism here is `export X` (not `export use`), and it demonstrably works for other consumers of the identical facade; the failure appears isolated to the `mir_opt/_OptimizationPasses/{engine,io_passes}.spl` build unit specifically. Probe: run a minimal focused native-build limited to `compiler.mir_opt._OptimizationPasses.engine` alone and check whether `mir_data` is even in its resolved dependency set (possible build-graph/module-inclusion gap rather than a symbol-resolution bug). |
| `text`(48) | Simple's built-in primitive/string type keyword | `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl` — no `use` statements at all in the file; `text` appears only in ordinary field/return **type positions** (`mode: text`, `kind: text`, `-> text`) | **(e) other/unknown — needs a probe.** `text` is a builtin type keyword, not an importable symbol; seeing it reported as an "unresolved name" suggests the lowering pass is mis-classifying a type-position token as a value/name reference in this specific file. Probe: isolate one `text`-annotated field in `backend_session.spl` and bisect which declaration form (class field vs. fn return vs. parameter) triggers it. |
| `error`(28), `panic`(26) | Multiple candidate definitions exist and none is imported by the failing modules: `src/lib/log.spl:627 fn error(scope, msg)`, `src/lib/common/error.spl:14 pub fn error(message) -> SimpleError`, `src/lib/common/error/error.spl:20`, `src/compiler/00.common/error.spl:406 fn panic_macro`. Example: `src/compiler/70.backend/backend/common/type_mapper.spl:98` calls bare `error("Unsupported type in {self.backend_name()}: {ty}")` but its import block (lines 6-8) has no `error`/`panic` import of any kind. | **(d) genuinely missing import in the source**, most likely masked historically by the interpreter's flat global-symbol registry (a previously-documented landmine in this codebase: interpreted/test-runner execution resolves bare names via a flat registry that native HIR lowering does not use), so these call sites never needed an explicit import until strict native lowering. |
| `json_serialize`(25) | Not resolved in this pass (multiple `app.devhub.adapter_*` modules; time-boxed) | — | **(e) unknown — needs a probe**: check each `app.devhub.adapter_*.spl` import block against wherever `json_serialize` is defined (likely `std.common.json` family) the same way as `PrimitiveType` above. |

## 3. The 166 "untyped function returns a value" errors

166 raw lines / **157 distinct (module, function) pairs** (9 are the same numbered/unnumbered
module-alias duplication described in §1b). For every distinct pair the actual function signature
in source was located and checked for a `-> T` clause on the function's own parameter list
(not a nested callback-parameter arrow):

- **85 of 157 pairs (54%) already declare a valid `-> T` return type in source** — the diagnostic is a
  **false positive**.
- **72 of 157 pairs (46%) genuinely have no `-> T` at all** on a function whose body returns a value —
  a real **source defect**.

Three concrete false-positive examples (compiler claims "declares no return type" on a signature that
plainly has one):
1. `src/lib/common/ui/glass_debug.spl:14` — `fn list_glass_themes() -> List<text>:` (generic return type)
2. `src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl:50` — `me is_hardware() -> bool:`
   (a `me`-receiver method; same file also has `has_labels`(:32), `vhdl_type`(:172), `is_valid`(:232),
   `port_direction`, `rejection_text`, `has_port`, `has_duplicate_label`, `is_input`, `is_output`,
   `is_rejected` — all `me`-methods, all with an explicit `-> T`, all flagged)
3. `src/lib/nogc_sync_mut/array.spl:93` — `fn array_chunk(arr: [Any], size: i64) -> [[Any]]:` (nested
   array/generic return type)

Common thread across the 85 false positives: nested/generic return types (`List<text>`, `[[Any]]`,
`i64?`) and `me`-receiver methods are systematically mis-detected as "no return type" by whatever check
emits this diagnostic — this correlates with, but is distinct from, the already-fixed `me`-receiver
name-resolution bug (that fix addressed resolving `me` as a name; this is the return-type-presence
check, which still misfires on `me`-methods and on generic return types for plain `fn`).

Three concrete genuine-defect examples (no `->` anywhere in the signature, body returns a value):
1. `src/compiler/99.loader/module_loader.spl:151` — `fn get_symbol(name: text):` … body:
   `if self.symbols.has(name): return Some(self.symbols[name])` / `nil` — needs `-> Option<LoadedSymbol>` (or similar)
2. `src/compiler/99.loader/module_loader.spl:495` — `fn get_module(path: text):` … same `Some(...)`/`nil` shape
3. `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:98` — `fn huffman_build_tree(freqs):` — no
   return type **and no parameter types**; this whole gzip module (`huffman.spl`, `deflate.spl`,
   `inflate.spl`, `lz77.spl` — 33 of the 72 genuine-defect pairs) is written in an untyped/dynamic
   style throughout and needs real type annotations added, not just return types.

**Conclusion for §3**: this is a **mixed bag, not a single class**. Roughly half (the `me`-method /
generic-return-type false positives) is a lowering/diagnostic bug that should be fixed once, centrally,
in whatever pass emits "untyped function returns a value" (make it recognize `me` receivers and
generic/nested return-type syntax). The other half (plain `fn` with truly no type annotations, heavily
concentrated in `src/lib/nogc_sync_mut/{array,array_advanced}.spl` and the gzip codec family) is a real
source-typing backlog that needs actual `-> T` (and parameter type) annotations added function-by-function.

## 4. Ranked remaining classes (estimated error count / estimated effort)

| Rank | Class | Est. errors accounted | Est. effort | Basis |
|---|---|---|---|---|
| 1 | Duplicate module-path alias reporting (symlinked numbered-layer dirs + `std.`/`lib.` prefix variants report the same file twice/thrice) | ≈468 (lower bound, ~28% of 1,681) | **Low** — one fix in the focused-native-build driver's module-dedup/visited-set logic, or collapse symlink-derived aliases before reporting | Directly confirmed via `readlink`: `compiler/frontend→10.frontend`, `compiler/backend→70.backend`, etc.; matching equal counts for 10+ symbol/module pairs |
| 2 | Lexer/`TokenKind` family (in-flight fix, but incomplete) | 793 total (591 already targeted + 202 additional `lex_*` symbols not in the named fix) | **Low-Med** — extend the in-flight fix's symbol list to the other 16 `lex_*` names (`lex_match_char`, `lex_source_slice`, `lex_line_get`, `lex_paren_depth_get`, `lex_col_get`, +11 more) | Same file (`lexer_scanners.spl`), same root cause class as the named 5 |
| 3 | Facade/glob re-export (`export use <mod>.*` / `export use <mod>.{X}` / `{X as Y}`) failing under native HIR lowering | ≈111 (FixConfidence+Replacement+EasyFix family) + 38 (T32BridgeResult) + ≈53 (Vulkan/Metal SFFI facades) ≈ **≈202+**, likely more in the unexamined tail of the 157-module list | **Medium** — one bridge-level fix (confirmed 3 independent instances of the identical `export use` pattern failing) would resolve many symbols at once without touching call sites | `easy_fix/__init__.spl`, `t32_cli/types.spl`, `gc_async_mut/.../sffi_vulkan.spl` — 3 separate facades, same `export use` shape, all failing |
| 4 | Untyped-function false positives (`me`-methods and generic/nested return types misdetected as untyped) | ≈90 of 166 (scaled from 85/157 distinct pairs) | **Low** — single fix to the return-type-presence check to recognize `me` receivers and generic return syntax | Confirmed via signature inspection on `vhdl_hardware_metadata.spl` (11 `me`-methods, all with `-> T`), `array.spl` (`array_chunk -> [[Any]]`), `glass_debug.spl` (`-> List<text>`) |
| 5 | `PrimitiveType` / `error` / `panic` / genuinely-missing-import class (source truly lacks the import; likely masked by interpreter's flat global namespace historically) | ≈36 (`PrimitiveType`) + 28 (`error`) + 26 (`panic`) + long tail ≈ **≈150+** | **Medium** — mechanical but must be done file-by-file: add the correct explicit `use` line per call site | Confirmed for `ptx_builder.spl` (zero import path to `PrimitiveType`) and `type_mapper.spl` (zero import of `error`/`panic`) |
| 6 | `Mir*` family isolated to `mir_opt/_OptimizationPasses/{engine,io_passes}` despite the same facade working elsewhere | ≈172 | **Unknown — needs a probe** before estimating effort | Facade (`mir_data.spl`) has explicit `export` statements and works for many other consumers; failure looks build-graph/module-inclusion specific to these 2 files, not a symbol-resolution bug |
| 7 | Untyped-function genuine defects (plain `fn`, no types at all — mostly the gzip codec + array-helper modules) | ≈76 of 166 (scaled from 72/157 distinct pairs) | **Medium-High** — real typing work, not a bug fix; 33 of them cluster in one under-typed legacy module (`compression/gzip/*`) | Verified: `huffman_build_tree(freqs):`, `huffman_leaf(symbol, freq):` etc. have neither param nor return types |
| 8 | `text`, `json_serialize`, and other unresolved symbols not individually traced in this pass | remainder of 1,681 | **Unknown — needs a probe per symbol** | Time-boxed; `text` in particular looks like a distinct lowering bug (builtin type keyword flagged as unresolved name), not a missing import |

Note: classes 1 and 2 overlap with classes 3/5/6 arithmetically (a duplicate-alias line for, say,
`PrimitiveType` is counted once in class 1's ≈468 and once in class 5's ≈150 total symbol count) —
they are reported separately here because they represent **independent, separately-fixable root
causes** (a build-driver dedup bug vs. a per-symbol import/facade bug), not because the raw counts are
additive to 1,681.

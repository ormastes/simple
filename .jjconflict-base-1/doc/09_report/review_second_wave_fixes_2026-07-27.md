# Adversarial review — second-wave stage-4 fixes (2026-07-27)

Read-only review of four commits landed on `main` today. All line references are
to the **`main`** content (`git show main:<path>`), not the working tree — this
checkout is on a detached HEAD (`584e74ece31d`) that predates all four commits,
so on-disk files differ. All four commits verified present on `main` and
`origin/main` via `git merge-base --is-ancestor`.

| # | Commit | Subject | Verdict |
|---|--------|---------|---------|
| 1 | `e599a617d6ef` | parser: `export NAME from MODULE` | **risky** — parses correctly, but does not fix the symptom it claims to fix |
| 2 | `40915eea6cb` | `text(x)` → `str(x)` (23 sites) | **sound** |
| 3 | `3ab74b15387` | 24 added `use` lines across 22 files | **sound** (two latent hazards noted) |
| 4 | `88ea42c396e4` | 70 return-type annotations | **defective** — 3 independently confirmed high-severity defects |

---

## 1. `e599a617d6ef` — parser support for `export NAME from MODULE`

**Verdict: risky.** The parsing is correct and safe. The *module path it emits*
cannot be resolved by the re-export chaser, so the declaration still does not
make the symbol visible to downstream consumers — which was the entire stated
motivation.

### HIGH — the emitted `"." + name` relative path is unresolvable in `find_reexport_source`

`src/compiler/10.frontend/core/parser_decls_use.spl:287-302` (main) emits
`decl_use_import("." + from_module, names, 0)` for the common bare-sibling case
(`export FixConfidence from types` → module `.types`).

Two different code paths consume that module string, and only one of them knows
about leading dots:

- `resolve_import_symbols` — `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:815`
  has an explicit `imp.module.starts_with(".")` branch that normalizes the
  relative path against the importing module's own name. This is the path the
  commit message cites, and it does work.
- `find_reexport_source` — `module_lowering.spl:601` resolves the hop with
  **`self.resolve_module_key(imp.module)` and nothing else**.
  `resolve_module_key` (`module_lowering.spl:536-573`) has **no leading-dot
  branch**. For `.types` its candidate list is exactly
  `".types"`, `".types.__init__"`, `"lib..types"`, `"lib..types.__init__"`
  (the `std.`-prefixed tier expansion at :557 is skipped because the name does
  not start with `std.`). `modules_by_name` is keyed by path-derived dotted
  names, which never begin with a dot, so all four miss and the function
  returns `""`. `next_key == ""` → the import is skipped → the chase reports
  `found: false`.

**Failure scenario.** A package facade `pkg/__init__.spl` contains
`export FixConfidence from types`. Consumer module C writes
`use std.tooling.easy_fix.{FixConfidence}`.
`resolve_import_symbols(C)` resolves the facade, calls `register_imported_symbol`
(`module_lowering.spl:470`); the facade does not *declare* `FixConfidence`, so
control reaches the re-export-chase `else` branch (`module_lowering.spl:~515`),
which calls `find_reexport_source` — which fails per the above. **Nothing is
registered, and C still dies with `unresolved name: FixConfidence`.** The new
`export … from …` line only helps code *inside* the facade file itself.

**Corroborating evidence that this is real, not theoretical:**

- `src/lib/nogc_sync_mut/tooling/easy_fix/__init__.spl:6-19` already carries a
  hand-written workaround for exactly this — both `export use .types.{…}` *and*
  a duplicated set of plain `export …` lines — with a comment saying
  `"export X from module` loses `module` in the current bridge".
- Commit **`3ab74b15387` is itself the workaround**: it adds 22 explicit
  `use std.tooling.easy_fix.types.{FixConfidence}` lines at consumer sites.
  In `src/app/io/_CliCommands/run_commands.spl` the pre-existing facade import
  `use std.tooling.easy_fix.{FixConfidence}` still sits at **:14**, eight lines
  below the newly added direct import at **:6** — the facade spelling was, and
  remains, a silent no-op. Same shape in `src/app/io/cli_lint_commands.spl:5`
  vs `:10`.

**Fix direction:** either emit an absolute/canonical module path from the
parser, or give `find_reexport_source` the same leading-dot normalization
`resolve_import_symbols:815` already has (it has `facade_name`, so it has the
context needed). Note this also fixes the pre-existing `export use .types.{…}`
idiom, which has the identical hole.

### Sound aspects (checked, no action)

- **Reachability.** The new branch cannot fire for any pre-existing form.
  `export use …` returns at `parser_decls_use.spl:181` (kind 27 → `parse_use_decl`),
  `export X.*` returns at :190, `export X.{a,b}` returns at :210. `export A as B`
  falls through and correctly supports an optional trailing `from` — no regression.
- **Token constants are correct.** `TOK_IDENT = 6` and `TOK_DOT = 164`
  (`src/compiler/10.frontend/core/tokens.spl:24,130`), matching the raw numeric
  literals the surrounding legacy code uses.
- **Alias encoding survives.** `"name:alias"` is decoded downstream:
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:512-519` splits on
  `":"` for `DECL_USE` (tag `"6"`) and sets `has_alias`/`alias`. So
  `export A as B from types` works. (Contrast: the export node path, tag `"7"` at
  `module_assembly.spl:527`, copies items raw and does **not** split — so plain
  `export A as B` keeps the literal `"A:B"`. Pre-existing, unchanged here.)
- **No misfire on the token after the name list.** `at_from`
  (`parser_decls_use.spl:287`) compares against `TOK_IDENT` + text `"from"`.
  `TOK_NEWLINE` (`tokens.spl:143`) is a real token the parser observes
  (`src/compiler/10.frontend/core/parser_stmts.spl:827`), so a following-line
  statement beginning with an identifier is separated by a newline token and
  cannot be mistaken for `from`.

### LOW findings

- **Malformed input errors, does not hang.** `parser_expect`
  (`src/compiler/10.frontend/core/parser.spl:230-246`) does **not** advance on
  mismatch, but the dotted loop is bounded (`for i in 0..100`) and its guard
  breaks on any non-`TOK_DOT` token, so there is no infinite loop. `export A from`
  at EOF emits a diagnostic and sets `par_had_error`, then still returns a bogus
  `decl_use_import(".", …)` node — harmless because the build fails on the
  diagnostic, but the node should not be created.
  `parser_decls_use.spl:288-302`.
- **Two spellings for one concept.** The sibling brace form emits a **bare**
  module name (`parser_decls_use.spl:210`, `decl_use_import(first_name, …)`)
  while the new branch emits a **dot-prefixed** one for the same
  "sibling module" situation. The two are resolved by different code paths with
  different capabilities (see the HIGH finding). Pick one.
- **Path depth cap.** `for i in 0..100` (`parser_decls_use.spl:293`) silently
  truncates a module path deeper than 100 segments rather than erroring. Also
  shadows the outer loop's `i` — harmless.

---

## 2. `40915eea6cb` — `text(x)` → `str(x)` at 23 sites

**Verdict: sound.** No defects found.

- **All 23 arguments are `i64` or `bool`**, verified against their declarations:
  `comptime_checker.spl:153` (`checker_error_count: i64`, declared :22);
  `draw_batcher.spl:50-52` (3× `i64` on `BatchStats`);
  `texture_atlas.spl:114,131` (`TextureId.raw: i64` per
  `src/lib/common/engine/ids.spl:26`, plus `w`/`h` `i64` params);
  `backend_session.spl:218,258,295,321` (16 sites, all `i64`/`bool`).
  The obvious float trap — `submit_us`/`present_us`/`readback_us`/`total_us` at
  `backend_session.spl:321` — is **`i64` microseconds**, not `f64`. No struct,
  enum, `T?`, `Any`, pointer, or already-`text` argument anywhere.
- **Diff hygiene holds.** Reverse-substituting `\bstr\(` → `text(` on every `+`
  line reproduces the `-` line byte-identically for all 10 hunks; net `str(`
  delta is exactly 23. `me to_text() -> text:`, `-> text:` returns, and
  `code: text` / `message: text` field annotations appear only as unchanged
  context.
- **Rendering identity is structural, not coincidental.** `str(x)` and `+`
  concatenation both route through the same `coerce_concat_operand`
  (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:307`, used for `+` at
  :1967-1968 and for `str` at
  `_MirLoweringExpr/switch_operators_calls.spl:2895`). The commit's cited
  evidence for `str` support checks out at all three layers (HIR
  `expressions.spl:51`, MIR `switch_operators_calls.spl:2891`, interp
  `interpreter_calls.spl:99`).
- **Fix is complete.** No real `text(x)` conversion calls remain in owned code
  (`src/lib`, `src/os`, `src/app`, `src/compiler`). Remaining grep hits are
  `fn text(...)` declarations, `text(text)` enum-variant constructors in the seed
  stdlib, `":has-text(\""` string literals, and comments.

### LOW

- The commit message's "semantics preserved / same rendering" claim is
  **scalar-only**. `str()` on a non-scalar falls through to `rt_value_to_string`,
  whereas bare `+` concatenation leaves the operand raw for `rt_strcat_tagged`
  to dereference — the two diverge for structs and `Any`. Not triggered by any
  of these 23 sites, but the blanket wording could mislead a future edit that
  adds a non-scalar argument.

---

## 3. `3ab74b15387` — added `use` lines across 22 files

**Verdict: sound.** The duplicate-import concern the author self-flagged is
benign, and no import names the wrong module.

- **Duplicate `FixConfidence` is legal and binds the right definition.**
  `SymbolTable.define` is documented and implemented as **first-write-wins for
  type-level symbols** (Class/Struct/Enum/Trait) —
  `src/compiler/20.hir/hir_types.spl:219-244`, with the early
  `return SymbolId(id: scope.symbols[name])` at :244. There is exactly **one**
  `FixConfidence` definition in the repo
  (`src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:24`), so both spellings
  denote the same enum regardless of order. Additionally, the new direct import
  is placed **first** in both files (`run_commands.spl:6` before the facade
  import at `:14`; `cli_lint_commands.spl:5` before `:10`), so the working
  spelling wins. The facade spelling was already a no-op — see finding 1.
- **No wrong-module imports.** Single definitions confirmed for every added
  symbol: `PrimitiveType` at
  `src/compiler/70.backend/backend/common/type_mapper.spl:221`; `MirBlock`,
  `MirInst`, `MirInstKind`, `MirOperand`, `MirOperandKind`, `MirFunction` at
  `src/compiler/50.mir/mir_instructions.spl:34,45,51,507,512,598`; `LocalId`,
  `MirConstValue`, `MirType`, `MirTypeKind` at
  `src/compiler/50.mir/mir_types.spl:27,65,130,135`. The module spelling
  `compiler.backend.common.type_mapper` used in `cuda/ptx_builder.spl:6` matches
  four pre-existing sibling imports (`cuda_type_mapper.spl:7`,
  `llvm_type_mapper.spl:7`, `c_type_mapper.spl:8`, `vulkan_type_mapper.spl:7`).

### MEDIUM (latent, not triggered by this commit)

- **`LintLevel` / `LintCategory` are doubly defined** —
  `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:32,553` versus
  `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:8,13`. The added lines in the
  two `90.tools/lint/_LintMain/` files correctly import only
  `{FixConfidence, Replacement, EasyFix}` and dodge the collision. But because
  these `use` lines sit at the top of the file and `define` is first-write-wins,
  **any future widening of these import lists to include `LintLevel` or
  `LintCategory` would silently rebind the compiler's own lint enums to
  easy_fix's**, with no diagnostic. Worth a guard comment on those two lines
  (`lint_checks.spl`, `traceability_and_assertions.spl`).

### LOW

- **Explicit imports now outrank pre-existing globs.**
  `_OptimizationPasses/engine.spl:15-16` and `io_passes.spl:15-16` are inserted
  *above* the glob imports at `:17` (`compiler.mir.mir_data.*`) and `io_passes.spl:18`
  (`…_OptimizationPasses.engine.*`). Under first-write-wins this changes which
  registration path wins: explicit item imports go through
  `rename_symbol` + `register_imported_type_methods`
  (`module_lowering.spl:474-492`), globs re-enter the same function via
  `register_glob_imported_symbols_depth` (`:705`) and hit the `already_bound`
  guard. Benign here because both routes name the same definitions, but it is a
  behavioral change, not a pure addition.

---

## 4. `88ea42c396e4` — 70 return-type annotations across 17 files

**Verdict: defective.** Three high-severity defects independently confirmed
against `main`, plus several medium ones. This commit should not have landed
as-is.

> Note: a first-pass reviewer reported these commits as "not an ancestor of
> HEAD / unlanded". That is a **checkout artifact** of this detached worktree —
> `git merge-base --is-ancestor 88ea42c396e4 main` succeeds. The commit is live
> on `main` and `origin/main`.

### HIGH — a spec that pins source text is now deterministically failing

`test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl:5`
asserts:

```
return source.to_contain("fn deflate_block_parse(data, offset):") and
```

but `main:src/lib/nogc_sync_mut/compression/gzip/inflate.spl:426` is now:

```
fn deflate_block_parse(data, offset) -> [Any]?:
```

The pinned literal no longer occurs in the file, so `to_contain` returns false
and the spec fails on every run. This is the only source-text pin among the 70
changed signatures, and the commit walked straight into it. **Build/test
breaking on `main` right now.**

### HIGH — gzip byte-array functions annotated `[Any]` but return `[u8]`

`main:src/lib/nogc_sync_mut/compression/gzip/huffman.spl:424`:

```
# Flush remaining bits (zero-pad to byte boundary), return final [u8] byte array
fn bitstream_finish(bs) -> [Any]:
```

The body is `var bytes = bs[0]` … `return bytes`, and `bs[0]` originates at
`bitstream_new` (`huffman.spl:374-376`) as `var bytes: [u8] = []`. The
function's own doc comment says `[u8]`. Same defect at
`gzip/deflate.spl:25` (`deflate_block_stored`) and `:60`
(`deflate_block_fixed`, whose last statement is `return bitstream_finish(bs)`).

Consumers demand `[u8]`:
`src/lib/nogc_sync_mut/compression/gzip/compress.spl:52-56,88-93` assigns the
result into `var deflate_empty: [u8] = []`; `src/lib/common/compress/deflate.spl:18-19`
and `src/lib/common/compress/gzip.spl:25` wrap it as `Ok(compressed)` inside
`-> Result<[u8], CompressionError>`. Declaring `[Any]` either type-errors at
those sites or, worse, forces boxed-`Any` elements where unboxed `u8` is
expected — silently corrupt gzip output. Correct annotation is `-> [u8]`.

### HIGH — `LlvmBackend.compile_module` annotated off its trait contract

`main:src/compiler/70.backend/backend/codegen_types.spl:156` declares the
universal backend interface:

```
fn compile_module(module: MirModule) -> Result<CodegenOutput, CompileError>
```

`main:src/compiler/70.backend/backend/llvm_backend.spl:256` now declares:

```
fn compile_module(module: MirModule) -> Result<LlvmCompileResult, text>:
```

**Both** type arguments deviate — the ok type (`LlvmCompileResult` vs
`CodegenOutput`) and the error type (`text` vs `CompileError`; every other
backend, including the otherwise-deviant `WasmBackend`, uses `CompileError`).
`backend_factory_full.spl:117` returns `LlvmBackend.create(...)` as a
`CodegenFactory.create` value, which is then invoked structurally as
`self.codegen.compile_module(module)` at `backend_api.spl:159` and
`backend_helpers.spl:407`. Annotating an implementation off-contract breaks the
structural match at those call sites.

### MEDIUM — `mono/instantiation.instantiate -> Result<Any, text>` (author self-flagged; the flag was justified)

`src/compiler/40.mono/instantiation.spl:36`. Two problems:

1. `instantiation.spl:53` does `return load_result`, where `load_result` comes
   from the trait method declared
   `fn load_template(name: text) -> GenericTemplate?`
   (`src/compiler/00.common/compilation_context.spl:176`) — an **Option, not a
   Result**. The pre-existing `load_result.is_err()` at :51 is the same latent
   bug; the annotation converts it into a hard type error.
2. `Any` erases the payload for the caller.
   `src/compiler/70.backend/linker/lazy_instantiator.spl:229-231` does
   `case Ok(compiled_unit): compiled_unit.code` — an erased-receiver field
   access, this repo's known miscompile class. The honest annotation is
   `Result<CompiledUnit, text>`.

### MEDIUM — `jit_instantiator.lookup -> Any?` (author self-flagged; also justified)

`src/compiler/99.loader/jit_instantiator.spl:124`. Two of the three return paths
yield `Some(MappedRecord(...))`; only the `self.records` path is genuinely
erased. Both callers immediately field-access the payload —
`jit_instantiator.spl:213` (`mapped_record.owner_id`) and
`module_loader.spl:468` (`value.owner_id`) — so `Any?` erases the receiver at
both. The Option-ness itself is fine (callers use `if val …` / `match Some(value)`);
the payload type should be `MappedRecord?`.

### Other MEDIUM / LOW

- `jit_instantiator.spl:348` `resolve -> i64?` — `:355-356` reads
  `val addr = rec["address"]` from an untyped `Dict`, so `return Some(addr)` is
  `Some(Any)`, not `Some(i64)`.
- `huffman.spl:221` `huffman_lookup -> [Any]?` imposes Option semantics on a
  nil-sentinel idiom: the body returns a **bare** `[entry[1], entry[2]]` (:234)
  and all four callers treat it as a plain nullable array
  (`deflate.spl:88-89,98,111,125`, `if code_info != nil: … code_info[0]`).
  Either the `return` must become `Some(...)` or the annotation is wrong. Same
  shape at `blocks/registry.spl:83-85` (`-> Any?` with a bare
  `return self.blocks[kind]`, while `unified_registry.spl:81` destructures
  `if val Some(block_def) = … lookup(keyword)`).
- `huffman.spl:35` `huffman_node_freq -> i64` returns `node[1]`, an `Any`
  element of an `[Any]` array (:38) — runtime-correct, statically an unchecked
  `Any → i64` narrowing.
- `driver_build/incremental.spl:628` `-> Dict<text,text>?` — spelling drift
  versus the repo's usual `{text:text}` form. Cosmetic.

### Clean

The `array.spl` / `array_advanced.spl` families across all three tiers
(`gc_async_mut`, `nogc_sync_mut`, `nogc_async_mut`) were checked tier-by-tier —
`array_chunk -> [[Any]]`, `array_drop -> [Any]`, `array_rotate_left -> [Any]`,
`transpose -> [[Any]]`, `mode -> Any?`, `median -> Any?`,
`index_of_subarray -> i64`. The nogc tiers carry extra guard paths
(`if size <= 0: return []`, ragged-matrix `return []`) but every one of them
yields the declared type. `lz77.spl:24 lz77_find_match -> [i64]`,
`backend_api.spl:82,100 -> Result<CompilerBackend, CompileError>`,
`module_loader.spl:151,495 -> LoadedSymbol?/LoadedModule?`, and
`jit_instantiator.spl:79 -> MappedRecord?` are all correct.

---

## Recommended actions, in priority order

1. **Revert or repair `88ea42c396e4`'s three high-severity annotations** —
   `inflate.spl:426` (breaks a live spec), `huffman.spl:424` + `deflate.spl:25,60`
   (`[Any]` should be `[u8]`), `llvm_backend.spl:256` (off trait contract).
2. **Make `e599a617d6ef` actually work** — teach `find_reexport_source`
   (`module_lowering.spl:601`) the leading-dot normalization that
   `resolve_import_symbols:815` already has, or emit an absolute path from
   the parser. Until then, `export … from …` is parsed but inert for
   downstream consumers, and the 22 workaround imports in `3ab74b15387`
   cannot be removed.
3. **Add a guard comment** on the two `90.tools/lint` easy_fix imports about the
   `LintLevel`/`LintCategory` first-write-wins collision.

# Paren-less container accessors silently drop the whole module out of JIT

- **Filed:** 2026-08-08
- **Status:** FIXED in the `run`/JIT lane 2026-08-08 (Rust seed driver). Fence
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** fixed in the `run`/JIT lane only (`exec_core.rs:1071/1353` + `check-no-jit-module-drop.shs`); the `compile` lane is fenced, not fixed. `bug_db.sdn` row is `fix-implemented-verification-pending`.
  remains for the `compile` lane. See "Upstream fix (landed)" below.
- **Severity:** High — silent ~100-1000x slowdown, correct output, no diagnostic
- **Fence:** `scripts/check/check-no-jit-module-drop.shs`

## Summary

A paren-less accessor on a builtin container — `.length`, `.len`, `.size`,
`.empty`, `.chars`, `.first`, `.last`, `.capacity` — parses as a **field
access**. There is no HIR lowering for it, so `hir/lower/expr/access.rs:400`
raises:

```
cannot infer field type while lowering <fn>: struct 'Array' field 'length'
```

(also `struct 'String'`, `struct 'Dict'`).

The two lanes disagree, and that is the whole defect:

| lane | behaviour |
|------|-----------|
| `bin/simple compile <f>` | **rc=1**, hard error, names struct + field |
| `bin/simple run <f>` (JIT) | **rc=0**, prints the correct value, whole enclosing module silently dropped to the tree-walk interpreter |

Measured 2026-08-08 on `bin/simple` (currently the Rust seed — it self-reports
`this Rust-built Simple binary is a bootstrap seed only`):

```
$ bin/simple run  scratch/bad.spl      # val xs = [1,2,3]; print xs.length
3                                       # rc=0, no diagnostic at all
$ bin/simple compile scratch/bad.spl
error: ... cannot infer field type while lowering main: struct 'Array' field 'length'
```

All eight family members were confirmed to raise it under `compile`:

```
xs.length   -> struct 'Array'  field 'length'
s.length    -> struct 'String' field 'length'
d.length    -> struct 'Dict'   field 'length'
xs.first    -> struct 'Array'  field 'first'
xs.empty    -> struct 'Array'  field 'empty'
s.chars     -> struct 'String' field 'chars'
xs.size     -> struct 'Array'  field 'size'
```

## Why `.length` accumulated the most sites

`.length` is the only member the **interpreter** both accepts and evaluates
correctly. `.size` and `.empty` also die at runtime (`undefined field: unknown
property or method 'size' on Array`), so they self-report the moment anyone runs
the code. `.length` prints the right number and says nothing. That asymmetry is
why it is the dominant member of the class.

## Finding 1 is WRONG — RETRACTED 2026-08-08 (re-measured)

> **Do not re-derive from Finding 1 below. It was refuted by direct A/B on
> 2026-08-08 and is kept only so the next lane does not re-refute it.**

`SIMPLE_JIT_STRICT=1` **does** escalate this family. Every member probed goes
rc=0 → rc=1 with the tag, on the deployed `bin/simple`:

| probe | strict=0 | strict=1 |
|-------|----------|----------|
| `[i64].length` | rc=0, prints `3`, `[INFO] … falling back` | **rc=1** `error: SIMPLE_JIT_STRICT: HIR lowering error … refusing to fall back` |
| `[i64].first` | rc=0, prints `1` | **rc=1** tagged |
| `"hello".length` | rc=0, prints `5` | **rc=1** tagged |
| `[i64].empty` | rc=1 (interpreter dies) | **rc=1** tagged |
| `[i64].size` | rc=1 (interpreter dies) | **rc=1** tagged |

The accessor family is **not** caught at an untagged semantic gate. It is
`LowerError::Unsupported` raised at `hir/lower/expr/access.rs:400`, returned by
`hir::lower_with_context_lenient_and_project_hint`, and routed straight through
`jit_strict_fallback_error("HIR lowering error", …)` at `exec_core.rs:1032` —
i.e. the tagged arm. Two-source confirmed: the seed source at
`exec_core.rs:1263-1267` and the binary's own observed output.

**How the original claim went wrong:** the quoted evidence
(`[INFO] JIT compilation failed, falling back to interpreter: semantic:
undefined field: unknown property or method 'empty' on Array`) is a **splice of
two non-adjacent lines**. The real `[INFO]` line says `HIR lowering error: …`;
the `error: semantic: undefined field …` line is emitted *later*, by the
**interpreter** dying at runtime after the fallback already happened. Reading
them as one line made an untagged gate appear where there is none.

Consequences: (a) `SIMPLE_JIT_STRICT` needed no new routing for this class;
(b) the remaining real defect was that it is **off by default**, which the
upstream fix below closes.

---

## Finding 1 (ORIGINAL, RETRACTED): `SIMPLE_JIT_STRICT=1` does NOT harden this

This was believed to be an existing mitigation that merely nothing invoked. It
is not. `SIMPLE_JIT_STRICT=1` only turns a fallback into a hard error for errors
routed through `jit_strict_fallback_error` (`driver/src/exec_core.rs:1261`) —
i.e. HIR/MIR `LowerError` and, separately, unresolved externs in
`codegen/jit.rs`. Only those messages carry the `SIMPLE_JIT_STRICT:` prefix that
`run_file_with_args` tests for:

```rust
if jit_err.contains("SIMPLE_JIT_STRICT:") { return Err(jit_err); }
// else: eprintln!("[INFO] JIT compilation failed, falling back to interpreter: ...")
```

The accessor family is caught **earlier**, at the semantic gate
(`pipeline/lowering.rs`), whose message is never tagged. So the `contains` test
is false and the driver falls back to the interpreter **regardless of strict
mode**. Verified directly:

```
$ SIMPLE_JIT_STRICT=1 bin/simple run scratch/t4.spl     # xs.empty
[INFO] JIT compilation failed, falling back to interpreter: semantic: undefined field: unknown property or method 'empty' on Array
```

Strict was set and it still fell back. Same for a struct with a genuinely absent
field (`class P has no field named y`).

**Scope of this claim, precisely.** What is proven is that the **`run`/JIT lane**
routes this class through the untagged semantic gate, so `SIMPLE_JIT_STRICT=1`
does not stop the fallback *for it*. It is NOT proven that `[jit-fallback]` is
unreachable in general — it was simply never emitted in any `run`-lane probe
attempted here. The `compile` lane does reach
`LowerError::CannotInferFieldType` (`access.rs:400`) for this exact family, and
the tree scan also produced `MIR lowering: Unsupported HIR constr` failures,
which is the other arm of `jit_strict_fallback_error`. Both arms are therefore
live; the defect is that the accessor family does not travel through them on the
`run` path.

**Consequence:** a `run`-based fence for this class would be vacuous. That is why
the landed fence drives `compile`.

## Finding 2: the drop message does not name the source file

`[jit-fallback] {kind}: {err}` and the `[INFO]` variant both name struct and
field but not the file. The fence works around this by compiling **one file at a
time** and attributing from the loop variable. Upstream, the message should
carry the path and span.

## Recommendation for the upstream fix

**Reject at semantic analysis, uniformly across all lanes. Do not lower them as
sugar, and do not try to reject them in the parser.**

1. **Not the parser.** `recv.length` is legitimate syntax — genuine `length`
   struct fields exist in this tree (`SvimPiece.length`, `RefcBinary ref.length`)
   and are declared in files other than the use site. The parser has no type
   information and cannot tell them apart. Scope here is not statically
   decidable; that is also why grep gives only an upper bound (a textual sweep
   produced 254, then 165, both over-reporting).

2. **Not sugar either.** Lowering `.length` to `.len()` would create two
   spellings for one operation and make paren-less `.len` mean something
   different from `.len()`. Worse, on a `Dict` receiver it would silently route
   into `Dict.len()`, which returns **−1** under native codegen
   (`doc/07_guide/language/dict_native_pitfalls.md`). Sugaring would convert a
   loud compile error into a wrong answer.

3. **Do this:** in the semantic gate, when a field access resolves to a builtin
   container (`Array` / `String` / `Dict`) and the field name matches a known
   method, emit a hard, actionable error naming file, line, and the fix
   (`use .len()`). It is already a hard error in the `compile` lane — the fix is
   to make the `run`/JIT lane agree instead of silently degrading.

4. **Independently, close the strict-mode hole:** route the semantic-gate
   failure through `jit_strict_fallback_error` so `SIMPLE_JIT_STRICT=1` actually
   covers the path where these land, and add the source path to the message. As
   it stands, strict mode advertises coverage it does not have — the same
   "advertised coverage that does not exist" pattern called out in
   `scripts/check/check-aot-lane-fences.shs`.

## Upstream fix (landed 2026-08-08)

`src/compiler_rust/driver/src/exec_core.rs` — **Rust seed only**.

**What changed.** `jit_strict_fallback_error` became
`jit_strict_fallback_error_for(kind, err, path)`, and when the HIR lowering
error is recognised as this class it returns a **hard error unconditionally**,
whether or not `SIMPLE_JIT_STRICT` is set. Recognition is deliberately narrow:
the message must contain `cannot infer field type while lowering` **and** name
one of `struct 'Array' | 'String' | 'Dict'` **and** name a field in
`length len size empty chars first last capacity`.

**Why this is safe (blast radius).** Every file in this class *already* fails
`bin/simple compile` with the identical diagnostic, so no build that works
today can regress — the change only makes `run` agree with `compile` instead of
silently degrading ~100-1000x. Measured negative controls on the rebuilt seed:

- genuine cross-file struct field — `class SvimPiece: var length: i64` in one
  file, `p.length` read in another — prints `42`, rc=0, byte-identical to the
  pre-fix binary. These never reach the error at all: they *resolve*.
- `"hi".ty` (builtin struct, field NOT in the family) and `[1,2,3].prefix`
  (ditto) still fall back **leniently**, rc unchanged from the pre-fix binary.
  This is what keeps the wider `struct 'ANY'` de-JIT cause — a different cause
  that *can* occur in code which compiles — out of the escalation.
- `Dict` receivers are matched but **not rewritten** anywhere; the fix is a
  rejection, never a sugar into `Dict.len()` (which returns −1 under native
  codegen, `doc/07_guide/language/dict_native_pitfalls.md`).

**Also landed:** the fallback message now carries the source path
(`[in <path>]`), closing Finding 2. Both the HIR and MIR arms pass it.

**No pure-Simple twin is needed.** `src/compiler/**` has **no JIT→interpreter
whole-module fallback machinery at all** — a positive-controlled grep over the
numbered dirs (`80.driver`, `95.interp`, `70.backend`) finds no `[jit-fallback]`,
no `SIMPLE_JIT_STRICT`, and no de-JIT path. The silent-degradation defect is
**seed-driver-only**; the pure-Simple compiler simply errors, like `compile`.

**Not done deliberately:** the JIT **panic** arm (`exec_core.rs:964`) is still
untagged and still falls back under strict. That is a different class with no
probe here, and tagging it is a policy change on a shared tree.

## Class size: bounds, not a number

One pass over the 418 textual candidates in `src/lib src/app src/os src/compiler`
flagged **17 files**. That is a **lower bound**, not the class size:

- **The compiler reports only the FIRST error per file.** `package/list.spl` was
  reported as `struct 'ANY' field 'prefix'` while *also* containing
  `manifest.stdlib_files.length` — a real accessor site the fence never named.
  After the fixes below, 4 files moved DROP -> UNMEASURABLE because a
  previously-masked second error surfaced. **The fence is not fixed-point: run it
  again after every round of fixes.**
- **Coverage denominator:** of the 418 compiled, **286 were UNMEASURABLE** (they
  fail to compile for unrelated reasons). The fence has an opinion about **115
  files**. That is the real coverage.
- Grep's 758 candidate files is the **upper** bound and over-reports ~44x,
  because genuine `length` struct fields are declared in other files.

Neither bound is the answer. Only repeated fence passes converge on one.

### Fixed in this pass (25 files, `.length` -> `.len()`)

All had container or string receivers. The rewrite is proven
**compilation-non-regressing** rather than semantics-preserving: every rewritten
site already failed to compile, so the change cannot have broken a working build,
and a compile pass confirmed 0 parse errors afterwards. Dict receivers were left
alone (`Dict.len()` returns -1 under native codegen).

### NOT fixed

- `src/compiler/10.frontend/c_import/c_import_resolve.spl` — `struct 'String'
  field 'length'`. It was edited in this lane, but a parallel session clobbered
  the working-copy edit before it could be landed. **Still an open DROP site.**

### Fixed 2026-08-09: `primitive_api.spl` and `baremetal_path.spl`

Both of the two remaining DROP sites named above are now clear (`check-no-jit-
module-drop.shs --file` on both: 0 DROP, was 2). Root causes, confirmed
independently for each:

- **`src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl`** (`struct
  'Array' field 'last'`) — this genuinely is the paren-less accessor family:
  `result_parts.last != Some("..")` should be `result_parts.last() !=
  Some("..")`. Proof it's semantics-preserving: the identical
  `bm_path_normalize`-equivalent function already exists with parens in three
  sibling tiers — `src/lib/nogc_sync_mut/path.spl:104`,
  `src/lib/gc_async_mut/path.spl:104`, `src/lib/nogc_async_mut/path.spl:104` —
  all read `result_parts.last() != Some("..")`. Only the `noalloc` copy was
  missing the parens. One-line fix.
- **`src/compiler/35.semantics/lint/primitive_api.spl`** (`struct 'String'
  field 'ty'`) — this is confirmed to be the RELATED-BUT-DIFFERENT cause
  flagged above, not the accessor family (`ty` is not in the 8-member list).
  Root cause: `compiler.frontend.ast.FunctionDef.params` /
  `StructDef.fields` / `ClassDef.fields` are declared `[text]` — flat `'name:
  Type'` strings (see the `# DESUGARED` markers in `ast.spl`) — not
  `[Param]`/`[ParserField]` objects. `primitive_api.spl` iterated `func.params`
  and field-accessed `.ty`/`.name` on each entry as if it held rich AST nodes;
  since the entries are actually `text`, the receiver statically resolves to
  the builtin `String` struct and HIR lowering has no `.ty` field on it. Sibling
  `semantic_api/checker.spl` already parses this exact flat-text shape
  correctly (`_param_name_of`/`_param_type_of`, using `'name: Type'` splitting)
  — `primitive_api.spl` now does the same via local `_pf_name_of`/`_pf_type_of`
  helpers, dropping the `Type`-enum-based matching entirely (also fixes the
  matching `Option<Type>` misuse on `func.return_type`, itself flat `text` +
  `has_return_type: bool`, not `text?`).
  **Blast radius:** `primitive_api.spl`'s `check_function`/`check_struct`/
  `check_class`/`check_module_items` are confirmed DEAD CODE — sibling
  `primitive_api_arena.spl`'s docstring states outright that "the live lint
  pipeline never builds" the typed-`Node` AST this file consumes, and a repo
  grep found zero constructors of `Node.Function(FunctionDef(...))` anywhere
  and zero external callers of these functions outside this file's own
  `__init__.spl` re-export. No live behavior depends on this file, so the
  rewrite is float-free correctness-repair, not a live-path risk.
  **After the fix**, `bin/simple compile` on this file now fails for a
  DIFFERENT, unrelated, pre-existing reason ("2 function(s) contain constructs
  that require the interpreter: `[PatternMatch]`" in `check_module_items` and
  `is_raw_primitive_expr`, both untouched by this change) — the field-type
  DROP was simply the FIRST-reported error masking this one, exactly the
  documented "compiler reports only the FIRST error per file" pattern above.
  Not a regression: confirmed via `git stash` A/B that the two pre-existing
  `primitive_api_lint_spec.spl` / `primitive_api_canary_spec.spl` test failures
  (unrelated to this file — one is an extern-signature-mirroring canary, the
  other is a `sffi_common`/`Handle` canary) are byte-identical in count and
  content with and without this fix.
- Similarly `src/lib/*/package/list.spl` (`struct 'ANY' field 'prefix'`) is
  still open — same class as `primitive_api.spl` was, not yet investigated.

**Verification:** `test/01_unit/lib/nogc_async_mut_noalloc/path/
baremetal_path_spec.spl` (2/2 pass, unaffected by the accessor rewrite —
covers `bm_path_normalize` including a `..` collapse case that exercises the
fixed line). No live spec exercises `primitive_api.spl`'s dead functions
directly; the fence itself (`compile`-lane) is the applicable oracle here and
now reports 0 DROP for both files.

## Fence

`scripts/check/check-no-jit-module-drop.shs` — fail-closed, exit 0/1/2 with a
verdict line stating how many modules were actually examined. It drives
`bin/simple compile` (non-executing, per-file attributable), runs a fatal
bidirectional `--selftest` before every scan, and treats an empty roster, an
unmeasurable file, and a non-firing selftest as ERROR rather than PASS.

Deliberately **not** wired into any pre-commit/pre-push hook: a per-file compile
over the candidate roster costs ~15-20 minutes and this checkout is shared by
about ten concurrent sessions.

### Injection test (both directions, on a real tree file)

```
src/lib/bitwise_utils.spl, unmodified   -> PASS — 1 module(s) checked, 0 drops
+ fn __injected_probe(elements: [i64]) -> i64: return elements.length
                                        -> FAIL — 1 file(s) checked, 1 drop
   DROP  src/lib/bitwise_utils.spl  struct 'Array' field 'length'
plant removed, blob back to 340ba81     -> PASS — 1 module(s) checked, 0 drops
```

The fence names the offending file, and it was shown to fire on a real tracked
source file rather than only on its own fixture.

## Incidental: `git checkout -- <path>` emptied a tracked file

While reverting the injection plant, `git checkout -- src/lib/bitwise_utils.spl`
restored the file to the **empty blob** `e69de29`, destroying 35 lines. The
content was recovered from a pre-edit copy and verified back to
`340ba81fdb0e87da87b2024e417eb83218bfcd90`. This is the documented empty-blob
trap in this checkout's index; do not use `git checkout --` to revert here
without pinning and re-verifying the expected blob SHA afterwards.

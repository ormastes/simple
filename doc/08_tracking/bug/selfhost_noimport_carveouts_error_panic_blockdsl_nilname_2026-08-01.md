# Remaining no-import carve-outs: `error`/`panic`, block-DSL bodies, `nilnilnilnilnilnil`

- **Date:** 2026-08-01
- **Status:** OPEN (investigated, not fixed — see "Why not fixed here")
- **Parent:** `selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
- **Sibling docs (FIXED this lane):**
  - `match_arm_underscore_subpattern_becomes_lambda_2026-08-01.md` (parent
    carve-outs 2 `_`/`_1` **and** 7 "declared in the same file" — one defect)
  - `float_cast_missing_from_selfhosted_primitive_casts_2026-08-01.md`
    (parent carve-out 6)

## Harness used for every claim below

Pure-Simple front end interpreted by `bin/simple_seed` (rebuilt 2026-08-01 from
origin `f93c9b2623`), driven by
`parse_full_frontend` -> `HirLowering.lower_module`, asserting on
`HirLowering.errors`. **Not** stage3/stage4: stage4 aborts at
`[ERROR] phase 3 FAILED` so its counts are early-abort artifacts, and stage3
runs the bootstrap-flat pipeline and never does this lowering at all.

Cost note for the next lane: the interpreted front end lowers roughly 100
source lines per usable probe run. A whole 499-line compiler module **times the
spec runner out**, which is why the two file-scoped findings below are still
open. Slice the file, or drive the front end from a compiled binary.

---

## 1. `error` and `panic` are NOT both builtins (parent carve-out 3)

**REPRODUCED.** Minimal case, 2 errors:

```
fn f(x: i64) -> i64:
    if x < 0:
        panic("neg")
    error("bad")
    0
```
→ `unresolved name: panic`, `unresolved name: error`.

### `panic` — PROVED a genuine builtin, PROVED missing self-hosted

The Rust seed has a dedicated `lower_abort_builtin`
(`src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:409`) plus
`"panic" => lower_builtin_call("rt_panic", ...)` at `calls.rs:512`. Its
docstring records the identical bug on the seed side: *"HIR lowering never knew
it. That made `panic(...)` lower as a plain identifier, fail with
`UnknownVariable: panic`, and (because a HIR lowering error discards the WHOLE
module) drop every module that transitively uses it back to the interpreter."*
The self-hosted front end is now in exactly that pre-fix state.

The runtime side already exists: `rt_panic(const char*)` is defined in
`src/runtime/runtime_native.c:7279`, declared in `src/runtime/runtime.h:300`,
and emitted by every backend (`llvm_backend.spl:472`,
`llvm_backend_tools.spl:305`, `llvm_lib_translate.spl:369`,
`wasm_runtime.spl:92`, `_MirToLlvm/asm_constraints_helpers.spl:149`).

Real callers: `src/compiler/15.blocks/blocks/testing.spl` (15+ sites).

**Type must be ANY, not NIL** — the seed's own comment: `panic` diverges, so it
has to unify with whatever the surrounding expression needs (`case Err(e):
panic(...)` inside a `-> T` match). Stamping NIL injects a bogus concrete type.
(The seed is internally inconsistent here: `lower_abort_builtin` uses ANY,
`lower_utility_builtin`'s `"panic"` arm uses NIL. ANY is the documented intent.)

### `error` — PROVED **not** a builtin anywhere

`error` has **no** builtin arm in the seed (no `"error" =>` in the seed's HIR
lowering) and no runtime symbol. Its only in-tree declarations are *methods*
and *static methods* on unrelated types: `00.common/config.spl:217`,
`00.common/diagnostics/diagnostic.spl:33`,
`00.common/diagnostics/diagnostic_v1.spl:127`,
`00.common/driver_source_file.spl:21`, `10.frontend/core/aop.spl:249`,
`35.semantics/macro_validation.spl:54`, plus the `me error(...)` diagnostics
sinks in `hir_lowering/types.spl:300` and `type_infer/context.spl:152`.

The bare free-function calls — `70.backend/backend/backend_factory_full.spl:44,
107, 185` and `70.backend/backend/common/type_mapper.spl:98` — therefore have
**no provider at all**. This is the parent doc's own thesis playing out: the
seed's flat global registry made these look resolved; the self-hosted front end
correctly reports them.

So the parent doc's carve-out 3 must be **split**: `panic` is a resolver gap
(fix in the compiler), `error` is a **source defect** in those two backend
files (fix at the call sites — they want a diagnostic sink or a `-> Result`,
not a nonexistent global).

### Why not fixed here

Registering `panic` the cheap way — adding it to `is_interp_builtin_fn` so
`lower_unresolved_ident` emits a `NamedVar` — would be a **cover-up**, not a
fix. There is no `HirExprKind.BuiltinCall` in the self-hosted HIR, and grep
finds **no** MIR interception of a callee named `panic`
(`src/compiler/50.mir/**`). A `NamedVar` for an unimplemented name links, per
`reference_native_link_fabricates_weak_empty_extern_definitions`, to a weak
`return 0` stub for any non-`rt_` symbol — turning a loud compile error into a
silent no-op abort. The honest fix rewrites the callee to `rt_panic` (which
does link) and is a HIR+MIR change that needs its own end-to-end verification,
including the bare `panic()` zero-argument form the seed synthesizes a message
for.

Adding `error` as a builtin would be strictly wrong.

---

## 2. Block-DSL body identifiers (parent carve-out 4) — NOT REPRODUCED

**INFERRED cause, not proved.** The reported names —
`x`, `y`, `pred`, `mse`, `model`, `target`, `test_data` in
`15.blocks/blocks/builtin_blocks_math.spl`, and `ls`, `la` in
`builtin_blocks_shell.spl` — do not sit in block literals at all. They sit
inside **raw docstrings** that show block-DSL usage examples:

```
struct LossBlockDef(BlockDefinition):
    r"""Loss block: math mode with automatic backward pass.
    ...
    Example:
        loss{
            pred = model(x)
            cross_entropy(pred, y)
        }
    """
```
(`builtin_blocks_math.spl:222-234`, and the `nograd{ ... }` docstring at
`:294-305`; `m{ x^2 + y^2 }` at `:158-159`.)

The working hypothesis is therefore that a `{...}` region inside a **raw**
(`r"""`) docstring is still being scanned as a string interpolation, so the
docstring's example code is parsed as an expression and its identifiers escape
into name resolution.

A minimal reconstruction of that struct-plus-raw-docstring shape lowered with
**0 errors**, so the trigger needs more of the real file than the interpreted
harness can run. Next step: slice `builtin_blocks_math.spl` around lines
150-200 and 220-310 and probe each slice.

Note `pred` is ALSO listed under parent carve-out 7 ("declared in the same
file"). That overlap is a coincidence of the census, not evidence: the
`selected` half of carve-out 7 is a different, now-fixed defect (see the
match-arm sibling doc).

## 3. `nilnilnilnilnilnil` (parent carve-out 5) — NOT REPRODUCED

`src/compiler/10.frontend/core/parser_preprocessor.spl` contains the literal
text `nil` **zero** times, so the identifier is definitely synthesized.

Hypotheses tested and **REFUTED**, each with a minimal file lowering at 0
errors:

| hypothesis | probe | result |
|---|---|---|
| 3 adjacent interpolations `"{atom}{joined_eq}{value_tok}"` (line 208) split into 6 segments, each read back nil | `f(atom,joined_eq,value_tok) -> "{atom}{joined_eq}{value_tok}"` | 0 errors |
| 2 separated interpolations `"{key}={value}"` (line 255) | same shape | 0 errors |
| lone-brace string literals `"{"` / `"}"` (lines 389, 461, 475) opening an unterminated interpolation | `if bc == "{": ... if bc == "}":` and `t.ends_with("{") and not t.ends_with("}")` | 0 errors |
| `for _ in <text>` (lines 223, 234, 262) | counted loop over text | 0 errors |

Two file slices (lines 180-256 and 360-499) were lowered and produced only
slice-truncation artifacts (`_pp_peek`, `_pp_take`, `out_lines`, …) — **no**
`nil`-concatenated name. The whole 499-line file times the spec runner out.

Still the most likely mechanism, per the parent doc's own reading: a name being
built by string-joining values that are all nil. In this repo that signature
has three known upstream sources — an unregistered `@extern fn` returning
silent nil, `.to_text()` on a bool erased to `Any` returning `"nil"` across a
function-parameter boundary under the JIT, and the native nil sentinel being
the raw word 3. **The bug is upstream of the identifier**; do not chase the
identifier.

Next step: bisect `parser_preprocessor.spl` in ~80-line slices, or drive the
front end from a compiled binary so the whole file fits in a run.

---

## Corrected carve-out ledger (supersedes the parent doc's list)

| parent # | name(s) | verdict |
|---|---|---|
| 2 | `_`, `_1` | **FIXED** — placeholder-lambda ate pattern-position `_` |
| 7 | `selected` | **FIXED** — same defect as 2 |
| 6 | `float` | **FIXED** — seed/self-host cast divergence |
| 3 | `panic` | OPEN — real resolver gap, needs `rt_panic` lowering |
| 3 | `error` | OPEN — **source defect**, not a resolver defect |
| 4 | block-DSL names | OPEN — Stage3 proved the active trigger is the ordinary strings returned by `examples()`; `\{` does not suppress bootstrap interpolation |
| 5 | `nilnilnilnilnilnil` | OPEN — 4 hypotheses refuted, upstream nil suspected |
| 7 | `pred` | OPEN — folds into 4, not into the fixed 7 |

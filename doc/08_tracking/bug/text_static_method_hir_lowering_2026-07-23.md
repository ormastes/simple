# HIR: static method call on builtin type name `text` unresolved (entry-closure)

**Found:** 2026-07-23, MCP native rebuild campaign (rMCP11).
**Status:** OPEN — call site worked around (std.string_core.char_from_code).

## Re-verification (2026-08-10)
Re-checked against current `main`: `is_static_method_call` still lives in
`src/compiler/35.semantics/resolve_strategies.spl` (now at line 291, was 271
at last check — file has moved but the same primitive-receiver gap is intact:
it still only recognizes `Class | Struct | Enum | Import` symbol kinds, never
a builtin-type marker symbol). The root cause, the ~15-way `char_from_code`
tier ambiguity, and the sibling-gap family (`i64.parse`, `f64.parse`,
`*.from_le_bytes`, `i64.chr`, `text.new/empty/with_capacity/from_bytes/
from_c_str/from_handle/from_ptr`) are unchanged and not fixed. No code change
made this session: a correct fix still requires the same
import-independent/cross-tier target-resolution policy change previously
assessed as broader than a scoped resolve-pass rule, and two of the
downstream files in the fix path
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`src/compiler/50.mir/_MirLowering/module_lowering.spl`) are explicitly
off-limits this session (owned by a concurrent agent). Status remains
**OPEN**; workaround must stay in place.

## Symptom
`text.from_char_code(ch)` in app.mcp.main_lazy_query_tools dies during
native entry-closure HIR lowering with `unresolved name: text`: the receiver
`text` is lowered as a value identifier (Var/NamedVar) instead of being
recognized as the builtin type and dispatched as `HirExprKind.StaticCall`.
The interpreter path accepts the same form.

## Expected
`<builtin type name>.<method>(args)` (text/i64/f64/...) should lower to
StaticCall on the corresponding type, matching interpreter semantics —
or the form should be rejected uniformly in both paths.

## Repro sketch
```simple
fn f(ch: i64) -> text:
    text.from_char_code(ch)
```
native-build --entry-closure over a module calling `f` → unresolved name: text.

## Workaround applied
`use std.string_core.{char_from_code}` and call the free function
(src/app/mcp/main_lazy_query_tools.spl `_mcp_json_escape`). **Keep this
workaround** — see investigation below, no fix has landed.

## Investigation update (2026-08-06)

Repro re-confirmed on current `main` (deployed `bin/simple`, currently the
Rust-seed binary per its own startup WARNING — see
`reference_bin_simple_symlink_stale_scratch_build...` memory note, a
pre-existing unrelated environment issue). `native-build --backend cranelift
--entry-closure --entry <repro>.spl` over the doc's exact repro:
```
fn f(ch: i64) -> text:
    text.from_char_code(ch)
```
now fails one layer later than the original report — HIR lowering itself no
longer hard-errors (`text` is in `is_interp_builtin_fn`,
`src/compiler/20.hir/hir_lowering/expressions.spl:59`, so the unresolved
identifier is accepted and emitted as `HirExprKind.NamedVar` with a
`SymbolKind.Function` marker symbol and `type_: nil`). The failure now
surfaces in **MIR lowering**:
```
[ERROR] MIR error: MIR lowering error: undefined variable: text
[ERROR] MIR error: MIR lowering error: unresolved method call: from_char_code
```
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` "undefined
variable: {name}" arm evaluating the receiver as a plain load, and
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2644`
"unresolved method call: {method}" for the `MethodResolution.Unresolved`
fallback). Net effect is unchanged: the form still cannot be native-built.

### Root cause, precisely located
The actual gap is in the semantic method-resolution pass, not HIR lowering
and not MIR:
- `src/compiler/35.semantics/resolve_strategies.spl:271`
  `is_static_method_call(receiver)` only recognizes a receiver symbol whose
  `kind` is `Class | Struct | Enum | Import`. A bare builtin/primitive type
  name (`text`, `i64`, `f64`, ...) used as a receiver is never a real
  symbol-table type entry (primitives are `HirTypeKind` values, not
  `Class`/`Struct`/`Enum` symbols) — worse, `text`'s marker symbol (defined by
  `lower_unresolved_ident`) has `SymbolKind.Function`, which this check
  doesn't even consider. So `is_static_method_call` returns `false`,
  `resolve_method` (line 18) falls through to instance/trait/UFCS resolution
  against a `nil` receiver type, and the call stays
  `MethodResolution.Unresolved` all the way to MIR.
- **MIR already has full, working support for this once resolved correctly**
  — no MIR change would be needed. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2309`
  `case StaticMethod(type_id, method_id):` ignores `type_id` entirely and
  just calls `method_id` directly with the evaluated args
  (`self.symbol_to_operand(method_id)` + `emit_resolved_direct_call`) — exactly
  right for a static/constructor-style call with no real receiver value.
  `src/compiler/70.backend/backend/interpreter.spl:599-608`'s
  `HirExprKind.StaticCall` / `MethodResolution.StaticMethod` arm is the same
  shape. **The blocker is entirely upstream of MIR**: getting
  `resolve_strategies.spl` to hand MIR/interpreter a correct
  `MethodResolution.StaticMethod(_, method_id)` for this receiver shape.

### Why I did not land a fix (scope stop)
Task instructions explicitly authorize stopping and reporting instead of
forcing a fix when the real scope is much broader than expected. That
threshold was hit here:

1. **"The interpreter path accepts the same form" is not a general
   mechanism to copy.** Traced to ground truth in the Rust seed:
   `src/compiler_rust/compiler/src/interpreter_call/mod.rs:1171` and
   `src/compiler_rust/compiler/src/interpreter_method/mod.rs:239,1690` all
   read literally `if type_name == "text" && method_name ==
   "from_char_code"` — a single hardcoded name-pair special case in a
   tree-walking interpreter, not a `StaticCall`/type-name-recognition
   mechanism. There is no existing "correct" general implementation anywhere
   in the codebase to mirror.
2. **Other builtin types have the same gap, confirmed worse than `text`'s.**
   `i64.parse("42")` fails even under the plain interpreter/JIT run (not just
   native-build): `error: semantic: variable \`i64\` not found` (verified
   live, see command below) — `i64`/`f64`/etc. are not even in
   `is_interp_builtin_fn` (`expressions.spl:51-59` lists only `int, float,
   bool, str, text`, never `i64`/`f64`/`u8`/...), and no hardcoded seed
   special case exists for them either. A repo grep found real call sites
   using this shape beyond `text.from_char_code`: `i64.parse` / `f64.parse`
   (`src/app/interpreter/{ast_convert_pattern,ast_convert_expr}.spl`,
   `src/app/interpreter/ffi/builtins.spl`), `i16/i32/i64/f32/f64/u64.from_le_bytes`
   (`src/app/interpreter/ffi/extern.spl`), `i64.chr`
   (`src/app/office/sheets/formula.spl`, doc comment), and `text.new` /
   `text.empty` / `text.with_capacity` / `text.from_bytes` /
   `text.from_c_str` / `text.from_handle` / `text.from_ptr` (constructor-style
   siblings of `from_char_code`, same receiver shape). A fix scoped to
   exactly `text.from_char_code` would leave this whole family open while
   looking closed.
3. **A general fix needs import-independent target resolution, which is
   broader/riskier than a scoped resolve-pass rule.** Even after teaching
   `is_static_method_call`/`resolve_static_method` to recognize a builtin
   type name receiver, resolving *which* real function backs
   `text.from_char_code` is not a simple symbol-table lookup: `char_from_code`
   has **~15 separate tier-specific definitions** across
   `src/lib/{common,nogc_sync_mut,nogc_async_mut,gc_async_mut}/**`
   (grep: `fn char_from_code` — checkpoint_format.spl, http/url.spl x3,
   compression/utilities.spl, replay/vm/devices/serial.spl, smtp/string.spl
   x2, buffer/string.spl, web_framework/{auth_middleware,password_reset}.spl
   as `extern`, ui/widget_interact_model.spl, plus the canonical
   `src/lib/common/string_core.spl:350`). The doc's own workaround picks the
   `common` tier explicitly via `use std.string_core.{char_from_code}`
   because it has to be picked, not because there's one true global. The
   caller's module never imports it, so nothing puts a `char_from_code`
   symbol in scope by default; the closest existing "resolve without an
   explicit `use`" helper
   (`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:896`
   `try_register_bootstrap_global_symbol`) (a) only runs under
   `SIMPLE_BOOTSTRAP=1`, (b) only finds names already present in
   `self.module_surfaces` (i.e. only works when the target file happens to
   already be part of the compiled source graph — not true for the doc's
   minimal entry-closure repro, confirmed by reproducing with `--source`
   scoped to just the repro file), and (c) explicitly bails out (`return
   false`) the moment a name resolves to more than one module surface — which
   `char_from_code` always would. Making this robust means either forcing an
   on-demand load of a specific stdlib file regardless of the build's
   `--source` set (touches module-loading, used by every compile) or
   inventing a disambiguation policy for name collisions across the
   `common`/`nogc_sync_mut`/`nogc_async_mut`/`gc_async_mut` tiers — both are
   "core identifier-resolution" changes with many unrelated call sites at
   risk, exactly the class of change the task said to stop on rather than
   force.
4. `src/compiler/50.mir/**` is out of scope for this session (a concurrent
   agent is mid-flight there) and, per point above, does not need to change
   anyway — confirmed by reading its existing `StaticMethod` arm, not by
   assumption.

**Verification commands used (for reproduction):**
```bash
# native-build entry-closure repro (fails, --source scoped to the repro dir only):
bin/simple native-build --source <dir-containing-repro> --backend cranelift \
  --entry-closure --entry <dir>/repro.spl -o <out> --cache-dir <scratch>/native_cache
# -> [ERROR] MIR error: MIR lowering error: undefined variable: text
#    [ERROR] MIR error: MIR lowering error: unresolved method call: from_char_code

# sibling gap, interpreter-level (fails even without native-build):
bin/simple run i64_parse_repro.spl   # fn main(): match i64.parse("42"): ...
# -> error: semantic: variable `i64` not found
```

### Recommended follow-up (not done here)
- Land the narrow resolve_strategies.spl recognition rule (builtin type name
  + `SymbolKind.Function` marker + `receiver.type_ == nil` -> treat as a
  static-call receiver) as a real but separate change, paired with an
  explicit, deliberate policy for resolving the target callable per
  (builtin-type, method) pair — e.g. a small compiler-owned dispatch table
  that names one canonical implementation per case (mirroring the Rust
  seed's per-name special-casing, but generalized and reviewed), rather than
  generic cross-tier symbol search.
- Track the sibling call sites above (`i64.parse`, `f64.parse`,
  `*.from_le_bytes`, `i64.chr`, `text.new`/`empty`/`with_capacity`/
  `from_bytes`/`from_c_str`/`from_handle`/`from_ptr`) as the same family;
  don't consider this bug closed until they're triaged too.
- Status stays **OPEN**. Do not revert the `main_lazy_query_tools.spl`
  workaround — it is still required.

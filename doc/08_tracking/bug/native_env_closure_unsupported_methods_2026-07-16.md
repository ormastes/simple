# native-build: std.env closure blocked by unsupported array/text methods

**Severity:** medium (loud fail — no silent wrongness; blocks any native-build
entry that transitively imports std.env.variables / std.path)
**Found:** 2026-07-16, q_optiontry_dynload lane (parity case dynload_tagged_text)
**Status:** FIXED (method-dispatch gap). Three compile-path root bugs fixed;
`find`/`join`/`last`/`pop` native method-dispatch gap also fixed (see
"Remaining gap" section — `find` landed at `40f113c8cc59`, re-verified by lane
Q7 on 2026-07-18). Only the separate, out-of-scope rt_env_* text-ABI runtime
cluster (SIGSEGV) remains open, tracked independently.

## Symptom

`bin/simple native-build --entry <x>.spl` with SIMPLE_NO_STUB_FALLBACK=1 fails
for any entry importing `std.nogc_sync_mut.env.platform.{detect_os}` (or
anything else that drags `std.env.variables`). At origin tip eaee86e1e4d the
failure surfaced as:

```
error: HIR lowering error in std.env.variables: unresolved name: rt_env_get
error: HIR lowering error in std.env.variables: unresolved name: name
```

## Three distinct compile-path root causes — all FIXED by this lane

1. **Cross-module extern re-export chain not resolved.**
   `use std.env.types.{rt_env_get}` where std.env.types is an `export use`
   facade (lib/nogc_async_mut/env/types.spl forwarding
   std.nogc_sync_mut.env.types) registered NOTHING:
   `register_imported_symbol` (20.hir/hir_lowering/_Items/module_lowering.spl)
   only looked in the imported module's OWN
   classes/structs/enums/traits/functions/constants. Fix: re-export chase —
   when nothing matches, follow the facade module's imports (alias-aware,
   glob-aware, depth-bounded) to the module that actually declares the item.

2. **Extern-only / export-use-only modules refused as "MIR module has no
   functions".** `driver_native_module_is_export_facade`
   (80.driver/driver_aot_output.spl) required `parsed.functions.len() == 0`
   (an extern-decl module keeps its externs in Module.functions with
   is_extern=true) and `parsed.exports.len() > 0` (an `export use` facade
   emits only an Import record, never an Export record, in the flat bridge).
   Fix: all-parsed-functions-extern counts as code-free, and import-only
   modules qualify as facades. A module with any NON-extern parsed function
   still hard-fails — that loudness (bug
   bootstrap_stage2_empty_mir_bodies_2026-07-05) is preserved.

3. **Docstring interpolation.** The flat bridge never strips docstrings from
   function bodies (Function.doc_comment stays empty) and
   `flat_bridge_build_string_interps` brace-scans EVERY string literal, so the
   doc example `substitute_vars("Hello ${name}!", ...)` in
   lib/nogc_async_mut/env/variables.spl lowered `{name}` as a REAL
   interpolation of an undefined variable — "unresolved name: name", fatal for
   the whole module. Fix: a bare string-literal expression statement whose
   value is DISCARDED (non-tail position in a value block; any position in a
   unit block) lowers as a plain literal, never as interpolation
   (`strip_discarded_string_interps`, 20.hir/hir_lowering/expressions.spl).
   Tail-position strings keep interpolating — `fn f() -> text: "hi {who}"`
   verified unchanged (a first, statement-level variant of this fix broke
   exactly that and was replaced).

## Remaining gap (`text.find` FIXED — method-dispatch gap CLOSED)

With the three fixes above, the std.env closure now reaches MIR lowering and
loud-fails on genuinely unimplemented native methods. At tip eaee86e1e4d that
was `.find`/`.join`/`.last`/`.pop`; re-verified at tip 56e5862775c only
`text.find` (expand_var_expr, lib/*/env/variables.spl) remained — join/last/pop
resolved upstream in the interim:

```
[ERROR] MIR error: MIR lowering error: unresolved method call: find
```

**Fixed** at `40f113c8cc59` ("fix(compiler): native text.find lowering + loud
undeclared field types + entry-scoped --clean") in
`50.mir/_MirLoweringExpr/method_calls_literals.spl`: `find` is handled in the
same erased-receiver text-method arm as `rfind` (arity 1, maps to the
already-deployed `rt_string_find` runtime extern — same runtime symbol
`rfind` already used, no new runtime surface needed).

NOTE (process landmine): a subsequent broad `chore(wc): session sync` commit
(`e6fa51c872e0`, 2026-07-17) reverted THIS DOC's "Remaining gap" section back
to "OPEN" wording (stale-WC-revert signature — see
`feedback_stale_wc_reverts_pushed_fixes.md`) while leaving the CODE fix intact
(`git blame` on method_calls_literals.spl:1735-1745 still attributes the
`find` arm to `40f113c8cc59`). The doc text below restores/reconfirms the fix;
if this section reads "OPEN" again in a future sync, re-check the code first
before re-doing the work.

**Re-verified by lane Q7, 2026-07-18** (worktree `wt_q7`, detached at
`a79a52ba817`), using the stale deployed seed
`bin/release/x86_64-unknown-linux-gnu/simple` (2026-07-17 build; the freshly
rebuilt seed has an unrelated native-build regression, see task notes):

1. Full repro (`use std.env.variables.{env_get}; print(env_get("HOME"))`)
   under `env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 ... native-build`:
   build now SUCCEEDS (exit 0, no "unresolved method call" anywhere in the
   log). Running the produced binary crashes with `SIGSEGV at address 0x3`
   inside libc `fputs` — this is the separate, already-known rt_env_* text-ABI
   runtime cluster (below), NOT the method-dispatch bug; `env_get` calls
   `rt_env_get`, a different runtime function than `rt_string_find`.
2. Isolated runtime probe (no `std.env` import, so `rt_env_get` is not in the
   picture at all):
   ```
   fn probe(s: text) -> i64:
       print(s.find(":-"))
       0
   fn main() -> i64:
       probe("a:-b")
   ```
   Interpreter oracle (`bin/simple run`) prints `1`. Native-build with the
   stale seed compiles clean (no unresolved-method error) and the produced
   binary runs to completion printing `1`, exit code 0 — no crash. This
   confirms `.find()` native dispatch is fully functional at runtime, not just
   compile-clean, and that the SIGSEGV above is isolated to the `rt_env_*`
   path, unrelated to `find`.

Regression test added:
`test/01_unit/compiler/mir/text_builtin_find_lowering_spec.spl` (mirrors the
landed `text_builtin_rfind_lowering_spec.spl` pattern: asserts the MIR for an
unresolved-receiver `.find(...)` call contains `rt_string_find`). Tagged
`only-compiled` like its sibling, so it is skipped (not run) under the
interpreted/fresh-seed `bin/simple test` invocation used in this
CPU-constrained lane session ("0 examples, 0 failures" — tag-filtered, not a
pass); it needs the full compiled test-runner harness to actually execute.
The runtime probe above is the e2e evidence for this fix; the spec is the
durable regression guard once the compiled harness runs it (e.g. full `bin/simple
test` / CI).

Additionally, even a direct `rt_env_get("HOME") != ""` probe that now BUILDS
crashes at runtime (SIGSEGV in libc strlen/fputs) — the known "env_set SEGV
only hits native-build" rt_env text ABI cluster, tracked separately (OPEN,
unaffected by this fix).

## Parity case disposition

`dynload_tagged_text` (scripts/check/check-native-seed-parity.shs) was
importing far more than intended: it only needs an OS name to pick a libc
path/symbol. Rewritten to use the existing `extern fn rt_platform_name() ->
text` runtime extern (returns exactly "linux"/"macos"/"freebsd"/"windows").
LLVM strict lane now builds and prints `dynload-ok`. The cranelift lane fails
with a PRE-EXISTING backend-wide "Failed to declare module statics" (fails
even for a bare `print "x"` at unmodified tip) — not related to this case or
these fixes.

## Reproduce

```
cat > /tmp/env_facade.spl <<'EOF'
use std.env.variables.{env_get}
fn main() -> i64:
    print(env_get("HOME"))
    0
EOF
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 \
  bin/simple native-build --entry /tmp/env_facade.spl -o /tmp/env_facade_bin --clean
# tip: unresolved name: rt_env_get / name; after fixes: unresolved method call: find/join/last/pop
```

# native-build: std.env closure blocked by unsupported array/text methods

**Severity:** medium (loud fail — no silent wrongness; blocks any native-build
entry that transitively imports std.env.variables / std.path)
**Found:** 2026-07-16, q_optiontry_dynload lane (parity case dynload_tagged_text)
**Status:** three compile-path root bugs fixed; remaining gap is native method
support (find/join/last/pop) plus the known rt_env_* text-ABI runtime cluster

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

## Remaining gap (`text.find` now FIXED, 2026-07-16 r_find_infer lane)

With the three fixes above, the std.env closure now reaches MIR lowering and
loud-fails on genuinely unimplemented native methods. At tip eaee86e1e4d that
was `.find`/`.join`/`.last`/`.pop`; re-verified at tip 56e5862775c only
`text.find` (expand_var_expr, lib/*/env/variables.spl) remained — join/last/pop
resolved upstream in the interim:

```
[ERROR] MIR error: MIR lowering error: unresolved method call: find
```

**Fixed** in `50.mir/_MirLoweringExpr/method_calls_literals.spl`: `find` is
now handled in the same erased-receiver text-method arm as `rfind` (arity 1,
maps to the already-deployed `rt_string_find` runtime extern — confirmed via
`nm` on the deployed `bin/release/x86_64-unknown-linux-gnu/simple` and a
direct extern-call probe under `bin/simple run`). `rt_string_find` was already
in use for `rfind`, so no new runtime surface was needed. Seed interpreter
parity confirmed: `interpreter_method/string.rs` ("find" arm) and
`rt_string_find` both return a plain i64, -1 for not-found (language contract
is `i64?`; the existing `rfind` comment's -1-vs-nil equivalence note applies
identically here). Dual-backend probe (found index / not-found / empty
needle) matches between `bin/simple run` (oracle) and `bin/simple
native-build` (native, no trailing newline): `6` / `-1` / `0` both sides.

Additionally, even a direct `rt_env_get("HOME") != ""` probe that now BUILDS
crashes at runtime (SIGSEGV in libc strlen) — the known "env_set SEGV only
hits native-build" rt_env text ABI cluster, tracked separately (unaffected by
this fix; still open).

`scripts/check/native-smoke-matrix.shs` was transiently blocked campaign-wide
(verified at origin/main tip 45dcd340f16: ALL 15 probes, including a bare
`print(1)`, failed with an unrelated pre-existing `error: semantic: type
mismatch: cannot convert dict to int` before reaching any of this fix's code
paths — see `native_build_dict_extern_regression_ca1e18c17_2026-07-16.md` /
`desugar_module_rt_dict_keys_crash_2026-07-16.md`). That was fixed upstream
(`b7f11bf098c`) by the time this lane's patch landed; re-verified at tip
`f92419e4fc3` with this fix applied: `total=15 pass=15 fail=0
codegen_fallback_hits=0`.

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

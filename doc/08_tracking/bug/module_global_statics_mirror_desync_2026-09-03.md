# Every module-level `var` was unassignable: `global_statics_by_id` mirror had no producer (2026-09-03)

- **Status:** RESOLVED — `e29d4a2aceb`
  (`fix(mir): mirror module statics into global_statics_by_id`).
- **Severity:** blocking. Any program that assigns to a module-level `var`
  failed `native-build` outright. It is the fatal that stood in front of
  `native-build src/app/mcp/main.spl`.
- **Symptom:** `MIR lowering error: assignment target has no local binding`
  (driver path) / `error: bootstrap MIR lowering: assignment target has no local
  binding` (bootstrap path).

## Root cause

`find_global_static` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
:222-225) resolves a module global through **only** the i64-keyed mirror
`global_statics_by_id`. Its own comment records why: it stopped scanning
`module.statics` to avoid the seed's struct-keyed `SymbolId` lookup defect.

Neither producer of a module static was ever updated to feed that mirror:

- `lower_static` (`50.mir/_MirLowering/module_lowering.spl`) wrote
  `module.statics[const_.symbol]` and nothing else.
- `lower_runtime_module_initializers_named` (same file) overwrote the same entry
  with the lowered initializer's type, also without touching the mirror.

Before the fix, `/usr/bin/grep -rn global_statics_by_id src/compiler/50.mir`
found exactly two writers, and neither is a module-global producer:
`materialize_folded_global_static_for_address` (address-taken **immutable**
folded `val`) and one lambda-lifting site in `switch_operators_calls.spl`.

So every module-level `var` was invisible to `find_global_static`, and the write
hook in `lower_assign_var` (`50.mir/mir_lowering_stmts.spl`) —

```
elif self.global_symbol_ids.contains(symbol_id) and self.find_global_static(symbol_id).?:
```

— failed its second conjunct, fell through to the per-function local path,
missed there too (a module global is not a local), and aborted the build.

Independent of the global's type: `text`, `[i64]` and `Dict<K,V>` all failed.
The history comment at `module_lowering.spl:132-149`, which attributes the same
message to the ArrayLit admission gap (`array_global_2026-07-25`, MCP
`dap_bridge.spl DAP_SESSIONS`), describes a genuinely different and narrower
cause; that fix worked at the time, and the mirror desync regressed the same
symptom later, when `find_global_static` was switched onto the i64 index.

## Evidence

Minimal repro (4 lines, ~27s):

```
var G_S: text = ""

fn setit():
    G_S = "abc"
```

`bin/simple.exe native-build` ->
`MIR lowering error: assignment target has no local binding at ...vstr.spl:4:5`.

Instrumented probe at the top of `lower_assign_var`:

```
[gprobe] sym=2 in_ids=true isnil=true q=nil at=...vstr.spl:4:5
```

`in_ids=true` (so `lower_const` HAD registered the symbol) with `isnil=true`
(the mirror lookup returns nothing) pins the failure to the mirror, not to the
initializer allowlist. A second probe inside `lower_static` confirmed it was not
returning early: `[sprobe] name=G_S sym=2 foldnil=false mutable=true` and no
EARLY-RETURN line — the static WAS created, just never mirrored.

Independent confirmation on a different compiler: the admitted stage2 binary
`/d/win-p3-mmap/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`
(sha256 `fcf4737281…`), which runs `in-process native-build` and therefore does
NOT read this tree's `.spl` driver, reproduces the identical error at
`vstr.spl:4:5`. So the defect is not an artifact of the invocation form, of the
Rust seed, or of this tree being 83 commits behind `origin/main`.

Upstream status checked before fixing: `git show origin/main:.../module_lowering.spl`
contains no `global_statics_by_id` write (only the `{}` initializer), and
`origin/main`'s `find_global_static` reads only the mirror. **The defect is live
on `origin/main`; this is not a re-fix.**

## Fix

`e29d4a2aceb` — both producers now mirror their entry:

- `lower_static`: `self.global_statics_by_id[sym_id] = lowered_static`
- `lower_runtime_module_initializers_named`:
  `self.global_statics_by_id[const_.symbol.id] = runtime_static`

Three smaller repairs rode along, each proven by the same fixtures:

1. `runtime_module_initializer_supported` now admits `DictLit`, which had no arm
   and no type-driven fallback, so a dict global never got a static to mirror (a
   second, narrower instance of the same message; `src/lib/nogc_sync_mut/log.spl:256`
   assigns `SCOPE_LEVELS = {}`). The runtime-init pass owns its storage and
   declares it as the i64 handle actually stored — the `ptr` that `Dict<K, V>`
   lowers to was rejected by llc with
   `'%l1' defined with type 'i64' but expected 'ptr'`.
2. Global link names now sanitize `:` and `\`, which a Windows source path
   carries into an LLVM global name (`expected '=' in global variable`). Purely
   additive; it widens a set of characters already replaced by `_`, in all three
   copies of that sequence.
3. The bootstrap MIR error path prints `file:line:col` like the driver path did.

## Specs

- Reproducing (behavioural):
  `test/01_unit/compiler/mir/module_dict_global_reassign_native_test.shs` —
  four fixtures (text / array / annotated-dict / inferred-dict global, each
  reassigned). FAIL before (`2 fixture(s) checked, annotated(no-local-binding)
  inferred(no-local-binding)`), PASS after (`4 fixture(s) checked, 0 module-global
  assignment lowering failures`). It also checks the computed VALUE wherever the
  host can link, so a placeholder lowering cannot pass it.
- Generalization (source):
  `test/01_unit/compiler/mir/module_global_static_mirror_source_spec.spl` —
  pins both mirror writes, the mirror-only read in `find_global_static`, the
  DictLit admission, the span enrichment and the link-name sanitization.

## Cross-platform

Pure `.spl` compiler logic, no OS conditional, no Rust touched. The Windows
link-name hunk fixes a defect only Windows paths trigger and changes no name
that was previously valid. Because module-global assignment now takes the
`StoreGlobal` path everywhere, the Unix native-smoke matrix should be re-run
once this is synced to `origin/main`.

## Still open behind this

`windows_native_capsule_receipt_invalid_blocks_every_native_build_2026-09-03.md`
— no `native-build` invocation completes a binary on this Windows host, so the
end-to-end "the MCP binary answers protocol" proof could not be taken here.

# Aliased `use ... { x as y }` (and qualified `use m` + `m.f()`) do not bind in the CODEGEN lane

**Status:** PARTIALLY FIXED 2026-08-10 — codegen now consumes the alias map;
`check-import-alias-codegen.shs` PASSes 5/5 and the `--expect-fail` negative
control correctly FAILs. **One sub-case remains RED:** an alias whose SOURCE
symbol is `main` (the six `os/kernel/arch/*/cstart.spl` baremetal victims) is
deliberately left unresolved — see "Remaining RED" below. Worked around at one
call site.
**Filed:** 2026-08-10
**Found by:** diagnosing `wm_action_applier_spec` `reason=zero-examples`
(`doc/08_tracking/bug/wm_action_applier_spec_dead_on_both_legs_vulkan_order_env_get_2026-08-10.md`).
**Runnable check:** `sh scripts/check/check-import-alias-codegen.shs`
(negative control: `--expect-fail`).

## Correction: the original "entry-file vs transitive" discriminator is FALSIFIED

The first filing of this bug named **entry-file vs transitive** as the surviving
discriminator. That is wrong, and it sent the workaround in the wrong direction.
A minimal two-form probe (`direct.spl` declaring the alias itself vs `entry.spl`
reaching it through `mid.spl`) shows the alias fails **identically in both
positions**. Position is not a variable at all.

The real discriminator is the **execution lane**: the interpreter binds every
import form correctly; the code-generation lane does not.

## Family table — import form x lane

Measured with the deployed `bin/simple` (the Rust seed).
Interpreter = `SIMPLE_EXECUTION_MODE=interpreter`; codegen = `SIMPLE_JIT_STRICT=1`
(**strict is mandatory** — without it the JIT silently falls back to the
interpreter and the defect reads as a pass). `direct` = the importing file is the
entry module; `transitive` = it is reached through one hop.

| Import form | example | interp direct | interp transitive | codegen direct | codegen transitive |
|---|---|---|---|---|---|
| plain selective | `use m.{f}` | OK | OK | OK | OK |
| **aliased selective** | `use m.{f as g}` | OK | OK | **BROKEN** | **BROKEN** |
| wildcard | `use m.*` | OK | OK | OK | OK |
| whole-module alias | `use m as T` + `T.f()` | OK | OK | OK | OK |
| **qualified** | `use m` + `m.f()` | OK | OK | **BROKEN** | **BROKEN** |

Two broken forms, not one. **The qualified form is a sibling defect the original
filing never found** — an unaliased `use m` followed by `m.f()` is equally dead
in codegen. Position (`direct` vs `transitive`) is uniform across every row.

Failure text differs by form:

```
use m.{f as g}   ->  unresolved external symbol 'g'
use m ; m.f()    ->  Runtime error: Function 'base_get' not found
                     Runtime error: unresolved symbol -- this is a code-generation dispatch gap
```

## Root cause

`src/compiler_rust/compiler/src/pipeline/module_loader.rs:575-616`
(`import_binding_marker_name` / `append_flattened_import_binding_markers`)
records each selective import as a `__simple_flatten_import_binding__=` const
marker carrying the `(importer, local, source_owner, source_name)` tuple — i.e.
the alias-to-original map the codegen would need.

Every consumer of that prefix is in the interpreter:

- `src/compiler_rust/compiler/src/interpreter_state.rs:65` (the prefix constant)
- `src/compiler_rust/compiler/src/interpreter_eval.rs:77` (decoder)
- `src/compiler_rust/compiler/src/interpreter_eval.rs:1401`
- `src/compiler_rust/compiler/src/interpreter/mod.rs:71`
- `src/compiler_rust/compiler/src/pipeline/module_loader.rs:634, 2524`

There is **no codegen consumer**. `/usr/bin/grep -rn
FLATTEN_IMPORT_BINDING_MARKER_PREFIX src/compiler_rust/` returns zero hits under
`codegen/`. So when a flattened unit is handed to Cranelift, the imported
function has been merged in under its **original** name (`base_get`) while the
call site still names the **local** binding (`g`, or `m.f`), and codegen emits an
unresolved external reference. The plain-selective and wildcard forms survive
only because local name == original name there; `use m as T` survives on a
different path.

Fix shape: teach the codegen call-lowering path to consult the same import
binding map (or rewrite call callees to their source symbol during flattening,
before codegen sees them), so that all five forms present identical symbols.

## Correction 2: the `qualified` row is NOT broken on current `main`

The family table above was measured with the deployed `bin/simple`
(2026-08-09 04:50). Re-measured 2026-08-10 with a seed built from `origin/main`
at `3ac1249c9ec`, only **one** row is broken:

```
  ok    plain_sel
  BROKEN alias_sel -- [jit-fallback] unresolved external symbol 'g'
  ok    wildcard
  ok    mod_alias
  ok    qualified          <- binds; the doc's "BROKEN" is stale
```

Do not re-derive the two-broken-forms claim from the table without re-measuring.

## The check had a fail-open that hid this

`check-import-alias-codegen.shs` invoked the binary as `$OLDPWD/$SIMPLE_BIN`
from inside each probe's temp dir. With an ABSOLUTE `SIMPLE_BIN` that
concatenates the repo root onto an already-absolute path, so **every** form ran
a nonexistent binary and reported `BROKEN ... <no diagnostic>` — and five broken
forms trivially satisfy "alias_sel and qualified are still broken", so
`--expect-fail` printed `PASS -- negative control live` over a run that measured
nothing. Fixed two ways, both strengthenings:

- `SIMPLE_BIN` is resolved to an absolute path once, up front; non-executable is
  `ERROR` exit 2.
- New fail-closed **harness sanity** gate: `plain_sel`, `wildcard` and
  `mod_alias` are CONTROL forms that bind before and after the fix. If any is
  broken the verdict is `ERROR -- nothing was checked`, exit 2, in **both**
  modes. A wholly dead binary can no longer read as a live negative control.

## Fix applied (2026-08-10)

`src/compiler_rust/compiler/src/`:

- `interpreter_state.rs` — `decode_marker_field` and a new
  `decode_import_binding_marker` lifted to `pub(crate)`, so the marker encoding
  has ONE decoder shared by both lanes. `interpreter_eval.rs` now calls it
  instead of carrying a private copy.
- `hir/lower/lowerer.rs` — new `import_alias_bindings: HashMap<String,String>`
  plus `collect_flattened_import_aliases` (scans the flattened module's marker
  consts) and `resolve_import_alias`.
- `hir/lower/module_lowering/module_pass.rs` — collector called from both
  `lower_module` and `lower_module_with_warnings`, before any expression lowers.
- `hir/lower/expr/mod.rs` — `lower_identifier` consults the alias map as its
  **last** resolution attempt, after locals, named callables and globals, so an
  alias recorded by one module can never hijack a real symbol in another module
  of the same flattened unit.

## Remaining RED — aliases whose source symbol is `main`

Module flattening does **not** mangle: two modules that both define `main` land
in `module.items` under the identical name, and only the interpreter's
`__simple_flatten_module_owner__=` attribute tells them apart — nothing under
`hir/` or `codegen/` consumes that attribute (`module_pass.rs:390-393` does a
bare `self.globals.insert(f.name, ...)`, last-wins).

Measured consequence of rewriting such an alias to the bare name:

```
use target.{main as baremetal_main}   # target.spl defines `main`
-> thread 'simple-main' has overflowed its stack
   fatal runtime error: stack overflow
```

`baremetal_main` bound the ENTRY module's `main`, giving unbounded recursion —
silently wrong code, which is strictly worse than the unresolved-symbol error it
replaced. The fix therefore **refuses** to rewrite when the source name is `main`
(and, generally, when the source name has more than one definition in the unit),
leaving today's honest hard error:

```
error: Cranelift JIT compile: SIMPLE_JIT_STRICT: unresolved external symbol
       'baremetal_main' would NULL-jump in JIT; refusing to fall back
```

So the **six `src/os/kernel/arch/*/cstart.spl` victims are NOT fixed** — the
highest-priority group in the victim list. They need owner-aware symbol naming
in the flattened lane (per-owner mangling, or teaching HIR to consume the
module-owner attribute), which is a larger change than this one. Filed as its
own item; do not close this bug as fully fixed.

## Impact — worse than "one dead spec"

Two distinct severities, and the mild one is the dangerous one:

- **JIT: silent whole-module drop to the interpreter.** The diagnostic is
  `[jit-fallback] ... whole module dropped to the interpreter (expect ~100-1000x
  slowdown)`. Nothing fails. Every aliasing module in the tree is paying an
  unadvertised 100-1000x tax, and no gate anywhere notices.
- **native/AOT: hard `error[E1002]`** aborting the compilation unit. For a spec
  this becomes `executed=0 ... reason=zero-examples` — a file that sits in the
  corpus claiming `@cover` while asserting nothing.

## Live victims

89 aliased selective imports in call position across `src/` (76 `use` lines,
116 alias pairs, 88 distinct alias names). Full list:
`scripts/check/import_alias_victims.txt`. Concentrations:

| area | call-position aliases | note |
|---|---|---|
| `src/lib/nogc_sync_mut/http_client.spl:6-7` | 22 | the single worst file; the entire HTTP client surface is aliased |
| `src/lib/nogc_async_mut/http/{headers,request,response}.spl` | 12 | same pattern, second tier |
| `src/os/kernel/arch/*/cstart.spl:5` | 6 | `main as baremetal_main` on every arch — **baremetal has no interpreter to fall back to** |
| `src/os/kernel/arch/user_entry_bridge.spl` | 4 | `dispatch_enter_user_blocking as dispatch_*_enter_user` |
| `src/compiler/70.backend`, `src/compiler/80.driver` | 5 | compiler's own backend |
| `src/lib/gc_async_mut/gpu/**` | 3 | incl. `backend_vulkan_glsl.spl:27` (latent sibling of the original victim) |

The six `cstart.spl` instances are the most alarming: those units are compiled
AOT for baremetal targets where the interpreter fallback does not exist, so they
are in the hard-`E1002` regime, not the slow regime.

## Can the `backend_vulkan_helpers.spl` workaround be reverted?

**No, not yet.** Commit `b413553ae9c` replaced the alias with a direct
`extern fn rt_env_get`. Since the defect is unfixed and the workaround is
behaviour-identical (`env_ops.env_get` is a one-line forwarder to that same
extern), reverting would re-break every spec whose closure reaches the
compositor. Revert it in the same change that fixes codegen, and prove it with
`check-import-alias-codegen.shs` returning PASS without `--expect-fail`.

## Unblock condition

All five rows of the family table bind in the codegen lane.
`sh scripts/check/check-import-alias-codegen.shs` exits 0 with
`PASS -- 5 form(s) checked, all bind in the codegen lane`, and the
`--expect-fail` negative control then correctly FAILS.

## Do not

Do not close this by converting the remaining aliased imports to plain imports.
That hides the defect; the alias form is valid grammar and must work. Equally, do
not "fix" the qualified row by rewriting `m.f()` call sites.

# Census: local binding shadowed by a module namespace (2026-08-18)

Status: OPEN (compiler defect, seed-side). This document is the **census** for
the defect class; it does not fix the compiler.

Cross-links (the two originally confirmed instances):

- `doc/08_tracking/bug/match_binding_shadowed_by_module_namespace_2026-08-18.md`
  — `src/lib/gc_async_mut/gpu/engine2d/engine.spl`, `match Ok(engine)`.
- `doc/08_tracking/bug/for_loop_var_shadowed_by_module_alias_2026-08-18.md`
  — `src/compiler_rust/lib/std/src/verification/lean/verification_diagnostics.spl`,
  `for diag in self.diagnostics` vs. the importer's `use ... as diag`.

## Symptom

```
semantic: method `foo` not found on type `dict` (receiver value: {SOME_CONST: ..., ...})
```

The binding evaluated to a **module namespace dict** instead of its value.

## Trigger, narrowed by direct experiment (this seed binary)

Before censusing, the trigger was pinned down with minimal probes run on the
current shared Rust seed (`bin/simple run`, interpreter fallback lane). Four
independent probes:

| probe | what it exercised | result |
|---|---|---|
| self-module name only (`tile.spl`, bindings named `tile`, no importer) | `for` + `match` | `FOR=b1b2`, `MATCH=b9` — **no bite** |
| same-file *brace* import `use a.b.color.{rgb}`, bindings named `color` | `val`, `for`, `match` | `CONTROL=b1`, `VAL=b5`, `FOR=b1b2`, `MATCH=b9` — **no bite** |
| importer binds the namespace (`use probe.lib_m as lib_m` / bare `use probe.lib_m`), callee has `for lib_m in ...` | `for`, cross-module | `CONTROL=b3` then **`error: semantic: method `show` not found on type `dict` (receiver value: {Box: <constructor:Box>, Box__new: <fn:Box__new>, Box__show: <fn:Box__show>, control: <fn:control>, run_for: <fn:run_for>})`** — **BITES** |
| importer binds the namespace, callee has `val`/`var`/`match Ok(...)` named the same | `val`, `var`, `match` | `CONTROL=b3`, `VAL=b4`, `VAR=b5`, `MATCH=b7` — **no bite** |
| same file as the bare `use probe.lib_v`, all three forms named `lib_v` | `val`,`match`,`for` | `SF_VAL=s4`, `SF_MATCH=s7`, then **`error: semantic: method `show` not found on type `dict` (receiver value: {Box: ..., control: <fn:control>, mk: <fn:mk>, run_match: ..., run_val: ..., run_var: ...})`** on the `for` — **only `for` bites** |

Conclusions used to tier the census:

1. **Only a namespace-BINDING `use` form creates the hostile binding**:
   bare `use a.b.M` (binds `M`) or `use a.b.X as M` (binds `M`).
   Brace/paren item imports (`use a.b.M.{X}`) and `use a.b.M.*` do **not**.
2. **The binding leaks across module boundaries** — an importer's alias
   poisons the *callee's* function scopes. This is exactly the mechanism of the
   `verification_diagnostics.spl` bug, and it is why a per-file census is not
   sufficient.
3. **On this seed only the `for` loop binding loses.** `val`/`var` and
   `match Ok(...)` currently win against the namespace binding in every probe
   above. The `match` instance in `engine.spl` was observed on a different lane;
   it is retained here as a real but not-currently-reproducible sub-class.
4. A module's own name is **not** in its own scope; `self-module` alone is inert.

## Method

`src/**/*.spl` + `test/**/*.spl`, excluding `src/compiler_rust/vendor/**` and
`src/runtime/vendor/**` per CLAUDE.md Owned-Code Scope. **36,972 files scanned.**

For every file: collect namespace binders (bare-`use` last segment, `as` alias)
from that file (*same-file-ns*) and from every file that imports this module by
its basename (*importer-ns*). Then match local bindings — `for <n> in`,
`Ok/Err/Some(<n>)`, `val`/`var <n>` — against those names, and flag whether the
binding is later used as a method receiver (`<n>.`) within 40 lines.

Tiers:

- **Tier A** — the colliding name is a namespace binder that is *actually in
  scope* for that module (same-file, or bound by an importer of that module).
  These are the live collisions.
- **Tier B** — the name merely coincides with a namespace binder used somewhere
  else in the tree. Only bites if both modules end up co-loaded. Reported as
  aggregate counts only; enumerating 102,425 rows is noise.

Analysis script lives in the session scratchpad and is deliberately **not**
committed (analysis tooling, not product code).

## Totals

| set | count |
|---|---|
| Tier A + Tier B collisions | 102,582 |
| Tier B (coincidental name, needs co-load) | 102,425 |
| **Tier A (namespace demonstrably in scope)** | **157** |
| Tier A used as a method receiver | 101 |
| Tier A by binding form | `val`/`var` 152, `match` 3, `for` 2 |
| Tier B `for`-form used as receiver | 1,082 |

### CONFIRMED vs SUSPECTED

- **CONFIRMED (defect class reproduced end-to-end):** the `for`-loop form.
  2 pre-existing instances, both already documented and worked around
  (`engine.spl`, `verification_diagnostics.spl`), plus the class-level probe
  evidence above.
- **CONFIRMED-CLASS, NEW, unfixed:** **1** Tier-A `for`-loop site —
  `src/app/sspec_maintain/report.spl:92`, `for report in reports:` where
  `src/compiler_rust/lib/std/src/verification/__init__.spl:24` does a bare
  `use report`. This is a genuine name collision on the proven-hostile binding
  form. It is marked **SUSPECTED-HIGH rather than CONFIRMED** because the bite
  additionally requires both modules to be loaded into the same program, which
  was not reproduced on any existing spec in this lane. No rename was applied:
  the rule for this lane is that a `.spl` site is only edited on a verified
  RED->GREEN pair, and no RED could be produced for it.
- **SUSPECTED (collision real, form not currently biting):** the 152 `val`/`var`
  and 3 `match` Tier-A rows. Every probe shows these forms winning against the
  namespace binding on the current seed. They become live the moment the
  resolution order changes, so they are recorded, not dismissed.
- **LATENT (Tier B):** 102,425 rows. Not actionable individually; the actionable
  conclusion is that the compiler fix is the only scalable remedy.

Note: `verification_diagnostics.spl:212` still holds `val diag = ...` — a Tier-A
`val` collision left behind by the `for`-loop-only fix in that bug record. It is
harmless on this seed by rule 3 above, and is listed below.

## Ranked Tier-A affected files

| file | colliding name(s) | forms | rows | used-as-receiver | lines |
|---|---|---|---|---|---|
| src/compiler_rust/lib/std/src/net/udp.spl | result | val-var:7 | 7 | 0 | 69,88,139,153,167,179,190 |
| src/compiler_rust/lib/std/src/net/tcp.spl | result | val-var:6 | 6 | 0 | 70,156,197,204,221,235 |
| src/compiler_rust/lib/std/src/tooling/dashboard/cache.spl | cache | val-var:5 | 5 | 5 | 160,166,171,176,181 |
| src/app/dashboard/cache.spl | cache | val-var:5 | 5 | 5 | 127,132,136,140,144 |
| src/app/dashboard/tooling.dashboard/cache.spl | cache | val-var:5 | 5 | 5 | 148,153,157,161,165 |
| test/03_system/infrastructure/multi_mode_test_runner_spec.spl | spec | val-var:5 | 5 | 0 | 396,443,451,459,465 |
| test/system/multi_mode_test_runner_spec.spl | spec | val-var:5 | 5 | 0 | 396,443,451,459,465 |
| src/lib/nogc_sync_mut/src/map.spl | map | val-var:4 | 4 | 4 | 32,55,474,479 |
| src/lib/nogc_async_mut/mcp/session.spl | session | val-var:4 | 4 | 4 | 175,205,217,227 |
| src/compiler_rust/lib/std/src/host/common/net/runtime.spl | result | val-var:4 | 4 | 0 | 26,36,53,71 |
| test/01_unit/lib/notebook/gpu_mode_resolver_spec.spl | spec | val-var:4 | 4 | 0 | 99,110,118,213 |
| test/01_unit/app/office/sheets/cell_format_spec.spl | spec | val-var:4 | 4 | 4 | 24,33,42,50 |
| src/lib/nogc_sync_mut/src/config.spl | config | val-var:3 | 3 | 3 | 570,612,725 |
| src/lib/common/parser/parser.spl | parser | val-var:3 | 3 | 3 | 439,453,458 |
| src/lib/nogc_async_mut/io/file.spl | file | val-var:3 | 3 | 3 | 11,152,160 |
| src/lib/nogc_async_mut/async/runtime.spl | runtime | val-var:2/match:1 | 3 | 3 | 238,264,267 |
| src/lib/nogc_async_mut/async_host/runtime.spl | runtime | val-var:3 | 3 | 2 | 24,29,82 |
| src/lib/gc_async_mut/pure/parser.spl | parser | val-var:3 | 3 | 3 | 434,448,453 |
| src/compiler/99.loader/module_resolver/manifest.spl | manifest | val-var:3 | 3 | 3 | 79,108,169 |
| src/compiler_rust/lib/std/src/verification/lean/runner.spl | runner | val-var:3 | 3 | 3 | 429,434,439 |
| src/compiler/00.common/config.spl | config | val-var:2 | 2 | 2 | 93,333 |
| src/compiler_rust/lib/std/src/host/async_nogc_mut/io/fs/file.spl | file | val-var:2 | 2 | 2 | 39,400 |
| src/compiler_rust/lib/std/src/host/async_gc_mut/io/fs/file.spl | file | val-var:2 | 2 | 1 | 31,307 |
| src/compiler_rust/lib/std/src/tooling/testing/discovery.spl | discovery | val-var:2 | 2 | 2 | 85,107 |
| src/compiler_rust/lib/std/src/tooling/testing/runner.spl | runner | val-var:2 | 2 | 2 | 309,366 |
| src/app/sspec_maintain/report.spl | report | for:2 | 2 | 1 | 92,103 |
| test/01_unit/app/office/sheets/number_format_spec.spl | spec | val-var:2 | 2 | 2 | 119,127 |
| test/integration/app/sj_daemon_mutual_exclusion_spec.spl | client | val-var:2 | 2 | 2 | 80,88 |
| test/02_integration/app/sj_daemon_mutual_exclusion_spec.spl | client | val-var:2 | 2 | 2 | 80,88 |
| src/lib/nogc_sync_mut/ui_test/client.spl | client | val-var:1 | 1 | 1 | 70 |
| src/lib/nogc_sync_mut/mcp/jj/resources.spl | resources | val-var:1 | 1 | 0 | 89 |
| src/lib/nogc_sync_mut/mcp/jj/prompts.spl | prompts | val-var:1 | 1 | 0 | 56 |
| src/lib/nogc_sync_mut/enterprise_store/store.spl | store | val-var:1 | 1 | 1 | 116 |
| src/lib/nogc_sync_mut/src/exp/run.spl | config | val-var:1 | 1 | 0 | 230 |
| src/lib/nogc_sync_mut/src/exp/config.spl | config | val-var:1 | 1 | 1 | 147 |
| src/lib/nogc_sync_mut/play/cdp/client.spl | client | val-var:1 | 1 | 0 | 351 |
| src/lib/nogc_sync_mut/redis/client.spl | client | val-var:1 | 1 | 1 | 12 |
| src/lib/nogc_sync_mut/database/server/transport.spl | transport | val-var:1 | 1 | 1 | 94 |
| src/lib/common/js/conformance/report.spl | report | val-var:1 | 1 | 1 | 26 |
| src/lib/common/aes/sbox.spl | sbox | val-var:1 | 1 | 0 | 54 |
| src/lib/common/ui/state.spl | state | val-var:1 | 1 | 1 | 19 |
| src/lib/nogc_async_mut/mcp/resources.spl | resources | val-var:1 | 1 | 1 | 107 |
| src/lib/nogc_async_mut/mcp/prompts.spl | prompts | val-var:1 | 1 | 1 | 71 |
| src/lib/nogc_async_mut/mcp/jj/resources.spl | resources | val-var:1 | 1 | 0 | 87 |
| src/lib/nogc_async_mut/mcp/jj/prompts.spl | prompts | val-var:1 | 1 | 0 | 56 |
| src/lib/nogc_async_mut/src/exp/run.spl | config | val-var:1 | 1 | 0 | 227 |
| src/lib/nogc_async_mut/io/driver.spl | driver | val-var:1 | 1 | 1 | 19 |
| src/lib/nogc_async_mut/http_server/parser.spl | parser | val-var:1 | 1 | 1 | 10 |
| src/lib/nogc_async_mut/http_server/config.spl | config | val-var:1 | 1 | 1 | 89 |
| src/lib/nogc_async_mut/async/io.spl | io | val-var:1 | 1 | 1 | 25 |
| src/lib/nogc_async_mut/process_set/config.spl | config | val-var:1 | 1 | 0 | 15 |
| src/lib/gc_async_mut/src/exp/run.spl | config | val-var:1 | 1 | 0 | 224 |
| src/lib/gc_async_mut/gpu/browser_engine/js/parser.spl | parser | val-var:1 | 1 | 1 | 770 |
| src/compiler/10.frontend/core/lexer.spl | lexer | val-var:1 | 1 | 1 | 475 |
| src/compiler/70.backend/codegen.spl | codegen | val-var:1 | 1 | 1 | 717 |
| src/compiler/70.backend/irdsl/parser.spl | parser | val-var:1 | 1 | 1 | 136 |
| src/compiler/40.mono/monomorphize/cache.spl | cache | val-var:1 | 1 | 1 | 229 |
| src/compiler/90.tools/duplicate_check/config.spl | config | val-var:1 | 1 | 1 | 179 |
| src/compiler/90.tools/sffi_gen/enum_gen.spl | types | val-var:1 | 1 | 1 | 106 |
| src/os/port/audit_stubs.spl | text | val-var:1 | 1 | 0 | 251 |
| src/os/port/initramfs_pack.spl | text | val-var:1 | 1 | 0 | 422 |
| src/compiler_rust/lib/std/src/host/sync_nogc_mut/io/fs/file.spl | file | val-var:1 | 1 | 0 | 35 |
| src/compiler_rust/lib/std/src/sdn/parser.spl | parser | val-var:1 | 1 | 1 | 741 |
| src/compiler_rust/lib/std/src/sdn/lexer.spl | lexer | val-var:1 | 1 | 1 | 519 |
| src/compiler_rust/lib/std/src/tooling/testing/coverage.spl | coverage | val-var:1 | 1 | 1 | 184 |
| src/compiler_rust/lib/std/src/tooling/dashboard/query.spl | query | val-var:1 | 1 | 1 | 218 |
| src/compiler_rust/lib/std/src/tooling/dashboard/config.spl | config | val-var:1 | 1 | 1 | 50 |
| src/compiler_rust/lib/std/src/diagram/config.spl | config | val-var:1 | 1 | 1 | 284 |
| src/compiler_rust/lib/std/src/vscode/manifest.spl | manifest | val-var:1 | 1 | 1 | 33 |
| src/compiler_rust/lib/std/src/spec/runner/cli.spl | cli | val-var:1 | 1 | 1 | 311 |
| src/compiler_rust/lib/std/src/spec/snapshot/config.spl | config | val-var:1 | 1 | 1 | 80 |
| src/compiler_rust/lib/std/src/verification/lean/verification_diagnostics.spl | diag | val-var:1 | 1 | 1 | 212 |
| src/compiler_rust/lib/std/src/verification/lean/verification_checker.spl | checker | val-var:1 | 1 | 1 | 234 |
| src/app/devhub/editor.spl | editor | val-var:1 | 1 | 0 | 49 |
| src/app/devhub/config.spl | config | val-var:1 | 1 | 1 | 79 |
| src/app/sj_daemon/main.spl | daemon | val-var:1 | 1 | 0 | 35 |
| src/app/ui.test_api/json.spl | json | val-var:1 | 1 | 0 | 66 |
| src/app/sj/main.spl | client | val-var:1 | 1 | 0 | 36 |
| src/app/snpm/manifest.spl | manifest | val-var:1 | 1 | 1 | 39 |
| src/app/cli/query.spl | query | val-var:1 | 1 | 0 | 222 |
| src/app/ui.web/json.spl | json | val-var:1 | 1 | 0 | 7 |
| src/app/ui.render/config.spl | config | val-var:1 | 1 | 0 | 27 |
| test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl | manifest | match:1 | 1 | 0 | 41 |
| test/01_unit/app/office/office_api_spec.spl | spec | val-var:1 | 1 | 1 | 163 |
| test/unit/compiler/module_resolver/type_domain_resolver_spec.spl | manifest | match:1 | 1 | 0 | 41 |
| test/fixture/enterprise_store/store_native_acid_probe.spl | store | val-var:1 | 1 | 1 | 15 |
## Real fix (unchanged from the two source bug records)

Name resolution must give a local binding — `for` variable, pattern binding,
`val`/`var` — strict precedence over a module-namespace binding, and a module
namespace bound by an importer must not be visible inside the imported module's
own function scopes at all. The fix is in the Rust seed and could not be built
or verified in this lane (shared seed, rebuild forbidden).

Unblock condition: rebuild the seed, then
`test/01_unit/language/match_binding_module_name_shadow_spec.spl` goes 2/2, and
a new `for`-loop equivalent of the probe in the table above goes green.

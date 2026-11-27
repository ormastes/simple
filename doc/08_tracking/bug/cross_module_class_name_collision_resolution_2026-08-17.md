# Bug: cross-module class-name collision — type resolution can pick the OTHER module's class

- **Date filed:** 2026-08-17
- **Status:** FIXED (verified 2026-11-11, lane ne5) — was: FIX IMPLEMENTED / VERIFICATION PENDING (2026-11-08)
- **Suspected layer:** semantic / type resolution (co-compilation symbol table keyed by bare class name)

Resolution: `93991c37304` added interpreter module-owner class resolution,
including fail-closed `ambiguous type` handling, and `285c714d224` added
owner-qualified flattened HIR struct/class declarations and lookups. Current
source retains both paths. Added `interpreter_same_name_type_regressions.rs`
for same-named `ModuleLoader` classes and duplicate `List<T>` declarations;
its integration test target compile-checks successfully, while execution is
blocked by unrelated existing runtime link symbols.

## Symptom (original incident, 2026-08-17)

Two different modules each defined a class named `ModuleLoader`:

- `src/compiler/99.loader/module_loader.spl` — compat shim (since renamed to
  `module_loader_compat.spl`)
- `src/compiler/99.loader/loader/module_loader.spl` — the real loader, whose
  `ModuleLoader` carried `compiler_ctx_cell: Dict<i64, CompilerContext>`
  (today at `loader/module_loader.spl:117` on the renamed
  `struct LazyModuleLoader`, line numbers per current tree)

Under the test harness both files were co-compiled into one compilation unit,
and type resolution inside the real loader module resolved `ModuleLoader` to
the COMPAT module's class, failing with:

```
class ModuleLoader has no field named compiler_ctx_cell
```

even though the local file's class had that field. Workarounds applied: the
class was renamed to `LazyModuleLoader` and the compat file renamed to
`module_loader_compat.spl`. The filename/class collision is gone from the
tree, but the underlying compiler defect — class-name resolution leaking
across modules when same-named classes co-compile — is what this record files.

## Minimal-repro attempt (2026-08-17)

Binary identity:

```
readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
bin/simple --version | head -2
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

Fixtures (kept in scratchpad since they do NOT reproduce; to re-run, copy the
directory back to `test/fixtures/class_name_collision/` so the
`use test.fixtures.class_name_collision.*` imports resolve):

`/mnt/data/tmp/claude-1000/-mnt-data-worktrees-simple-main/827bbe32-99cd-4da9-928d-b194b567c83f/scratchpad/class_name_collision/`

Two variants, both run via
`SIMPLE_TIMEOUT_SECONDS=900 timeout 400 bin/simple test <spec> --no-session-daemon`:

1. **Distinct filenames** (`foo_alpha.spl` + `inner/foo_beta.spl`, each
   `class Foo` with a module-unique field, both imported directly by
   `collision_spec.spl`):

   ```
   1 example, 0 failures
   SPEC FILE VERDICT: test/fixtures/class_name_collision/collision_spec.spl declared>=1 executed=1 passed=1 failed=0 dropped=0
   PASS test/fixtures/class_name_collision/collision_spec.spl
   ```

2. **Same basename in sibling dirs + transitive import** (`dup_mod.spl` and
   `inner/dup_mod.spl` each defining `class Bar`; the inner one pulled in
   transitively via `inner/uses_inner.spl`, which reads the inner-unique field
   inside its own module — the original incident's shape):

   ```
   SPEC FILE VERDICT: test/fixtures/class_name_collision/dup_basename_spec.spl declared>=1 executed=1 passed=1 failed=0 dropped=0
   PASS test/fixtures/class_name_collision/dup_basename_spec.spl
   ```

Verdict: **not reproduced minimally** with 2-module fixtures on this seed
binary. The original failure needed the full 99.loader co-compilation set; the
trigger is likely scale- or order-dependent (which module's class registers
last), so a 2-module unit picking the RIGHT class proves nothing about a
1000-file unit.

## Corroborating evidence the mechanism exists

The very first fixture run emitted this diagnostic from the harness itself
(verbatim, about an unrelated stdlib symbol):

```
warning: public function `skip` has 2 co-compiled definitions with 2 differing signatures (...); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
```

i.e. co-compiled units DO key symbols by bare name with a
last-definition-wins fallback for functions. The original incident is the same
failure class applied to CLASS types: no module-qualified type identity, so
whichever same-named class registers last shadows the other for field
resolution.

## Unblock condition

Class/type identity in the semantic layer must be module-qualified
(module_id + name), not bare-name; or same-name class co-compilation must be a
hard error rather than silent shadowing. Reproduction path when someone picks
this up: reintroduce a same-named class pair inside a large co-compiled unit
(e.g. temporarily re-add a second `ModuleLoader` under `99.loader/`) and run
the loader specs — or extend the scratchpad fixtures until the
register-order-dependent shadowing shows.

## 2026-11-11 addendum (lane ne5)

**Status: FIXED — verification completed this lane.**

Verified green under the refreshed seed (`bin/simple.exe`, 2026-11-11 build,
build-commit 0791c2b7f4a7), interpreter mode, `--no-cache` (seed-smoke):

- `test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl` — 2/2
- `test/01_unit/compiler/interpreter/class_same_name_constructor_layout_spec.spl` — 2/2
- `test/01_unit/compiler/interpreter/cross_module_name_collision_resolution_spec.spl` — 3/3
- `test/01_unit/compiler/interpreter/enum_same_name_import_collision_spec.spl` — 3/3
- `test/01_unit/compiler/interpreter/same_name_type_collision_prevention_spec.spl` — 2/2
- `test/01_unit/compiler/interpreter/crossmodule_class_mutparam_writeback_spec.spl` — 1/1

Total 13 examples, 0 failures.

Two fixture-side blockers had to be cleared before the row's own verification
could run (both visibility-only; the collision semantics under test are
unchanged):

1. `class_name_collision_warning_spec` imports the collision-diagnostic API of
   `compiler.core.interpreter.eval_tables`; all five entry points
   (`struct_table_reset/register/lookup/collisions/get_module`) were private,
   so the spec ERRORed under the seed's visibility rule. Widened to `pub`. The
   same-name different-signature `struct_table_register` in
   `src/runtime/simple_core/core_memory.spl` already coexists under the
   2026-11-09 owner decision (call sites resolve by import path, else exact
   arg-type match; ambiguous-neither is a compile error).
2. The `test/fixtures/flat_fn_shadow/*` helpers the specs import directly were
   defined without `pub`: added to `load_config`, `c_val`, `tag_b`,
   `mode_a_level`, `mode_b_name`, `mode_b_mix`, `pair_a_sum`, `pair_b_text`,
   `circle_b_label`.

Fixing-commit archaeology: `285c714d2248` ("fix(seed-jit): module-qualified
struct identity for same-named flattened structs") is in this repo. The other
cited hash, `93991c37304`, is not a git object here (authored in another
clone); the equivalent landed work is visible as `b80584d93d7d` (loader
duplicate type names), PR #7498 (`r15-class-registry-modqual-20261107`),
`8e443ed51f4b` and `9728f2ac2e70`. Current source retains both the
interpreter module-owner resolution path and the owner-qualified flattened-HIR
path described above.

# The braced name list in a `use` declaration was never checked

**Status:** PARTIALLY FIXED — reporting landed, narrowing deliberately deferred
**Filed:** 2026-08-04
**Measured at:** `8ce9fe53a047d6c9fe95c6b1b7cc28095f6cfea0` (pristine detached worktree,
`/dev/shm/lane_uselist_20260804/wt`)
**Instrument:** the compiler itself — a check added to the interpreter module loader,
built from this worktree. Not a static scanner.

## 1. Where the name list was dropped

Two engines, two different drop sites. Only the first one runs today.

### 1a. Rust seed (the engine that actually executes specs)

`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:829-835`:

```rust
let requested_names = requested_group_import_names(use_stmt);
// Selective filtering in the interpreter loader is too aggressive for real
// modules: exported entrypoints often depend on private helper functions and
// internal imports whose names do not match the requested export list. Keep
// the full module so runtime evaluation remains correct.
// Move instead of clone — `module` is not used after this point.
let mut filtered_items: Vec<Node> = module.items;
```

The variable is named `filtered_items` and nothing is filtered. `requested_names` survives
only as an input to the `__init__.spl` sibling-preload heuristic further down; it never
reaches registration and is never compared against what the module provides.

**The filter that would have used it is dead code.** `should_keep_selective_export`
(`module_loader.rs:358`) has **no production call site**. Its only references are at
lines 1114 and 1670+, both inside `#[cfg(test)] mod tests` (which begins at line 1109).
Nine unit tests exercise a function that never runs — the tests are green and the
behaviour they describe has never shipped.

### 1b. Pure-Simple self-hosted compiler (canonical tool, not currently deployed)

`src/compiler/10.frontend/core/interpreter/module_loader_core.spl:409`, `load_module_selective`.
Here the list IS consulted, but only as a fast-path heuristic:

```
    var all_available = true
    for name in imported_names:
        if func_table_lookup(name) < 0:
            all_available = false
            break
    if all_available and imported_names.len() > 0:
        module_mark_loaded(module_name, "", imported_names)
        return 1

    # Full load
    val load_ok = load_module(module_name, current_file)
```

`load_module` calls `register_module_functions()`, which registers the module's **whole**
surface. So the braced list answers only "are these names already registered by somebody?"
— never "does THIS module provide them?". A name absent from the module produces no
diagnostic on either branch.

Note the fast path is itself a hazard: if every braced name happens to already be in the
global function table — registered by a *different* module — the named module is marked
loaded and **never read from disk**.

### Correction to the original framing

The lane report said "the `{...}` list is never consulted". More precisely: in the Rust
seed it is consulted for an unrelated purpose and never for admission; in the pure-Simple
loader it is consulted as a presence heuristic and never for admission. In neither engine
is it ever compared against the resolved module's actual surface. The observable
consequence is exactly as described.

## 2. Minimal reproduction (independent of the chacha20 lane)

`probe_mod.spl` defines `real_one` and `also_real`. `probe_bad.spl`:

```
use probe_mod.{real_one, totally_bogus_name}

fn main():
    print("bad-arm result=" + (real_one() + 1).to_text())
```

Before this change, verbatim: `bad-arm result=42`, exit 0, **no diagnostic of any kind**.

## 3. What was implemented — reporting, not restricting

`module_loader.rs`, +158 lines, purely additive. For an `ImportTarget::Group` import the
loader now collects the surface the resolved module actually provides and emits
`[use-warning]` for each braced name absent from it.

Surface = exports ∪ module functions ∪ classes ∪ enums (plus their variants and methods)
∪ `locally_defined_names` ∪ explicit `export use x.{A, B}` re-export lists.

Deliberate false-positive guards:

- A module whose surface is genuinely unknowable — it re-exports through `export use x.*`
  or a bare `export use {..}` that pulls from siblings — is **skipped**, not guessed at.
- The surface is recorded per resolved path, so the check also runs on module-cache hits
  where the AST is gone.
- Deduped per (module, name, importer).
- Warning only, never fatal. Silenced by `SIMPLE_NO_DEPRECATED_WARNINGS`, the same switch
  the sibling `[gc-warning]` check honours.

### Not fatal, on purpose

The repo already treats an unresolved `use` as a warning, so an exit-status oracle here is
fail-open either way. Making this fatal in the same change would convert a silent hazard
into a mass build break with no migration path.

### Deliberately NOT changed: what gets registered

Restricting the registered surface to the braced list is the correct eventual fix. It is
not done here, and this lane does **not** claim it is safe. It would change symbol
resolution repo-wide, and this repo has documented bare-name-collision and last-wins
registry behaviour. It needs its own lane with a full before/after resolution census.

Note that narrowing is *harder* than it looks for a second reason: the in-tree comment at
`module_loader.rs:830` records that a previous attempt at selective filtering was reverted
because "exported entrypoints often depend on private helper functions". Any narrowing
must therefore separate *what a module registers for its own evaluation* from *what an
importer may name* — those are currently the same set.

## 4. Sabotage verification (both arms required)

Run against the built binary, `SIMPLE_EXECUTION_MODE=interpret`.

**Arm A — braced name the module genuinely lacks. Must fire, naming the symbol:**

```
[use-warning] 'totally_bogus_name' is named in `use probe_mod.{...}` but module
'/.../probe_mod.spl' does not provide it (imported from /.../probe_bad.spl)
bad-arm result=42
```

Fires, names the symbol, and the program still runs — confirming non-fatal.

**Arm B — every braced name the module genuinely has. Must be silent:**

```
good-arm result=42
```

`grep -c '^\[use-warning\]'` = **0**. A check that fired here would be worthless.

**Arm C — the original subject, unmodified `chacha20_spec.spl`:**

```
[use-warning] 'chacha20_keystream' is named in `use std.crypto.chacha20.{...}` but module
'/.../src/std/common/crypto/chacha20.spl' does not provide it (imported from
test/01_unit/lib/crypto/chacha20_spec.spl)
```

Confirmed true positive: `chacha20.spl` defines `chacha20_block` and `chacha20_encrypt`;
`fn chacha20_keystream` is defined **nowhere in `src/`**. The spec reports
`Results: 12 total, 12 passed, 0 failed` regardless.

## 4a. The sharpest form of the defect: braces downgrade a hard error to nothing

The single-symbol import form is, and always was, **enforced**. Only the braced form was not.
Same module, same missing symbol, same binary:

```
$ simple run probe_single.spl     # use probe_mod.totally_bogus_name
error: runtime: Module "probe_mod" does not export 'totally_bogus_name'
                                                    # program does not run

$ simple run probe_braced.spl     # use probe_mod.{totally_bogus_name}
braced-arm ran                                      # before this change: silent
```

Adding one pair of braces turned a hard error into no diagnostic at all. The enforcement
lives in `load_and_merge_module`'s `import_item_name` branch, which is populated for
`ImportTarget::Single`/`Aliased` and left `None` for `ImportTarget::Group` — so the group
form skipped the only check that existed.

## 5. Compiler-measured count vs the static census

**Instrument.** Each spec is loaded with `SIMPLE_EXECUTION_MODE=interpret simple run <spec>`
and the `[use-warning]` lines are collected. Loading is enough — module resolution happens
at `use` evaluation, before any test body executes — which is ~200x cheaper than a test run
and, crucially, excludes the test runner's own imports (running via `simple test` adds 7
warnings from the runner's own `std.test_runner.*` modules to every single file).

**Coverage.** 2,766 of 18,905 spec paths (14.6%): a 2,352-file alphabetical prefix plus two
sets with clean denominators — the **264** census-implicated files that still exist, and a
**150**-file random control drawn from the files the census called clean.

| | measured |
|---|---|
| distinct names warned | **636** |
| distinct (name, module) pairs | 615 |
| distinct spec files warned | 409 |
| — of the 636: declared **nowhere** in owned `src/` | **542** |
| — of the 636: declared in `src/` but **not in the module named** | **94** |

### What the disagreement with 1,003 means

The two instruments are **not measuring the same predicate**, so neither number corrects the
other.

- The census asks: *is this name declared anywhere in owned `src/`+`test/`?* → 1,003 names.
- This check asks: *does the module the `use` line actually names provide it?* → 636 names.

These overlap but neither contains the other:

1. **542 of my 636 are the census's class**, found from 14.6% of the corpus. Scaled against
   coverage that is consistent with — not smaller than — the census's 1,003 over the whole
   corpus. The instruments agree in direction; there is no contradiction to resolve.
2. **94 names are a class the census structurally cannot see.** They *are* declared in
   `src/` — just not in the module the `use` line names. A repo-wide "is it declared
   anywhere" predicate scores these as healthy. They are real defects: the `use` line
   misidentifies where the symbol comes from, and only worked because registration is
   whole-module. Example from the spot check: `allow_all_policy` is declared in
   `src/app/llm_caret/tools.spl`, not in the module it is imported from.
3. **The 636 is a hard lower bound.** 239 of the 264 flagged files exit non-zero, most on a
   `semantic` error, and an unresolved *module* is a hard error that **aborts the load** —
   so every `use` line after the first bad one in those files was never evaluated and could
   not be checked. The count is truncated by an unknown amount.
4. **The census's clean set is not clean.** Of the 150 control files the census did not
   flag, **16 still warned, contributing 35 distinct names**. This is point 2 showing up as
   a measured false-negative rate in the census, not a defect in it — it is the direct
   consequence of the repo-wide predicate.

**Conclusion:** the census's 1,003 and this check's 636 are both real and both partial. The
compiler-side check is authoritative for *"does the named module provide this?"*, which is
the question a reader of a `use` line is actually asking; the census remains the better
instrument for *"does this symbol exist at all?"*. Neither should be quoted as the total.

### Reproducing

```sh
SIMPLE_EXECUTION_MODE=interpret SIMPLE_TIMEOUT_SECONDS=0 \
  simple run <spec> 2>&1 | grep '^\[use-warning\]'
```

`SIMPLE_TIMEOUT_SECONDS=0` is required: a bare directory-mode `simple test` run is killed by
`kill_simple_monitor` at 60s CPU and exits **143** having produced only the runner's own
startup warnings — which reads exactly like a clean corpus.

## 6. Follow-ups this lane deliberately did not do

1. **Narrow the registered surface to the braced list.** Section 3. Needs its own lane.
2. **Pure-Simple parity — `module_loader_core.spl:409`.** Not implemented here, and the
   reason is itself a finding: the obvious implementation (mirror
   `check_gc_family_boundary`, push to `eval_warnings`) would be **invisible**.
   `eval_get_warnings()` is exported from `eval.spl:208` and `__init__.spl:15` and has
   **no consumer anywhere in `src/`** — `eval_warnings` is a write-only sink, so the
   existing `[gc-warning]` messages pushed into it are already unreachable except under
   `SIMPLE_COMPILER_TRACE=1`. Shipping a second check into a dead sink would have been
   vacuous. Fix the sink first, then add the check.
3. **Delete or wire up `should_keep_selective_export`.** It is dead production code with
   nine live tests. Either is defensible; leaving both is not.
4. **The `load_module_selective` fast path** (`module_loader_core.spl:417-426`) can mark a
   module loaded without reading it, when the braced names collide with names another
   module already registered. Untested and unmeasured.

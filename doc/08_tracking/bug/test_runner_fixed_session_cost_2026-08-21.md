# `simple test <dir>` pays ~400s of fixed cost before running any test

Status: PARTIALLY FIXED (root mechanism identified; first two collisions removed)
Date: 2026-08-21
Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed), origin/main tree at `/mnt/data/worktrees/testperf`
Host caveat: shared box under concurrent load; wall times are an envelope, the SPLIT is the load-bearing part.

## Measured split

`simple test test/01_unit/compiler/config/` — 7 spec files, 163 examples.

| phase | pre | post (2 collisions removed) |
|---|---|---|
| single-spec lane (`test/.../compiler_config_spec.spl`) total wall | **4.2s** | 4.2s |
| directory lane total wall | **413s** (6m53s) | 364s (6m04s) |
| `[setup] discover` | **64ms** (7 files) | 44ms |
| `[setup] cover-check` | 0ms | 0ms |
| `Session setup:` (runner-reported) | 10.2s | 10.1s |
| actual test execution (`Time:`) | 4.2s | 4.2s |
| **unaccounted: module load of `test_runner_new/main.spl`** | **~400s** | ~350s |
| spec results | 163/163 pass | 163/163 pass |

The premised causes are NOT the current dominant cost:
- **Discovery is not quadratic and is already scoped** — 64ms for a 7-file target; `discover_all_requested_files` (`src/app/test_runner_new/test_runner_main.spl:157`) delegates to `discover_test_files_fast` for a single target.
- **Doc regeneration is already gated** — `generate_spipe_docs_for_results` (`test_runner_main.spl:84`) returns 0 immediately unless `options.format == "doc"`; a scoped run makes zero docgen calls.

## Root mechanism

The ~400s is module load, and it is dominated by a single line in the seed's output:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'CompilerContext'
  field 'handle' (declared fields: alive) [in src/app/test_runner_new/main.spl]:
  whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

`src/compiler/99.loader/compiler_sffi.spl` (compat surface) **redeclared every
symbol** of `src/compiler/99.loader/loader/compiler_sffi.spl` (the real module)
as a stub with a *different field shape*: `class CompilerContext{alive}` vs
`struct CompilerContext{handle}`, `class TypeInfo{type_name}` vs
`struct TypeInfo{kind,name,...}`. Both modules land in one HIR symbol table, so
the name binds to the compat stub while a real construction site is lowered;
lowering aborts, and **one abort drops the whole enclosing module to the
interpreter**. The fast single-spec lane
(`src/compiler_rust/driver/src/main.rs:244 test_should_use_light_daemon_client`
-> `test_runner_client.spl`) never touches that graph: zero jit-fallbacks, 4.2s.

## Fix landed

`src/compiler/99.loader/compiler_sffi.spl` is now a re-export shim of the real
module (27 lines, was 95); the 21 duplicate declarations are gone. Only the 4
helpers with no real counterpart (`type_args_is_empty`, `code_bytes_len`,
`code_len`, `bytes_len`) remain defined there. Verified 163/163 still green.

## Still open — the chain is not exhausted

After removing `CompilerContext` and `TypeInfo`, the next duplicate surfaces
immediately (`CudaModule` field `is_valid` vs `handle`), and a static census of
the tree finds **1,657 type names declared more than once** (top: `StackFrame`
x18, `Scope` x16, `Breakpoint` x15). Chasing them one at a time cannot close
this. The real fixes belong in the compiler:

1. HIR lowering must resolve a struct-literal's type from the **module scope of
   the construction site**, not a globally shared name binding.
2. A single unresolvable field must not drop the **whole module** to the
   interpreter — the blast radius is what turns a local defect into a 100x
   slowdown of everything in the file.

Until (1)/(2) land, no honest wall-time budget row can be set for the directory
lane; `scripts/check/check-perf-regression-tests.shs` therefore pins the
**mechanism** (no shadow declarations in the loader compat surface), not a time.

## Tests

- `test/01_unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl`
  (mirrored to `test/unit/...`): 4 of 5 examples FAIL on the pre-fix file,
  5/5 pass post-fix.
- 4 mechanism rows in `scripts/check/check-perf-regression-tests.shs`
  (`PASS — 22 mechanism(s) checked, 0 regressed`).

## Rejected

`use lazy` on the 14 conditional-only imports of `test_runner_main.spl` was
tried and **reverted**: measured 112s (eager) vs 126s (lazy) on the same repo
for `--list`, i.e. no gain outside noise. The graph is loaded regardless; the
cost is the interpreter fallback, not the import count.

# `file_read` has 23 definitions across two incompatible return types

**Status:** OPEN
**Found:** 2026-08-16 — during the SCV file-read/rendering coverage review at
`f6cadcc36aff61d16d988651ea36a040d2af6aad`, as the direct sibling of the
`file_read_bytes` defect
(`doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`)
**Severity:** latent misdispatch — same class as the `file_read_bytes` defect, but
~4x wider and, unlike that one, previously untracked
**Component:** `src/lib/**`, `src/compiler/**`, `src/app/**`, `src/os/**`

## Defect

`file_read(path: text)` is defined **23** times with **two mutually incompatible
return types**:

| return type | count | notes |
|---|---|---|
| `-> text` | 20 | only ONE is exported: `src/lib/nogc_sync_mut/io_runtime.spl:97` (`pub fn`) |
| `-> text?` | 3 | all module-local, all under `src/compiler/` |

The three optional-returning definitions:

| module | line |
|---|---|
| `src/compiler/40.mono/monomorphize/hot_reload.spl` | 22 |
| `src/compiler/99.loader/module_resolver/manifest.spl` | 22 |
| `src/compiler/99.loader/module_resolver/resolution.spl` | 539 |

Each of the three declares its own `extern fn rt_file_read_text(path: text) -> text`
and wraps the result into `text?`, so the optionality is added locally rather than
coming from a shared source. The remaining 20 return bare `text`.

This is the identical shape to the `file_read_bytes` defect closed on 2026-08-16
(`[i64]` vs `[u8]`), except that defect was tracked and this one was not. The
2026-08-09 doc covers only the `_bytes` family; nothing records the `text` family.

## Why it matters — this is SCV's dominant read path

The 2026-08-16 unification migrated SCV's **byte** path (27 call sites, 10 modules).
SCV's **text** path is roughly 5x larger and was untouched:

- **136 `file_read(` call sites** across **21 of 27** `src/lib/scv/*.spl` modules.
- They import via `use app.io.mod (file_read, ...)`, which is a re-export shim
  (`src/app/io/mod.spl:16,236`) onto `std.nogc_sync_mut.io.file_ops.file_read`
  (`src/lib/nogc_sync_mut/io/file_ops.spl:75`, `-> text`).

Verified during the review that this resolution is correct — SCV does **not** bind to
the stub `src/app/io/mod_stub.spl:47`, and does not bind to any `text?` definition.

## Current exposure

Risk is confined to a compilation closure that co-compiles a `-> text` and a
`-> text?` definition; per the 2026-08-09 doc, the ambiguous-dispatch warning surfaces
only the pair that actually collides in a given closure, so the absence of a warning is
not evidence of absence.

- **SCV is not currently exposed.** All three `text?` definitions live under
  `src/compiler/`, which SCV does not import.
- **The compiler modules are the risk zone**, since that is where both shapes coexist.
- The 20 `-> text` definitions being module-local (only `io_runtime.spl` exports one)
  limits blast radius but is also what let the spread grow to 23 unnoticed: each module
  quietly adds its own copy rather than importing the `pub` one.

## No guard covers this family

`test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl` (81 lines)
is the guard the 2026-08-09 doc refers to. It contains **zero** references to the plain
`file_read` family — grep for `file_read\b` / `file_read(` in it returns nothing. So the
23-definition text family is entirely unguarded, and no existing test would fail if a
24th definition (or a third return type) were added tomorrow.

A sibling guard modelled on that spec is the cheapest containment step, and it can land
independently of any de-duplication work.

## Not verified by execution

Static analysis only. The mandated pure-Simple self-hosted evidence path was
unavailable at this tip: `bootstrap/stage{1,2,3}/simple` are byte-identical
(md5 `2244f18ce2e694fb7ca395e9916404c3`) and all three segfault (exit 139) on a
two-line hello-world; they expose only `compile`/`native-build`, and
`compile src/lib/scv/store.spl` fails with
`HIR lowering error in src/app/io/cli_ops.spl: unresolved name: __p-1`.
`bin/simple` is the Rust seed and is not admissible as test evidence.

Consequently: **no claim is made here that any specific call site misdispatches
today.** What is established is the definition spread and the return-type split.

## Suggested fix

Mirror the `file_read_bytes` resolution:

1. Keep one canonical `-> text` definition and have modules import it rather than
   redefining. `src/lib/nogc_sync_mut/io_runtime.spl:97` is already the `pub` one.
2. Give the optional shape a unique name (`file_read_opt`, matching the
   `file_read_bytes_i64` precedent) and migrate the three `src/compiler/` callers,
   so the two shapes can never collide in one closure.
3. Note the 2026-08-09 doc records that *full* convergence of `file_read_bytes` was
   attempted and reverted because it hung the compiler. Expect the same hazard here
   and land the rename before attempting any de-duplication.

## Related

- `doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`
  — sibling defect, byte family, signatures unified 2026-08-16, full convergence still open.

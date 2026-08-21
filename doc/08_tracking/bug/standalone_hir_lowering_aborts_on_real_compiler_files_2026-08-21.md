# Standalone parse+lower aborts on real compiler files (`split` on i64)

Date: 2026-08-21
Reporter: agent A5+Y2 (Any hardening)
Status: OPEN

## Symptom

Lowering a real compiler source file to HIR outside the driver — i.e.
`parse_full_frontend(...)` followed by `HirLowering.lower_module(...)` — aborts
the whole process:

```
error: semantic: method `split` not found on type `i64` (receiver value: 32)
```

No caller code is on the stack; the failure is inside the seed's own
parse/lower path.

## Reproduce

```simple
use compiler.frontend.{parse_full_frontend}
use compiler.common.config.{Logger}
use compiler.hir.hir_lowering.*
use compiler.hir.hir_lowering.module_surface_types.{ModuleSurfacesByName}
use compiler.hir.hir_types.{HirModule}

fn probe_run(path: text) -> i64:
    val content = rt_file_read_text(path) ?? ""
    val pm = parse_full_frontend(content, path, "m", Logger(level: 0))
    var lowering = hirlowering_for_module("", ModuleSurfacesByName.empty())
    val hm: HirModule = lowering.lower_module(pm)
    hm.functions.len()
```

- `src/compiler/00.common/assurance/policy_names.spl` → lowers fine.
- `src/compiler/00.common/assurance/unsafe_capabilities.spl` → aborts as above.

The probe contains no `split` call of its own, which is how the failure was
attributed to lowering rather than to the caller.

Two other standalone-lowering limits were observed in the same session and are
probably the same family: a fixture containing an `enum` plus an enum-literal
construction aborts with `undefined field 'symbol': cannot access field on value
of type 'nil'`, and a fixture containing a `struct` aborts with
`class HirFunction has no field named is_generic_template`.

## Consequence

Any tool that wants typed HIR for one file at a time — the Any-escape census
(`scripts/check/check-any-escape-census.shs`), and any future per-file semantic
audit — cannot process the compiler's own sources in a single process: one bad
file kills the run.

## Current mitigation, not a fix

The census invokes the driver ONE PROCESS PER FILE and classifies an aborted
file as UNANALYZABLE — counted, named in the verdict, and never counted as
clean. That bounds the blast radius; it does not make the file analyzable. The
unanalyzable count is part of the recorded baseline so it cannot drift silently.

## Update 2026-08-21 (test-infrastructure lane) — narrowed, NOT fixed

The fix belongs in `src/compiler/20.hir/**`, which this lane does not edit, so
this is a handoff with the narrowing done.

**The trigger is a declaration KIND, not a `split` call in the input.**
`src/compiler/00.common/assurance/unsafe_capabilities.spl` contains no `split`
and no literal `32` (`grep -n "split\|32"` returns nothing), so the receiver
`32` is compiler-internal. The file's structural difference from the
known-good `policy_names.spl` is that it declares an **enum and a struct** —
exactly the two constructs the record's own "same family" note says also abort
in reduced fixtures (`undefined field 'symbol'` for an enum literal,
`class HirFunction has no field named is_generic_template` for a struct). Treat
all three as one defect in standalone (non-driver) lowering of type
declarations, not three.

**Prime suspect for the `split` abort, cheapest to probe first:**
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:286-291`

```
fn _hir_text_index_of(value: text, needle: text) -> i64:
    ...
    rt_string_len(value.split(needle)[0])
```

It is the only `.split` in `hir_lowering/` whose receiver is a bare parameter
rather than a locally-typed text value, so it is the one call an erased
caller can reach with an `i64`. The `text` annotation is not enforced on the
interpreter path, which is why the abort surfaces as
`method \`split\` not found on type \`i64\`` with no caller frame. Confirm by
logging `value` at entry before changing anything — do not "fix" it by
coercing the receiver, since that would hide whichever caller is passing a
span/offset where a name is expected.

Consequence for the Any census is unchanged: it stays one process per file with
UNANALYZABLE counted and named.

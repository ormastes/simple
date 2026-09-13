# Stage-2 native codegen: SEGVs compiling a method that writes a `self.<dict>[k] = v` inside a guarded `if`

- Status: OPEN (2026-09-14)
- Lane: BOOT-20 (`work/bootstrap-s3-2-2026-09-14`), found while chasing
  `stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`
- Binary: pinned Stage-2 candidate `bin/release/aarch64-unknown-linux-gnu/simple.phase2`,
  sha256 short form `80911c47f07cdb64b4c3`
- Class: native-codegen-only compiler crash (SEGV, rc 139), reproduced OUTSIDE
  the compiler's own sources with a minimal standalone probe program

## Symptom

`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 <stage2-candidate>
native-build probe.spl -o out` dumps core (rc 139) during the `mir` build
phase (after `hir`/`monomorphize` complete cleanly), for a probe program that
has nothing to do with the real compiler — it never runs, produces no
binary, and the candidate process itself crashes while *compiling* it.

## Minimal reduction (measured 2026-09-14)

```simple
struct EnumLike:
    tag: text

class Big:
    imported_enums: {text: EnumLike}
    imported_enum_owners: {text: text}

impl Big:
    me register_inner(local_name: text, owner: text, materialize_enum: bool):
        if materialize_enum and not self.imported_enum_owners.contains_key(local_name):
            self.imported_enum_owners[local_name] = owner

fn main():
    var b = Big(imported_enums: {}, imported_enum_owners: {})
    b.register_inner("Kind", "mod_a", true)
    if b.imported_enum_owners.contains_key("Kind"):
        print("PRESENT:" + b.imported_enum_owners["Kind"])
    else:
        print("MISSING")
```

`native-build` on this SEGVs (rc 139) during MIR lowering, after printing
`any-escape pass` warnings for both dict fields (`E-MC-ANY-002`, "erased
value escapes its type_erasure boundary"). No binary is produced.

### Bisected

| shape | outcome |
|---|---|
| Two dict-field writes (`enums[k]=`, `owners[k]=`) inline in `fn main()`, no class method | compiles and runs (see the companion bug doc for its own separate defect: a `text`-valued bracket-read on a hit returns garbage) |
| Same two writes moved into a class `me` method (`do_insert`), called once from `main` | **SEGVs the compiler** |
| A single dict-field write (`owners[k]=owner`, guarded `if`) inside a class method | **still SEGVs the compiler** — this is not dual-write-specific |
| Same single write with 6-24 additional unrelated dict/scalar fields on the class | still SEGVs |

So the trigger is not "two co-located dict writes," it is **any
`self.<dict-field>[k] = v` write inside a guarded `if` block, inside a class
method** (as opposed to inline in a top-level `fn`). This is a strict subset
of the pattern already used, without crashing, in the REAL compiler's own
`register_imported_symbol_inner`
(`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:370-373`)
— that method is part of the ALREADY-COMPILED Stage-2 binary and runs fine at
its own runtime (modulo the silent data-corruption bug filed separately); the
SEGV reproduced here is the SAME compiler crashing while compiling a NEW
instance of an analogous pattern in someone else's source, not a crash in its
own execution. The two are very likely the same underlying MIR-lowering
defect for this shape, surfacing two different ways depending on which
generation of "compile this pattern" is involved.

## Not investigated further (out of BOOT-20's budget)

The exact MIR-lowering pass and IR shape responsible were not isolated —
that needs either a Stage-2 rebuild with added diagnostics (the pre-built
candidate cannot be instrumented without rebuilding it) or a gdb-attached
repro (see `.claude/memory` notes on `ptrace_scope`/`perf_event_paranoid`
constraints on this host, which blocked attach-based profiling for a
similar wall in `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`).
Candidate next step for whoever picks this up: reproduce with
`SIMPLE_COMPILER_TRACE=1` / `RUST_BACKTRACE=1` equivalents already wired
into the native-build pipeline, or run the probe under `gdb --args
<candidate> native-build probe.spl -o out` to get a backtrace at the SEGV
site directly (this lane did not have a free gdb slot to spend on a
secondary defect once the primary one was reduced and worked around).

## Why this did not block BOOT-20's fix

The workaround in `stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`
does not add a new method-scoped dict write of this shape — it reads from
`self.symbols.symbols` (already read this way elsewhere in the same file,
e.g. `claim_materialized_payload_binding`) and touches no new dict field, so
it does not exercise this second defect.

## Related

- `doc/08_tracking/bug/stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`
  — the primary BOOT-20 defect (silent wrong `contains_key`/bracket-read,
  not a crash), found first; this SEGV was found while building probes to
  isolate it.
- `doc/07_guide/language/dict_native_pitfalls.md` — existing truth table of
  native Dict defects; neither this SEGV nor the sibling doc's text-value
  bracket-read garbage is yet listed there.

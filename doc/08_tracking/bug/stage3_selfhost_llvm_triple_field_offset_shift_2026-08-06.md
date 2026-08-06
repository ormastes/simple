# Stage 3 self-host blocker: LLVM module header triple shifted by one struct slot

- **Date:** 2026-08-06
- **Status:** FIXED (workaround at the call site; the seed fail-open is still live)
- **Blocker:** #6 on the Stage 3 self-host critical path (task #18)
- **Symptom:**
  `llc: error: unable to get target for 'unknown-linux-<enum@0x27c1498b0>', see --version and --triple.`
  Stage 3 translated 5,674 bootstrap MIR functions + 86 statics and wrote a
  5.9 MB `.ll`, then `llc` rejected the module header.

## Not two defects — one field-offset shift

The emitted header line was:

```
target triple = "unknown-linux-<enum@0x27c1498b0>"
```

The obvious reading is "empty `arch`, plus an `env` that reached text
formatting as a raw enum handle". That reading is wrong, and the tell is a
character that is **not** there: **there is no leading `-`**.

`emit_module_header` composes the triple as
`"{header_target.arch}-{header_target.vendor}-{header_target.os}"`. An empty
`arch` would render `"-unknown-linux"`. The separator between `arch` and
`vendor` is gone too, so `arch` is not empty — every field read is displaced by
one slot.

`struct LlvmTargetTriple` (src/compiler/70.backend/backend/llvm_target.spl:17-22)
declares `arch, vendor, os, env`. With a +1 shift:

| read        | actually returns | value          | rendered            |
|-------------|------------------|----------------|---------------------|
| `.arch`     | `vendor`         | `"unknown"`    | `unknown`           |
| `.vendor`   | `os`             | `"linux"`      | `linux`             |
| `.os`       | `env`            | `Some("gnu")`  | `<enum@0x27c1498b0>`|
| `.env`      | past the end     | not a `Some`   | `nil` arm taken     |

That reproduces the observed string character-for-character, **including the
missing `-gnu` suffix**: the `match header_target.env` at line 124 falls to the
`nil` arm because the shifted read lands past the struct, so the `Some` arm
that appends `-{target_env}` never runs.

### Is the `<enum@0x...>` the known enum-to-text defect?

It is the known enum/erased-value-to-text rendering class (sibling of native
tuple-to-text printing a raw pointer), but it is **not the defect here**. The
renderer behaved normally; it was simply handed an `Option` that arrived in a
text slot because of the shifted read. Fixing the shift removes the enum from
that slot entirely. There is no missing conversion at the call site.

## Root cause

`src/compiler/70.backend/backend/llvm_ir_builder.spl:114` and `:116`
(pre-fix line numbers), inside `LlvmIRBuilder.emit_module_header`:

```
val target = LlvmTargetTriple.from_target(llvm_builder_target())
val header_target = if mir_target_context_os_from(requested, "") == "baremetal":
```

Both were **untyped locals**. An untyped local loses the owner type, MIR emits
`owner_name: None`, and the seed layout pass fails open to
`owner_has_vtable = Some(true)` — reserving a vtable slot that a plain struct
does not have, so every subsequent field read is off by one.

This is the same defect shape as blocker #5
(`stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06.md`), where the
fail-open went the other way (`Some(false)`) and produced a RELRO SIGSEGV. The
underlying Rust-seed fail-open at `native_project/compiler.rs:1707` is
**still live and open**; fixing it requires a seed rebuild, which would replace
the pinned `stage2-runtime-authority` other lanes measure against. Not done
here.

## Fix

Annotate both locals explicitly:

```
val target: LlvmTargetTriple = LlvmTargetTriple.from_target(llvm_builder_target())
val header_target: LlvmTargetTriple = if ...
```

One edit; it corrects all four components at once, which is itself the
confirmation that the cause was a single shift rather than two independent
defects.

## Masking worth recording

`target datalayout` in the broken output was **correct** — the x86_64 ELF
layout — which made the header look half-healthy. That was an accident, not a
signal: `datalayout()` (llvm_target.spl:142-174) matches on `self.arch`, the
shifted read returned `"unknown"`, no `case` arm matched, and the
`case _:` default happens to be exactly the x86_64 ELF datalayout. A correct
datalayout next to a corrupt triple is therefore not evidence that `arch` was
read correctly.

## Related sibling (not changed)

`llvm_target.spl:333` has the same untyped-local shape
(`val triple = LlvmTargetTriple.from_target_with_mode(...)`) but the value is
only passed by reference into a `LlvmTargetConfig` constructor and never
field-read locally, so the shift cannot manifest there. Left alone to keep the
fix minimal; noted here so the family is enumerated rather than forgotten.

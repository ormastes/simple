# Stage 3 frontier: one `unresolved name` whose name and location disagree (2026-08-25)

## Status

SOURCE FIXED; rebuilt Stage 2 and Stage 3 evidence pending. Stage 3 is the
frontier after the Stage-2 `is_empty` misdispatch fix (`3edcb8c2605`). It failed
**much later and on a single error**.

## How far the chain got

| stage | result |
|---|---|
| Stage 2 | builds, **admitted**, and compiles + runs a hello world (`native-build` → `hi`, rc=0) |
| Stage 3 | **fails**, after 523 s of HIR work, on exactly ONE distinct error |
| Stage 4 / 5 / deploy | not reached; nothing deployed |

## The error

```
[hir-fatal] source_idx=228 path=src/compiler/10.frontend/core/parser.spl error_idx=0
  text=HIR lowering error in src/compiler/10.frontend/core/parser.spl:
       unresolved name: is_option_generic_tag
       at src/compiler/10.frontend/core/parser.spl:36:8
```

Three log lines, one distinct error. Nothing else fails.

## Root cause

The unresolved name is accurate: `parser.spl` calls
`is_option_generic_tag(base)` while its explicit `compiler.core.types` imports
included `option_generic_type_register` but omitted the predicate. The call was
introduced by `3dc5b8dd8a` and is already present in the measured
`f4bfeda746b` tree. The earlier claim that the file did not reference the name
was incorrect.

The reported location remains a separate diagnostic defect.
`parser.spl:36` is `extern fn rt_env_get(key: text) -> text`; column 8 is
`rt_env_get`, not `is_option_generic_tag`. The symbol is defined and exported
by `src/compiler/10.frontend/core/types.spl`.

The parser now imports `is_option_generic_tag` explicitly beside its registry
owner. `stage3_parser_optional_generic_import_spec.spl` pins the consumer import
and call.
Only a rebuilt admitted Stage 2 followed by Stage 3 can close the runtime row.

The focused source-owner spec passed in interpreter mode with the bootstrap
seed (one example, zero failures). This is diagnostic evidence only, not
self-host acceptance. The dedicated sparse worktree has no pure-Simple
`bin/simple`, so the Simple optimizer was unavailable for the touched `.spl`
files and was not replaced with a Rust implementation or claimed as run.

## Prior worth testing first

This has the shape of the defect class that dominated the Stage-2 investigation: a
value of the wrong kind occupying a slot, surfacing as a confident but wrong
report. The Stage-2 root cause was a **name-only lookup** that discarded a type
qualifier and bound a call to an unrelated same-named method
(`bootstrap_stage2_empty_mir_bodies_2026-07-05`). A name/location mismatch in an
`unresolved name` diagnostic is consistent with the resolver reporting one symbol's
identity against another's span.

The name/location mismatch must not override direct source evidence: resolve
the named symbol at the real call site first, while tracking the stale span as
diagnostic metadata debt.

## Measured on

Boot worktree at `f4bfeda746b` (current main, carrying both the `is_empty` fix and
the sibling lane's `unresolved type` import-provenance fixes). Stage 2 admitted,
`parent_compiler_sha256=8571caf28a24c8e3379f5255b84b2d48d25e47ef35a7d7f7d130bf306a55dc12`,
Stage-3 authorization via the typed reason `verify-landed-compiler-fix`
(`5c8383578ef`).

**Note on staleness:** an earlier Stage-3 run against the worktree's old commit
(`d4b1dee0d63`) failed at ~6 min with *hundreds* of `unresolved type` errors in
`resolve_lookup_helpers.spl`. Those were already fixed on main by a sibling lane;
the worktree was 165 lines behind on that file alone. That run's frontier was an
artifact of a stale tree and should not be cited.

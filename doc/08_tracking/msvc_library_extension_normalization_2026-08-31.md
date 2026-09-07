# MSVC configured-library extension normalization

**Date:** 2026-08-31
**Status:** OPEN — rejected from the completed provider-hardening cycle
**Scope:** final `_link_native_msvc` configured-library assembly only

## Defect and exact reproduction

Configured libraries currently use a case-sensitive suffix check:

```simple
for lib in config.libraries:
    if lib.ends_with(".lib"):
        msvc_config.libs.push(lib)
    else:
        msvc_config.libs.push("{lib}.lib")
```

With `config.libraries = ["C:\\configured\\SIMPLE_COMPILER.LIB"]`, final
assembly first produces `C:\configured\SIMPLE_COMPILER.LIB.lib`. For the
default/`auto` bundle with no discovered archives, fallback selection then adds
`simple_compiler.lib`. Basename dedup correctly ignores case and slash style,
but cannot identify the corrupted basename `SIMPLE_COMPILER.LIB.lib` as the
same library. Mixed-case input such as `Simple_Compiler.Lib` fails identically.

## Required fix and regression coverage

Add one small normalization helper for a raw configured MSVC library: recognize
`.lib` case-insensitively while preserving the caller's original spelling and
path; append `.lib` only when the suffix is genuinely absent. Use it at the
configured-library ingestion point before fallback/provider merge.

Add a final-assembly test, not only a helper/dedup test. It must assemble raw
`SIMPLE_COMPILER.LIB` and `Simple_Compiler.Lib` inputs with the empty-archive
default/`auto` fallback and prove that each original input survives unchanged,
no `.lib.lib` appears, and no second `simple_compiler.lib` is appended. Retain a
suffixless input case proving that `foo` still becomes `foo.lib`.

## Semantics already accepted; do not reopen

- Explicit runtime authority is validated before Windows dispatch.
- Complete discovered provider archives win; default/`auto` with no archives
  falls back to `simple_compiler.lib`; named bundles do not silently fall back.
- MSVC provider merge deduplicates case-insensitive normalized basenames and
  does not apply Unix archive rescans.
- Caller spelling/path is retained when a configured library already names a
  `.lib`; this fix is extension recognition, not canonical renaming.

## Runtime archive census

The admitted logical runtime archive set is exactly three names:

| Role | MSVC | Unix/MinGW |
|---|---|---|
| compiler aggregate/fallback | `simple_compiler.lib` | `libsimple_compiler.a` |
| compiler backfill | `simple_compiler_backfill.lib` | `libsimple_compiler_backfill.a` |
| native aggregate | `simple_native_all.lib` | `libsimple_native_all.a` |

The defect applies to any raw configured MSVC `.lib`, but the fallback collision
is directly observable with `simple_compiler.lib`. No provider archive census,
selection rule, or support-library closure needs to change.

## Fresh-cycle next steps

1. Start from the post-provider-hardening head and keep this as a separate fix.
2. Add the normalization helper and the final-assembly regression described
   above; avoid altering provider selection or archive discovery.
3. Run the focused linker spec, then the normal compiler/core verification gates
   once in that fresh cycle, respecting the three-cycle cap.
4. Record Windows-host evidence if available; otherwise report that limitation
   without weakening the deterministic assembly test.

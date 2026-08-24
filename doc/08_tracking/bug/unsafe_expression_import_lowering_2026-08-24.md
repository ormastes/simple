# Unsafe expression import lowering resolves `unsafe` as a function

**Status:** Seed parser/HIR fix implemented and focused-tested; deployed
imported-module execution remains pending
**Observed:** 2026-08-24
**Area:** frontend/import lowering and lexical unsafe expressions

## Reproduction

An imported module containing:

```simple
val value = unsafe(capabilities: [ffi]):
    rt_env_get("KEY")
```

is accepted by source-only tooling, but executing a caller that imports and
invokes the containing function fails with:

```text
semantic: function `unsafe` not found
```

The statement/block form parses and executes:

```simple
var value = ""
unsafe(capabilities: [ffi]):
    value = rt_env_get("KEY")
```

## Required resolution

Lower expression-form unsafe through the same lexical capability HIR node as
the block form. It must preserve the inner expression type and value, reject
missing capabilities identically in every compiler stage, and introduce no
closure, allocation, dynamic dispatch, or runtime wrapper. Add an executed
imported-module fixture; source-shape acceptance alone is insufficient.

## 2026-08-24 TLS transcript reproduction

`src/os/tls13/transcript.spl` now uses value-bound lexical unsafe blocks for
the hosted SHA-256 accelerator. The focused `_finished_probe_spec.spl` reaches
the imported module and fails two transcript-dependent examples with the same
`semantic: function unsafe not found` diagnostic; the unrelated finished-key
example passes. This confirms the defect on a security-critical imported
module rather than only a synthetic environment-read reproducer.

The source is intentionally not rewritten to an extra helper-call workaround:
lexical unsafe must lower as a zero-runtime-cost HIR marker. Fixing the compiler
remains required for authoritative execution of the hardened transcript path.

## 2026-08-24 seed parser resolution

The Rust seed parser now recognizes a colon-terminated `unsafe(...)` or
`danger(...)` header from primary-expression position, using the same
`Expr::UnsafeBlock` node as statement position. It first scans to the matching
`)` and requires the following `:`, so an ordinary expression such as
`unsafe(1)` remains an ordinary call. The shared parser consumes capability
metadata without constructing a discarded fake call expression.

Focused parser evidence passes for both the value-bound block and the ordinary
call disambiguation. Focused HIR evidence also passes and proves that the
value-bound block remains `HirExprKind::UnsafeBlock` with its `i64` tail type.
This is a parser/HIR-only change: it adds no runtime wrapper, closure,
allocation, copy, or dispatch. Rebuilding/deploying the seed and rerunning the
imported TLS fixture remain separate admission evidence.

## 2026-08-24 rebuilt-seed result

A clean `cargo build -p simple-driver --bin simple` rebuilt the seed from the
parser/HIR fix, but an imported `std.io_runtime` function containing a
value-bound unsafe block still fails in executable compiler paths:

```text
[CODEGEN BODY] Function 'env_get' body compilation failed:
GlobalLoad: unresolved identifier 'ffi'
...
error[E1002]: function `unsafe` not found
```

The JIT failure proves the capability list is still lowered as ordinary
expression data in at least one imported-module route; the interpreter
fallback independently preserves the original call-to-`unsafe` failure. The
focused direct parser/HIR tests therefore cover less than the production
import/JIT/fallback path and are not sufficient admission evidence.

Required next evidence is an imported module compiled through both JIT and
interpreter fallback, with the unsafe block tail value observed and `ffi`
absent from generated global loads. Until that passes, safe-owner migrations
using this expression form must remain unpushed or be considered blocked by
the compiler defect; helper extraction is not an acceptable language fix.

## 2026-08-24 codegen gap localized (independent lane)

The rebuilt-seed result above is reproduced verbatim on `origin/main`
(`045e38290f0`) with the deployed seed, and the surviving gap is localized:

```text
$ ./bin/simple native-build <any-fixture>.spl -o out.bin ; echo NB_RC=$?
[CODEGEN BODY] Function 'env_get' body compilation failed: GlobalLoad: unresolved identifier 'ffi' (not a global, function, const-data name, or import)
[INFO] JIT compilation failed, falling back to interpreter: ... 4 function body/bodies failed to compile: [env_get, env_get_opt, getpid, time_now_unix_micros]
error[E1002]: function `unsafe` not found
NB_RC=1
```

Localization: `grep -rn UnsafeBlock src/compiler_rust/compiler/src/codegen/`
returns **zero lines**. The parser/HIR fix constructs `Expr::UnsafeBlock` /
`HirExprKind::UnsafeBlock`, but the seed codegen has no case for that node, so
it degrades into generic call/global lowering — hence `unresolved identifier
'ffi'` (the capability list read as an identifier expression) and
`function 'unsafe' not found`. The fix must add codegen handling, not more
parser/HIR work.

Blast radius, measured: a control fixture containing **no** `unsafe` at all
fails identically, because the failure comes entirely from imported
`src/lib/nogc_sync_mut/io_runtime.spl:280` (`env_get`), which is verbatim this
defect's shape. So **every** `native-build` on `origin/main` is blocked by this
defect, not only programs that themselves use `unsafe`.

Not this defect: the Stage 3 self-host vanish point
(`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:149`) uses the
**statement/block** form, not the expression form, so the hypothesis that
Defect A and this defect are the same bug is refuted at the syntactic level.
Whether the block form also mis-lowers under native codegen is UNMEASURED:
`SIMPLE_ALLOW_STUB_FALLBACK=1` does not produce a binary here — the worker
wrapper dies with `failed to spawn process 'bin/simple'` (`RC=255`) for all
fixtures including the control.

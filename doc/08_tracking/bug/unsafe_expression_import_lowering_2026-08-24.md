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

## 2026-08-24 RESOLVED — the codegen localization above is WRONG; defect was a stale binary

**The "codegen gap" section above is retracted.** It is a false localization and
the next lane should not chase it.

`grep -rn UnsafeBlock src/compiler_rust/compiler/src/codegen/` returning zero
lines is the **correct and intended** state, not a defect. `unsafe` is a
capability assertion, and the capability list is compile-time metadata:

- HIR keeps the node so the safety pass can see it —
  `hir/analysis/unsafe_ffi_checker.rs:156`, whose own header comment (`:4`) says
  it "runs before MIR erases `UnsafeBlock`".
- **MIR then erases it** — `mir/lower/lowering_expr.rs:234`:
  `HirExprKind::UnsafeBlock(stmts) => self.lower_block_expr(stmts)`.

Codegen consumes MIR, so it never sees `UnsafeBlock` **by design**. There was no
codegen case to add, and none was added.

### What was actually wrong

The measurement that produced the codegen hypothesis used a **stale deployed
seed binary** built before the parser fix `d2d0bec2e40` ("fix(parser): retain
value-bound unsafe blocks"). That fix landed 2026-08-24 17:21:44 UTC; the tip it
was measured against (`045e38290f0`) is 17:55:50 UTC — only 34 minutes later, so
the deployed binary predated it. The source was already correct end to end
(parser -> HIR -> MIR -> codegen); only the binary was old.

Both reported signatures are producible **only** from the pre-fix AST shape (a
call to a function named `unsafe` with `ffi` as an argument), which is why the
interpreter — which handles `UnsafeBlock` correctly at
`interpreter/expr/control.rs:310` — also reported `function 'unsafe' not found`:
it never received an `UnsafeBlock` at all. Both backends failing identically
implicated the parse, not codegen.

### Evidence — freshly built seed from UNMODIFIED origin/main source

`cargo build --release --bin simple` (BUILD_RC=0), binary size 60513440,
mtime 2026-08-24 18:12. No source change of any kind:

```text
unsafe-expression-form: OK (NB_RC=0, RUN_RC=0, output [42])
unsafe-statement-form:  OK (NB_RC=0, RUN_RC=0, output [42])
ordinary-call-disambig: OK (NB_RC=0, RUN_RC=0, output [42])
```

**Both forms work** — answering the open question in "Required resolution": the
expression form and the statement form both native-build AND execute, with the
unsafe block's tail value (42) surviving MIR erasure intact. On the
`io_runtime`-importing control fixture all three old signatures now count
**zero**: `function 'unsafe' not found` = 0, `unresolved identifier 'ffi'` = 0,
`env_get ... body compilation failed` = 0.

### Blast-radius claim also retracted

"Every `native-build` on origin/main is blocked by this defect" is false. With a
current binary, standalone native-builds succeed. The `io_runtime`-importing
control fixture still fails, but on an **unrelated** defect with no connection to
`unsafe`:

```text
error: 37:1: borrow of `local(13)` may still be active at return
       |||RELATED:6:1:borrow created here
       |||HELP:ensure borrow ends before returning
```

plus `[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime
dependency=Option/Result`. That borrow-checker/import defect is now the
remaining blocker for importing `io_runtime` and needs its own record; it is NOT
this bug.

### Regression gate

`scripts/check/check-unsafe-block-native-build.shs` — behavioural (native-builds
and RUNS both forms plus an ordinary-call disambiguation fixture), not a source
grep, precisely because the erasure above makes a grep meaningless. Selftest
first and fatal (5 fixtures); verdict last on stdout; PASS/FAIL/ERROR = 0/1/2;
0 builds executed or a missing seed binary is ERROR, never a pass.

Mutation-tested against the real mechanism — reverting `d2d0bec2e40`'s two
parser files and rebuilding turns it RED with the exact reported signature:

```text
MUTGATE_RC=1
FAIL — 3 case(s) checked, offender(s): unsafe-expression-form(unsafe-not-found)
       unsafe-statement-form(unsafe-not-found)
       ordinary-call-disambig(unsafe-not-found)
```

This doubles as an independent reproduction of the reported failure from the
pre-fix parser, confirming the stale-binary diagnosis. Source was restored and
`git status` verified clean before commit.

**Action for other lanes: rebuild your seed. No compiler change is needed for
`unsafe`.**

# Stage 3 self-host: 1,088 HIR `unresolved type` fatals across 538 files, including builtins

- **Filed:** 2026-08-31
- **Status:** OPEN — first observation; Stage 3 had not been reachable before today
- **Blocks:** Stage 3 self-host, therefore Stages 4 and 5
- **Platform:** aarch64-apple-darwin. **NOT shown to be macOS-specific.**
- **Reached via:** Stage 2 admission (`8cef6333ac8`) + planner-admission-v2 receipt
  (target `//bootstrap:stage3`, reason `verify-landed-compiler-fix`)

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage3
--backend=llvm --bootstrap-receipt=<path>` reaches Stage 3 and fails:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); Stage 4 unavailable
error: --stop-after-stage3 requires a successful Stage 3 compiler
```

Full stderr (816 KB) at
`build/bootstrap/stage3/<triple>/stage3-tmp/native-build-stderr-<pid>.log`.

## Measured scope

1,088 `[hir-fatal]` diagnostics across 538 distinct files. Most frequent
unresolved names:

| count | name |
|---|---|
| 162 | `HirBinOp` |
| 148 | `HirUnaryOp` |
| 126 | `HirAssignOp` |
| 115 | `Option` |
| 67 | `Dict` |
| 44 | `Result` |
| 32 | `TargetCapsKind` |

**`Option`, `Dict` and `Result` are language builtins.** Their appearing as
"unresolved type" is the load-bearing observation: this is not a missing import in
one module, it is builtin/prelude type registration failing on the Stage-3
self-host path. The compiler-internal enums (`HirBinOp`/`HirUnaryOp`/`HirAssignOp`)
are the same failure applied to types reached through re-export chains.

Companion diagnostic naming the mechanism:

```
[hir-callable-dep-origin-unresolved] owner=compiler.common.di dependency=Dict:
no declaration, re-export hop, or explicit import of this name in the owner
```

## Attribution — stated honestly

This is the FIRST time Stage 3 has been reachable in this work. Until Stage 2 was
admitted earlier today it failed at the admission gate, so nothing downstream ever
executed. That means:

- This failure is **not shown to be a regression** from the nine defects fixed to
  reach admission. It may be long-standing and simply never observed.
- It is equally **not shown to be pre-existing**. No baseline exists. Do not assert
  either direction without evidence.

A cheap discrimination, if needed: the nine fixes are all in codegen/lowering
(MIR, backend, one frontend desugar). This failure is in NAME RESOLUTION, a
different layer none of them touched. That is suggestive of pre-existing, not
proof.

## Difference from the Stage-2 fixture

Stage 2 admission compiles a 3-line fixture plus one imported module. Stage 3
compiles the ENTIRE compiler (538 files here). The defect needs a module graph of
real size, which is why no smaller repro surfaced during admission work.

## Next

Determine where builtin/prelude types (`Option`, `Dict`, `Result`) are registered
for a self-host compile and why that registration is absent or unreachable in
Stage 3. Fix that first: 115+67+44 = 226 of the 1,088 fatals are builtins, and the
re-export-hop failures may share the same root.

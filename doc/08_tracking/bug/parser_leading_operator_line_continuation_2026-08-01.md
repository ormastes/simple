# Leading-operator line continuation does not parse — breaks a landed frozen contract file

**Date:** 2026-08-01
**Status:** OPEN
**Severity:** HIGH — `src/lib/common/ui/gpu_web_capacity_manifest.spl`, a frozen
C0 contract already on `main`, currently fails to parse, so every module that
imports it is unbuildable
**Found by:** webrender_gpu_offload lane (wave-1 CPU reference), while writing
`src/lib/common/ui/draw_ir_v3_execution_route.spl`
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(the live `bin/simple` has no `lint`/`test` subcommand, so it could not be
cross-checked — see the open bootstrap/redeploy issue)

## Symptom

Continuing an expression onto the next line with the operator at the START of
the continuation line fails with a whole-file parse error and no location:

```
src/lib/common/ui/gpu_web_capacity_manifest.spl:1:0: error[PARSE001]: Source did not parse
```

## Minimal reproduction

Fails:

```simple
fn q1(a: text, b: text) -> text:
    return a
        + " reason=" + b
```

Also fails with `val`, with `var`, and with a plain reassignment:

```simple
    val line = a
        + " reason=" + b
```

```simple
    line = line
        + " tail"
```

Parses fine — the operator is TRAILING on the first line:

```simple
fn r2(a: text, b: text) -> text:
    return a +
        " reason=" + b
```

Also fine — no continuation at all:

```simple
    var line = a
    line = line + " reason=" + b
```

So the defect is specifically **leading-operator continuation**, independent of
`return` / `val` / `var` / reassignment. Multi-line call arguments, multi-line
`fn` signatures and multi-line struct literals are unaffected.

## Blast radius

`src/lib/common/ui/gpu_web_capacity_manifest.spl` (frozen C0 contract, landed)
uses the leading form at `gpu_web_capacity_breach_receipt`:

```simple
fn gpu_web_capacity_breach_receipt(breach: GpuWebCapacityBreach) -> text:
    return breach.bound
        + " requested=" + breach.requested.to_text()
```

Verified directly:

```
$ simple.pre-segv-fix-20260731 lint src/lib/common/ui/gpu_web_capacity_manifest.spl
src/lib/common/ui/gpu_web_capacity_manifest.spl:1:0: error[PARSE001]: Source did not parse
Found 1 error(s), 3 warning(s), 0 auto-fix(es) available
```

The file is a **frozen contract** (shared rule 1,
`doc/03_plan/platform/structural_compute/README.md`): it must not be edited
in place, so the fix belongs in the parser, not in the contract file. Until it
lands, the capacity manifest cannot be imported by any consumer, and
`test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl` cannot run.

`src/lib/common/ui/draw_ir_v3_execution_route.spl` therefore does NOT import
the capacity manifest; it constructs its capacity-overflow denial from a
command count instead, and carries an in-file boundary note pointing here.

## Why this is a real grammar gap, not a style preference

Leading-operator continuation is the form the repo's own landed code already
uses, it is what a formatter naturally produces for long concatenations, and
it is accepted by the seed compiler's own sources elsewhere. Silently
normalising every call site to the trailing form would hide a parser defect —
`.claude/rules` requires filing it instead.

## Next steps

1. Fix continuation handling in the self-hosted lexer/parser so a line
   beginning with a binary operator continues the previous logical line.
2. Add a regression spec covering `return` / `val` / `var` / reassignment for
   at least `+`, `-`, `and`, `or`.
3. Re-run `lint` on `src/lib/common/ui/gpu_web_capacity_manifest.spl` and on
   its spec; both should go clean with no edit to the frozen file.
4. Re-import `GpuWebCapacityVerdict` into
   `src/lib/common/ui/draw_ir_v3_execution_route.spl` and replace
   `draw_ir_v3_route_capacity_denial` with a verdict-taking form, so the
   breached bound name flows into the fallback receipt.

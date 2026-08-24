# A single-expression function body loses its tail return when it is the last declaration in the file

- **Filed:** 2026-08-24 (Lane P, slice A)
- **Status:** OPEN — characterised to a 2-line reproduce; fix not attempted (see below)
- **Severity:** high — silently breaks library-only modules. Real product code hits it:
  `src/compiler/00.common/bootstrap_low_memory_config.spl` (a whole module that is
  one `pub fn`) cannot be compiled at all.

## Symptom

```
[ERROR] MIR error: MIR lowering error: E-SFFI-016: missing return in non-unit function 'f'
error: in-process SMF compile: MIR lowering error: E-SFFI-016: missing return in non-unit function 'f'
```

raised at `src/compiler/50.mir/_MirLowering/function_lowering.spl:571`, in the
`else` arm where the tail-expression result optional (`result`) is `nil`. HIR
lowering reports `post-lowering count=0` first — the loss happens before MIR,
which only observes the missing tail value.

## Minimal reproduce (2 lines, whole file)

`test/01_unit/compiler/10.frontend/fixtures/tail_expr_last_decl.spl`
```
pub fn f(a: text) -> i64:
    1
```
`simple compile <file> --format=smf -o out.smf` → E-SFFI-016. Verified against
`build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
(132945096 bytes, 2026-08-24 02:50).

## Trigger conditions — BOTH are required

Measured by bisecting the fixture; each row is a whole file.

| file content | tail return lost? |
|---|---|
| `fn f(a: text) -> i64:` / `    1` | **YES** |
| same, but `-> bool` / `a == "1"` | **YES** |
| same, with `pub` removed | **YES** |
| same, with or without a trailing newline | **YES** (not a newline-at-EOF issue) |
| body of TWO statements, tail is a bare name (`val r = ...` / `r`) | no |
| single-statement body, followed by ANY other declaration (`fn main()` or `fn g()`) | no |
| single-statement body with an explicit `return` | no |

So: **a value-returning function whose body is exactly one bare expression
statement, and which is the last declaration in the file.** Adding a second
statement to the body, or any declaration after it, makes it compile. An
explicit `return` is the workaround — and per the house rule against silently
normalising a workaround, that workaround must not be applied to product code in
place of this fix.

## Why it is filed, not fixed

The compiler under test is a prebuilt stage2 binary; a source edit to the parser
or HIR lowering cannot be exercised by it, so no fails-before/passes-after
evidence could be produced in this lane. The fixture above is the deliverable so
the fix lands against a failing test.

## Where detection belongs

**Compiler.** The error already exists and is precise (E-SFFI-016) — the defect
is upstream of it, in whatever drops the single tail expression. Lint is the
wrong venue: this is not a pattern in the source, the source is correct; and a
`scripts/check/` gate cannot see it. The cheap durable detection is simply that
library-only modules get compiled at all — which is what produced this finding.

## Related occurrences found in the same census

`src/compiler/00.common/di_test_tmp.spl` fails the same way
(`missing return in non-unit function 'test_fn'`).

# Native binaries silently drop an interpolated `print` — root-caused to the desugar layer

- **Status:** FIXED (frontend desugar) — see "Fix" below. Two sibling defects
  found by the family sweep remain OPEN and are recorded at the bottom.
- **Filed:** 2026-08-10 (original), root-caused and fixed 2026-08-10.
- **Severity:** high. *Fail-open* silent data loss: the build succeeds, the
  binary runs, exit code is 0, and the expected output never appears. Strictly
  worse than a loud build failure, and it invalidates any native-lane check
  whose oracle is "it built".

## Correction to the original filing

The original report said the trigger was *interpolation containing a call*
(`print "x={f()}"`). That attribution is wrong — the call is a confound. The
actual trigger is narrower and simpler:

> **An interpolated string literal written DIRECTLY as an argument to `print`.**

No call is required. `print "B={x}"` with `x` a plain local drops just as
completely. Binding the same literal to a `val` first makes it work.

## Measured form x lane table

Binary measured: the deployed seed
`bin/release/x86_64-unknown-linux-gnu/simple`, size 29577536, mtime
`2026-08-09 04:50:31 UTC`. Native rows were built in a **pinned pristine tree**
extracted from origin `9199d13a7dd` into `/dev/shm/q32tree`, because the shared
working copy carries ~14 files of other sessions' in-flight compiler edits and
cannot be measured against.

| form | source | interpreter | JIT | native |
|---|---|---|---|---|
| plain literal (POSITIVE CONTROL) | `print "A-LIT"` | `A-LIT` | `A-LIT` | `A-LIT` |
| interpolation, **no call** | `print "B={x}"` | `B=7` | `B=7` | **(nothing), rc=0** |
| call, no interpolation | `val v = f(); print v` | `C` `5` | `C` `5` | `C5` |
| interpolation + call | `print "D={f()}"` | `D=5` | `D=5` | **(nothing), rc=0** |
| interpolation + call returning text | `print "E={g()}"` | `E=gg` | `E=gg` | **(nothing), rc=0** |
| concat instead of interpolation | `print "F=" + f().to_text()` | `F=5` | `F=5` | `F=5` |

The single most informative program is `m_probe.spl`, which puts every form in
one `main`:

```
print "START"                 -> START        emitted
val s = "B={x}"; print s      -> B=7          emitted   <-- val-bound WORKS
print "C={x}"                 -> (dropped)              <-- direct arg DROPPED
print "{x}"                   -> (dropped)              <-- direct arg DROPPED
print "END"                   -> END          emitted
```

native stdout: `STARTB=7AFTER-BOUNDAFTER-INLINEEND`
interpreter stdout: the same tokens, one per line.

So the drop is **per-statement**, not a crash: execution continues normally and
the surrounding prints are unaffected. That is exactly the shape that reads as
success to any probe scoring `native-build` exit status.

## Root cause — the desugar layer, not MIR and not the backend

Disassembling the emitted `__simple_main` of the failing binary was decisive:

```
bin_a_lit  (works)      lea <"A-LIT">; call rt_interp_cstr; call rt_print
bin_b_interp_var (bad)  lea <"">;      call rt_interp_cstr; call rt_interp_cstr; call rt_print
```

The failing binary loads a **zero-length** string constant (verified by reading
the bytes at the `lea` target), contains no `rt_strcat` symbol at all, and has
no `B=` string anywhere in `.rodata`. The *extra* `rt_interp_cstr` proves the
interpolation lowering did run — it is `bootstrap_coerce_to_raw_str` on the
seg-0 const — so this is not the "print called with zero args" branch.

Instrumenting the pristine tree confirmed it directly:

```
[Q32] lower_bootstrap_print_call rt=rt_print nargs=1
[Q32] lower_string_interpolation value='' interps=1
```

`lower_string_interpolation` is handed **an empty template text with one
interpolation**. From there the loss is mechanical:
`split_interpolation_segments("")` returns `[""]`, so
`slot_count = min(interps.len(), segments.len() - 1) = min(1, 0) = 0` — the
guard intended to protect against a segment/interp mismatch instead discards the
only interpolation, and the literal text was already gone. The lowering emits a
bare `""` const. **MIR is behaving correctly given its input**; the input is
already destroyed.

The text is destroyed here:

- `src/compiler/10.frontend/core/_AstExpr/accessors.spl:16`
  ```
  fn expr_interpolated_string(parts: [i64], span_id: i64) -> i64:
      val idx = expr_alloc(EXPR_INTERPOLATED_STRING, span_id)
      expr_owner_args_set(idx, parts)      # <- args only; str slot never set
      idx
  ```
  Contrast its sibling `expr_promote_interpolated_string` two lines below, which
  *does* `expr_owner_str_set(idx, value)`.

- Its only two callers are both in the **desugar** layer:
  `src/compiler/10.frontend/desugar/placeholder_lambda.spl:654` and `:795`
  (`replace_placeholders` and `replace_placeholders_fixed_slot`). Both rebuild
  an interpolated-string node from new part-exprs and return
  `expr_interpolated_string(new_parts, 0)` — dropping `expr_s_val[eid]`, the
  verbatim template text of the node they are rebuilding.

- The flat->rich bridge then reads that empty slot:
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:874`
  `ExprKind.StringLit(expr_get_str(idx), interpolations)`.

This also explains the direct-argument-versus-`val`-bound asymmetry: the
placeholder-lambda desugar walks **call arguments** (it was extended to the
driver/native-build parse path in `b9ed8aa45f2`), so a literal in argument
position is rebuilt and stripped, while the same literal bound to a `val` never
enters that rewrite and keeps its text through
`flat_bridge_build_string_interps`.

The prior stream's warning generalises: a `50.mir` symptom had a `10.frontend`
cause for the second time in two days.

## Fix

`expr_interpolated_string_with_text(value, parts, span_id)` added to
`accessors.spl`, and both desugar rebuild sites switched to it, passing
`expr_s_val[eid]`. The bare constructor is left in place for genuinely new
nodes, with a doc comment stating the rule.

**Revert-proof.** Both halves are a real native build of the SAME fixture
(`m_probe.spl`) with the SAME seed binary, differing only by this patch:

| tree | native stdout |
|---|---|
| pristine origin `9199d13a7dd`, no fix | `STARTB=7AFTER-BOUNDAFTER-INLINEEND` |
| same tree + this fix | `STARTB=7AFTER-BOUNDC=7AFTER-INLINE7END` |

The two direct-argument interpolations (`C=7` and the bare `7`) are absent
before and present after. Nothing else in the output changes, so the patch is
not masking the difference by altering unrelated lowering. (The missing
newlines in both rows are sibling defect 1 below, which this change does not
touch.)

## The check, and why its oracle is stdout

`scripts/check/check-native-print-stdout-oracle.shs`. It builds each fixture,
**runs the binary**, and compares its stdout byte-for-byte against the
interpreter's. A successful build with empty output is a FAIL. It carries:

- a **positive control** (`pc_plain`) so a generally broken native lane cannot
  masquerade as a pass on the interesting rows, and
- a **negative control** (`nc_mismatch`) whose expectation is deliberately
  wrong. If that row ever *matches*, the comparison is not running and the
  check reports ERROR rather than PASS. A run that compares zero fixtures is an
  ERROR, never a pass.

## Siblings found by the family sweep — both OPEN

1. **Native `print` omits the trailing newline.** MIR maps `print` to
   `rt_print` (`runtime_native.c:2008`, no newline) rather than `rt_println`
   (`:2012`), at
   `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:4258`.
   Every native binary therefore runs its output together —
   `STARTB=7...END` above — while the interpreter and JIT emit one line per
   `print`. This affects *every* native program, not just interpolated ones.
   NOT fixed in the same commit deliberately: three concurrent sessions are
   mid-bootstrap and a global native output-shape change would land under
   them. It needs its own change with the bootstrap lanes re-run.

2. **JIT reads a class field default as one less than the interpreter.**
   `class C: var n: i64 = 4` with `me get(self) -> i64: self.n` prints `K=4`
   under the interpreter and `K=3` under JIT. Unrelated to interpolation;
   surfaced by the family fixtures. Needs its own filing and bisection.

Also noted: `println` is a hard runtime error under the interpreter
("deprecated, use print") but silently accepted and executed by JIT. The two
lanes disagree about whether the program is even legal.

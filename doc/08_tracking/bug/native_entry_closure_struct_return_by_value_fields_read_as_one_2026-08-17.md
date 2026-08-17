# A struct RETURNED BY VALUE reads every field as `1` under native-build `--entry-closure`

Date: 2026-08-17
Status: OPEN — root cause isolated, codegen fix not attempted
Owner: native codegen / aggregate return ABI
Severity: HIGH — silent wrong values, no diagnostic, on the exact Stage-2/3 path

## The minimal reproduction (same module, no imports)

```simple
struct W3:
    ok: bool
    length: i64
    tag: i64

fn make(n: i64) -> W3:
    W3(ok: n > 0, length: n, tag: 77)

fn main():
    val inline_v = W3(ok: true, length: 3, tag: 77)
    print("inline len={inline_v.length} tag={inline_v.tag}")
    val ret_v = make(3)
    print("returned len={ret_v.length} tag={ret_v.tag}")
```

```
SIMPLE_BOOTSTRAP=1 bin/simple native-build --source <dir> \
    --entry <dir>/user3.spl --entry-closure -o user3.bin
./user3.bin
```

Observed, verbatim:

```
inline len=3 tag=77returned len=1 tag=1
```

The locally-constructed value is correct. The value RETURNED BY VALUE from a
function has every field read back as `1`. There is no error, no warning, and
no crash — the program exits 0 with wrong answers.

Interpreted execution of the same source is correct (`bin/simple run` prints
`true 3` for the two-field variant), so this is a native-codegen aggregate
return defect, not a frontend one.

## Scope established by controls

| shape | result |
|---|---|
| struct built inline in the same function | CORRECT |
| struct returned from a fn in the SAME module | **WRONG (all fields `1`)** |
| struct returned from a fn in ANOTHER module | **WRONG (all fields `1`)** |
| same source under `bin/simple run` (interpreted) | CORRECT |

Cross-module is therefore NOT the discriminator — return-by-value is. The
earlier framing in
`stage2_cross_module_codec_result_field_inference_2026-08-14.md` (a
cross-module inference problem) is a symptom of this.

## Why this matters for Stage 2 / Stage 3

The self-hosted compiler returns aggregates by value constantly. Two live
consequences already filed under other names:

- `stage2_cross_module_codec_result_field_inference_2026-08-14.md` — `.ok` on
  `encode_provider_query_result_v1(...)`'s returned struct. Its "explicitly
  annotate the result" workaround does not fix the value, only the diagnostic.
- The stage-3 probe in
  `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:730-732`
  prints `[hir-field-type] struct=CompiledUnit field=entry_point
  actual=2589120870` and the SAME value for `struct=BackendError field=span`.
  That probe calls `rt_enum_discriminant` on `self.lower_field(sf)`'s
  RETURNED-BY-VALUE `HirField`. `2589120870` is `0x9A52D966` — a 32-bit slice
  of a pointer, not one of `HirTypeKind`'s ~20 variants
  (`src/compiler/20.hir/hir_types.spl:830`). One garbage value repeated across
  two unrelated structs is a fixed wrong slot, exactly the signature above.
  That garbage `HirTypeKind` then drives a `match`, which is a credible
  precursor for `stage3_selfhost_exit_139_2026-08-14.md` /
  `stage3_post_file_copy_exit139_2026-08-14.md` (exit 139 = SIGSEGV).

This is the same family the exit-139 doc already names ("under the Stage 2 ABI
that aggregate transport corrupts the callee"), but reproduced here in eight
lines instead of a whole-compiler build.

## Not gateable by an SSpec today

Specs execute interpreted, where the defect does not reproduce. A regression
gate for this must be a native-build fixture (build the reproducer above, run
the binary, assert `len=3 tag=77` on BOTH lines). Do not write an SSpec that
"passes" here — it would be vacuous.

## Also noted

The `[hir-field-type]` probe cited above is UNGATED and hard-codes two
struct/field names. Per `.claude/rules/code-style.md` it should become a
level-gated log rather than an always-on `eprint`; it was left in place
deliberately because a live Stage-3 lane is currently reading its output.

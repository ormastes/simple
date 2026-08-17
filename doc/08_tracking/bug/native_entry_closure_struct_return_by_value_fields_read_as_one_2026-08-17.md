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

## Reproduce-first evidence

`test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl`
was written BEFORE any fix and run against the current tree. It is RED on
exactly the subprocess example and green on the two interpreter guards, which
is the intended shape — the interpreter is not affected:

```
  ✗ agrees between a locally built struct and a returned one after native-build
    expected subject to be truthy, got false
3 examples, 1 failure
SPEC FILE VERDICT: ... declared>=3 executed=3 passed=2 failed=1 dropped=0
Results: 3 total, 2 passed, 1 failed
```

The class sweep is
`test/01_unit/compiler/codegen/native_aggregate_return_transport_class_spec.spl`
(all-i64 struct, forwarded return, nested struct, tuple — one build).

Both specs stay RED until the aggregate-return transport is fixed. Per
`.claude/rules/testing.md` they are left red deliberately rather than softened;
the unblock condition is a codegen fix on the `native-build --entry-closure`
aggregate return path.

## Not fixed here

No codegen change was attempted. The defect is in the native return-value ABI
and needs an owner who can change lowering and re-verify by rebuilding — which
this lane could not do without contending with the live Stage-3 build.

## Spec-authoring note

The first draft embedded the fixture with `{inline_v.length}` interpolation.
That is resolved by the SPEC's lexer, not the fixture's: the file died with
`semantic: variable \`inline_v\` not found` and `executed=0 reason=zero-examples`
before any example ran. Embedded fixture sources must avoid `{...}` entirely.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

LIVE by content — and NOT ours to fix: `hir/lower/expr/access.rs` is a lane explicitly claimed by another concurrent session. The guessed field index is still there: src/compiler_rust/compiler/src/hir/lower/expr/access.rs:286-291, `self.get_field_info(recv_hir.ty, field).ok().map(|(field_index,_)| field_index).or_else(|| self.try_resolve_global_field_index_by_name(...)).unwrap_or(0)` — a failed resolution still silently yields field 0, which is the documented 'every field reads as field 0' mechanism. Handed to the access.rs owner unmodified.

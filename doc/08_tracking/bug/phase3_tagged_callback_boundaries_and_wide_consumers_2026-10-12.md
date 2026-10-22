# Tagged callback lowering lost concrete expression types; wide boxes lost ordinary consumers

Date: 2026-10-12. Status: source repairs committed; native qualification pending.

The unannotated helper `fn invoke_word(callback, value): callback(value)` returned
zero while direct and local calls returned eight. The callback repair retained
the expression tail and introduced a proven tagged callable ABI. Its first
bootstrap attempt exposed two concrete type-boundary mistakes. The associated
Simple runtime constructor change also exposed ordinary consumers that had
assumed every signed integer was an inline tag.

## Observed compiler failures

Frozen attempt5's `build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`
reports these errors among four failed files:

```text
MirLowering.lower_binary_expr: struct 'ANY' field 'span'
MirLowering.any_callable_lambda_body_supported: struct 'ANY' field 'expr'
```

`lower_binary_expr` declares `expr_value: HirExpr`. Introduced code instead used
the undeclared identifier `expr` in both fatal diagnostics and result metadata:

```simple
self.error_fatal("tagged Any addition requires the admitted core-c-bootstrap runtime owner", Some(expr.span))
self.remember_local_hir_type(added.id, HirType(kind: HirTypeKind.Any, span: expr.span), 0, 0)
```

The repair uses the actual `expr_value.span` in all three introduced locations.
Diagnostic text and fatality remain authoritative.

The interpolation scan used this inferred loop boundary:

```simple
if val interpolation_items = interps:
    for item in interpolation_items:
        if not self.any_callable_lambda_body_supported(item.expr): return false
```

`HirExprKind.StringLit` declares `[HirInterpolation]?`, and
`HirInterpolation.expr` declares `HirExpr`. The repair publishes
`typed_items: [HirInterpolation]` and indexes an explicit
`item: HirInterpolation`; the recursive expression check remains intact.

Commit `d74720b829c1f0fc38905c888fef0a9244f07ef5` fixes both boundaries.
`test/01_unit/compiler/mir/inferred_callback_word_abi_spec.spl` includes actual
frontend/HIR/MIR cases for contextual tagged addition and interpolated strings.
The suite has 18 authored cases. They have not been executed for this repair.

## Ordinary signed-wide regression and repair

Simple's default `rt_value_int` now preserves signed values outside the 61-bit
inline range as owned `INT1` leaves. These leaves use the numeric membership
registry before any header projection. The specialized tagged addition path
handled them, but ordinary text, legacy addition and array helpers did not:

- `rt_to_string` returned empty text for `rt_value_int(INT64_MIN/MAX)`.
- Simple legacy `rt_any_add` selected text concatenation for every heap operand.
- Array query local integer helpers accepted only tag zero and projected by
  `>> 3`; query equality compared box addresses.

Commit `0611bdc98ab272ebb2052fa9bd957762cb80d2b5` fixes ordinary `rt_to_string`
and its `rt_value_to_string` delegate. Registered strings are identified before
header access, owned signed boxes use `rt_raw_i64_to_string`, and owned UInt
boxes use full-width decimal extraction. Bool, nil and string identity remain.

Commit `e2799a1ccc7bcf30d4468f249d34392030d2e733` repairs the ordinary numeric
consumers. Simple legacy addition dispatches owned signed-wide pairs to its
genuine tagged numeric implementation. The C namesake retains its raw-i64 ABI.
Array query classification, projection and result construction use the numeric
owner; sum/min/max/sorting now consume full signed payloads. Lookup, last lookup,
count and uniqueness compare proven signed payloads, preserving word identity
for other values. Signed and UInt zero truth checks establish ownership first.

## Actual runtime checks and required owner closure

`test/01_unit/runtime/simple_tagged_add_contract_test.c` contains **61 numbered
positive guards and five negative modes**. It checks default wide constructors,
both general text conversion entry points, ordinary signed-wide addition,
fresh equal boxes in real arrays, sum wrapping, extrema, uniqueness and sort
order. Earlier guards cover low mantissa bits, actual Float transient scope
reclamation, surviving Int/UInt leaves, early reclaim followed by scope end,
registry rebuilding and repeated numeric shutdown.

Use actual admitted `--no-mangle` Simple objects for **core_values, core_string,
core_memory and core_array_query**, plus their real core_array/core_array_ops,
dict/enum/closure and selected host-primitive closure. Resolve the lifecycle
hooks and transient APIs from those Simple objects. C runtime_native, C array
providers, Rust value owners and mocked transient functions do not qualify this
contract. The test declares actual Simple integer-handle array signatures and
integer-returning lifecycle hooks rather than core-C header variants.

The existing archive construction route in
`scripts/check/check-simple-core-runtime-smoke.shs` builds actual source entries
with `native-build --entry-closure --no-mangle --emit-archive`. Its final archive
excludes entry-specific `_init_all.o` aggregators because ordinary Simple
executables generate their own initializer. A C entry must arrange the real
selected module initialization too: `core_memory`'s scope counter starts at one.
Do not manufacture initial state in the fixture to conceal an omitted initializer.

Before linking, retain each selected source/object hash, compiler build receipt
and `llvm-nm --defined-only` output, including the **core_array_query member**.
The selected Simple exports must own `rt_tagged_add`, numeric constructors and
projections, `numeric_box_kind`, Float validity/reclaim, scope begin/end,
runtime init/shutdown and the array query symbols used by the contract. Resolve
their host dependencies using the actual selected provider receipt. A source
filename or matching header alone does not establish object ownership.

The owner-qualified native launcher must compile the C entry against that
recorded closure, retain its exact compiler/link argv and link map, then retain
the provider export census and input hashes again after linking. Check the map
for the same Simple member owners; no C array/runtime substitute may satisfy a
missing export. On Windows use the selected MSVC-target Clang and its admitted
SDK/host library inputs; do not guess a platform archive or use the Linux/Darwin
core-C capsule builder as Windows evidence.

Run the produced executable and check raw results with this strict protocol:

```python
import subprocess

positive = subprocess.run([actual_executable], capture_output=True)
assert positive.returncode == 0  # all 61 positive guards reached
numeric_error = b"panic: rt_tagged_add: operands require signed integer, float or text\n"
float_text_error = b"panic: rt_tagged_add: Simple text+Float formatting is unsupported\n"
for mode in ("nil", "uint", "unregistered", "text-unregistered", "text-float"):
    result = subprocess.run([actual_executable, mode], capture_output=True)
    expected = float_text_error if mode == "text-float" else numeric_error
    assert result.returncode == 1
    assert result.stderr == expected
```

Return 30/31, a crash, a partial diagnostic or a different exit code fails the
negative check. Retain the executable hash and actual terminal receipts.

## Validation and closure criteria

Static diff checks passed for the focused commits. No compiler, native C build,
runtime executable or unit-test job ran in the repair checkout. Frozen attempt5
sources and caches remain preserved. The required runtime source identities must
rebuild and pass their existing admission checks normally.

Close these regressions only after canonical compilation of both failing compiler
modules, the real callback boundary fixture, and the owner-qualified 61-guard
Simple runtime contract pass with all five exact negative receipts. Keep the
regression cases and the concrete typed boundaries; no diagnostic suppression,
fixture rewrite or baseline exception replaces that evidence.

Simple Float text formatting and broad Float/UInt/aggregate query semantics
remain separately unqualified. Pure-core callback admission remains closed.
Presence-based three-lane CI success does not establish those capabilities.

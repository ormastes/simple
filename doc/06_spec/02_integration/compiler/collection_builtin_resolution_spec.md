# collection_builtin_resolution_spec

> Production frontend-to-HIR evidence for collection planner builtin identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# collection_builtin_resolution_spec

Production frontend-to-HIR evidence for collection planner builtin identity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/collection_builtin_resolution_spec.spl` |
| Updated | 2026-09-29 |
| Generator | `simple spipe-docgen` (Simple) |

Production frontend-to-HIR evidence for collection planner builtin identity.
This prerequisite remains open until typed Array operations carry an admitted
identity distinct from same-spelled user methods. No rewrite is tested here.

## Scenarios

### production typed Array collection identity

#### should retain a resolved operation identity for a typed Array map

- Parse and lower a source program with an explicitly typed Array
- Resolve typed calls through the existing production resolver owner
   - Expected: errors.len() equals `0`
   - Expected: if typed_array: "array" else: "untyped" equals `array`
   - Expected: identity equals `builtin-array-map`
   - Expected: observed equals `1`
- Round trip the admitted identity through the authoritative HIR codec
   - Expected: hir_module_encode(decoded.unwrap()) equals `encoded`
- Reject older codec identities instead of reusing incompatible cache entries
- Lower the canonical builtin call through the existing Array MIR loop
   - Expected: mir_lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse and lower a source program with an explicitly typed Array")
val source = "fn main():\n    val items: [i64] = [1, 2]\n    val mapped = items.map(\\item: item + 1)\n"
val parsed = parse_full_frontend(source, "collection_builtin_identity", "collection_builtin_identity", Logger(level: 0))
var lowering = HirLowering.with_filename("collection_builtin_identity.spl")
val hir = lowering.lower_module(parsed)
step("Resolve typed calls through the existing production resolver owner")
val (resolved, errors) = resolve_methods_quiet(hir)
expect(errors.len()).to_equal(0)
var observed = 0
for function in resolved.functions.values():
    if function.name == "main":
        for statement in function.body.stmts:
            match statement.kind:
                case HirStmtKind.Let(_, _, initializer):
                    if initializer != nil:
                        match initializer.kind:
                            case HirExprKind.MethodCall(receiver, method, _, resolution):
                                if method == "map":
                                    observed = observed + 1
                                    var typed_array = false
                                    if receiver.type_ != nil:
                                        match receiver.type_.kind:
                                            case HirTypeKind.Array(_, _): typed_array = true
                                            case _: ()
                                    expect(if typed_array: "array" else: "untyped").to_equal("array")
                                    var identity = "unresolved-or-user-method"
                                    match resolution:
                                        case MethodResolution.BuiltinCollection(CollectionBuiltinOperation.ArrayMap):
                                            identity = "builtin-array-map"
                                        case _: ()
                                    expect(identity).to_equal("builtin-array-map")
                            case _: ()
                case _: ()
expect(observed).to_equal(1)
step("Round trip the admitted identity through the authoritative HIR codec")
val encoded = hir_module_encode(resolved)
expect(encoded.starts_with(hir_codec_header())).to_be(true)
val decoded = hir_module_decode(encoded)
expect(decoded != nil).to_be(true)
expect(hir_module_encode(decoded.unwrap())).to_equal(encoded)
step("Reject older codec identities instead of reusing incompatible cache entries")
expect(hir_module_decode(encoded.replace(hir_codec_header(), "spl-hircodec-v2 flatpool-v1")) == nil).to_be(true)
expect(hir_canonical_codec_header()).to_start_with("spl-hircodec-canonical-v2 ")
step("Lower the canonical builtin call through the existing Array MIR loop")
var mir_lowering = MirLowering.new(resolved.symbols)
val mir = mir_lowering.lower_module(resolved)
expect(mir_lowering.errors.len()).to_equal(0)
val emitted = serialize_mir_module(mir)
expect(emitted).to_contain("rt_array_get")
expect(emitted).to_contain("rt_array_push")
```

</details>

#### should keep a same named user method outside builtin identity

- Parse a named receiver with a method spelled map
   - Expected: errors.len() equals `0`
   - Expected: observed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a named receiver with a method spelled map")
val source = "class Custom:\n    fn map(f):\n        7\n\nfn main():\n    val items: Custom = Custom()\n    val mapped = items.map(\\item: item + 1)\n"
val parsed = parse_full_frontend(source, "user_map_identity", "user_map_identity", Logger(level: 0))
var lowering = HirLowering.with_filename("user_map_identity.spl")
val (resolved, errors) = resolve_methods_quiet(lowering.lower_module(parsed))
expect(errors.len()).to_equal(0)
var observed = 0
for function in resolved.functions.values():
    if function.name == "main":
        for statement in function.body.stmts:
            match statement.kind:
                case HirStmtKind.Let(_, _, initializer):
                    if initializer != nil:
                        match initializer.kind:
                            case HirExprKind.MethodCall(_, method, _, resolution):
                                if method == "map":
                                    observed = observed + 1
                                    var builtin = false
                                    match resolution:
                                        case MethodResolution.BuiltinCollection(_): builtin = true
                                        case _: ()
                                    expect(builtin).to_be(false)
                            case _: ()
                case _: ()
expect(observed).to_equal(1)
```

</details>

#### should execute canonical map and filter through the HIR interpreter

- Resolve and execute each existing Array callback operation
   - Expected: errors.len() equals `0`
   - Expected: observed equals `if method == "map": 5 else: 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve and execute each existing Array callback operation")
for method in ["map", "filter"]:
    val callback = if method == "map": "\\item: item + 1" else: "\\item: item > 1"
    val result = if method == "map": "mapped[0] + mapped[1]" else: "mapped[0]"
    val source = "fn main():\n    val items: [i64] = [1, 2]\n    val mapped = items." + method + "(" + callback + ")\n    " + result + "\n"
    val parsed = parse_full_frontend(source, "builtin_execute", "builtin_execute", Logger(level: 0))
    var lowering = HirLowering.with_filename("builtin_execute.spl")
    val (resolved, errors) = resolve_methods_quiet(lowering.lower_module(parsed))
    expect(errors.len()).to_equal(0)
    val backend = InterpreterBackendImpl.new()
    val execution = backend.interpret_hir_module(resolved)
    expect(execution.is_ok()).to_be(true)
    var observed: i64 = -1
    match execution.unwrap():
        case BackendResult.Value(Value.Int(value)): observed = value
        case _: ()
    expect(observed).to_equal(if method == "map": 5 else: 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

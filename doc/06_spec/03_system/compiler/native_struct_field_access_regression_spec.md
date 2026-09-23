# native_struct_field_access_regression_spec

> Native struct-field access regression for the self-hosted AOT path.

<!-- sdn-diagram:id=native_struct_field_access_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_struct_field_access_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_struct_field_access_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_struct_field_access_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_struct_field_access_regression_spec

Native struct-field access regression for the self-hosted AOT path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_struct_field_access_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Native struct-field access regression for the self-hosted AOT path.

## Scenarios

### self-hosted native struct field access

#### compiles and reads a text field from a local struct

- compiles and reads a text field from a local struct
- Write the minimal struct-field AOT repro
   - Expected: dir_create_all(BUILD_DIR) is true
   - Expected: remove_file_if_exists(BINARY_PATH) is true
- Compile through the deployed self-hosted native-build path
   - Expected: compiled.exit_code equals `0`
- Run the native artifact and observe the exact field value
   - Expected: ran.exit_code equals `0`
   - Expected: ran.stdout equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles and reads a text field from a local struct")
step("Write the minimal struct-field AOT repro")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(remove_file_if_exists(BINARY_PATH)).to_equal(true)
expect(file_write(
    SOURCE_PATH,
    "struct S:\n" +
    "    name: text\n" +
    "fn main():\n" +
    "    val v = S(name: \"A\")\n" +
    "    print(v.name)\n"
)).to_equal(true)

step("Compile through the deployed self-hosted native-build path")
val compiled = shell(
    "env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 " +
    "bin/simple native-build --entry " + SOURCE_PATH + " -o " + BINARY_PATH + " --clean"
)
expect(compiled.exit_code).to_equal(0)

step("Run the native artifact and observe the exact field value")
val ran = shell(BINARY_PATH)
expect(ran.exit_code).to_equal(0)
expect(ran.stdout).to_equal("A")
```

</details>

#### rejects an erased receiver with conflicting narrow and wide layouts

- rejects an erased receiver with conflicting narrow and wide layouts
- Write distinct narrow and wide sentinels that share a field name at different slots
   - Expected: dir_create_all(BUILD_DIR) is true
- Run it through the JIT lowering path and require an ambiguity refusal
   - Expected: erased.exit_code == 0 is false
- Observe that neither narrow nor wide sentinel is guessed


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an erased receiver with conflicting narrow and wide layouts")
step("Write distinct narrow and wide sentinels that share a field name at different slots")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(file_write(
    ERASED_SOURCE_PATH,
    "struct ZzSmall:\n" +
    "    zzq: i64\n" +
    "\n" +
    "struct ZzBig:\n" +
    "    p0: i64\n" +
    "    p1: i64\n" +
    "    zzq: i64\n" +
    "    p2: i64\n" +
    "    p3: i64\n" +
    "\n" +
    "fn read_zzq(o: any) -> i64:\n" +
    "    return o.zzq\n" +
    "\n" +
    "fn main():\n" +
    "    var s = ZzSmall(zzq: 7)\n" +
    "    var w = ZzBig(p0: 11, p1: 13, zzq: 42, p2: 17, p3: 19)\n" +
    "    print(read_zzq(w))\n"
)).to_equal(true)

step("Run it through the JIT lowering path and require an ambiguity refusal")
val erased = shell(
    "env -u SIMPLE_EXECUTION_MODE -u SIMPLE_RUNTIME_MODE " +
    "bin/simple run " + ERASED_SOURCE_PATH + " 2>&1"
)
expect(erased.exit_code == 0).to_equal(false)

step("Observe that neither narrow nor wide sentinel is guessed")
expect(erased.stdout).to_contain("cannot infer field")
```

</details>

#### rejects conflicting erased-receiver layouts independently of declaration order

- rejects conflicting erased-receiver layouts independently of declaration order
- Declare a wide target and narrow sentinel in reverse order
   - Expected: dir_create_all(BUILD_DIR) is true
- Run it through the JIT lowering path and require an ambiguity refusal
   - Expected: ordered.exit_code == 0 is false
- Observe that the dynamic layout remains fail-closed after order reversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects conflicting erased-receiver layouts independently of declaration order")
step("Declare a wide target and narrow sentinel in reverse order")
expect(dir_create_all(BUILD_DIR)).to_equal(true)
expect(file_write(
    ORDER_SOURCE_PATH,
    "struct ZzWide:\n" +
    "    q0: i64\n" +
    "    q1: i64\n" +
    "    zzr: i64\n" +
    "    q2: i64\n" +
    "    q3: i64\n" +
    "    q4: i64\n" +
    "\n" +
    "struct ZzMid:\n" +
    "    m0: i64\n" +
    "    zzr: i64\n" +
    "    m1: i64\n" +
    "\n" +
    "struct ZzTiny:\n" +
    "    zzr: i64\n" +
    "\n" +
    "fn read_zzr(o: any) -> i64:\n" +
    "    return o.zzr\n" +
    "\n" +
    "fn main():\n" +
    "    var t = ZzTiny(zzr: 7)\n" +
    "    var w = ZzWide(q0: 1, q1: 2, zzr: 42, q2: 3, q3: 4, q4: 5)\n" +
    "    print(read_zzr(w))\n"
)).to_equal(true)

step("Run it through the JIT lowering path and require an ambiguity refusal")
val ordered = shell(
    "env -u SIMPLE_EXECUTION_MODE -u SIMPLE_RUNTIME_MODE " +
    "bin/simple run " + ORDER_SOURCE_PATH + " 2>&1"
)
expect(ordered.exit_code == 0).to_equal(false)

step("Observe that the dynamic layout remains fail-closed after order reversal")
expect(ordered.stdout).to_contain("cannot infer field")
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

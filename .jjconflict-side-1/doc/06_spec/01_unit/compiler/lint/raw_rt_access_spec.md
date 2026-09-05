# raw_rt_access_spec

> Purpose: Prove that RAW-RT-001: raw extern fn rt_* outside privileged tiers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# raw_rt_access_spec

Purpose: Prove that RAW-RT-001: raw extern fn rt_* outside privileged tiers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/raw_rt_access_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RAW-RT-001: raw extern fn rt_* outside privileged tiers.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### RAW-RT-001: raw extern fn rt_* outside privileged tiers

#### when declared in src/compiler/ (CLI-closure, now covered)

#### detects extern fn rt_* in src/compiler/70.backend/backend/

- detects extern fn rt_* in src/compiler/70.backend/backend/
- Verify: detects extern fn rt_* in src/compiler/70.backend/backend/
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-001`
   - Expected: findings[0].name equals `rt_new_intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects extern fn rt_* in src/compiler/70.backend/backend/")
step("Verify: detects extern fn rt_* in src/compiler/70.backend/backend/")
# @req: REQ-COMPILER-LINT-001
val source = "extern fn rt_new_intrinsic(x: i64) -> i64\n"
val findings = check_raw_rt_access(source, "src/compiler/70.backend/backend/llvm_native_link.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-001")
expect(findings[0].name).to_equal("rt_new_intrinsic")
```

</details>

#### detects extern fn rt_* in any src/compiler/ subdirectory

- detects extern fn rt_* in any src/compiler/ subdirectory
- Verify: detects extern fn rt_* in any src/compiler/ subdirectory
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects extern fn rt_* in any src/compiler/ subdirectory")
step("Verify: detects extern fn rt_* in any src/compiler/ subdirectory")
val source = "extern fn rt_cli_arg_count() -> i64\n"
val findings = check_raw_rt_access(source, "src/compiler/00.common/config.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reports the accurate line number for a non-first-line declaration

- reports the accurate line number for a non-first-line declaration
- Verify: reports the accurate line number for a non-first-line declaration
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the accurate line number for a non-first-line declaration")
step("Verify: reports the accurate line number for a non-first-line declaration")
val source = "use std.io\n\nfn helper():\n    pass\n\nextern fn rt_new_intrinsic(x: i64) -> i64\n"
val findings = check_raw_rt_access(source, "src/compiler/00.common/config.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].line_num).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### when declared in application/CLI code (already covered)

#### detects extern fn rt_* in src/app/

- detects extern fn rt_* in src/app/
- Verify: detects extern fn rt_* in src/app/
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects extern fn rt_* in src/app/")
step("Verify: detects extern fn rt_* in src/app/")
val source = "extern fn rt_file_read_text(path: text) -> text\n"
val findings = check_raw_rt_access(source, "src/app/cli/main.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-001")
```

</details>

#### accepts an explicitly ffi-unsafe raw declaration

- accepts an explicitly ffi-unsafe raw declaration
- Verify: explicit ffi authority acknowledges the raw declaration
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts an explicitly ffi-unsafe raw declaration")
step("Verify: explicit ffi authority acknowledges the raw declaration")
val source = "@unsafe(reason: \"raw nullable file boundary\", capabilities: [ffi])\nextern fn rt_file_read_text(path: text) -> text?\n"
val findings = check_raw_rt_access(source, "src/app/cli/main.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### when declared in a sanctioned provider

#### flags an ordinary product library instead of exempting all src/lib

- flags an ordinary product library instead of exempting all src/lib
- Verify: flags an ordinary product library instead of exempting all src/lib
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags an ordinary product library instead of exempting all src/lib")
step("Verify: flags an ordinary product library instead of exempting all src/lib")
val source = "extern fn rt_file_read_text(path: text) -> text\n"
val findings = check_raw_rt_access(source, "src/lib/nogc_sync_mut/product/config.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### allows a named SFFI provider

- allows a named SFFI provider
- Verify: allows a named SFFI provider
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows a named SFFI provider")
step("Verify: allows a named SFFI provider")
val source = "extern fn rt_file_read_text(path: text) -> text\nfn read(path: text): rt_file_read_text(path)\n"
val findings = check_raw_rt_access_with_allowlist(source, "src/lib/nogc_sync_mut/io/file_sffi.spl", "suffix:_sffi.spl\n")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### does not flag extern fn rt_* in src/runtime/

- does not flag extern fn rt_* in src/runtime/
- Verify: does not flag extern fn rt_* in src/runtime/
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag extern fn rt_* in src/runtime/")
step("Verify: does not flag extern fn rt_* in src/runtime/")
val source = "extern fn rt_gc_alloc(size: i64) -> i64\n"
val findings = check_raw_rt_access_with_allowlist(source, "src/runtime/gc/alloc.spl", "src/runtime/\n")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### RAW-RT-002: direct raw runtime use

#### warns on a direct call without a local extern declaration

- warns on a direct call without a local extern declaration
- Verify: warns on a direct call without a local extern declaration
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-002`
   - Expected: findings[0].name equals `rt_file_read_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a direct call without a local extern declaration")
step("Verify: warns on a direct call without a local extern declaration")
val source = "fn load(path: text):\n    rt_file_read_text(path)\n"
val findings = check_raw_rt_access(source, "src/app/config/load.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-002")
expect(findings[0].name).to_equal("rt_file_read_text")
expect(findings[0].note).to_contain("file_read_text")
expect(findings[0].note).to_contain("simple lint --fix")
```

</details>

#### accepts a call contained by a minimal ffi-unsafe block

- accepts a call contained by a minimal ffi-unsafe block
- Verify: lexical ffi containment discharges the raw-call lint
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a call contained by a minimal ffi-unsafe block")
step("Verify: lexical ffi containment discharges the raw-call lint")
val source = "@unsafe(reason: \"raw nullable file boundary\", capabilities: [ffi])\nextern fn rt_file_read_text(path: text) -> text?\nfn load(path: text) -> text?:\n    unsafe(capabilities: [ffi]):\n        rt_file_read_text(path)\n"
val findings = check_raw_rt_access(source, "src/app/config/load.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### still rejects an uncontained call after a tagged declaration

- still rejects an uncontained call after a tagged declaration
- Verify: declaration authority does not leak into ordinary code
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still rejects an uncontained call after a tagged declaration")
step("Verify: declaration authority does not leak into ordinary code")
val source = "@unsafe(reason: \"raw nullable file boundary\", capabilities: [ffi])\nextern fn rt_file_read_text(path: text) -> text?\nfn load(path: text) -> text?:\n    rt_file_read_text(path)\n"
val findings = check_raw_rt_access(source, "src/app/config/load.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("RAW-RT-002")
```

</details>

#### warns on a direct selective import

- warns on a direct selective import
- Verify: warns on a direct selective import
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a direct selective import")
step("Verify: warns on a direct selective import")
# Split the token so the seed's eager source-import scan does not treat
# this fixture string as an import belonging to the spec itself.
val source = "u" + "se std.runtime.{r" + "t_http_request}\n"
val findings = check_raw_rt_access(source, "src/app/http/client.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-002")
```

</details>

#### warns on a product-side private alias import

- warns on a product-side private alias import
- Verify: warns on a product-side private alias import
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a product-side private alias import")
step("Verify: warns on a product-side private alias import")
val source = "u" + "se runtime.primitive.{r" + "t_memcpy as _memory_copy_primitive}\nfn copy(): _memory_copy_primitive()\n"
val findings = check_raw_rt_access(source, "src/app/product/native_copy.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-002")
```

</details>

#### allows that alias only when the canonical policy sanctions its provider path

- allows that alias only when the canonical policy sanctions its provider path
- Verify: allows that alias only when the canonical policy sanctions its provider path
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows that alias only when the canonical policy sanctions its provider path")
step("Verify: allows that alias only when the canonical policy sanctions its provider path")
val source = "u" + "se runtime.primitive.{r" + "t_memcpy as _memory_copy_primitive}\nfn copy(): _memory_copy_primitive()\n"
val policy = "src/app/provider_cli/native_provider_v1.spl\n"
val findings = check_raw_rt_access_with_allowlist(source, "src/app/provider_cli/native_provider_v1.spl", policy)
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### ignores comment and string decoys

- ignores comment and string decoys
- Verify: ignores comment and string decoys
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores comment and string decoys")
step("Verify: ignores comment and string decoys")
val source = "# rt_process_run(cmd, args)\nval example = \"rt_file_read_text(path)\"\n"
val findings = check_raw_rt_access(source, "src/app/example.spl")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### ignores calls, imports, and markers inside multiline strings

- ignores calls, imports, and markers inside multiline strings
- Verify: ignores calls, imports, and markers inside multiline strings
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores calls, imports, and markers inside multiline strings")
step("Verify: ignores calls, imports, and markers inside multiline strings")
val source = "val docs = \"\"\"\nr" + "t_process_run(cmd, args)\nu" + "se app.io.{process_run}\n@runtime_intrinsics\n\"\"\"\nfn clean(): 1\n"
val findings = check_raw_rt_access(source, "src/app/docs.spl")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### does not match rt_ embedded in a larger imported identifier

- does not match rt_ embedded in a larger imported identifier
- Verify: does not match rt_ embedded in a larger imported identifier
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not match rt_ embedded in a larger imported identifier")
step("Verify: does not match rt_ embedded in a larger imported identifier")
val source = "u" + "se product.api.{support_r" + "t_hook}\n"
val findings = check_raw_rt_access(source, "src/app/product.spl")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reports at most one direct-use finding per source line

- reports at most one direct-use finding per source line
- Verify: reports at most one direct-use finding per source line
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports at most one direct-use finding per source line")
step("Verify: reports at most one direct-use finding per source line")
val source = "fn run(): rt_process_run(cmd, args) + rt_process_run(cmd, args)\n"
val findings = check_raw_rt_access(source, "src/app/run.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### RAW-RT-003: removed product aliases

#### warns on a product-side rt alias declaration

- warns on a product-side rt alias declaration
- Verify: warns on a product-side rt alias declaration
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `RAW-RT-003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns on a product-side rt alias declaration")
step("Verify: warns on a product-side rt alias declaration")
val source = "fn rt_old_read(path: text): file_read_text(path)\n"
val findings = check_raw_rt_access(source, "src/app/compat.spl")
expect(findings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(findings[0].code).to_equal("RAW-RT-003")
```

</details>

### raw rt wrapper fix lookup

#### returns safe known replacements and no invented replacement

- returns safe known replacements and no invented replacement
- Verify: returns safe known replacements and no invented replacement
   - Expected: raw_rt_wrapper_replacement("rt_process_run") equals `process_run`
   - Expected: raw_rt_wrapper_replacement("rt_unknown_device_op") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns safe known replacements and no invented replacement")
step("Verify: returns safe known replacements and no invented replacement")
expect(raw_rt_wrapper_replacement("rt_process_run")).to_equal("process_run")
expect(raw_rt_wrapper_replacement("rt_unknown_device_op")).to_equal("")
```

</details>

#### uses exact canonical prefix and suffix allowlist semantics

- uses exact canonical prefix and suffix allowlist semantics
- Verify: uses exact canonical prefix and suffix allowlist semantics
   - Expected: raw_rt_provider_allowlist_allows("/repo/src/lib/provider/x.spl", policy) is true
   - Expected: raw_rt_provider_allowlist_allows("/repo/src/app/io/file_sffi.spl", policy) is true
   - Expected: raw_rt_provider_allowlist_allows("/repo/src/lib/providerish/x.spl", policy) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses exact canonical prefix and suffix allowlist semantics")
step("Verify: uses exact canonical prefix and suffix allowlist semantics")
val policy = "src/lib/provider/\nsuffix:_sffi.spl\n"
expect(raw_rt_provider_allowlist_allows("/repo/src/lib/provider/x.spl", policy)).to_equal(true)
expect(raw_rt_provider_allowlist_allows("/repo/src/app/io/file_sffi.spl", policy)).to_equal(true)
expect(raw_rt_provider_allowlist_allows("/repo/src/lib/providerish/x.spl", policy)).to_equal(false)
```

</details>

### RAW-RT-002 auto-fix

#### offers a safe rename only when the canonical wrapper facade is in scope

- offers a safe rename only when the canonical wrapper facade is in scope
- Verify: offers a safe rename only when the canonical wrapper facade is in scope
   - Expected: replacements equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("offers a safe rename only when the canonical wrapper facade is in scope")
step("Verify: offers a safe rename only when the canonical wrapper facade is in scope")
val source = "u" + "se app.io.mod.{process_run}\nfn run():\n    rt_process_run(cmd, args)\n"
var replacements = 0
var applied = ""
for result in lint_cli_source(Linter.new(), "/tmp/raw_rt_fix.spl", source):
    if result.lint.code == "RAW-RT-002" and result.line == 3:
        match result.lint.easy_fix:
            case Some(fix):
                for rep in easyfix_replacements(fix):
                    replacements = replacements + 1
                    applied = source.slice(0, rep.start) + rep.new_text + source.slice(rep.end)
            case nil:
                val _ = 0
expect(replacements).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(applied).to_contain("    process_run(cmd, args)")
expect(applied).to_not_contain("    rt_process_run(cmd, args)")
```

</details>

#### targets the lexical call rather than an earlier string decoy

- targets the lexical call rather than an earlier string decoy
- Verify: targets the lexical call rather than an earlier string decoy


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("targets the lexical call rather than an earlier string decoy")
step("Verify: targets the lexical call rather than an earlier string decoy")
val source = "u" + "se app.io.mod.{process_run}\nfn run():\n    sink(\"r" + "t_process_run(x, y)\", rt_process_run(cmd, args))\n"
var applied = ""
for result in lint_cli_source(Linter.new(), "/tmp/raw_rt_decoy_fix.spl", source):
    if result.lint.code == "RAW-RT-002" and result.line == 3:
        match result.lint.easy_fix:
            case Some(fix):
                for rep in easyfix_replacements(fix):
                    applied = source.slice(0, rep.start) + rep.new_text + source.slice(rep.end)
            case nil:
                val _ = 0
expect(applied).to_contain("\"rt_process_run(x, y)\", process_run(cmd, args))")
```

</details>

#### keeps an actionable warning but withholds an unsafe bare rename

- keeps an actionable warning but withholds an unsafe bare rename
- Verify: keeps an actionable warning but withholds an unsafe bare rename
   - Expected: warned is true
   - Expected: replacements equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps an actionable warning but withholds an unsafe bare rename")
step("Verify: keeps an actionable warning but withholds an unsafe bare rename")
val source = "fn run():\n    rt_process_run(cmd, args)\n"
var warned = false
var replacements = 0
for result in lint_cli_source(Linter.new(), "/tmp/raw_rt_no_scope.spl", source):
    if result.lint.code == "RAW-RT-002":
        warned = true
        match result.lint.easy_fix:
            case Some(fix):
                replacements = replacements + easyfix_replacements(fix).len()
            case nil:
                val _ = 0
expect(warned).to_equal(true)
expect(replacements).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### recognizes the canonical std.io_runtime selective import

- recognizes the canonical std.io_runtime selective import
- Verify: recognizes the canonical std.io_runtime selective import
   - Expected: replacements equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recognizes the canonical std.io_runtime selective import")
step("Verify: recognizes the canonical std.io_runtime selective import")
val source = "u" + "se std.io_runtime.{process_run}\nfn run():\n    rt_process_run(cmd, args)\n"
var replacements = 0
for result in lint_cli_source(Linter.new(), "/tmp/raw_rt_std_fix.spl", source):
    if result.lint.code == "RAW-RT-002" and result.line == 3:
        match result.lint.easy_fix:
            case Some(fix): replacements = replacements + easyfix_replacements(fix).len()
            case nil: val _ = 0
expect(replacements).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### when the file opts out with @runtime_intrinsics

#### does not flag a src/compiler/ file marked @runtime_intrinsics

- does not flag a src/compiler/ file marked @runtime_intrinsics
- Verify: does not flag a src/compiler/ file marked @runtime_intrinsics
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not flag a src/compiler/ file marked @runtime_intrinsics")
step("Verify: does not flag a src/compiler/ file marked @runtime_intrinsics")
val source = "@runtime_intrinsics\n\nextern fn rt_new_intrinsic(x: i64) -> i64\n"
val findings = check_raw_rt_access(source, "src/compiler/70.backend/backend/llvm_native_link.spl")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### when the extern is not an rt_* intrinsic

#### ignores a non-rt_ extern fn

- ignores a non-rt_ extern fn
- Verify: ignores a non-rt_ extern fn
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores a non-rt_ extern fn")
step("Verify: ignores a non-rt_ extern fn")
val source = "extern fn curl_easy_init() -> i64\n"
val findings = check_raw_rt_access(source, "src/app/cli/main.spl")
expect(findings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### RawRtAccessFinding formatting

#### produces formatted output

- produces formatted output
- Verify: produces formatted output


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces formatted output")
step("Verify: produces formatted output")
val f = RawRtAccessFinding(
    code: "RAW-RT-001",
    severity: "WARNING",
    message: "test message",
    name: "rt_thing",
    note: "test note",
    line_num: 3,
    column: 2
)
val output = f.fmt()
expect(output).to_contain("RAW-RT-001")
expect(output).to_contain("WARNING")
expect(output).to_contain("test message")
expect(output).to_contain("test note")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1349a62ad8da4082d28869727c1cd11b27fb3f8b772542e64e2fe07342888c50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1349a62ad8da4082d28869727c1cd11b27fb3f8b772542e64e2fe07342888c50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1349a62ad8da4082d28869727c1cd11b27fb3f8b772542e64e2fe07342888c50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/raw_rt_access_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/raw_rt_access_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/raw_rt_access_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/raw_rt_access_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/raw_rt_access_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/raw_rt_access_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects extern fn rt_* in src/compiler/70.backend/backend/' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/raw_rt_access_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects extern fn rt_* in any src/compiler/ subdirectory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/raw_rt_access_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the accurate line number for a non-first-line declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

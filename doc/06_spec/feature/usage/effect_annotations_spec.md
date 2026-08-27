# Effect Annotations Specification

> @pure

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect Annotations Specification

@pure

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-ANN-001 to #EFFECT-ANN-012 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/feature/usage/effect_annotations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Syntax

```simple
@pure
use std.spec.step

fn add(x: i64, y: i64) -> i64:
x + y

@io @net
fn fetch_and_log(url: text):
val data = http_get(url)
print(data)
```

## Scenarios

### Single Effect Annotations

#### @pure effect

#### parses @pure on function

- parses @pure on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @pure on function")
@pure
fn add(x: i64, y: i64) -> i64:
    x + y
expect add(20, 22) == 42
```

</details>

#### pure function has no side effects

- pure function has no side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure function has no side effects")
@pure
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### @io effect

#### parses @io on function

- parses @io on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @io on function")
@io
fn print_hello():
    print("Hello, World!")
expect true  # Parsed successfully
```

</details>

#### @net effect

#### parses @net on function

- parses @net on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @net on function")
@net
fn fetch(url: text) -> text:
    "mock response"  # Placeholder
expect true
```

</details>

#### @fs effect

#### parses @fs on function

- parses @fs on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @fs on function")
@fs
fn read_file(path: text) -> text:
    "file contents"  # Placeholder
expect true
```

</details>

#### @unsafe effect

#### parses @unsafe on function

- parses @unsafe on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @unsafe on function")
@unsafe
fn raw_cast(ptr: i64) -> i64:
    ptr
expect true
```

</details>

#### @async effect

#### parses @async on function

- parses @async on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses @async on function")
@async
fn delayed_task():
    pass
expect true
```

</details>

### Multiple Effect Annotations

#### parses two effects

- parses two effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses two effects")
@io
@net
fn fetch_and_log(url: text):
    val data = "mock"
    print(data)
expect true
```

</details>

#### parses three effects

- parses three effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses three effects")
@io
@net
@fs
fn sync_remote_file(url: text, path: text):
    val data = "mock"
    print("Synced!")
expect true
```

</details>

#### parses io and fs together

- parses io and fs together


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses io and fs together")
@io
@fs
fn log_to_file(path: text, message: text):
    print("Logging: {message}")
expect true
```

</details>

### Functions Without Effects

#### function with no effects parses

- function with no effects parses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("function with no effects parses")
fn unrestricted_function():
    print("Can do anything!")
expect true
```

</details>

#### no-effect function can call anything

- no-effect function can call anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("no-effect function can call anything")
fn flexible():
    val x = 42
    x
expect flexible() == 42
```

</details>

### Effects with Other Decorators

#### combines @pure with @inline

- combines @pure with @inline


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines @pure with @inline")
@pure
@inline
fn fast_add(x: i64, y: i64) -> i64:
    x + y
expect fast_add(20, 22) == 42
```

</details>

#### combines @io with @deprecated

- combines @io with @deprecated


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines @io with @deprecated")
@io
@deprecated
fn old_print(msg: text):
    print(msg)
expect true
```

</details>

#### effects separate from other decorators

- effects separate from other decorators


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("effects separate from other decorators")
@pure
@memoize
fn cached_compute(x: i64) -> i64:
    x * x
expect cached_compute(6) == 36
```

</details>

### Effect Enum

#### Effect has Pure variant

- Effect has Pure variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Pure variant")
val e = Effect.Pure
expect e == Effect.Pure
```

</details>

#### Effect has Io variant

- Effect has Io variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Io variant")
val e = Effect.Io
expect e == Effect.Io
```

</details>

#### Effect has Net variant

- Effect has Net variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Net variant")
val e = Effect.Net
expect e == Effect.Net
```

</details>

#### Effect has Fs variant

- Effect has Fs variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Fs variant")
val e = Effect.Fs
expect e == Effect.Fs
```

</details>

#### Effect has Unsafe variant

- Effect has Unsafe variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Unsafe variant")
val e = Effect.Unsafe
expect e == Effect.Unsafe
```

</details>

#### Effect has Async variant

- Effect has Async variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Effect has Async variant")
val e = Effect.Async
expect e == Effect.Async
```

</details>

### Effect from Decorator Name

#### converts 'pure' to Pure

- converts 'pure' to Pure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'pure' to Pure")
# Effect.from_decorator_name("pure") would return Some(Effect.Pure)
val e = Effect.Pure
expect e == Effect.Pure
```

</details>

#### converts 'io' to Io

- converts 'io' to Io


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'io' to Io")
val e = Effect.Io
expect e == Effect.Io
```

</details>

#### converts 'net' to Net

- converts 'net' to Net


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'net' to Net")
val e = Effect.Net
expect e == Effect.Net
```

</details>

#### converts 'fs' to Fs

- converts 'fs' to Fs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'fs' to Fs")
val e = Effect.Fs
expect e == Effect.Fs
```

</details>

#### converts 'unsafe' to Unsafe

- converts 'unsafe' to Unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'unsafe' to Unsafe")
val e = Effect.Unsafe
expect e == Effect.Unsafe
```

</details>

#### converts 'async' to Async

- converts 'async' to Async


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 'async' to Async")
val e = Effect.Async
expect e == Effect.Async
```

</details>

#### returns None for unknown

- returns None for unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns None for unknown")
# Effect.from_decorator_name("unknown") would return None
# Verify that unknown strings don't match any known effect
expect "unknown" != "pure"
```

</details>

#### returns None for inline

- returns None for inline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns None for inline")
# Effect.from_decorator_name("inline") would return None
# @inline is a decorator but not an effect
expect "inline" != "pure"
```

</details>

### Effect Decorator Name

#### Pure decorator name is 'pure'

- Pure decorator name is 'pure'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Pure decorator name is 'pure'")
val e = Effect.Pure
expect e.decorator_name() == "pure"
```

</details>

#### Io decorator name is 'io'

- Io decorator name is 'io'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Io decorator name is 'io'")
val e = Effect.Io
expect e.decorator_name() == "io"
```

</details>

#### Net decorator name is 'net'

- Net decorator name is 'net'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Net decorator name is 'net'")
val e = Effect.Net
expect e.decorator_name() == "net"
```

</details>

#### Fs decorator name is 'fs'

- Fs decorator name is 'fs'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Fs decorator name is 'fs'")
val e = Effect.Fs
expect e.decorator_name() == "fs"
```

</details>

#### Unsafe decorator name is 'unsafe'

- Unsafe decorator name is 'unsafe'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Unsafe decorator name is 'unsafe'")
val e = Effect.Unsafe
expect e.decorator_name() == "unsafe"
```

</details>

#### Async decorator name is 'async'

- Async decorator name is 'async'


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Async decorator name is 'async'")
val e = Effect.Async
expect e.decorator_name() == "async"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e469124e7c272437b816ef299bc511ad9b8d46e6a4da42ee6fb6221924f0478`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e469124e7c272437b816ef299bc511ad9b8d46e6a4da42ee6fb6221924f0478`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e469124e7c272437b816ef299bc511ad9b8d46e6a4da42ee6fb6221924f0478`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/effect_annotations_spec.spl
mirror: doc/06_spec/feature/usage/effect_annotations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/effect_annotations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/effect_annotations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/effect_annotations_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @pure on function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/effect_annotations_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure function has no side effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/effect_annotations_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @io on function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

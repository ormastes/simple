# libc_string_copy_spec

> Verifies the libc string copy behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_string_copy_spec

Verifies the libc string copy behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_copy_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc string copy behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS libc — string copy/concat functions

### strcpy

#### copies a non-empty string

- Verify: copies a non-empty string
   - Expected: dst.len() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dst[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dst[4] equals `111)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies a non-empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "hello".bytes()
val dst = libc_strcpy(src)
expect(dst.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[4]).to_equal(111)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### copies an empty string

- Verify: copies an empty string
   - Expected: dst.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies an empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dst = libc_strcpy("".bytes())
expect(dst.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strncpy

#### copies when n is larger than source length

- Verify: copies when n is larger than source length
   - Expected: dst.len() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dst[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dst[1] equals `105)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dst[2] equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dst[4] equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies when n is larger than source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "hi".bytes()
val dst = libc_strncpy(src, 5)
expect(dst.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[1]).to_equal(105)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[2]).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[4]).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### truncates when n is smaller than source length

- Verify: truncates when n is smaller than source length
   - Expected: dst.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dst[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dst[2] equals `108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: truncates when n is smaller than source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "hello".bytes()
val dst = libc_strncpy(src, 3)
expect(dst.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dst[2]).to_equal(108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns empty array when n is 0

- Verify: returns empty array when n is 0
   - Expected: dst.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns empty array when n is 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dst = libc_strncpy("hello".bytes(), 0)
expect(dst.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### clamps negative n to 0

- Verify: clamps negative n to 0
   - Expected: dst.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: clamps negative n to 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dst = libc_strncpy("hello".bytes(), -5)
expect(dst.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strcat

#### concatenates two non-empty strings

- Verify: concatenates two non-empty strings
   - Expected: result.len() equals `10)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: result[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: result[5] equals `119)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: result[9] equals `100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: concatenates two non-empty strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "hello".bytes()
val b = "world".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(10)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[5]).to_equal(119)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[9]).to_equal(100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### concatenates when first is empty

- Verify: concatenates when first is empty
   - Expected: result.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: concatenates when first is empty")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "".bytes()
val b = "hi".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### concatenates when second is empty

- Verify: concatenates when second is empty
   - Expected: result.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: concatenates when second is empty")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "hi".bytes()
val b = "".bytes()
val result = libc_strcat(a, b)
expect(result.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strncat

#### concatenates when n is larger than b length

- Verify: concatenates when n is larger than b length
   - Expected: result.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result[0] equals `97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: result[3] equals `100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: concatenates when n is larger than b length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, 10)
expect(result.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### truncates b when n is smaller than b length

- Verify: truncates b when n is smaller than b length
   - Expected: result.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result[0] equals `97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: result[3] equals `100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: truncates b when n is smaller than b length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "ab".bytes()
val b = "cdef".bytes()
val result = libc_strncat(a, b, 2)
expect(result.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns a when n is 0

- Verify: returns a when n is 0
   - Expected: result.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result[0] equals `97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns a when n is 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, 0)
expect(result.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result[0]).to_equal(97)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### clamps negative n to 0

- Verify: clamps negative n to 0
   - Expected: result.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: clamps negative n to 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = "ab".bytes()
val b = "cd".bytes()
val result = libc_strncat(a, b, -5)
expect(result.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strdup

#### duplicates a non-empty string

- Verify: duplicates a non-empty string
   - Expected: dup.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dup[0] equals `116)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dup[3] equals `116)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: duplicates a non-empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "test".bytes()
val dup = libc_strdup(src)
expect(dup.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dup[0]).to_equal(116)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dup[3]).to_equal(116)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### duplicates an empty string

- Verify: duplicates an empty string
   - Expected: dup.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: duplicates an empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dup = libc_strdup("".bytes())
expect(dup.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strndup

#### duplicates when n is larger than source length

- Verify: duplicates when n is larger than source length
   - Expected: dup.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dup[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: duplicates when n is larger than source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "hi".bytes()
val dup = libc_strndup(src, 10)
expect(dup.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dup[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### truncates when n is smaller than source length

- Verify: truncates when n is smaller than source length
   - Expected: dup.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: dup[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: dup[2] equals `108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: truncates when n is smaller than source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val src = "hello".bytes()
val dup = libc_strndup(src, 3)
expect(dup.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dup[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(dup[2]).to_equal(108)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns empty array when n is 0

- Verify: returns empty array when n is 0
   - Expected: dup.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns empty array when n is 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dup = libc_strndup("hello".bytes(), 0)
expect(dup.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### clamps negative n to 0

- Verify: clamps negative n to 0
   - Expected: dup.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: clamps negative n to 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val dup = libc_strndup("hello".bytes(), -5)
expect(dup.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strnlen

#### returns full length when maxlen is larger

- Verify: returns full length when maxlen is larger
   - Expected: libc_strnlen(s, 10) equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns full length when maxlen is larger")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val s = "hello".bytes()
expect(libc_strnlen(s, 10)).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns maxlen when smaller than length

- Verify: returns maxlen when smaller than length
   - Expected: libc_strnlen(s, 3) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns maxlen when smaller than length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val s = "hello".bytes()
expect(libc_strnlen(s, 3)).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 for empty string

- Verify: returns 0 for empty string
   - Expected: libc_strnlen("".bytes(), 10) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: returns 0 for empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strnlen("".bytes(), 10)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### clamps negative maxlen to 0

- Verify: clamps negative maxlen to 0
   - Expected: libc_strnlen(s, -5) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: clamps negative maxlen to 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val s = "hello".bytes()
expect(libc_strnlen(s, -5)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strlcpy

#### copies fully when buffer is large enough

- Verify: copies fully when buffer is large enough
   - Expected: r.bytes.len() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.bytes[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: r.total equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies fully when buffer is large enough")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcpy("hello".bytes(), 10)
expect(r.bytes.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### truncates to dstsize-1 and reports full source length

- Verify: truncates to dstsize-1 and reports full source length
   - Expected: r.bytes.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.bytes[0] equals `104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: r.bytes[1] equals `101)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: r.total equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: truncates to dstsize-1 and reports full source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcpy("hello".bytes(), 3)
expect(r.bytes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[0]).to_equal(104)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[1]).to_equal(101)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### copies nothing for dstsize 0 but still reports source length

- Verify: copies nothing for dstsize 0 but still reports source length
   - Expected: r.bytes.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.total equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies nothing for dstsize 0 but still reports source length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcpy("hi".bytes(), 0)
expect(r.bytes.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### copies nothing for dstsize 1 (NUL slot only)

- Verify: copies nothing for dstsize 1 (NUL slot only)
   - Expected: r.bytes.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.total equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: copies nothing for dstsize 1 (NUL slot only)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcpy("hi".bytes(), 1)
expect(r.bytes.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strlcat

<details>
<summary>Advanced: appends when room remains</summary>

#### appends when room remains

- Verify: appends when room remains
   - Expected: r.bytes.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.bytes[2] equals `99)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: r.bytes[3] equals `100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: r.total equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: appends when room remains")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcat("ab".bytes(), "cd".bytes(), 10)
expect(r.bytes.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[2]).to_equal(99)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>


</details>

#### truncates appended src to remaining space

- Verify: truncates appended src to remaining space
   - Expected: r.bytes.len() equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.bytes[3] equals `100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: r.total equals `7)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: truncates appended src to remaining space")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcat("abc".bytes(), "defg".bytes(), 5)
expect(r.bytes.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.bytes[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(7)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### leaves dst unchanged when buffer already full

- Verify: leaves dst unchanged when buffer already full
   - Expected: r.bytes.len() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: r.total equals `6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-core
# @req: REQ-OS-LIBC_LIBC_STRING_COPY-001
step("Verify: leaves dst unchanged when buffer already full")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = libc_strlcat("abcde".bytes(), "x".bytes(), 5)
expect(r.bytes.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(r.total).to_equal(6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ccbb5d0de300dca4e2fd1d26c4ca45d9eeaa1b8e8d2ef8f2151c437ef92ec418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccbb5d0de300dca4e2fd1d26c4ca45d9eeaa1b8e8d2ef8f2151c437ef92ec418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccbb5d0de300dca4e2fd1d26c4ca45d9eeaa1b8e8d2ef8f2151c437ef92ec418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_string_copy_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

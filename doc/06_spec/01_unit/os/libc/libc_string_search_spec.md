# libc_string_search_spec

> Verifies the libc string search behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_string_search_spec

Verifies the libc string search behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_search_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc string search behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS libc — musl-shaped string search / span / tokenize / compare

### strstr

#### finds substring at start

- Verify: finds substring at start
   - Expected: libc_strstr("hello world".bytes(), "hello".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds substring at start")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strstr("hello world".bytes(), "hello".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds substring in middle

- Verify: finds substring in middle
   - Expected: libc_strstr("hello world".bytes(), "world".bytes()) equals `6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds substring in middle")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strstr("hello world".bytes(), "world".bytes())).to_equal(6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when not found

- Verify: returns -1 when not found
   - Expected: libc_strstr("hello world".bytes(), "xyz".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when not found")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strstr("hello world".bytes(), "xyz".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 for empty needle

- Verify: returns 0 for empty needle
   - Expected: libc_strstr("hello".bytes(), "".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns 0 for empty needle")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strstr("hello".bytes(), "".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when needle longer than haystack

- Verify: returns -1 when needle longer than haystack
   - Expected: libc_strstr("hi".bytes(), "hello".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when needle longer than haystack")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strstr("hi".bytes(), "hello".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strspn

#### counts leading accepted bytes

- Verify: counts leading accepted bytes
   - Expected: libc_strspn("abc123xyz".bytes(), "abc".bytes()) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: counts leading accepted bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strspn("abc123xyz".bytes(), "abc".bytes())).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 when first byte not in accept

- Verify: returns 0 when first byte not in accept
   - Expected: libc_strspn("123abc".bytes(), "abc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns 0 when first byte not in accept")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strspn("123abc".bytes(), "abc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns full length when all bytes accepted

- Verify: returns full length when all bytes accepted
   - Expected: libc_strspn("aabbcc".bytes(), "abc".bytes()) equals `6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns full length when all bytes accepted")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strspn("aabbcc".bytes(), "abc".bytes())).to_equal(6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty string

- Verify: handles empty string
   - Expected: libc_strspn("".bytes(), "abc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strspn("".bytes(), "abc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty accept

- Verify: handles empty accept
   - Expected: libc_strspn("abc".bytes(), "".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty accept")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strspn("abc".bytes(), "".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strcspn

#### counts until first rejected byte

- Verify: counts until first rejected byte
   - Expected: libc_strcspn("abc123xyz".bytes(), "123".bytes()) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: counts until first rejected byte")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcspn("abc123xyz".bytes(), "123".bytes())).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns full length when no rejected bytes

- Verify: returns full length when no rejected bytes
   - Expected: libc_strcspn("abcxyz".bytes(), "123".bytes()) equals `6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns full length when no rejected bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcspn("abcxyz".bytes(), "123".bytes())).to_equal(6)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 when first byte is rejected

- Verify: returns 0 when first byte is rejected
   - Expected: libc_strcspn("123abc".bytes(), "123".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns 0 when first byte is rejected")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcspn("123abc".bytes(), "123".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty string

- Verify: handles empty string
   - Expected: libc_strcspn("".bytes(), "123".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcspn("".bytes(), "123".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty reject

- Verify: handles empty reject
   - Expected: libc_strcspn("abc".bytes(), "".bytes()) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty reject")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcspn("abc".bytes(), "".bytes())).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strpbrk

#### finds first byte from accept set

- Verify: finds first byte from accept set
   - Expected: libc_strpbrk("hello world".bytes(), "ol".bytes()) equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds first byte from accept set")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strpbrk("hello world".bytes(), "ol".bytes())).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when no byte from accept found

- Verify: returns -1 when no byte from accept found
   - Expected: libc_strpbrk("hello world".bytes(), "xyz".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when no byte from accept found")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strpbrk("hello world".bytes(), "xyz".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds first matching position

- Verify: finds first matching position
   - Expected: libc_strpbrk("abc123def".bytes(), "123".bytes()) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds first matching position")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strpbrk("abc123def".bytes(), "123".bytes())).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty string

- Verify: handles empty string
   - Expected: libc_strpbrk("".bytes(), "abc".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strpbrk("".bytes(), "abc".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles empty accept

- Verify: handles empty accept
   - Expected: libc_strpbrk("abc".bytes(), "".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles empty accept")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strpbrk("abc".bytes(), "".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### memchr

#### finds byte within n bytes

- Verify: finds byte within n bytes
   - Expected: libc_memchr("hello".bytes(), 108, 5) equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds byte within n bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memchr("hello".bytes(), 108, 5)).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when byte not in first n

- Verify: returns -1 when byte not in first n
   - Expected: libc_memchr("hello".bytes(), 122, 5) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when byte not in first n")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memchr("hello".bytes(), 122, 5)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### respects n limit

- Verify: respects n limit
   - Expected: libc_memchr("hello".bytes(), 111, 3) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: respects n limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memchr("hello".bytes(), 111, 3)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles n=0

- Verify: handles n=0
   - Expected: libc_memchr("hello".bytes(), 104, 0) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles n=0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memchr("hello".bytes(), 104, 0)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds first occurrence

- Verify: finds first occurrence
   - Expected: libc_memchr("aabaa".bytes(), 97, 5) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds first occurrence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memchr("aabaa".bytes(), 97, 5)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### memrchr

#### finds last byte within n bytes

- Verify: finds last byte within n bytes
   - Expected: libc_memrchr("hello".bytes(), 108, 5) equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds last byte within n bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memrchr("hello".bytes(), 108, 5)).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when byte not found

- Verify: returns -1 when byte not found
   - Expected: libc_memrchr("hello".bytes(), 122, 5) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when byte not found")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memrchr("hello".bytes(), 122, 5)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### respects n limit

- Verify: respects n limit
   - Expected: libc_memrchr("hello".bytes(), 111, 3) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: respects n limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memrchr("hello".bytes(), 111, 3)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles n=0

- Verify: handles n=0
   - Expected: libc_memrchr("hello".bytes(), 104, 0) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles n=0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memrchr("hello".bytes(), 104, 0)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### finds last occurrence

- Verify: finds last occurrence
   - Expected: libc_memrchr("aabaa".bytes(), 97, 5) equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: finds last occurrence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_memrchr("aabaa".bytes(), 97, 5)).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strcasecmp

#### compares case-insensitively as equal

- Verify: compares case-insensitively as equal
   - Expected: libc_strcasecmp("Hello".bytes(), "hello".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: libc_strcasecmp("ABC".bytes(), "abc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: compares case-insensitively as equal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcasecmp("Hello".bytes(), "hello".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(libc_strcasecmp("ABC".bytes(), "abc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when a < b

- Verify: returns -1 when a < b
   - Expected: libc_strcasecmp("abc".bytes(), "abd".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when a < b")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcasecmp("abc".bytes(), "abd".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 1 when a > b

- Verify: returns 1 when a > b
   - Expected: libc_strcasecmp("abd".bytes(), "abc".bytes()) equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns 1 when a > b")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcasecmp("abd".bytes(), "abc".bytes())).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles different lengths

- Verify: handles different lengths
   - Expected: libc_strcasecmp("ab".bytes(), "abc".bytes()) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles different lengths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcasecmp("ab".bytes(), "abc".bytes())).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### ignores case in comparison

- Verify: ignores case in comparison
   - Expected: libc_strcasecmp("AbC".bytes(), "aBc".bytes()) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: ignores case in comparison")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strcasecmp("AbC".bytes(), "aBc".bytes())).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strncasecmp

#### compares first n bytes case-insensitively

- Verify: compares first n bytes case-insensitively
   - Expected: libc_strncasecmp("Hello World".bytes(), "hello earth".bytes(), 5) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: compares first n bytes case-insensitively")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncasecmp("Hello World".bytes(), "hello earth".bytes(), 5)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### respects n limit

- Verify: respects n limit
   - Expected: libc_strncasecmp("ABC".bytes(), "ABX".bytes(), 2) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: respects n limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncasecmp("ABC".bytes(), "ABX".bytes(), 2)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns -1 when a < b within n

- Verify: returns -1 when a < b within n
   - Expected: libc_strncasecmp("abc".bytes(), "abd".bytes(), 3) equals `-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns -1 when a < b within n")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncasecmp("abc".bytes(), "abd".bytes(), 3)).to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns 0 when n is 0

- Verify: returns 0 when n is 0
   - Expected: libc_strncasecmp("abc".bytes(), "xyz".bytes(), 0) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns 0 when n is 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncasecmp("abc".bytes(), "xyz".bytes(), 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles case in comparison

- Verify: handles case in comparison
   - Expected: libc_strncasecmp("AbC".bytes(), "aBd".bytes(), 2) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles case in comparison")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strncasecmp("AbC".bytes(), "aBd".bytes(), 2)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### strerror

#### returns messages for standard errno values

- Verify: returns messages for standard errno values
   - Expected: libc_strerror(0) equals `Success`
   - Expected: libc_strerror(1) equals `Operation not permitted`
   - Expected: libc_strerror(2) equals `No such file or directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns messages for standard errno values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strerror(0)).to_equal("Success")
expect(libc_strerror(1)).to_equal("Operation not permitted")
expect(libc_strerror(2)).to_equal("No such file or directory")
```

</details>

#### returns Unknown error for unmapped values

- Verify: returns Unknown error for unmapped values
   - Expected: libc_strerror(999) equals `Unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns Unknown error for unmapped values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strerror(999)).to_equal("Unknown error")
```

</details>

#### handles EPERM (1) and ENOENT (2)

- Verify: handles EPERM (1) and ENOENT (2)
   - Expected: libc_strerror(1) equals `Operation not permitted`
   - Expected: libc_strerror(2) equals `No such file or directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles EPERM (1) and ENOENT (2)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strerror(1)).to_equal("Operation not permitted")
expect(libc_strerror(2)).to_equal("No such file or directory")
```

</details>

#### handles ENOMEM (12)

- Verify: handles ENOMEM (12)
   - Expected: libc_strerror(12) equals `Out of memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles ENOMEM (12)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strerror(12)).to_equal("Out of memory")
```

</details>

#### handles EACCES (13)

- Verify: handles EACCES (13)
   - Expected: libc_strerror(13) equals `Permission denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles EACCES (13)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(libc_strerror(13)).to_equal("Permission denied")
```

</details>

### strtok_r

#### tokenizes simple delimited string

- Verify: tokenizes simple delimited string
   - Expected: tok1.found is true
   - Expected: tok1.tok_start equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok1.tok_end equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok2.found is true
   - Expected: tok2.tok_start equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok2.tok_end equals `7)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok3.found is true
   - Expected: tok3.tok_start equals `8)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok3.tok_end equals `11)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: tokenizes simple delimited string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok1 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), 0)
expect(tok1.found).to_equal(true)
expect(tok1.tok_start).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok1.tok_end).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val tok2 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), tok1.nextpos)
expect(tok2.found).to_equal(true)
expect(tok2.tok_start).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok2.tok_end).to_equal(7)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val tok3 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), tok2.nextpos)
expect(tok3.found).to_equal(true)
expect(tok3.tok_start).to_equal(8)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok3.tok_end).to_equal(11)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns found=false when exhausted

- Verify: returns found=false when exhausted
   - Expected: tok2.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns found=false when exhausted")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok = libc_strtok_r("abc".bytes(), ",".bytes(), 0)
val tok2 = libc_strtok_r("abc".bytes(), ",".bytes(), tok.nextpos)
expect(tok2.found).to_equal(false)
```

</details>

#### handles multiple delimiters

- Verify: handles multiple delimiters
   - Expected: tok1.tok_start equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok1.tok_end equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok2.tok_start equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok2.tok_end equals `4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles multiple delimiters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok1 = libc_strtok_r("a,;b,;c".bytes(), ",;".bytes(), 0)
expect(tok1.tok_start).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok1.tok_end).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val tok2 = libc_strtok_r("a,;b,;c".bytes(), ",;".bytes(), tok1.nextpos)
expect(tok2.tok_start).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok2.tok_end).to_equal(4)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### handles leading delimiters

- Verify: handles leading delimiters
   - Expected: tok.tok_start equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok.tok_end equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles leading delimiters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok = libc_strtok_r(",,abc".bytes(), ",".bytes(), 0)
expect(tok.tok_start).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok.tok_end).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### returns found=false for empty string

- Verify: returns found=false for empty string
   - Expected: tok.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: returns found=false for empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok = libc_strtok_r("".bytes(), ",".bytes(), 0)
expect(tok.found).to_equal(false)
```

</details>

#### handles a trailing delimiter (no empty final token)

- Verify: handles a trailing delimiter (no empty final token)
   - Expected: tok1.found is true
   - Expected: tok1.tok_start equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok1.tok_end equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: tok2.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-simpleos-libc-musl-search
# @req: REQ-OS-LIBC_LIBC_STRING_SEARCH-001
step("Verify: handles a trailing delimiter (no empty final token)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tok1 = libc_strtok_r("abc,".bytes(), ",".bytes(), 0)
expect(tok1.found).to_equal(true)
expect(tok1.tok_start).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(tok1.tok_end).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val tok2 = libc_strtok_r("abc,".bytes(), ",".bytes(), tok1.nextpos)
expect(tok2.found).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b4e3abe3aa871ba9f759ec5b252aac01e3a39e4b023a7bc47ec132fda75b6c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b4e3abe3aa871ba9f759ec5b252aac01e3a39e4b023a7bc47ec132fda75b6c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b4e3abe3aa871ba9f759ec5b252aac01e3a39e4b023a7bc47ec132fda75b6c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_string_search_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_search_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_string_search_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_string_search_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_search_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

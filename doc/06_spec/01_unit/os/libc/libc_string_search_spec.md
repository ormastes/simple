# Libc String Search Specification

> Tests covering SimpleOS libc — musl-shaped string search / span / tokenize / compare, strstr, strspn, strcspn, strpbrk, memchr, memrchr, strcasecmp, strncasecmp, strerror, strtok_r.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc String Search Specification

## Scenarios

### SimpleOS libc — musl-shaped string search / span / tokenize / compare

### strstr

#### finds substring at start

- finds substring at start
   - Expected: libc_strstr("hello world".bytes(), "hello".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds substring at start")
expect(libc_strstr("hello world".bytes(), "hello".bytes())).to_equal(0)
```

</details>

#### finds substring in middle

- finds substring in middle
   - Expected: libc_strstr("hello world".bytes(), "world".bytes()) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds substring in middle")
expect(libc_strstr("hello world".bytes(), "world".bytes())).to_equal(6)
```

</details>

#### returns -1 when not found

- returns -1 when not found
   - Expected: libc_strstr("hello world".bytes(), "xyz".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when not found")
expect(libc_strstr("hello world".bytes(), "xyz".bytes())).to_equal(-1)
```

</details>

#### returns 0 for empty needle

- returns 0 for empty needle
   - Expected: libc_strstr("hello".bytes(), "".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 for empty needle")
expect(libc_strstr("hello".bytes(), "".bytes())).to_equal(0)
```

</details>

#### returns -1 when needle longer than haystack

- returns -1 when needle longer than haystack
   - Expected: libc_strstr("hi".bytes(), "hello".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when needle longer than haystack")
expect(libc_strstr("hi".bytes(), "hello".bytes())).to_equal(-1)
```

</details>

### strspn

#### counts leading accepted bytes

- counts leading accepted bytes
   - Expected: libc_strspn("abc123xyz".bytes(), "abc".bytes()) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("counts leading accepted bytes")
expect(libc_strspn("abc123xyz".bytes(), "abc".bytes())).to_equal(3)
```

</details>

#### returns 0 when first byte not in accept

- returns 0 when first byte not in accept
   - Expected: libc_strspn("123abc".bytes(), "abc".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 when first byte not in accept")
expect(libc_strspn("123abc".bytes(), "abc".bytes())).to_equal(0)
```

</details>

#### returns full length when all bytes accepted

- returns full length when all bytes accepted
   - Expected: libc_strspn("aabbcc".bytes(), "abc".bytes()) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns full length when all bytes accepted")
expect(libc_strspn("aabbcc".bytes(), "abc".bytes())).to_equal(6)
```

</details>

#### handles empty string

- handles empty string
   - Expected: libc_strspn("".bytes(), "abc".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty string")
expect(libc_strspn("".bytes(), "abc".bytes())).to_equal(0)
```

</details>

#### handles empty accept

- handles empty accept
   - Expected: libc_strspn("abc".bytes(), "".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty accept")
expect(libc_strspn("abc".bytes(), "".bytes())).to_equal(0)
```

</details>

### strcspn

#### counts until first rejected byte

- counts until first rejected byte
   - Expected: libc_strcspn("abc123xyz".bytes(), "123".bytes()) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("counts until first rejected byte")
expect(libc_strcspn("abc123xyz".bytes(), "123".bytes())).to_equal(3)
```

</details>

#### returns full length when no rejected bytes

- returns full length when no rejected bytes
   - Expected: libc_strcspn("abcxyz".bytes(), "123".bytes()) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns full length when no rejected bytes")
expect(libc_strcspn("abcxyz".bytes(), "123".bytes())).to_equal(6)
```

</details>

#### returns 0 when first byte is rejected

- returns 0 when first byte is rejected
   - Expected: libc_strcspn("123abc".bytes(), "123".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 when first byte is rejected")
expect(libc_strcspn("123abc".bytes(), "123".bytes())).to_equal(0)
```

</details>

#### handles empty string

- handles empty string
   - Expected: libc_strcspn("".bytes(), "123".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty string")
expect(libc_strcspn("".bytes(), "123".bytes())).to_equal(0)
```

</details>

#### handles empty reject

- handles empty reject
   - Expected: libc_strcspn("abc".bytes(), "".bytes()) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty reject")
expect(libc_strcspn("abc".bytes(), "".bytes())).to_equal(3)
```

</details>

### strpbrk

#### finds first byte from accept set

- finds first byte from accept set
   - Expected: libc_strpbrk("hello world".bytes(), "ol".bytes()) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds first byte from accept set")
expect(libc_strpbrk("hello world".bytes(), "ol".bytes())).to_equal(2)
```

</details>

#### returns -1 when no byte from accept found

- returns -1 when no byte from accept found
   - Expected: libc_strpbrk("hello world".bytes(), "xyz".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when no byte from accept found")
expect(libc_strpbrk("hello world".bytes(), "xyz".bytes())).to_equal(-1)
```

</details>

#### finds first matching position

- finds first matching position
   - Expected: libc_strpbrk("abc123def".bytes(), "123".bytes()) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds first matching position")
expect(libc_strpbrk("abc123def".bytes(), "123".bytes())).to_equal(3)
```

</details>

#### handles empty string

- handles empty string
   - Expected: libc_strpbrk("".bytes(), "abc".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty string")
expect(libc_strpbrk("".bytes(), "abc".bytes())).to_equal(-1)
```

</details>

#### handles empty accept

- handles empty accept
   - Expected: libc_strpbrk("abc".bytes(), "".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles empty accept")
expect(libc_strpbrk("abc".bytes(), "".bytes())).to_equal(-1)
```

</details>

### memchr

#### finds byte within n bytes

- finds byte within n bytes
   - Expected: libc_memchr("hello".bytes(), 108, 5) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds byte within n bytes")
expect(libc_memchr("hello".bytes(), 108, 5)).to_equal(2)
```

</details>

#### returns -1 when byte not in first n

- returns -1 when byte not in first n
   - Expected: libc_memchr("hello".bytes(), 122, 5) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when byte not in first n")
expect(libc_memchr("hello".bytes(), 122, 5)).to_equal(-1)
```

</details>

#### respects n limit

- respects n limit
   - Expected: libc_memchr("hello".bytes(), 111, 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("respects n limit")
expect(libc_memchr("hello".bytes(), 111, 3)).to_equal(-1)
```

</details>

#### handles n=0

- handles n=0
   - Expected: libc_memchr("hello".bytes(), 104, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles n=0")
expect(libc_memchr("hello".bytes(), 104, 0)).to_equal(-1)
```

</details>

#### finds first occurrence

- finds first occurrence
   - Expected: libc_memchr("aabaa".bytes(), 97, 5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds first occurrence")
expect(libc_memchr("aabaa".bytes(), 97, 5)).to_equal(0)
```

</details>

### memrchr

#### finds last byte within n bytes

- finds last byte within n bytes
   - Expected: libc_memrchr("hello".bytes(), 108, 5) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds last byte within n bytes")
expect(libc_memrchr("hello".bytes(), 108, 5)).to_equal(3)
```

</details>

#### returns -1 when byte not found

- returns -1 when byte not found
   - Expected: libc_memrchr("hello".bytes(), 122, 5) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when byte not found")
expect(libc_memrchr("hello".bytes(), 122, 5)).to_equal(-1)
```

</details>

#### respects n limit

- respects n limit
   - Expected: libc_memrchr("hello".bytes(), 111, 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("respects n limit")
expect(libc_memrchr("hello".bytes(), 111, 3)).to_equal(-1)
```

</details>

#### handles n=0

- handles n=0
   - Expected: libc_memrchr("hello".bytes(), 104, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles n=0")
expect(libc_memrchr("hello".bytes(), 104, 0)).to_equal(-1)
```

</details>

#### finds last occurrence

- finds last occurrence
   - Expected: libc_memrchr("aabaa".bytes(), 97, 5) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("finds last occurrence")
expect(libc_memrchr("aabaa".bytes(), 97, 5)).to_equal(4)
```

</details>

### strcasecmp

#### compares case-insensitively as equal

- compares case-insensitively as equal
   - Expected: libc_strcasecmp("Hello".bytes(), "hello".bytes()) equals `0`
   - Expected: libc_strcasecmp("ABC".bytes(), "abc".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("compares case-insensitively as equal")
expect(libc_strcasecmp("Hello".bytes(), "hello".bytes())).to_equal(0)
expect(libc_strcasecmp("ABC".bytes(), "abc".bytes())).to_equal(0)
```

</details>

#### returns -1 when a < b

- returns -1 when a < b
   - Expected: libc_strcasecmp("abc".bytes(), "abd".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when a < b")
expect(libc_strcasecmp("abc".bytes(), "abd".bytes())).to_equal(-1)
```

</details>

#### returns 1 when a > b

- returns 1 when a > b
   - Expected: libc_strcasecmp("abd".bytes(), "abc".bytes()) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 1 when a > b")
expect(libc_strcasecmp("abd".bytes(), "abc".bytes())).to_equal(1)
```

</details>

#### handles different lengths

- handles different lengths
   - Expected: libc_strcasecmp("ab".bytes(), "abc".bytes()) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles different lengths")
expect(libc_strcasecmp("ab".bytes(), "abc".bytes())).to_equal(-1)
```

</details>

#### ignores case in comparison

- ignores case in comparison
   - Expected: libc_strcasecmp("AbC".bytes(), "aBc".bytes()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("ignores case in comparison")
expect(libc_strcasecmp("AbC".bytes(), "aBc".bytes())).to_equal(0)
```

</details>

### strncasecmp

#### compares first n bytes case-insensitively

- compares first n bytes case-insensitively
   - Expected: libc_strncasecmp("Hello World".bytes(), "hello earth".bytes(), 5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("compares first n bytes case-insensitively")
expect(libc_strncasecmp("Hello World".bytes(), "hello earth".bytes(), 5)).to_equal(0)
```

</details>

#### respects n limit

- respects n limit
   - Expected: libc_strncasecmp("ABC".bytes(), "ABX".bytes(), 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("respects n limit")
expect(libc_strncasecmp("ABC".bytes(), "ABX".bytes(), 2)).to_equal(0)
```

</details>

#### returns -1 when a < b within n

- returns -1 when a < b within n
   - Expected: libc_strncasecmp("abc".bytes(), "abd".bytes(), 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns -1 when a < b within n")
expect(libc_strncasecmp("abc".bytes(), "abd".bytes(), 3)).to_equal(-1)
```

</details>

#### returns 0 when n is 0

- returns 0 when n is 0
   - Expected: libc_strncasecmp("abc".bytes(), "xyz".bytes(), 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns 0 when n is 0")
expect(libc_strncasecmp("abc".bytes(), "xyz".bytes(), 0)).to_equal(0)
```

</details>

#### handles case in comparison

- handles case in comparison
   - Expected: libc_strncasecmp("AbC".bytes(), "aBd".bytes(), 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles case in comparison")
expect(libc_strncasecmp("AbC".bytes(), "aBd".bytes(), 2)).to_equal(0)
```

</details>

### strerror

#### returns messages for standard errno values

- returns messages for standard errno values
   - Expected: libc_strerror(0) equals `Success`
   - Expected: libc_strerror(1) equals `Operation not permitted`
   - Expected: libc_strerror(2) equals `No such file or directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns messages for standard errno values")
expect(libc_strerror(0)).to_equal("Success")
expect(libc_strerror(1)).to_equal("Operation not permitted")
expect(libc_strerror(2)).to_equal("No such file or directory")
```

</details>

#### returns Unknown error for unmapped values

- returns Unknown error for unmapped values
   - Expected: libc_strerror(999) equals `Unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns Unknown error for unmapped values")
expect(libc_strerror(999)).to_equal("Unknown error")
```

</details>

#### handles EPERM (1) and ENOENT (2)

- handles EPERM (1) and ENOENT (2)
   - Expected: libc_strerror(1) equals `Operation not permitted`
   - Expected: libc_strerror(2) equals `No such file or directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles EPERM (1) and ENOENT (2)")
expect(libc_strerror(1)).to_equal("Operation not permitted")
expect(libc_strerror(2)).to_equal("No such file or directory")
```

</details>

#### handles ENOMEM (12)

- handles ENOMEM (12)
   - Expected: libc_strerror(12) equals `Out of memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles ENOMEM (12)")
expect(libc_strerror(12)).to_equal("Out of memory")
```

</details>

#### handles EACCES (13)

- handles EACCES (13)
   - Expected: libc_strerror(13) equals `Permission denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles EACCES (13)")
expect(libc_strerror(13)).to_equal("Permission denied")
```

</details>

### strtok_r

#### tokenizes simple delimited string

- tokenizes simple delimited string
   - Expected: tok1.found is true
   - Expected: tok1.tok_start equals `0`
   - Expected: tok1.tok_end equals `3`
   - Expected: tok2.found is true
   - Expected: tok2.tok_start equals `4`
   - Expected: tok2.tok_end equals `7`
   - Expected: tok3.found is true
   - Expected: tok3.tok_start equals `8`
   - Expected: tok3.tok_end equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("tokenizes simple delimited string")
val tok1 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), 0)
expect(tok1.found).to_equal(true)
expect(tok1.tok_start).to_equal(0)
expect(tok1.tok_end).to_equal(3)

val tok2 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), tok1.nextpos)
expect(tok2.found).to_equal(true)
expect(tok2.tok_start).to_equal(4)
expect(tok2.tok_end).to_equal(7)

val tok3 = libc_strtok_r("abc,def,ghi".bytes(), ",".bytes(), tok2.nextpos)
expect(tok3.found).to_equal(true)
expect(tok3.tok_start).to_equal(8)
expect(tok3.tok_end).to_equal(11)
```

</details>

#### returns found=false when exhausted

- returns found=false when exhausted
   - Expected: tok2.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns found=false when exhausted")
val tok = libc_strtok_r("abc".bytes(), ",".bytes(), 0)
val tok2 = libc_strtok_r("abc".bytes(), ",".bytes(), tok.nextpos)
expect(tok2.found).to_equal(false)
```

</details>

#### handles multiple delimiters

- handles multiple delimiters
   - Expected: tok1.tok_start equals `0`
   - Expected: tok1.tok_end equals `1`
   - Expected: tok2.tok_start equals `3`
   - Expected: tok2.tok_end equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles multiple delimiters")
val tok1 = libc_strtok_r("a,;b,;c".bytes(), ",;".bytes(), 0)
expect(tok1.tok_start).to_equal(0)
expect(tok1.tok_end).to_equal(1)

val tok2 = libc_strtok_r("a,;b,;c".bytes(), ",;".bytes(), tok1.nextpos)
expect(tok2.tok_start).to_equal(3)
expect(tok2.tok_end).to_equal(4)
```

</details>

#### handles leading delimiters

- handles leading delimiters
   - Expected: tok.tok_start equals `2`
   - Expected: tok.tok_end equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles leading delimiters")
val tok = libc_strtok_r(",,abc".bytes(), ",".bytes(), 0)
expect(tok.tok_start).to_equal(2)
expect(tok.tok_end).to_equal(5)
```

</details>

#### returns found=false for empty string

- returns found=false for empty string
   - Expected: tok.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns found=false for empty string")
val tok = libc_strtok_r("".bytes(), ",".bytes(), 0)
expect(tok.found).to_equal(false)
```

</details>

#### handles a trailing delimiter (no empty final token)

- handles a trailing delimiter (no empty final token)
   - Expected: tok1.found is true
   - Expected: tok1.tok_start equals `0`
   - Expected: tok1.tok_end equals `3`
   - Expected: tok2.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("handles a trailing delimiter (no empty final token)")
val tok1 = libc_strtok_r("abc,".bytes(), ",".bytes(), 0)
expect(tok1.found).to_equal(true)
expect(tok1.tok_start).to_equal(0)
expect(tok1.tok_end).to_equal(3)

val tok2 = libc_strtok_r("abc,".bytes(), ",".bytes(), tok1.nextpos)
expect(tok2.found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_string_search_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS libc — musl-shaped string search / span / tokenize / compare, strstr, strspn, strcspn, strpbrk, memchr, memrchr, strcasecmp, strncasecmp, strerror, strtok_r.
- SimpleOS libc — musl-shaped string search / span / tokenize / compare
- strstr
- strspn
- strcspn
- strpbrk
- memchr
- memrchr
- strcasecmp
- strncasecmp
- strerror
- strtok_r

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-simpleos-libc-musl-search`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf763c8fde816cd2c6a3a35f9e445a01ec8ad4d015b0f904169568cc934d521d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf763c8fde816cd2c6a3a35f9e445a01ec8ad4d015b0f904169568cc934d521d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf763c8fde816cd2c6a3a35f9e445a01ec8ad4d015b0f904169568cc934d521d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_string_search_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_string_search_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_string_search_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_string_search_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_string_search_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 55 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/libc/libc_string_search_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_string_search_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds substring at start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_search_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds substring in middle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/libc/libc_string_search_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 when not found' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

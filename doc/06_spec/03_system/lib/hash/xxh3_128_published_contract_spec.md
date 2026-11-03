# xxh3_128_published_contract_spec

**Status: AUTHORED_UNRUN.** This is an authored manual, not spipe-docgen output. No scenario has qualified execution evidence; no zero-stub or coverage claim is made.

Executable: `test/03_system/lib/hash/xxh3_128_published_contract_spec.spl`. SHA-256: `aa5228e2ec845820700c1981d54c6555e8689e4e72220d72ca18651077dd0a2d`.

## Workflow

1. Load the published vector. Inputs repeat binary bytes `00 7f 80 ff`; custom secrets use `(13*i+5) mod 256`.
2. Hash through the production API. Exercise the pure-Simple kernel or its public streaming wrapper.
3. Compare the expected digest. Exact low/high words or canonical text are independent xxHash v0.8.3 reference results; invalid secrets must return an empty array.

## Evidence and limitations

Oracle source and requirement mapping: `doc/03_plan/sys_test/xxh3_128_spec_boundaries_20261103.md`. Evidence class: independent-reference-vector (oracle executed); pure-Simple production execution UNRUN. Capture declarations describe intended binary evidence, not existing capture files. An observation alone cannot pass: each scenario has exact assertions.

After an admitted runtime is available, execute the spec and run `simple spipe-docgen test/03_system/lib/hash/xxh3_128_published_contract_spec.spl --output doc/06_spec --no-index`; require genuine zero-stub output and replace this authored provenance only from retained results.

<details><summary>Executable SSpec</summary>

```simple
"""
## Purpose and audience
Published XXH3-128 binary representation and secret contract for library maintainers comparing pure-Simple behavior to xxHash v0.8.3.
## Operator workflow
Run this spec with an admitted native runner, --native-backend=llvm --assert-ran --no-cache.
## Compatibility and limitations
AUTHORED_UNRUN. No admitted runtime was available; branch coverage is UNMEASURED.
XXH3 is non-cryptographic. This tests the production API, not the upstream C library.
## Verification guidance and troubleshooting
Independent oracle: xxHash e626a72bc2321cd320e953a0ccf1584cad60f363, xxhash.h.
Input repeats 00 7f 80 ff; secret byte i is (13*i+5) mod 256.
Retain actual test counts and branch denominators before claiming coverage.
"""
# codex-system-test
# Lifecycle: doc/03_plan/sys_test/xxh3_128_spec_boundaries_20261103.md
# @manual_section: XXH3-128 published contract
# @evidence-display: links
use std.spec.*
use std.common.hash.xxh3.{xxh3_128, xxh3_128_hex, xxh3_128_with_secret}

# @inline
fn binary_input(n: i64) -> [u8]:
    val pattern: [u8] = [0u8, 127u8, 128u8, 255u8]
    var data: [u8] = []
    for i in 0..n:
        data.push(pattern[i % 4])
    data

# @inline
fn secret_input(n: i64) -> [u8]:
    var data: [u8] = []
    for i in 0..n:
        data.push(((13 * i + 5) % 256).to_u8())
    data

describe "XXH3-128 published binary contract":
    it "should preserve binary octets and canonical high-word-first serialization":
        # @req REQ-HASH-XXH3-005
        # @capture(binary): 00 7f 80 ff and exact canonical 128-bit output
        step("Load the published vector")
        val input: [u8] = [0u8, 127u8, 128u8, 255u8]
        step("Hash through the production API")
        val digest = xxh3_128(input)
        val canonical = xxh3_128_hex(input)
        step("Compare the expected digest")
        expect(digest.low).to_equal(0x122a2693be716e1bu64) # oracle: pinned upstream default vector
        expect(digest.high).to_equal(0xa7dde2cbf750eed6u64) # oracle: pinned upstream default vector
        expect(canonical).to_equal("a7dde2cbf750eed6122a2693be716e1b") # oracle: XXH128 canonical high word then low word

    it "should accept a minimum secret at its first complete long-input block":
        # @req REQ-HASH-XXH3-004
        # @req REQ-HASH-XXH3-003
        # @capture(binary): exact minimum-secret 576-byte digest
        step("Load the published vector")
        val input = binary_input(576)
        val secret = secret_input(136)
        step("Hash through the production API")
        val digest = xxh3_128_with_secret(input, secret)
        step("Compare the expected digest")
        expect(digest).to_equal([0xd9e7cd4086b97da8u64, 0xa1a762c499e1705cu64]) # oracle: pinned upstream withSecret vector

    it "should reject a secret one byte below the published minimum":
        # @req REQ-HASH-XXH3-004
        # @capture(binary): invalid-secret result contains no digest words
        step("Load the published vector")
        val input = binary_input(576)
        val secret = secret_input(135)
        step("Hash through the production API")
        val digest = xxh3_128_with_secret(input, secret)
        step("Compare the expected digest")
        expect(digest).to_equal([]) # oracle: local fail-closed contract for upstream secret precondition
```
</details>

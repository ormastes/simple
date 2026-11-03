# gxhash128_short_spec

**AUTHORED_UNRUN.** Authored manual; no Simple execution, docgen, scorer or branch-coverage result. Rust reference oracle execution does not qualify this product.

Executable: `test/01_unit/lib/hash/gxhash128_short_spec.spl`. SHA256: `c5abb4b42f9f1fe212d63400acf45d67be45f2ba36d6822201ca22765c391226`.

Pin: upstream gxhash4.0.0, commit5e00a497289d1c2f0ae07e5f956654c77f1cfc09. Full128 reference corpus SHA256: d23002a7b9282b0879b3327aef18826aa27d67578eb30d4e77483739c2e71767. No self-generated goldens.

Scenario flow: load the independent vector, call the actual production API, compare complete bytes. Binary evidence is not captured until an admitted run.

- should match all16 bytes at length 0 seed 0
- should match all16 bytes at length 0 seed 42
- should match all16 bytes at length 0 seed -1
- should match all16 bytes at length 0 seed -9223372036854775808
- should match all16 bytes at length 1 seed 0
- should match all16 bytes at length 1 seed 42
- should match all16 bytes at length 1 seed -1
- should match all16 bytes at length 1 seed -9223372036854775808
- should match all16 bytes at length 2 seed 0
- should match all16 bytes at length 2 seed 42
- should match all16 bytes at length 2 seed -1
- should match all16 bytes at length 2 seed -9223372036854775808
- should match all16 bytes at length 7 seed 0
- should match all16 bytes at length 7 seed 42
- should match all16 bytes at length 7 seed -1
- should match all16 bytes at length 7 seed -9223372036854775808
- should match all16 bytes at length 15 seed 0
- should match all16 bytes at length 15 seed 42
- should match all16 bytes at length 15 seed -1
- should match all16 bytes at length 15 seed -9223372036854775808
- should match all16 bytes at length 16 seed 0
- should match all16 bytes at length 16 seed 42
- should match all16 bytes at length 16 seed -1
- should match all16 bytes at length 16 seed -9223372036854775808

<details><summary>Executable SSpec (authored, not executed)</summary>

```simple
# gxHash4.0.0 independent full128 KATs. Simple status: AUTHORED_UNRUN.
# Oracle: upstream5e00a497289d1c2f0ae07e5f956654c77f1cfc09 Rust AES/SSE2.
use std.spec.step
use std.spipe.*
use std.common.hash.gxhash.{gxhash128}

fn gxhash_pattern(length: i64) -> [u8]:
    var data: [u8] = []
    var i: i64 = 0
    while i < length:
        data.push(((i * 31 + 7) % 256).to_u8())
        i = i + 1
    data

describe "gxHash128 short reference boundary cases":
    it "should match all16 bytes at length 0 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(0)
        val expected: [u8] = [0x7eu8, 0x1eu8, 0x3cu8, 0x32u8, 0xd6u8, 0x74u8, 0x2au8, 0x9eu8, 0x5du8, 0x8au8, 0xcdu8, 0x92u8, 0xeau8, 0x89u8, 0xabu8, 0x59u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 0 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(0)
        val expected: [u8] = [0x11u8, 0xc8u8, 0x02u8, 0x0bu8, 0xbbu8, 0xe4u8, 0x38u8, 0xd6u8, 0x8fu8, 0x3bu8, 0xd1u8, 0x93u8, 0x57u8, 0x29u8, 0x98u8, 0x53u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 0 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(0)
        val expected: [u8] = [0x02u8, 0x29u8, 0x16u8, 0xd1u8, 0x92u8, 0x41u8, 0x13u8, 0xedu8, 0x1fu8, 0x83u8, 0xbdu8, 0x56u8, 0x69u8, 0x20u8, 0x80u8, 0x10u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 0 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(0)
        val expected: [u8] = [0x82u8, 0xd1u8, 0x51u8, 0x19u8, 0x74u8, 0x15u8, 0x35u8, 0x5eu8, 0x30u8, 0x9au8, 0x52u8, 0x6du8, 0xc5u8, 0xcbu8, 0xceu8, 0x9au8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 1 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(1)
        val expected: [u8] = [0x4au8, 0xd7u8, 0xc5u8, 0x06u8, 0x19u8, 0x4au8, 0x1du8, 0xbdu8, 0x2au8, 0xc9u8, 0x47u8, 0x6eu8, 0x38u8, 0xb0u8, 0xd0u8, 0xb6u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 1 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(1)
        val expected: [u8] = [0xb6u8, 0x71u8, 0xc3u8, 0xccu8, 0x40u8, 0x9cu8, 0x03u8, 0xfdu8, 0xb0u8, 0x8eu8, 0x67u8, 0xf4u8, 0x6eu8, 0x24u8, 0xcau8, 0xc4u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 1 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(1)
        val expected: [u8] = [0x97u8, 0x39u8, 0x36u8, 0xf5u8, 0x54u8, 0x5du8, 0xe1u8, 0x7eu8, 0xfdu8, 0x8du8, 0x91u8, 0x7eu8, 0x57u8, 0xc6u8, 0x3fu8, 0x24u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 1 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(1)
        val expected: [u8] = [0x45u8, 0xf4u8, 0x41u8, 0xabu8, 0x7du8, 0x5eu8, 0x94u8, 0xf4u8, 0xb6u8, 0x56u8, 0x9fu8, 0x36u8, 0xd2u8, 0xe2u8, 0x46u8, 0x41u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 2 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(2)
        val expected: [u8] = [0xa8u8, 0x21u8, 0xeeu8, 0x40u8, 0xd6u8, 0x85u8, 0xdfu8, 0xbbu8, 0x2fu8, 0x8fu8, 0x1eu8, 0xc1u8, 0xdeu8, 0x2cu8, 0xfcu8, 0x4cu8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 2 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(2)
        val expected: [u8] = [0x9au8, 0xb7u8, 0xc0u8, 0x33u8, 0x42u8, 0xf5u8, 0x53u8, 0x3au8, 0x9du8, 0xd9u8, 0xd5u8, 0x6du8, 0x10u8, 0xa9u8, 0x18u8, 0xfbu8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 2 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(2)
        val expected: [u8] = [0x73u8, 0x3fu8, 0xcdu8, 0x8du8, 0x17u8, 0xaau8, 0xccu8, 0x7du8, 0xd4u8, 0xcdu8, 0xebu8, 0x7du8, 0x8au8, 0xaeu8, 0xe4u8, 0x90u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 2 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(2)
        val expected: [u8] = [0x19u8, 0x03u8, 0xd3u8, 0x47u8, 0xbcu8, 0x8fu8, 0x9fu8, 0x53u8, 0x69u8, 0x3au8, 0x29u8, 0x9bu8, 0x51u8, 0x30u8, 0x76u8, 0xa8u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 7 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(7)
        val expected: [u8] = [0x24u8, 0x5cu8, 0x72u8, 0x0bu8, 0x7fu8, 0xfcu8, 0x52u8, 0x7bu8, 0x00u8, 0xf0u8, 0xf9u8, 0x43u8, 0x99u8, 0x54u8, 0xefu8, 0x84u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 7 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(7)
        val expected: [u8] = [0x23u8, 0x13u8, 0xb9u8, 0x43u8, 0xc6u8, 0x24u8, 0xf6u8, 0x3au8, 0xbcu8, 0x36u8, 0x2fu8, 0x8du8, 0x21u8, 0x94u8, 0x3fu8, 0xf8u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 7 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(7)
        val expected: [u8] = [0xd4u8, 0xbeu8, 0x94u8, 0xdbu8, 0x93u8, 0xdeu8, 0x5bu8, 0x3du8, 0x96u8, 0xcbu8, 0xc2u8, 0x84u8, 0xd7u8, 0x6fu8, 0x34u8, 0x9du8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 7 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(7)
        val expected: [u8] = [0x99u8, 0x96u8, 0x01u8, 0x44u8, 0x76u8, 0x23u8, 0x5du8, 0x93u8, 0xe2u8, 0x5cu8, 0x6bu8, 0xafu8, 0x5fu8, 0x14u8, 0x7cu8, 0x73u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 15 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(15)
        val expected: [u8] = [0x2fu8, 0xaau8, 0x0au8, 0x0bu8, 0x08u8, 0xacu8, 0x2cu8, 0x10u8, 0xf7u8, 0x1au8, 0xdau8, 0x9au8, 0x1du8, 0xcdu8, 0x97u8, 0xadu8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 15 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(15)
        val expected: [u8] = [0x4fu8, 0xd4u8, 0x34u8, 0xe1u8, 0x97u8, 0x42u8, 0x05u8, 0x62u8, 0xf5u8, 0xd5u8, 0xc6u8, 0xb7u8, 0x2cu8, 0x9bu8, 0xe6u8, 0xf5u8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 15 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(15)
        val expected: [u8] = [0x4du8, 0x71u8, 0x47u8, 0xdau8, 0x0du8, 0xb7u8, 0x68u8, 0x8eu8, 0x64u8, 0x1bu8, 0x72u8, 0x54u8, 0xdfu8, 0x76u8, 0x9du8, 0xa0u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 15 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(15)
        val expected: [u8] = [0x0au8, 0x59u8, 0x8cu8, 0xedu8, 0x6cu8, 0xbau8, 0xa5u8, 0x9cu8, 0xbfu8, 0x31u8, 0x4bu8, 0xc0u8, 0xaeu8, 0x35u8, 0x88u8, 0xd9u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 16 seed 0":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(16)
        val expected: [u8] = [0xe5u8, 0xadu8, 0x11u8, 0xc0u8, 0xb9u8, 0x40u8, 0x5du8, 0xe1u8, 0xb7u8, 0xe0u8, 0xa3u8, 0xadu8, 0xe8u8, 0x2au8, 0xc8u8, 0x4au8]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 16 seed 42":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(16)
        val expected: [u8] = [0x21u8, 0x5au8, 0xa2u8, 0x1eu8, 0x19u8, 0xd0u8, 0xc7u8, 0xffu8, 0x2fu8, 0x7cu8, 0x89u8, 0xdau8, 0x70u8, 0x86u8, 0xbfu8, 0x5du8]
        step("Hash through the production API")
        val actual = gxhash128(input, 42)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 16 seed -1":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(16)
        val expected: [u8] = [0x7au8, 0x94u8, 0xd0u8, 0x9eu8, 0x69u8, 0x6eu8, 0x01u8, 0x27u8, 0xceu8, 0x71u8, 0xacu8, 0x68u8, 0xc3u8, 0xf0u8, 0xa5u8, 0x7bu8]
        step("Hash through the production API")
        val actual = gxhash128(input, -1)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)

    it "should match all16 bytes at length 16 seed -9223372036854775808":
        # @req REQ-HASH-GXHASH-001
        step("Load the independent reference vector")
        val input = gxhash_pattern(16)
        val expected: [u8] = [0xfeu8, 0xe8u8, 0xc5u8, 0x3cu8, 0x5bu8, 0x7bu8, 0x6fu8, 0x42u8, 0x5au8, 0x99u8, 0x3du8, 0xbbu8, 0x0bu8, 0x2au8, 0x31u8, 0x97u8]
        step("Hash through the production API")
        val actual = gxhash128(input, -9223372036854775808)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)
```
</details>

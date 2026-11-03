# gxhash128_binary_spec

**AUTHORED_UNRUN.** Authored manual; no Simple execution, docgen, scorer or branch-coverage result. Rust reference oracle execution does not qualify this product.

Executable: `test/02_integration/lib/hash/gxhash128_binary_spec.spl`. SHA256: `36b62280e2a947a42317375adbf77631a9733170e95fcb1f0cfb4823a2f2d43a`.

Pin: upstream gxhash4.0.0, commit5e00a497289d1c2f0ae07e5f956654c77f1cfc09. Full128 reference corpus SHA256: d23002a7b9282b0879b3327aef18826aa27d67578eb30d4e77483739c2e71767. No self-generated goldens.

Scenario flow: load the independent vector, call the actual production API, compare complete bytes. Binary evidence is not captured until an admitted run.

- should retain every binary byte and serialize the independent digest

<details><summary>Executable SSpec (authored, not executed)</summary>

```simple
# Byte construction -> public gxHash API -> byte persistence representation.
# Library integration only; no SCV provider integration is claimed. UNRUN.
use std.spec.step
use std.spipe.*
use std.common.hash.gxhash.{gxhash128}
use std.common.aes.utilities.{bytes_to_hex}

describe "gxHash128 binary input and serialization":
    it "should retain every binary byte and serialize the independent digest":
        # @req REQ-HASH-GXHASH-003
        step("Load the published vector")
        var input: [u8] = []
        var i: i64 = 0
        while i < 256:
            input.push(((i * 31 + 7) % 256).to_u8())
            i = i + 1
        # Odd multiplier visits every byte, including00/7f/80/ff.
        val before = input
        step("Hash through the production API")
        val digest = gxhash128(input, 42)
        var encoded: [i64] = []
        for byte in digest:
            encoded.push(byte.to_i64())
        step("Compare the expected digest")
        expect(bytes_to_hex(encoded)).to_equal("095b209a470d370043b9493a487d1c12")
        expect(input).to_equal(before)
        expect(digest.len()).to_equal(16)
```
</details>

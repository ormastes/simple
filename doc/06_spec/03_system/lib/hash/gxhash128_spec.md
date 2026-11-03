# gxhash128_spec

**AUTHORED_UNRUN.** Authored manual; no Simple execution, docgen, scorer or branch-coverage result. Rust reference oracle execution does not qualify this product.

Executable: `test/03_system/lib/hash/gxhash128_spec.spl`. SHA256: `53df240598fe8d4539f5a665d5a7e34340e0b2c1ed91a6212197afa9d518f130`.

Pin: upstream gxhash4.0.0, commit5e00a497289d1c2f0ae07e5f956654c77f1cfc09. Full128 reference corpus SHA256: d23002a7b9282b0879b3327aef18826aa27d67578eb30d4e77483739c2e71767. No self-generated goldens.

Scenario flow: load the independent vector, call the actual production API, compare complete bytes. Binary evidence is not captured until an admitted run.

- should match the pinned upstream Hello World128-bit vector

<details><summary>Executable SSpec (authored, not executed)</summary>

```simple
# gxHash1284.0.0 published output contract. AUTHORED_UNRUN.
# Historical paper rev1 (2023) explains design; pinned4.0.0 defines bytes.
# @evidence-display: links
use std.spec.step
use std.spipe.*
use std.common.hash.gxhash.{gxhash128}

describe "gxHash128 published one-shot digest":
    it "should match the pinned upstream Hello World128-bit vector":
        # @req REQ-HASH-GXHASH-001
        step("Load the published vector")
        val input: [u8] = [72,101,108,108,111,32,87,111,114,108,100]
        # Upstream u128 c270913193acccf4aa07094dea48fd62, serialized LE.
        val expected: [u8] = [0x62,0xfd,0x48,0xea,0x4d,0x09,0x07,0xaa,0xf4,0xcc,0xac,0x93,0x31,0x91,0x70,0xc2]
        step("Hash through the production API")
        val actual = gxhash128(input, 0)
        step("Compare the expected digest")
        expect(actual).to_equal(expected)
```
</details>

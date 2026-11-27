# gxhash_aes_round_spec

**AUTHORED_UNRUN.** Authored manual; no Simple execution, docgen, scorer or branch-coverage result. Rust reference oracle execution does not qualify this product.

Executable: `test/01_unit/lib/hash/gxhash_aes_round_spec.spl`. SHA256: `1dfb2d5e4a3ad525968d95171bfb74451a12946f7533834b3cd30ac324f97576`.

Pin: upstream gxhash4.0.0, commit5e00a497289d1c2f0ae07e5f956654c77f1cfc09. Full128 reference corpus SHA256: d23002a7b9282b0879b3327aef18826aa27d67578eb30d4e77483739c2e71767. No self-generated goldens.

Scenario flow: load the independent vector, call the actual production API, compare complete bytes. Binary evidence is not captured until an admitted run.

- should preserve Intel AESENC column ordering
- should omit MixColumns in the final AES round

<details><summary>Executable SSpec (authored, not executed)</summary>

```simple
# Independent x86 AESENC/AESENCLAST oracle; Simple AUTHORED_UNRUN.
use std.spec.step
use std.spipe.*
use std.common.aes.sbox.{aes_sbox}
use std.common.hash.gxhash.{_gx_round}

describe "gxHash portable AES round semantics":
    it "should preserve Intel AESENC column ordering":
        # @req REQ-HASH-GXHASH-002
        step("Load the independent AES round vector")
        val state: [u8] = [0,16,32,48,64,80,96,112,128,144,160,176,192,208,224,240]
        val key: [u8] = [0xd6,0xaa,0x74,0xfd,0xd2,0xaf,0x72,0xfa,0xda,0xa6,0x78,0xf1,0xd6,0xab,0x76,0xfe]
        step("Apply the production regular round")
        val actual = _gx_round(state, key, false, aes_sbox())
        step("Compare all round bytes")
        expect(actual).to_equal([0x89u8,0xd8,0x10,0xe8,0x85,0x5a,0xce,0x68,0x2d,0x18,0x43,0xd8,0xcb,0x12,0x8f,0xe4])

    it "should omit MixColumns in the final AES round":
        # @req REQ-HASH-GXHASH-002
        step("Load the independent AES round vector")
        val state: [u8] = [0,16,32,48,64,80,96,112,128,144,160,176,192,208,224,240]
        val key: [u8] = [0xd6,0xaa,0x74,0xfd,0xd2,0xaf,0x72,0xfa,0xda,0xa6,0x78,0xf1,0xd6,0xab,0x76,0xfe]
        step("Apply the production final round")
        val actual = _gx_round(state, key, true, aes_sbox())
        step("Compare all round bytes")
        expect(actual).to_equal([0xb5u8,0xf9,0x94,0x71,0xdb,0xcf,0x93,0xfe,0x17,0xd6,0xcf,0xa0,0x6c,0x61,0xa6,0x19])
```
</details>

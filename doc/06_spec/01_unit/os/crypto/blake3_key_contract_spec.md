# OS BLAKE3 key contract and boundaries

AUTHORED_UNRUN. Authored manual, not spipe-docgen output; no zero-stub or execution claim.

Spec SHA256 (LF canonical bytes): `4e2858989131d69da8769b50a732f31f052e683210ab13aebdb234ae0722b3ab`.
Official vector artifact SHA256: `dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624`.

The invalid-key scenarios require empty output for lengths 0,31,33 before word decoding. Positive scenarios call the actual OS owner with published hash, keyed, derive and XOF vectors. Load the published vector, hash through the production API, compare every expected byte. Branch coverage remains UNMEASURED. No run artifact exists.

<details><summary>Authored executable scenarios</summary>

```simple
"""
OS BLAKE3 key contract and missing tree boundaries.
Proof class: production owner; AUTHORED_UNRUN. No admitted runtime available.
Official vectors f55849f89cd85083c1c9daa2c5de20766f309c00:
SHA256 dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624.
These call os.crypto.blake3, not the separately tested common implementation.
"""
# codex-system-test
use std.spec.*
use os.crypto.blake3.{blake3, blake3_keyed, blake3_kdf, blake3_xof}

# @inline
fn load_blake3_vectors(n: i64) -> [u8]:
    var data: [u8] = []
    for i in 0..n:
        data.push((i % 251).to_u8())
    data

describe "OS BLAKE3 exact key length contract":
    it "should reject a 0-byte key before decoding any key words":
        # @req REQ-HASH-BLAKE3-003
        step("Construct an invalid key under the production API contract")
        val key = load_blake3_vectors(0)
        step("Hash through the production API")
        val digest = blake3_keyed(key, [0u8])
        step("Verify the invalid key produces no digest")
        expect(digest).to_equal([])

    it "should reject a 31-byte key before decoding any key words":
        # @req REQ-HASH-BLAKE3-003
        step("Construct an invalid key under the production API contract")
        val key = load_blake3_vectors(31)
        step("Hash through the production API")
        val digest = blake3_keyed(key, [0u8])
        step("Verify the invalid key produces no digest")
        expect(digest).to_equal([])

    it "should reject a 33-byte key before decoding any key words":
        # @req REQ-HASH-BLAKE3-003
        step("Construct an invalid key under the production API contract")
        val key = "whats the Elvish word for friend".bytes() + [0u8]
        step("Hash through the production API")
        val digest = blake3_keyed(key, [0u8])
        step("Verify the invalid key produces no digest")
        expect(digest).to_equal([])

describe "OS BLAKE3 independent published boundaries":
    it "should match official hash for 64 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-001
        step("Load the published vector")
        val data = load_blake3_vectors(64)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([78u8, 237u8, 113u8, 65u8, 234u8, 74u8, 92u8, 212u8, 183u8, 136u8, 96u8, 107u8, 210u8, 63u8, 70u8, 226u8, 18u8, 175u8, 156u8, 172u8, 235u8, 172u8, 220u8, 125u8, 31u8, 76u8, 109u8, 199u8, 242u8, 81u8, 27u8, 152u8])

    it "should match official hash for 65 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-001
        step("Load the published vector")
        val data = load_blake3_vectors(65)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([222u8, 30u8, 95u8, 160u8, 190u8, 112u8, 223u8, 109u8, 43u8, 232u8, 255u8, 253u8, 14u8, 153u8, 206u8, 170u8, 142u8, 182u8, 232u8, 201u8, 58u8, 99u8, 242u8, 216u8, 209u8, 195u8, 14u8, 203u8, 107u8, 38u8, 61u8, 238u8])

    it "should match official hash for 1023 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-001
        step("Load the published vector")
        val data = load_blake3_vectors(1023)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([16u8, 16u8, 137u8, 112u8, 238u8, 218u8, 62u8, 185u8, 50u8, 186u8, 172u8, 20u8, 40u8, 199u8, 162u8, 22u8, 59u8, 14u8, 146u8, 76u8, 154u8, 158u8, 37u8, 179u8, 91u8, 186u8, 114u8, 178u8, 143u8, 112u8, 189u8, 17u8])

    it "should match official hash for 1025 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-001
        step("Load the published vector")
        val data = load_blake3_vectors(1025)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([208u8, 2u8, 120u8, 174u8, 71u8, 235u8, 39u8, 179u8, 79u8, 174u8, 207u8, 103u8, 180u8, 254u8, 38u8, 63u8, 130u8, 213u8, 65u8, 41u8, 22u8, 193u8, 255u8, 217u8, 124u8, 140u8, 183u8, 251u8, 129u8, 75u8, 132u8, 68u8])

    it "should match official hash for 2049 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-002
        step("Load the published vector")
        val data = load_blake3_vectors(2049)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([95u8, 77u8, 114u8, 244u8, 13u8, 122u8, 95u8, 130u8, 177u8, 92u8, 162u8, 178u8, 228u8, 75u8, 29u8, 227u8, 194u8, 239u8, 134u8, 196u8, 38u8, 201u8, 92u8, 26u8, 240u8, 182u8, 135u8, 149u8, 34u8, 86u8, 48u8, 48u8])

    it "should match official hash for 3073 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-002
        step("Load the published vector")
        val data = load_blake3_vectors(3073)
        step("Hash through the production API")
        val digest = blake3(data)
        step("Compare the expected digest")
        expect(digest).to_equal([113u8, 36u8, 180u8, 149u8, 1u8, 1u8, 47u8, 129u8, 204u8, 127u8, 17u8, 202u8, 6u8, 158u8, 201u8, 34u8, 108u8, 236u8, 184u8, 162u8, 200u8, 80u8, 207u8, 230u8, 68u8, 227u8, 39u8, 210u8, 45u8, 62u8, 28u8, 211u8])

    it "should match official keyed_hash for 1025 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-003
        step("Load the published vector")
        val data = load_blake3_vectors(1025)
        step("Hash through the production API")
        val digest = blake3_keyed("whats the Elvish word for friend".bytes(), data)
        step("Compare the expected digest")
        expect(digest).to_equal([53u8, 125u8, 197u8, 93u8, 224u8, 199u8, 227u8, 130u8, 201u8, 0u8, 253u8, 110u8, 50u8, 10u8, 204u8, 4u8, 20u8, 107u8, 224u8, 29u8, 182u8, 168u8, 206u8, 114u8, 16u8, 183u8, 24u8, 155u8, 214u8, 100u8, 234u8, 105u8])

    it "should match official derive_key for 3073 input bytes and 32 output bytes":
        # @req REQ-HASH-BLAKE3-003
        step("Load the published vector")
        val data = load_blake3_vectors(3073)
        step("Hash through the production API")
        val digest = blake3_kdf("BLAKE3 2019-12-27 16:29:52 test vectors context".bytes(), data)
        step("Compare the expected digest")
        expect(digest).to_equal([114u8, 97u8, 60u8, 158u8, 201u8, 255u8, 126u8, 64u8, 248u8, 245u8, 193u8, 115u8, 120u8, 76u8, 83u8, 42u8, 216u8, 82u8, 232u8, 39u8, 219u8, 162u8, 191u8, 133u8, 178u8, 171u8, 75u8, 118u8, 247u8, 7u8, 144u8, 129u8])

    it "should match official hash for 3073 input bytes and 65 output bytes":
        # @req REQ-HASH-BLAKE3-004
        step("Load the published vector")
        val data = load_blake3_vectors(3073)
        step("Hash through the production API")
        val digest = blake3_xof(data, 65)
        step("Compare the expected digest")
        expect(digest).to_equal([113u8, 36u8, 180u8, 149u8, 1u8, 1u8, 47u8, 129u8, 204u8, 127u8, 17u8, 202u8, 6u8, 158u8, 201u8, 34u8, 108u8, 236u8, 184u8, 162u8, 200u8, 80u8, 207u8, 230u8, 68u8, 227u8, 39u8, 210u8, 45u8, 62u8, 28u8, 211u8, 154u8, 39u8, 174u8, 59u8, 121u8, 214u8, 141u8, 137u8, 218u8, 155u8, 242u8, 91u8, 194u8, 113u8, 57u8, 174u8, 101u8, 163u8, 36u8, 145u8, 138u8, 95u8, 155u8, 120u8, 40u8, 24u8, 30u8, 82u8, 207u8, 55u8, 60u8, 132u8, 243u8])
```
</details>

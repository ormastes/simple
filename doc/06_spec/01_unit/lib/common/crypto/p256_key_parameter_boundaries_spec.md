# p256_key_parameter_boundaries_spec

Status: **AUTHORED_UNRUN**. Branch coverage: **UNMEASURED**.

Authored companion; admitted execution and zero-stub spipe-docgen generation remain pending.

Executable: `test/01_unit/lib/common/crypto/p256_key_parameter_boundaries_spec.spl`

Spec SHA-256: `400b19c8d6649773515741ce8fd74a263f7cd82d7cc5264594367aa84ca8b85c`

Execution artifact SHA-256: absent. Proof class: production API assertions authored, not executed.

## Scenario flow

- REQ-TLS-ECDH-BOUNDARY-001: validate P-256 key parameters
- should reject 31 and 33 byte private scalars
  - Submit adjacent invalid scalar widths to public key derivation
- should reject a private scalar above the subgroup order
  - Submit the largest 256-bit value
- should distinguish an unreduced Y coordinate from curve membership
  - Keep X reduced and set Y to the largest 256-bit value

<details><summary>Executable SSpec</summary>

```simple
"""
# P-256 key agreement parameter boundaries
AUTHORED_UNRUN; branch coverage UNMEASURED. RFC 8446 section 4.2.8.2
requires peer point validation; this common API also checks private scalars.
Existing NIST CDH KATs cover successful derivation, X overflow, zero and n.
These cases cover the missing Y-bound and private-scalar width paths.
"""
use std.spec.*
use std.spec.step
use std.common.crypto.ecdh_p256.{p256_public_key, p256_ecdh_shared_secret}

fn p256_boundary_bytes(count: i64, byte: u8) -> [u8]:
    var output: [u8] = []
    var i: i64 = 0
    while i < count:
        output.push(byte)
        i = i + 1
    output

fn p256_boundary_error(result: Result<[u8], text>) -> text:
    match result:
        Ok(value):
            fail("Expected a malformed P-256 input error")
            "unexpected success"
        Err(error): error

fn p256_boundary_one() -> [u8]:
    var scalar = p256_boundary_bytes(31, 0u8)
    scalar.push(1u8)
    scalar

fn p256_boundary_large_y() -> [u8]:
    var point: [u8] = [4u8]
    var i: i64 = 0
    while i < 32:
        point.push(0u8)
        i = i + 1
    while i < 64:
        point.push(255u8)
        i = i + 1
    point

describe "REQ-TLS-ECDH-BOUNDARY-001: validate P-256 key parameters":
    it "should reject 31 and 33 byte private scalars":
        step("Submit adjacent invalid scalar widths to public key derivation")
        expect(p256_boundary_error(p256_public_key(p256_boundary_bytes(31, 1u8)))).to_equal("E-ECDH-P256-005: private scalar must be 32 bytes in [1, n-1]")
        expect(p256_boundary_error(p256_public_key(p256_boundary_bytes(33, 1u8)))).to_equal("E-ECDH-P256-005: private scalar must be 32 bytes in [1, n-1]")

    it "should reject a private scalar above the subgroup order":
        step("Submit the largest 256-bit value")
        expect(p256_boundary_error(p256_public_key(p256_boundary_bytes(32, 255u8)))).to_equal("E-ECDH-P256-005: private scalar must be 32 bytes in [1, n-1]")

    it "should distinguish an unreduced Y coordinate from curve membership":
        step("Keep X reduced and set Y to the largest 256-bit value")
        expect(p256_boundary_error(p256_ecdh_shared_secret(p256_boundary_one(), p256_boundary_large_y()))).to_equal("E-ECDH-P256-003: peer Y coordinate is not reduced mod p")
```

</details>

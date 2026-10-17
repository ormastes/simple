# BUG-X86-NEGATIVE-IMM64-20261017

Date: 2026-10-17. Status: focused native behavior PASS; broad qualification pending.
Authoritative bug database reconciliation: pending (qualified DB tool unavailable).

Owner: x86_64 native instruction encoder, `emit_i64_bytes`.
Frozen source: `15f7ca45871b1250abf44c91efb6004625035035`.
Path: `src/compiler/70.backend/backend/native/encode_x86_64.spl:122`.

`X86_OP_MOV_REG_IMM` calls this helper to emit the immediate after REX.W and
B8+register. The high 32 bits use signed division by 4294967296. Division
truncates toward zero, while extracting the upper word requires arithmetic
right shift. For -1, the current immediate is `FF FF FF FF 00 00 00 00`,
loading 4294967295 instead of -1. For -4294967297 it incorrectly emits -1.
Exact negative multiples of 2^32 and nonnegative values are unaffected.

The minimal fix replaces `value / 4294967296` with `value >> 32`.
The existing low-word path remains valid: signed remainder is in the range
[-4294967295, 4294967295], and `emit_i32` normalizes negative words with +2^32.
Arithmetic shift yields a high word within [-2147483648, 2147483647], so
`emit_i32` remains valid without overflow at either signed i64 extremum.

Existing language-semantic evidence is
`test/unit/compiler/common/gc_config_spec.spl`: arithmetic signed right shift,
truncating division and signed remainder scenarios. The x86 selector also
uses signed `idiv` for quotient/remainder.

Regression source: `x86_negative_imm64_spec.spl`, nine scenarios including
actual instruction encoding to RAX and R8; dedicated BDD runner UNRUN.
Host evidence: `host_integer_oracle.ps1` and `.log`, eight exact integer cases,
three original counterexamples, corrected bytes match .NET signed-i64 bytes.
This host oracle does not qualify the compiler or execute the Simple backend.

Focused qualification used the genuine co-located source project with the
separately reviewed SIMD dependency fixes. MIR passed65/65 and emitted54 new
AMD64 COFF objects. Automatic runtime source discovery then failed because
that tiny project has no src/runtime; --runtime-path is an artifact/archive
contract. Strict completion linked those54 new objects, the canonical hosted
entry and38 hash-verified real C1 runtime objects without FORCE, fabricated
stubs or old SPL object grafts. Actual map ownership resolves pow through UCRT.

Exactly one native execution exited0 with the exact expected80-byte stdout:
`X86 NEGATIVE IMM64 PROBE: PASS (12 byte-vector cases; 14 signed32 parser cases)`
followed by LF; stderr was empty. It exercised all original ten immediate/MOV
vectors plus both complete EVEX register arrays and fourteen parser cases.
Executable pre/post SHA256:
724f23e723bbc4ab8f9f77d57284f6d10f156c225f120d14a95ea884a81024bf.
An exclusive ledger blocks repeat execution. No fourth SPL build occurred.

The reused runtime pack has a disclosed historical transitive-header closure
provenance gap; this diagnostic does not claim fresh runtime admission. Broad
compiler/lib/MCP checks remain unrun, and the source PR remains a draft.
No merge or release has occurred. Other workarounds remain owned separately.
Evidence: C:/dev/simple-bootstrap-storage/phase3-validation-20261016/x86-negative-imm64-20261017/co-located-cycle3/strict-link.

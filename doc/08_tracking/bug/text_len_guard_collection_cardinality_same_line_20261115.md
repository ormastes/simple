# BUG-CHECK-TEXT-LEN-COLLECTION-CARDINALITY-001

Status: guard false positive reproduced by the normal push hook; detector repair remains open.

The reviewed workload registry validator binds `pin = image.split("@sha256:")`.
That value is an array of text parts: `pin.len() != 2` checks collection
cardinality. The same condition independently bounds the original image with
`image.byte_len() > 4096`. No array length feeds a byte slice or byte offset.

The normal push of source commit `96df50724ec1f946e222fdb947be5cb0bab2aae9`
reported this collection length as `(len() as byte width)` and blocked one new
unit-mix row. `scripts/check/check-text-len-unit-mix.shs` Rule 2 marks a `len()`
receiver when it shares a source line with another receiver's byte-family
operation. Its lexical binding exception covers `[u8]`, not general collections.
The checker did not infer the `[text]` result of `split` or distinguish the
independent boolean branches. This is not evidence of a workload text-width bug.

The final-sixth-cycle source clarification names the array `pin_parts: [text]`,
retains array `.len()` cardinality and digest validation in their original
short-circuit order, then places the independent image byte bound in the next
guard with the identical error. No check is removed or reordered relative to
another, and the next registry validation statements remain after both guards.
This is explicit source dimensional separation for the guard, not a detector
repair, baseline exemption, suppression, or array `byte_len()` conversion.

The existing production-call case in
`test/01_unit/lib/container/linux_fresh_workload_projection_v2_spec.spl`
("rejects local transports, short names and malformed registry manifest pins")
remains unchanged and **NOT_RUN**. Its valid qualified registry pin and invalid
transport/pin cases still target the same public validator. No new native,
compiler, runtime or deterministic timing qualification is claimed.

Future detector work should recognize collection-cardinality bindings and
independent boolean branches, while retaining rejection of genuine text
lengths passed as byte widths. That broader detector change is outside this
landing. The accepted source tree and failed push log remain preserved in the
source landing receipt; no source/native counter reset or seventh cycle is
authorized.

# Target 6 native reverse SMF section invalid in archive publication closure

Status: partially resolved; SMF assembly now succeeds, but the persisted
archive publisher's native integration spec still fails at the later draft
reverse-projection check.

The earlier compact cold graph spec passed 2/2 when its entry closure had 315
source units. Adding persisted CAS archive publication and its integration
cases expands the native closure. The resulting executable links, but every
example fails before archive admission: `cold_hir_reverse_projection_v1`
returns `cold-reverse-section-invalid:smf-section-invalid`. The section
validator groups invalid kind, invalid digest, and nonpositive extent under
that reason; the specific field has not yet been isolated. The positive case
never publishes index `CURRENT`, and the stale-payload case never reaches its
intended check.

The first expanded spec crashed after it asserted a failed `is_ok()` result
and then unwrapped that error as a generation. Test branches now guard those
unwraps and print the builder reason. The latest native build linked 323
source units (3 compiled, 320 cached) in 9.80 seconds at 496,592 KiB peak
build RSS; the spec ran at 2,320 KiB peak RSS and reported 4 failures.
Its process exit code was 0 despite that text verdict, so exit status alone
must not be treated as a pass. The test-runner exit-status defect also needs
an owner fix before native SPipe execution can be a reliable gate.

On 2026-09-29, native disassembly and GDB showed the builder returned a valid
69-byte reverse payload. The original `payload!` path passed its `Some` wrapper
to SHA-256 and produced an invalid section extent. Explicit `if val` binding
fixed that. The export caller then read `reverse.payload` from struct offset 8
although GDB showed the payload at offset 0; explicit Result unwrap moved the
spec past SMF assembly. The current textual verdict is 4 failures, first reason
`cold-drafts-reverse-projection-mismatch:a`. The compiler layout evidence and
remaining investigation are in
`native_match_result_struct_field_projection_offset_2026-09-29.md`.

Next step: inspect the recomputed projection and artifact digest in the draft
check. Require all four examples, including positive publication and stale
payload rejection, to pass before calling the publication path verified.

Later evidence: the two recomputed reverse section digests matched, while the
artifact's reverse digest was zero because another `match Ok(value): value`
struct binding projected the wrong field. Explicit unwrap moved that check
forward. A module-level SHA-256 sentinel then arrived as zero in the native
binary; replacing it with its verified literal moved the spec forward again.
The graph validator's optional lookup required explicit binding. The last
textual verdict from the pushed candidate is **2 passes, 2 failures**: the graph
and negative input cases pass, while persisted publication and stale payload
rejection do not. Both remaining cases lack a CAS archive generation. The
earlier file-wrapper diagnosis was incorrect: tagged `0xb` is true. The next
failure was archive manifest validation; see
`native_archive_manifest_validation_2026-09-29.md`. The newer archive fixes
resolved a native null mutable-reference crash and advanced CAS through
generation-file creation and sealing. The latest textual verdict remains 2/4:
`CURRENT` is absent, so both publication cases still fail.

# Target 6 native reverse SMF section invalid in archive publication closure

Status: open; blocks the persisted archive publisher's native integration
spec and V2 graph publication qualification.

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

Next step: inspect the reverse section's kind, digest syntax, and payload
extent in this exact native closure, then fix the producer or native lowering
cause. Re-run the four-example spec and require both its textual verdict and
the publisher's positive and stale-payload assertions to pass before calling
the publication path verified.

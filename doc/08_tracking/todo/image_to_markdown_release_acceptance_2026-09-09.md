# Image-to-Markdown release acceptance

**Status:** Blocked. Source, design, deterministic fixtures, and executable
acceptance scenarios are present, but this feature is not release-admitted.

Remaining acceptance work:

1. Produce an admitted pure-Simple self-hosted runtime after resolving
   `bootstrap_stage2_backend_object_path_status_2026-09-08`.
2. Run the image-to-Markdown unit and system SPipe suites with that runtime and
   retain their receipts.
3. Measure NFR-004 warm startup, representative request latency, and max RSS.
4. Run the NFR-005 multilingual/table/chart corpus and demonstrate at least
   95% acceptance against the approved oracle.
5. Re-run the working and staged direct-env guards after isolating or resolving
   unrelated violations in `src/app/io/debug_stubs.spl` and
   `src/app/io/file_shell.spl`.

**Owner:** image-to-Markdown implementation owner
**Final reviewer:** highest-capability architecture/verification reviewer

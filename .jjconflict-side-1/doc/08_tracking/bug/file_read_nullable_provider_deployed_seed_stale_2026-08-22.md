# Nullable file-read provider deployment gate

The source providers now agree that `rt_file_read_text` returns nil when a file
cannot be read and returns text, including valid empty text, on success. Native
C and Rust runtime providers already had this behavior; the Rust interpreter
provider was corrected and its focused unit test passes.

The currently deployed `bin/simple` bootstrap predates that interpreter fix and
still converts a missing file to empty text. Therefore the new checked
`file_read_result` facade must not yet be cited as cross-lane verification
evidence. Rebuild/deploy the self-hosted tool, then verify the same empty-file
and missing-file contract in interpreter, JIT, native, and sealed dynload lanes.

Evidence completed:

`cargo test -p simple-compiler file_read_text_distinguishes_empty_success_from_failure --lib`

The temporary Simple cross-lane spec was removed after reaching the mandated
three-cycle cap against the stale deployed binary. Recreate it only after the
new provider is deployed.

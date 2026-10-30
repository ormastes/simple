# Native test wrapper imports a nonexistent bounded reader

Status: source candidate; actual native plain and SSpec regression pending.

The plain-run2 attempt using admitted producer bdd4 and runner9c2a reached
source-authority refresh and selected115 files, then failed HIR before creating
an executable. The generated MC/DC prelude imported env_get,
file_is_regular_no_follow and file_read_text_bounded from std.io, resolved as
lib.nogc_async_mut.io. The bounded reader has no declaration in this source
revision: its only occurrences are these generator strings. Thus adding source
roots alone cannot fix this failure.

The default profile intentionally enables MC/DC; this is not evidence of an
accidentally inherited mode. Do not disable normal-profile MC/DC to qualify a
plain test. The repair emits imports from the actual sync environment/file
owners and calls file_read_regular_no_follow_bounded. Its Result failure is
rejected explicitly before unwrap; path no-follow, maximum length, expected
length and digest verification are retained. This avoids both an unresolved
facade route and treating a read refusal as empty content.

Regression uses the existing actual plain fixture
 test/fixtures/test_runner_source_routes/calibration/plain_green_test.spl
and one native SSpec through the rebuilt standalone runner. Their generated
entry must include the real provider imports and Result admission, compile,
execute assertions and emit structured test receipts. No green result is
claimed until those runs complete. No compiler validation or MC/DC policy is
relaxed. Existing file_ops owns no-follow and byte-length admission.

Evidence: /tmp/simple-phase2-runner-native-attempt11-20261030/plain-run2/
run.stdout.log and generated entry in the detached plain2 execution checkout.
PR5332 changed compiler selection in this source file but did not repair this
prelude; the narrow hunk is intended to compose with that newer release change.

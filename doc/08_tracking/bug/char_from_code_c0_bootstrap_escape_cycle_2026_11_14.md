# Character provider C0 constants depend on the lexer they support

Status: production repair independently reviewed; changed-source projection
passed all ten groups. Updated compiler qualification remains pending. This is
separate from the Unicode lexer repair.

The retained actual-lexer projection at
`/tmp/simple-unicode-escape-lexer-probe-20261115` compiled with producer SHA256
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
Fixture `4d5dff0561ab4640a7e508b7ea88ae28c76be432` passed nine groups but failed
the numeric-byte check for provider control characters 11 and 12; execution
exit was 1. Immutable evidence commit `a4c9deea836deb39509426e8954b5ae0414efc7c`
retains the commands, hashes, run log, and bounded resource receipts.

The actual `src/lib/common/string_core.spl::char_from_code_inline` implementation
special-cased values 11 and 12 by returning fixed-width Unicode string literals.
The old producer preserves those literals as text. The lexer calls this same
provider to materialize decoded Unicode scalars, so compiling a repaired lexer
with an old producer can retain this circular bootstrap dependency. Source
causality is distinct from the previously observed literal NUL separator bug.

The repair removes only those two special cases. The existing validated
`_utf8_char_from_codepoint_inline` owner already encodes all values below 128
as a one-byte array and calls the actual `rt_bytes_to_text` boundary. Values
11 and 12 now use that path. The 9/10/13 fast paths, NUL policy, non-ASCII scalar
encoding and invalid-scalar rejection are unchanged. No runtime interface,
replacement decoder, or syntax workaround is introduced.

The existing SSpec case compared provider output with the same problematic
escape literals and could hide the defect. It now asserts byte length 1 and
numeric byte value for each code. The native fixture
`test/fixtures/compiler/char_from_code_c0_provider_native_probe.spl` checks the
actual provider and public alias with numeric oracles. Both remain UNRUN.

The parent authorized one finite changed-source projection with the same ten
numeric-oracle groups, because the production provider is shared by those
scanner paths. It uses separate immutable source/cache/evidence and retains
the prior nine-PASS/one-FAIL attempt. This evidence cannot qualify a rebuilt
compiler or replace the unchanged facts-key golden, which remains pending an
updated producer.

## Changed-source execution

Source commit `c736d8b05f510154eb6d2b62bb3a7a715e355ef7` was extracted into
separate fixture `/tmp/simple-unicode-provider-probe-20261115`, commit
`c5be372d05e8e961520620d65b249c92e7cb22ed`. Independent review verified exact
production declarations and that the ten-group harness was byte-identical to
the earlier attempt. No oracle or provider substitute changed.

Compile exit 0, run exit 0: **10/10 projection groups passed**, including the
previously failing C0 group. Evidence commit
`7808aeb6588f917062abd69d8466ed52adb23ab7` retains the actual command, source and
binary hashes, logs, and resource receipts. Source SHA256:
`3b4656b521da1a53ab3afb2948dfc993e4b2bc82d476c71c0527b6c4def0249b`.
Binary SHA256:
`daf3741cd68034300acca53875d8c98fa5716a679455fb4b278c3a8472ee04f8`.
Producer SHA remains the pinned 855f48d3 above. Memory was capped at 2 GiB,
swap 0, launch available memory 65,338,830,848 bytes, peak 842,813,440 bytes,
elapsed 9.22 seconds, under the 90-second deadline. Independent Astra review
accepted these scoped receipts without rerunning execution.

The earlier nonpassing evidence is unchanged. This is qualification of the
actual extracted lexer/provider functions, not a rebuilt compiler, whole
SSpec suite, or the independent facts-key golden. Those remain pending.

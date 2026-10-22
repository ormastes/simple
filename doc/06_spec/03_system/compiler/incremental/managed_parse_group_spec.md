# Managed parser worker and durable flat artifacts

REQ-IM-007 / REQ-IM-008. Executable:
`test/03_system/compiler/incremental/managed_parse_group_spec.spl`.
Status: authored, runtime and docgen UNRUN. No process launch is claimed.

The spec invokes the actual parser, flat capture/restore bridge, filesystem
cache and worker entry. Inputs are real malformed-good-malformed Simple source,
not predetermined success/failure DTOs.

1. Parse the good logical source through the ordinary bridge. Require an
   `answer` function in its rich AST and a nonempty captured flat payload.
2. Install a digest-pinned three-module snapshot and execute an action. Require
   ERROR/OK/ERROR order, canonical diagnostic codes and stable identity notes,
   and exact good-payload parity with the ordinary bridge. Rebuild its rich AST
   from the stored payload and check `answer` again. Neither error module may
   create a reusable cache receipt.
3. Reinstall the owner from disk and repeat. Only the good module may report
   reuse; both failed diagnostics must match their original canonical values.
   Encode/decode the result SDN record without changing diagnostics.
   Separately edit only the first module, advance the request snapshot and
   generation, then require actual cache reuse for the unchanged good module.
   The changed module reparses; the old action generation remains rejected.
4. Independently corrupt a blob, receipt, source identity in the receipt, or
   feature authority. Require a genuine reparse with the original good artifact
   digest and `reused=false`. Unknown cache I/O failures remain errors in the
   implementation; they do not silently trigger successful reparse.
5. Change source bytes after install. Require a source-identity error before
   parsing/cache lookup. Reject installation with a changed target or inadequate
   source byte budget, and reject changed policy/action generation.
6. Invoke the worker entry with matching shutdown and verify every installed
   marker field through the real wire reader, including aggregate source bytes.
   Reject a foreign shutdown identity and an unsafe mailbox filename.
7. Feed the full target frontend an excluded syntactically invalid function,
   an included `selected` function and a `schema` domain with payload `Person`.
   Assert those independent AST expectations, then require worker cold and
   replacement-owner warm artifacts to match the actual frontend capture.
8. Select warning capture policy and require explicit installation refusal;
   changing an admitted owner to warning policy yields a policy rejection.
   Restore the previous process policy before assertions. Warning-success
   transport remains an open support gap, not a completed acceptance criterion.

Live compiled-worker parity and durable replacement-process reuse remain owned
by `parser_qualification_evidence.spl` and require an admitted pinned producer,
worker image, process provider and resource envelope. These authored direct-owner
tests do not establish that qualification.

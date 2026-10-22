# C7 controlled Result ABI observations

Selected requirement: `generic_formal_verification_hardening_plan.md` C7 requires actual compiler/runtime translation observations and deliberate corruption refusal. This slice implements raw observation production for builtin `Result<i64,i64>`; the authenticated refinement/checker obligations remain open.

## Contract and ownership

Implementation owner: `/root/astra_enum_extension_hardening`; merge owner: `/root`; independent source reviewer: root-routed reexport reviewer. Sidecars: N/A, bounded three-owner lane.

- `enum_wire.spl` constructs typed Ok and Err values internally, validates both runtime owners and tags before either payload read, and returns copied scalar projections. No external handle, integer-to-handle cast, manual allocation/free, or payload logging.
- `result_abi_observation_capture.spl` runs the actual canonical MIR builtin registration on fresh metadata. Both qualified and bare maps must agree on exactly Result/Ok/Err and canonical owner/tag values. The raw comparator checks both source outcomes and every observed word; it has no certificate authority.
- `result_abi_raw_collector.spl` validates all five requested paths (including embedded NUL) before any provider read. Its cached byte length and existing byte_at operation share the UTF-8 byte domain, preserving valid Unicode filenames without scalar-index rescans. The existing no-shell SHA-256 owner measures each artifact before and after capture. Missing/noncanonical digests or path/byte drift refuse the record.

Raw outputs explicitly say UNAUTHENTICATED and NOT_CHECKED. Requested target context is a request, not observed execution identity. The measured registration file does not establish which registration code was loaded. Neither a path hash nor unchanged pre/post hashes authenticate execution or rule out an intervening replacement. Mutable raw records must never be used as admission credentials.

## Acceptance and authored coverage

| Requirement | Actual route | Authored controls |
|---|---|---|
| REQ-C7-RESULT-RAW | canonical registration + typed runtime constructors/getters | exact metadata, both outcomes, zero/-1/MIN/MAX i64, wrong owner, unknown/swapped tags, malformed/extra/shadowed metadata |
| REQ-C7-RESULT-CORRUPTION | non-authorizing comparator on copied actual projections | owner/tag/payload mutation for each outcome, omitted/reordered/rewritten source rows |
| REQ-C7-RESULT-MEASURE | existing file hash provider around actual capture | known file bytes, all five roles, all empty/NUL path positions, absent file, noncanonical hash, real file replacement and drift comparison |
| REQ-C7-RESULT-TRUST | raw-only schema and unchanged qualified validator | explicit open statuses; false checked flag with absent authority refuses certificate |

The initial twelve SSpec scenarios were snapshotted before production implementation. Revision 2 adds a test-first Unicode filename scenario: a real multibyte path must measure the known file digest, while appended NUL plus suffix must refuse in every artifact role. There are now thirteen SSpec scenarios. One unchanged native fixture additionally covers both outcomes and projection corruption. All are **AUTHORED / UNRUN**. The file replacement scenario exercises the same comparator with two actual measurements; it does not inject a race inside the one-shot collector. Read ordering is covered by a late invalid path taking precedence over an earlier absent file and by source inspection; no provider-call instrumentation is claimed.

## Cost, privacy, and cleanup

Fixed two typed constructions and six runtime getter calls; existing runtime getters may scan the allocation registry. No constant-time getter or leak-free claim. Fresh MIR metadata setup is bounded, with no global cache. Five roles are hashed twice: provider work is proportional to total artifact bytes; no shell, process launch, recursive scan, or hot request integration. Raw payloads and paths stay in memory and are not automatically persisted/published. Tests create an owned temporary directory and clean their files before assertions; collector never deletes input artifacts.

## Qualification still required

Execute the existing SSpec/native runners only with a qualified pure-Simple producer and runtime bound to these exact source images. No runner/compiler/Lean execution or docgen was performed here. Independent checker provenance, loaded compiler/runtime/probe and target identity, runtime refinement to ResultTaggedAbi.validate_sound, axiom audit, C6 trust choice, and qualified certificate/admission remain OPEN. DCE PR4017 and ordinary optimization dispatch are unchanged. This does not complete all C7 or robust/enum features.

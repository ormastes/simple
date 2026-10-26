# Conversion guard specs import removed bare names

- Date: 2026-10-11
- Status: test repair verified in scoped Phase1; branch landing pending Phase3 PASS.
- Bug ID: `utf8_guard_specs_import_removed_conversion_names_2026-10-11`
- Scope: four existing unit specs, twelve cases in two independent batches; no library implementation or assertion changes.
- Bug DB reconciliation: pending a qualified pure-Simple database/tool route. No reconstructed historical DB entry is current proof.

The UTF8 and CBOR guard specs imported `bytes_to_text` / `text_to_bytes` even though their owners declare `base_encoding_bytes_to_text`, `cbor_bytes_to_text` and `cbor_text_to_bytes`. Bare conversion names were removed to avoid interpreter collisions; see [the earlier compiler collision report](crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21.md). The seed warned that each import was missing, then continued through another available bare conversion. A passing case in that run did not establish that the specified owner executed.

Repair each import with an explicit alias to its declared owner. Existing local calls and every assertion remain unchanged. The three specs themselves prevent recurrence: restoring the missing imports reproduces four UTF8 failures and one CBOR text conversion failure, and the evidence gate rejects missing-import warnings even when a case happens to pass. No stub, assertion weakening, source guard workaround or admission bypass was introduced.

The separate `codec_byte_text_guard_spec.spl` imported the same removed bare name from `std.common.encoding.codec`, whose declaration is `codec_bytes_to_text`. Its three historically executed failures had no retained green cases. The same explicit owner alias repairs that spec without changing its assertions or the codec.

## Retained acceptance

Initial observation: three files, nine executed cases, four passed / five failed. Owner admission is false because of the missing imports. Collector exit 1; wall 1.6089094 seconds; peak RSS 61,060 KiB. A separate cycle2 preflight rejected Git checkout line-ending drift before any collector/seed dispatch; it is preserved.

Corrected owner-bound cycle2: three files, nine executed / nine passed / zero failed / zero skipped; no missing-import or root-source escape warning. Collector exit 0; wall 1.4105797 seconds; peak RSS 61,136 KiB. Closed Job and source/seed/helper pins authenticated before and after. These small diagnostic measurements support this scoped test repair; they do not establish whole-suite performance or memory behavior. No green rerun or third feature cycle was used.

Runtime: immutable Rust bootstrap seed SHA256 `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`, explicit Stage1 test routing. This is Phase1 evidence only, not pure Phase2 qualification. Actual command: `phase1-seed.exe test test/failed-only --mode=interpreter --sequential`, with a 1 GiB process-tree cap and 120-second bound. The 79-file dependency capture uses committed source `abb0891dcc048958ea2030759802ad7ae0cedc76`, including the already-landed `94f4` UTF8 byte-copy fix. Tested private commit: `546e44f8731b1ce25a6cab9f1b197d9948b5895d`.

Evidence packet: `build/sol-phase1-unicode-release-20261011/next-failed-unrun-plan/owner-alias-cycle2-corrected/`.

- Request SHA256: `f8d786f575c4cc9b65b597936e50e1745963f0d6a8d1f42c30125c3b7880d4a4`.
- RESULT SHA256: `2da071a9e7ef7072508a967efb2af484b82a8955a36a8d07f15ce8bccd978b4c`.
- Closed receipt SHA256: `862abcdb3b3cdfe337226327c1e02da27867e60aef0cc30ea6958c7aac4a4b61`.
- Retained test log SHA256: `f30a4ccd6acc85783255d0af3c25c64269382ffd3845c6233f093631a6e60a6f`.
- Source-only pure alias review SHA256: `fea075c91c054efc82b293157802752b5327d35a05305cbe6228d5ebaefcf224`.

The version-specific seed summary parser requires three unique files, declared/executed counts 5+2+2, matching ✓/✗ outcomes, per-file status, aggregate counts and exit status, with zero skips. Seven malformed-summary/exit controls were rejected using the retained initial log. Pure HIR source at `abb0891dcc048958ea2030759802ad7ae0cedc76` preserves aliases as lexical lookup keys; dynamic pure runtime and module visibility acceptance remain unexecuted. Full CLI and whole Phase1/2/3 qualification remain separate blockers. Production landing commit: pending the parent-owned `release_phase3` flow; no release or merge claim.

## Independent codec prevention batch

Current owner-bound Phase1 execution: one file, three executed / three passed / zero failed / zero skipped. Owner admission is true; no missing-import or source escape warnings. Collector exit 0, wall 2.2072512 seconds, peak RSS 63,328 KiB, authenticated closed Job and all 90 source/seed/helper pins stable. The prior nine passed cases were excluded. The strict summary parser is explicitly scoped to one unique file and exactly three actual case outcomes. No second codec run was used. SIMD/UTF extern declarations were retained without shims; this execution does not qualify the pure tool or the broader SIMD surface.

Packet: `build/sol-phase1-unicode-release-20261011/next-failed-unrun-plan/codec-owner-batch/`, private source commit `bede3d82b89f1e4b78e9c79f984bad1c174492dd`.

- Request SHA256: `63891e54ccf19a6cb676c3852dfe90ab64758bc69901913e0bb8f3a94619b3f7`.
- RESULT SHA256: `ffbbc204e3d4ec36b298d0b4aaaa6b9918cb2dd5b22cdb9d0c848897d5bc3ffc`.
- Closed receipt SHA256: `2ad5b0b00b9aa7c1dee48804226327c0dff960d468f35ddca385a4f9d3b37827`.
- Retained log SHA256: `e9dd23ef154bb299d6832aaf5632f26283f485f199ba338945cdeb801023f3d5`.

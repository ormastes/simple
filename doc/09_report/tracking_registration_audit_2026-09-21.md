# Bug and TODO registration audit — 2026-09-21

## Current candidate verification — 2026-09-23

The linear candidate `48337a7a4618973da90c035a951207aab01b1380` is based on
`daa9dc619a8ee2498cd08339183393282f8ab524`. The documentation-only correction
containing this section preserves that candidate's database and checker bytes.
Its bug database CRC32 is `2046825929`; the 15 added TODO rows are IDs 323–337.
All main bug and TODO rows are preserved, no duplicate bug/TODO IDs were found,
and all 846 added bug IDs have exact documents. The fixture suite passed all
25 fixtures; both direct-env working and staged guards passed, and tracked
executable specs under `doc/06_spec` remain zero.

The current read-only production audit reports **FAIL: 2,559 rows, 4,623
non-index documents, 1,554 explicit unresolved records, and 92 findings**:
48 bug rows without exact documents, 19 malformed rows, one TODO status
mismatch, 19 unregistered bug documents, and five unregistered TODO documents.
Registration therefore remains incomplete. The gate stays advisory; these
results do not establish acceptance of the tracked implementations.

All counts, CRCs, TODO IDs, attachment-completion claims, timings, and local
evidence paths in the historical sections below describe their stated baseline
or earlier intermediate snapshot, not this current candidate.

## Historical scope and result

Baseline: `e0dd873da1b7828389db4eb60e82972cc8245313`. The audit reads all
4,492 bug Markdown files, all 61 TODO Markdown files, 1,367 bug rows, and
319 TODO rows. It also scans 1,169 related Markdown files: platform guides
and other documentation whose path names Windows, Linux, FreeBSD, SimpleOS,
SOSIX, or macOS. Nineteen related files have an unresolved Status or Known
Issues section; these include plans and feature records requiring owner review.

**Registration remains incomplete. No implementation status was changed.**
The complete identified issue list is in
[the findings table](tracking_registration_audit_2026-09-21_findings.tsv).
Rows in that table can overlap: one record may have a status conflict and a
missing evidence path. Paths and line numbers refer to the baseline above.

## Platform counts

Classification uses document filename, title, and explicit Platform/Target/Host/OS
metadata; row classification uses ID, title/description, and owner path.
`common` means no platform was declared by those fields; it does not assert
execution on every OS. Multiple named platforms are `cross-platform`.
Explicit macOS-only records are shown separately to avoid counting them as common.
Reproduction prose alone does not establish a record's platform.

| Platform | Bug docs | TODO docs | Bug DB rows | TODO DB rows | Unregistered unresolved bug docs | Unregistered unresolved TODO docs |
|---|---:|---:|---:|---:|---:|---:|
| common | 4,093 | 48 | 1,267 | 297 | 740 | 9 |
| windows | 86 | 2 | 12 | 3 | 29 | 1 |
| linux | 37 | 1 | 11 | 2 | 16 | 0 |
| freebsd | 3 | 0 | 2 | 0 | 0 | 0 |
| simpleos | 198 | 7 | 57 | 8 | 40 | 3 |
| cross-platform | 15 | 1 | 5 | 9 | 4 | 0 |
| other platform (macOS) | 60 | 2 | 13 | 0 | 17 | 2 |
| total | 4,492 | 61 | 1,367 | 319 | 846 | 15 |

The last two columns are baseline candidates without an exact ID, date-spelling
candidate, or explicit row reference. Date spellings and row references were
used to distinguish mapping work from wholly missing registration; they are
not automatic aliases. Three more unresolved bug documents have mapping
ambiguity. The strict exact-ID guard therefore reports 846 bug documents after
the three additions below (849 before). Of the 846 wholly unlinked baseline
bug candidates, only 86 state a P0–P3 severity explicitly. The audit does not
invent severity, owner, or implementation state for the remainder.

## Findings retained for owner triage

- 357 exact-ID document/DB lifecycle contradictions. Both values are retained.
- 43 bug rows without an exact basename document after three reviewed semantic
  aliases are applied. Some remaining rows cite another document or source-only
  evidence.
- Three date-alias collisions: `stage3_current_source_hir_rss_termination_2026-08-14`,
  `compiled_checker_asm_volatile_indent_gap_2026-08-03`, and
  `llvm_constants_lost_ret_zero_2026-08-01`. Each has both underscore-date and
  hyphen-date IDs. This audit does not merge their differing states.
- Twenty bug rows have extra fields from unquoted annotation commas. Parsing
  follows `src/lib/nogc_sync_mut/database/core.spl:668`, which toggles at every
  double quote; generic CSV parsing is not the canonical SDN grammar.
- Twenty-five missing owner paths and 25 missing exact evidence paths. The
  inventory checks tracked paths, including directory owners, so sparse checkout
  absence is not mistaken for deleted source. Free-text evidence is not parsed
  as an authoritative path.
- Twenty-two authored bug statuses are outside the core validator vocabulary:
  21 `fix-implemented-verification-pending` and one `resolved-duplicate`.
  These are reported as schema drift and preserved. TODO statuses are 155 open,
  158 closed, and six blocked; none is empty under the canonical SDN splitter.
- No exact duplicate bug/TODO IDs were found. Shared evidence documents are
  not aliases: several TODO tasks can legitimately point into the same file.
- Baseline bug DB CRC32 is valid: `3241038213`. TODO DB has no checksum header.

Documents without an explicit recognized lifecycle value are not silently
classified as open or closed. Investigation notes, generated indexes, historical
reports, and marker-only TODO notes require separate owner classification.
Related guide Known Issues are advisory candidates, not automatically new bugs.
For example, the SimpleOS GUI guide's serial garbling and clean-rebuild stub
nondeterminism need issue identity/ownership triage; its heap item already maps
to an existing record.

## Registration corrections

Three existing documents explicitly state OPEN and a canonical severity. Their
missing rows are added to `bugs_active`, with the document as owner/evidence
path and its Status line as the citation. Original documentation is unchanged.

| ID | Severity | State |
|---|---|---|
| `stage2_msvc_link_uses_gnu_driver_flags_2026-09-12` | P1 | open |
| `simpleos_arm64_riscv64_embedded_gui_missing_theme_install_call_2026-09-06` | P3 | open |
| `value_access_ownership_spec_never_executes_2026-09-18` | P2 | open |

Existing row bytes and lifecycle values remain unchanged. The resulting CRC32
was `2308762869`, resealed by the canonical tool. No TODO IDs were regenerated.
The TODO README's incorrect legacy/deprecated notice is replaced with the actual
canonical directory and numeric-ID contract.

At the user's direction, the remaining unresolved document backlog is now
attached to the canonical databases: 843 bug documents receive new rows in
`bugs_active`, three bug documents use explicit reviewed aliases to their older
authoritative rows, and 15 TODO documents receive stable numeric rows. Together
with the three rows above, this attaches all 864 unresolved documents identified
by the baseline audit without shadowing the older P1/P2 lifecycle records. An
authored P0-P3 value is retained when present. Where the document has no
priority, P3 is an explicit schema placeholder marked `untriaged`; it is not a
severity or closure decision. At that historical snapshot, TODOs 322, 323, 324,
327, 328, and 330 were restored
to `blocked` with nonempty blockers matching their source records. The unrelated
pre-existing `sffi_v2_provider_admission` status mismatch remains for owner
triage. Other lifecycle values remained unchanged. That intermediate bug
database CRC32 was `1764979789`; the current CRC appears above.

## Executable regression and evidence

The new read-only owner is
`scripts/check/check-tracking-doc-registration.shs`. Its fixture suite is
`test/01_unit/scripts/tracking_doc_registration_test.shs`.

The prior status guard reports PASS for a fixture containing a registered OPEN
record plus an unregistered BLOCKED record. The new owner detects that orphan
and also covers recursive plain/lowercase OPEN, TODO documents, source-only
TODO rows, curated TODO rows, token boundaries, fenced examples, marker-only
notes, reverse links, exact date identity, three reviewed semantic aliases,
semantic duplicate rejection, blocked TODO status/blocker consistency, the five
additional exact generated-row lifecycle repairs, malformed fields, cross-table
duplicate IDs, and missing database errors. Twenty-five executable fixtures pass.

The historical post-repair production audit reported FAIL: 2,547 rows, 4,550
non-index documents, and 64 findings. Document-to-database attachment gaps
identified in that snapshot were closed. Its remaining findings were 43 database rows without an exact
document, 20 malformed pre-existing rows, and one pre-existing blocked TODO
document whose database row still says open. That status conflict predates this
registration change and remains for owner triage. This audit is not enabled as a
new CI merge gate over that backlog.

That historical MSYS audit took 14.41 seconds and reported maximum
RSS 125,496 KiB through `/usr/bin/time -v`, while independent fixture/DB checks
were running on the same host. This is a local side-effect bound,
not a before/after improvement or a Windows Job Object process-tree measurement.
No self-hosted Simple runner was available; no seed was substituted. Shell
fixture results do not establish acceptance of any tracked implementation.

Retained local evidence is under `build/tracking-audit/`: original inventory,
related-platform inventory, registration fixture log, the prior guard's orphan
log, full audit output, resource measurement, unique-ID gate, and CRC reseal log.
The earlier unique-ID check passed over 3,039 rows in six SDN tables. That
historical audit parsed 2,547 bug/TODO rows without exact or semantic duplicate-ID findings.
The direct-env guard passes; tracked executable specs under `doc/06_spec` remain
zero.
Independent admission review and CI gates remain required before merge.

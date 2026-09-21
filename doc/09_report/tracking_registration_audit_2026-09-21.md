# Bug and TODO registration audit — 2026-09-21

## Scope and result

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
- 46 bug rows without an exact basename document; 18 have a date-spelling
  candidate. Some remaining rows cite another document or source-only evidence.
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
attached to the canonical databases: 846 bug documents are registered in
`bugs_active`, and 15 TODO documents receive stable numeric rows. Together with
the three rows above, this registers all 864 unresolved documents identified by
the baseline audit. An authored P0-P3 value is retained when present. Where the
document has no priority, P3 is an explicit schema placeholder marked
`untriaged`; it is not a severity or closure decision. Every new row remains
open and points back to its document as the evidence owner. Existing lifecycle
values remain unchanged. The bug database CRC32 is now `1699616582`.

## Executable regression and evidence

The new read-only owner is
`scripts/check/check-tracking-doc-registration.shs`. Its fixture suite is
`test/01_unit/scripts/tracking_doc_registration_test.shs`.

The prior status guard reports PASS for a fixture containing a registered OPEN
record plus an unregistered BLOCKED record. The new owner detects that orphan
and also covers recursive plain/lowercase OPEN, TODO documents, source-only
TODO rows, curated TODO rows, token boundaries, fenced examples, marker-only
notes, reverse links, exact date identity, malformed fields, cross-table duplicate
IDs, and missing database errors. Fifteen executable fixtures pass.

The post-registration production audit remains intentionally FAIL: 2,550 rows,
4,550 non-index documents, and 66 findings. All document-to-database attachment
gaps are closed. The remaining findings are 46 database rows without an exact
document and 20 malformed pre-existing rows. They are reverse-link/schema repair
work rather than missing database attachment. This audit is not enabled as a new
CI merge gate over that backlog.

The final MSYS audit took 14.41 seconds and reported maximum
RSS 125,496 KiB through `/usr/bin/time -v`, while independent fixture/DB checks
were running on the same host. This is a local side-effect bound,
not a before/after improvement or a Windows Job Object process-tree measurement.
No self-hosted Simple runner was available; no seed was substituted. Shell
fixture results do not establish acceptance of any tracked implementation.

Retained local evidence is under `build/tracking-audit/`: original inventory,
related-platform inventory, registration fixture log, the prior guard's orphan
log, full audit output, resource measurement, unique-ID gate, and CRC reseal log.
The earlier unique-ID check passed over 3,039 rows in six SDN tables. The
post-registration audit parses 2,550 bug/TODO rows without duplicate-ID findings.
The direct-env guard passes; tracked executable specs under `doc/06_spec` remain
zero.
Independent admission review and CI gates remain required before merge.

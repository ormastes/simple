# RenameWindow independent Astra source review

Date: 2026-10-26. Workspace: D:/dev/simple-coremux-shared-20261025.
Requested integrated HEAD: 9cb95a1552b. Reviewed source cycle: 1.
STATUS: WARN / source review accepted; executable evidence NOT_RUN.
No concrete scoped P0/P1/P2 finding was identified.

Five unit cases and two system scenarios are authored, zero executed. No compiler,
build, helper, native fixture, product or test was launched. No production edit
or commit was made. This review does not admit a CoreMux provider.

## Frozen input identity

All eight manifest file hashes matched. The adapter-plan hash also matched.
The source manifest SHA256 is
d2344fb617f07128b829476309d017f33f4fc5eea2cb357785dbd1d5a9952228.

| Path | SHA256 |
| --- | --- |
| src/lib/common/contracts/mux/request_validation_v1.spl | 55f68a18d2b12c39c5cd5e87c2237c2005e87353b014f09725932f8901220b56 |
| src/os/apps/smux/window_metadata_service.spl | f9e808b57b26a2a39ccdb39ccd5395666d914bfd82feba8da867f59ad1959b47 |
| src/os/apps/smux/api.spl | bd58e1f031118fa02914d6d1610fbc869a5de6da6c79896f7efdbab618ab87b2 |
| test/01_unit/tools/smux_window_metadata_spec.spl | c749a5954a881d643672c118d27e753f5b8a92f577d2652e666773aeb6b8d095 |
| test/03_system/tools/smux_window_rename_spec.spl | 639083bd2466a94eedb44cabc6febc556985ea13bc729f48fa271d385367ecc5 |
| doc/06_spec/01_unit/tools/smux_window_metadata_spec.md | 9e075df490220a1747d2f12da3d84f8cff47e39ea2f75ab500a30390bc39d673 |
| doc/06_spec/03_system/tools/smux_window_rename_spec.md | d6bb3d82b42dc42420cb475660ecfbaea713efbff9c518dffc930b9dca270c5c |
| doc/09_report/smux_window_rename_source_2026_10_26.md | 7bde00dd8d43dfa7b10747c7ab4ac6ad8f82fab82124c9c9984bd9f7d4475db6 |
| build/review/coremux-server-adapter-plan-v2.md | 37b4a0dcf64c89e15da61338055272f458c5c55f3a1578bf261101624d849cab |

## Production findings

The additive public mux_validate_name_v1 at request_validation_v1.spl:29
delegates to the existing check_text policy, using the same 256-byte bound,
nonempty and clean flags. RenameWindow request validation now calls that helper.
UTF8 validation, NUL/C0/DEL/C1 refusal and literal spaces/Unicode behavior are
preserved. No shell/token transformation, alternate validator, or ASCII-only
policy is introduced.

window_metadata_service.spl:6 validates actual session/window existence and
membership before changing metadata. It rejects collision with another window's
name or ID in the same session; cross-session display names and the target's own
ID are allowed. Collisions are checked before the unchanged-name return. An
otherwise valid identical name returns the original state without replacing the
window. This does not repair or normalize any preexisting duplicate names admitted
through other APIs.

The explicit constructor at line22 preserves every current MuxWindow field except
name: identity/session, active state, layout, canvas, manual rectangle/reference
dimensions, zoom and presentation. The existing replace_window preserves the
other registry entries, counters, client records, panes and metrics. Rename has
no child-host calls and no additional mutable service registry.

api.spl:413 refuses exhausted revision authority and closing session/window/pane
ownership before applying the transform. It returns errors before publication.
A successful transform is published once through the existing _publish seam and
sole _svc authority. The configuration comparator includes the window name and
all preserved geometry/presentation fields; unchanged state does not tick the
revision. No asynchronous callback or reentrant host operation intervenes between
snapshot and commit. Exhausted authority refuses even an identical-name request,
consistent with the existing write guard.

## Authored control quality

The five unit cases cover byte boundaries including astral Unicode, forbidden
controls, unknown/foreign membership, name/ID collisions, cross-session names,
identity-name handling, no-op configuration equality and inverse-rename
preservation of manual geometry, zoom, presentation and pane authority. They call
the production validator and transform. No placeholder pass was found.

The first system scenario calls the real service API, checks one publication,
unchanged no-op revision and no publication on refusal. It releases its owned
session before asserting the collected outcome.

The second scenario starts cmd.exe through the actual PTY API, splits, sets a
title, zooms, attaches/detaches, renames and checks retained child PID, PTY handle,
incarnation, viewport, zoom and title. PowerShell computes RENAME_42 from a split
literal and multiplication; the complete expected marker is absent from the
echoed command. The observation is therefore not satisfied by echo alone.
Positive PID existence is supplemented by child-computed output.

Admission failure is an error outcome, not a skip/pass. Outer cleanup runs before
assertions, including after failed child acquisition or intermediate operation.
It collects retained owned PIDs and checks absence after checked session cleanup.
Capture/cleanup attempts are finite. Those outer deadlines do not preempt a
single blocking native call; qualification still needs an external watchdog.
A scalar PID check can encounter reuse and does not prove descendant quiescence
alone; real provider/process-tree cleanup receipts remain required.

Both manual mirrors accurately state authored/NOT_RUN status and the in-process
API boundary. They do not claim a network route, simulated native failure, or
automatic provider admission. Canonical docgen and runtime receipts are pending.

## Remaining gates and scope boundary

Closing-state refusal, exhausted-authority behavior, genuine deferred/failed
native close, configured library/provider selection and canonical runtime checks
remain execution gates. The source cases do not manufacture failure injection or
claim branch coverage percentages.

The adapter plan enumerates 30 commands plus nine other operations. Its
RenameWindow row correctly distinguishes this implemented owner mechanism from
pending typed dispatch/receipt and runtime qualification. The remaining server
loop, startup admission, capability table, object-ref scope and command routes
are explicitly pending. This review closes only the bounded rename source
review, not full CoreMux or tmux parity.

## Publication-only EOF normalization

The publication receipt
doc/09_report/smux_window_rename_publication_normalization_2026_10_26.sdn
(SHA256 714efbbbe9d8db0af3267da925c9cecf205e8708a51b254ec17bd654cd5e3ed3)
was independently checked against retained copies under
build/review/rename-eof-before/. All three before/after hashes matched. Strict
UTF8 decoding succeeded and each retained prefix before trailing CR/LF bytes was
identical. No semantic document or production-source change was reviewed here.

| Path | Before SHA256 | Published SHA256 |
| --- | --- | --- |
| doc/03_plan/agent_tasks/coremux_server_adapter_2026_10_26.md | 57e7bb52a69b00cda4fdcecb4644b96cc153830acbebedc03b5b3d2f407ff7d7 | ae54867d1a7beeaaaef85821fd0bba56a2bc39a7a00de03e02cf75430cfc10c1 |
| doc/06_spec/01_unit/tools/smux_window_metadata_spec.md | 9e075df490220a1747d2f12da3d84f8cff47e39ea2f75ab500a30390bc39d673 | bc2ccae8af78a85630f539d2a9ae87c359e263ebd13c3d104f065836351732f7 |
| doc/06_spec/03_system/tools/smux_window_rename_spec.md | d6bb3d82b42dc42420cb475660ecfbaea713efbff9c518dffc930b9dca270c5c | 81f6468942c1f7dfa301335d2f08644949574345d4d580daadbe1f7e0295f4f3 |

The two manual hashes above supersede their earlier source-freeze pins only for
publication. Original pins remain preserved in this report. The third path is
the tracked adapter-plan copy. The private matrix remains unchanged at
37b4a0dcf64c89e15da61338055272f458c5c55f3a1578bf261101624d849cab.
Source acceptance and NOT_RUN status are unchanged. No production rereview,
test/check rerun, staging or commit was performed.

## Cycle 2: tmux-compatible nonunique labels

Source correction cycle 2. STATUS: WARN / source accepted; all execution NOT_RUN.
No remaining scoped P0/P1/P2 finding was identified in this six-path delta.
Five unit cases and two system scenarios remain authored, zero executed.

The v2 manifest build/review/smux-window-rename-source-v2.sdn matched SHA256
ef6b7ab2d301e7a9664752566b8fa92047665bda0391fb9db8c02d4b4765dcf2.
All six file hashes matched:

| V2 path | SHA256 |
| --- | --- |
| src/os/apps/smux/window_metadata_service.spl | dc9c2781f8857ddbbfc9b79cf011d860dd4c870e6d635f84f5cab56cc7510569 |
| test/01_unit/tools/smux_window_metadata_spec.spl | a4b67c4f576386d241c181aea72d0f57b4b95c2d730e76a0bd8b3550eeb8de37 |
| test/03_system/tools/smux_window_rename_spec.spl | e63bb4e8a82e6b75bc0f117f0c93b8fca93630e174fe57fc89d0e1e56418e564 |
| doc/06_spec/01_unit/tools/smux_window_metadata_spec.md | bf0bc266ca90687b1539009ea6a48423e85d3f298b1d932acecba8ebf2fc2c86 |
| doc/06_spec/03_system/tools/smux_window_rename_spec.md | fee7eb237fe0efd8854a3585555ac4c95bed3e18cd66d9857b1eabbabb71060b |
| doc/09_report/smux_window_rename_source_2026_10_26.md | eea9dfeb8208e4e3f8728aa845c6dd93a1f2c2b672aebcabfa0294646fee31fb |

### Policy correction and primary evidence

The v1 collision-refusal policy and its earlier acceptance above are superseded.
The official tmux Getting Started wiki states that window names do not have to
be unique. This was independently retrieved through the context fetch/index tools
at the immutable [cf5a82fad1144475335e078548b6ed18fc37422c revision](https://github.com/tmux/tmux/wiki/Getting-Started/cf5a82fad1144475335e078548b6ed18fc37422c).
That supports treating names as display labels rather than uniqueness authority.

The production delta removes only the peer-name/peer-ID collision loop and adds
a clarifying comment. Canonical clean UTF8 validation, existence/membership,
unchanged-name handling and the full metadata-preserving constructor remain.
Duplicate names, peer-ID-like labels and own-ID-like labels are accepted without
changing IDs. Inspected ServiceState.find_window_idx matches window.id exactly;
an ID-like label does not acquire stable-ID target authority.

The future name-based ResolveTarget path is not implemented by this correction.
Its ambiguity refusal remains an integration requirement. This review does not
claim full tmux target grammar, index semantics or resolver parity.

### Updated oracle review

The changed unit scenario checks two equal names, independent exact IDs and
lookup slots; then a label equal to a sibling ID, followed by an actual rename
of that sibling. It verifies that the first window remains untouched.

The system metadata path checks four real API configuration changes against the
captured baseline: Unicode rename (+1), peer-ID-like label (+2), sibling rename
through its actual ID (+3), then duplicate label (+4). The intermediate snapshot
checks both labels, avoiding a false pass from only checking a returned record.
Repeated same-name requests and invalid/control/foreign-session refusals leave
the expected revision unchanged. Distinct IDs remain addressable after the
duplicate-label operation. These are authored production-path assertions, not
executed results.

The live-child scenario and outer cleanup-before-assert structure are unchanged.
Updated manuals/report accurately supersede the earlier uniqueness policy and
retain NOT_RUN status. No concurrent L1 record/context fields, API publication,
common contracts, service revision or L2 launch changes were accepted under this
review. Original v1 pins and publication-normalization evidence remain preserved.
No source edit, build, executable/test launch, staging or commit was performed.

# Phase 2 tooling feature verification

Status: INCOMPLETE. User selected Phase 2 feature checking while Phase 3 is
unavailable and authorized landing features once they work with Phase 2.
This does not qualify Phase 3 or permit bypassing feature verification.

Frozen initial source: aa3ded114ec, release base bb7fcfa4673 plus the tooling
fixes and modern stdio specs. Isolated checkout:
`D:/dev/simple-tooling-phase2-check-20261026`.

Producer: pure-Simple Phase 2, SHA256
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`.
Its matching frozen runtime capsule is under
`C:/dev/simple-phase3-bootstrap-owned/build/bootstrap/phase2-runtime-capsules/`
with that digest. Target Windows MSVC, LLVM, core-c-bootstrap runtime bundle.
The exact producer's provenance/admission and sanity receipts were inspected.
A fresh Hello native build and execution passed (exit0, expected output).
It exposes compile/native-build, not general check/test commands.

## First finite collection

Evidence: `build/tooling-phase2/<row>/` and `matrix.sdn`; separate private
caches, enforced 6GiB caps and 900-second collector bounds per row.

| Row | Current evidence |
| --- | --- |
| MCP | MIR FAILED: inferred token value cannot dispatch contains; shared CodecError payload mismatch; additional non-array loop errors. No link. |
| LSP MCP | MIR FAILED: CodecError payload mismatch; file_text_session byte-array loops inferred I64. No link. |
| Markdown LSP | HIR FAILED: unresolved parser helpers and array type. Uncommitted earlier Markdown repair is preserved in its original checkout, not silently included here. |
| T32 CLI | HIR FAILED: app.t32_cli.mod does not export t32_cli_main. |
| T32 MCP | Source loading FAILED: t32_mcp sibling-qualified imports unresolved by this producer's default roots. |
| CMM | Initial main.spl path absent; corrected server module reaches HIR and fails unresolved print_raw. This is a setup correction, not a server PASS. |
| SSpec runner | RUNNING, exec session7725; source frozen until terminal. No examples executed. |

## Typed Result payload investigation

Bug: `phase2_result_payload_nominal_type_loss_2026_10_26` (open, unproved root).
The shared text-I/O contracts already declare correct Result payload types.
CodecError contains kind, byte_offset and reason; none may be discarded.
Current old-producer diagnostics do not identify which two of six wrappers
caused the identical Codec variant mismatches.

Proposed falsifiable workaround after the live runner finishes: explicitly
type Result call locals and forwarded codec payloads; explicitly type byte-
buffer Result locals and retain array push results. Check actual byte values
and structured error kind/offset before accepting it. Do not replace array
loops merely to conceal I64 inference or weaken errors into strings. Bind the
token tuple's kind/value to text before retrying envelope lowering. A failure
remains a failure; no placeholder passes, guard bypasses or invented test counts.

Landing requires the selected feature's real native behavior and applicable
SSpec/core gates, reviewed exact PR contents, and merge. No feature is yet
admitted for landing from this Phase 2 cohort.


## First collection terminal and typed retry

The SSpec runner terminated with exit139 at MIR entry after its286-module HIR
closure and monomorphization. Peak RSS1827404 KiB; no executable or examples
passed. CMM server also failed HIR on unresolved print_raw. Initial rows are
terminal before source edits; retained logs remain immutable.

Changed-source compatibility attempt two pins token tuple fields to text,
codec Result expressions and forwarded CodecError locals to declared types,
and byte-buffer Results to their concrete sum type. Array append results are
retained. This preserves error fields and byte-loop semantics; it is an
unqualified old-producer workaround until actual values/error regressions pass.
LSP MCP retry: build/tooling-phase2/lsp-mcp-typed, exec session73187, same private
cache owner and enforced limits. No overall PASS or landing admission yet.

## Changed-source results

LSP MCP typed attempt two FAILED with the same Codec payload and byte-array
MIR errors. Removed the ineffective shared text-I/O edits; preserved the failed
log at `lsp-mcp-typed/`. No claim that explicit bindings repaired that owner.

The envelope's separately typed tuple fields compiled in an actual-production-
parser native probe. Executing `mcp_envelope_probe.exe` exited0 and reported
16 input cases /96 actual assertions. This qualifies the focused parser input
set only, not the full MCP consumer or a general SSpec run. Source fixture and
receipts remain in `build/tooling-phase2/envelope-probe/` and its sibling file.

Copied the existing uncommitted Markdown repair into this isolated cohort,
preserving its original checkout. Phase2 compiled/linked the repaired17-module
closure, and initialize/shutdown/exit ran successfully. A real didOpen followed
by documentSymbol returned First/Second headings and correct source lines.
However folding request ID3 and string request IDstring-id both returned ID0.
This is a functional protocol failure, not PASS. Captures:
`build/tooling-phase2/markdown-functional.stdout` and `.stderr`.
Markdown remains unqualified for landing despite compile/link and handshake
success. The same cohort's parser/fence and document-mutation requirements
remain to be verified. No unsupported full-feature readiness inference.

## Markdown request correlation repair

Phase2 Markdown attempt three compiled/linked the19-module closure successfully
(`markdown-ids/`). Wire dispatch now validates the root envelope and carries its
lexical ID to raw response handlers. Existing integer-call interfaces remain
adapters. This removes both string-to-integer coercion and failed optional
numeric conversion defaulting to zero, without accepting nested IDs as root IDs.

Actual native folding requests passed with IDs3, string-id, an escaped quote/
backslash string, integer9007199254740993, and genuine Korean/emoji. The live
document produced two fold ranges for each. Seven responses exactly matched
initialize, five requests, shutdown; notifications produced no replies, frame
lengths parsed exactly, and exit0. Captures: `markdown-ids.stdout`/`.stderr`.
Added3 meaningful SSpec examples for raw success/error IDs and the retained
integer facade; these are authored, not executed by the crashed general runner.
Document changes, parser edge cases, and remaining qualification are incomplete.

## Markdown state and fenced-block checks

The prior IDs binary passed full document replacement (Updated supersedes the
old headings) and closing (subsequent symbols empty). Captures: markdown-state.
That exchange exposed raw-line symbol/definition scans leaking fenced headings.
Changed these handlers to use cached parsed blocks; retained physical source
line ranges. Folding now stops at a closing fence rather than merging adjacent
fenced runs. Phase2 attempt four compiled/linked successfully (markdown-blocks).

Actual native checks passed: Visible/Last symbols omit Hidden inside code;
the link to hidden returns null; adjacent fences fold separately at1..3 and4..6
without a merged1..6 range; process exits0 and frames parse exactly. Captures:
markdown-blocks.stdout/.stderr. Added two meaningful SSpec regressions, UNRUN
under the unavailable general runner. Unicode source-position semantics and
remaining advertised methods still require checks before landing.

## Markdown UTF-16 positions and actual method checks

The prior candidate emitted endCharacter12 for a heading requiring6 UTF-16
units and returned no action for a line3 quickfix. Numeric position parsing
used optional text-to-integer conversion, the same old-producer hazard as IDs.
Phase2 Markdown attempt five replaces it with overflow-checked decimal parsing,
maps inbound completion columns from UTF-16 to whole UTF-8 code points, and
counts outbound symbol/edit columns in UTF-16. JSON string values now use the
shared decoder, preserving Unicode escapes and surrogate pairs.

The19-module candidate compiled/linked. Actual native requests verified escaped
Korean/emoji document content, symbol endCharacter6, definition target line2,
line3 quickfix replacement, and Unicode line4 edit endCharacter9 with exact
new text. Completion and heading hover responses were also observed in that
exchange; no broader correctness is inferred merely from a result response.
Captures: markdown-utf16.stdout/.stderr; build evidence markdown-utf16/.
Added a meaningful UTF-16 conversion SSpec, authored/UNRUN. The general runner
still crashes before examples. No overall verification PASS or merged feature
is claimed. Five Markdown Phase2 build/repair cycles accounted, one remaining.

## Markdown transport headers: final sixth cycle

A valid Content-Length-first / Content-Type-second request exposed truncated
body consumption in the old header loop. Final Markdown cycle six consumes all
headers through the blank separator, rejects duplicate lengths, and parses
decimal lengths with overflow/invalid-character refusal. The19-module native
candidate compiled/linked (markdown-headers). Actual exchanges passed two
consecutive initialize requests for each header order; IDs11/12 and frame
boundaries matched. Negative, junk-suffixed and overflowing lengths refused
without emitting a fabricated JSON response. Captures: markdown-headers-*.
No further Markdown repair/build cycles under the six-cycle cap.

The general runner's second attempt enables supported SIMPLE_COMPILER_TRACE
for diagnosis, retains checks/limits and remains live (session59391). A smaller
existing production wrapper owner was located:
std.test_runner.test_result_wrapper.preprocess_spipe_native_result_file_in.
It preserves authored helpers/imports and lowers real cases to the framework's
rt_bdd counters/results, rejecting zero execution. A small generator entry may
call this function to run focused authored specs without replacing the runner
framework or claiming full runner qualification. Execution is still pending.

## Canonical wrapper execution blocker collected

The traced general runner terminated exit139. Its last trace identifies
MIR module start idx0 app.test_runner_new.main, after HIR/monomorphization;
this is a boundary observation, not a proven defect in that entry function.
The smaller generator importing the existing production wrapper owner also
terminated exit139 at MIR entry after a93-module closure. Its source invokes
preprocess_spipe_native_result_file_in for the authored Markdown/parser specs;
it did not run, so no generated spec or BDD example execution is claimed.
Evidence: sspec-runner-traced/ and spec-generator/ under build/tooling-phase2.

This is three distinct runner-path diagnostic attempts (general, traced,
smaller production generator), all retained. Stop the unchanged shared crash
loop and investigate the compiler owner before any further build retry. Existing
native wire/probe checks remain focused evidence, not canonical SSpec PASS.
No feature is landed while its mandatory verification is unavailable.

## T32 Windows alias preparation

Inspection found src/app/t32_cli, mcp_t32 and cmm_lsp were regular path-text
files (tracked mode120000), not usable directory aliases. This invalidates a
source-only interpretation of the earlier CLI missing-export diagnostic.
The canonical scripts/setup/materialize-symlinks-windows.shs ran in this
isolated owner: created55, already_ok0, failed0, strict_missing1, exit0.
Receipt is outside the checkout as required:
`D:/dev/simple-tooling-phase2-evidence-20261026/materialization.sdn`.
The receipt's producer hash identifies the materializer, not the compiler.
Two earlier setup refusals (Windows-form receipt path; receipt inside source
owner) performed no successful conversion and remain in separate retained logs.

T32 CLI changed-input verification is live, exec session85862, evidence
build/tooling-phase2/t32-cli-materialized, pinned Phase2 producer and unchanged
feature source. No CLI execution or PASS inferred from successful link setup.

## Materialized follow-up failures and process-facade repair

Materialized T32 CLI collection reached the real source helper and failed HIR
on unresolved rt_process_run in src/app/mcp_t32/json_helpers.spl:328. This
supersedes the placeholder's missing-export diagnostic. The helper already
imports std.io_runtime.process_run; changed only the erroneous direct runtime
call to that established platform facade, preserving arguments and tuple/error
semantics. Its owner resolves POSIX tool paths on Windows and uses the bounded
process path there. Actual behavior is still required, not inferred from import.
New build: t32-cli-process-facade/, session10511, RUNNING at last observation.

Materialized production wrapper-generator attempt also terminated exit139 at
MIR0/93, peak704540 KiB. This rules out missing alias materialization as a
sufficient remedy for that crash. Canonical examples executed remain zero.
Evidence: spec-generator-materialized/. Four runner-path attempts accounted;
do not rerun this input without a compiler-owner repair or new diagnostic.

The corrected T32 CLI source passes HIR and reached MIR0/143, but the build
remains live; no executable behavior is claimed. The working direct-env guard
now FAILS on direct rt_env/rt_process calls exposed through materialized
src/app/{cmm_lsp,mcp_t32,t32_cli} aliases. These are existing underlying example
sources newly visible as app leaves, not a PASS to suppress. Facade migration
and normal gate verification remain necessary before feature landing. Preserve
materializer-created junctions/hardlinks; do not stage their apparent link
deletions or unrelated command/document aliases in a source commit.

## Materialized leaf facade migration

Seven physical example files now import std.io_runtime env/process facades
instead of declaring/calling raw environment/CWD/process primitives. The working
guard passes against the materialized app aliases. Independent static review
found no new P0/P1; imports resolve at top level and process tuples retain
stdout/stderr/i64 status. Semantics are explicitly the facade contracts:
env_get_opt treats unset AND empty as absent (nonempty debug/log defaults now
apply to empty values); cwd_process falls back to "." on raw CWD failure, so
old empty-CWD/PWD recovery branches are no longer taken in that case. This is
not claimed to be a purely mechanical behavior-identical rename.

Actual Phase2 object attempts for startup_log and CLI session both FAILED in
the shared TextIoError.Codec / file_text_session I64-array MIR failure family.
Neither emitted a qualifying object. Evidence: t32-startup-facades/ and
t32-session-facades/. Source migration is reviewed but runtime UNVERIFIED;
do not merge it merely because the guard is green. The same underlying compiler
boundary blocks MCP/LSP and these leaf consumers. Retain their independent
failure rows rather than repeating the unchanged shared failure.

## Shared payload crash reduced to one module

See phase2_result_payload_native_crash_2026_10_26.md and the paired canonical
fixtures under test/fixtures/compiler/phase2_result_byte_codec/. The Result
composition crashes before object generation; direct payload control compiles,
links and executes3 actual assertions. This is stronger boundary evidence,
not a root-cause proof or general SSpec PASS. Six shared compiler/runner
diagnostic attempts are now accounted. Stop this repair/build loop pending an
explicit extension; preserve the failed and passing inputs without green reruns.

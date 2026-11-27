# Tooling completion: Astra guidance and review

Status: SOURCE_REVIEW_COMPLETE_VERIFICATION_BLOCKED. The requested goal is not
complete; no release, overall verification PASS, or merge admission.

Owner: root orchestrator. Final source reviewer: Astra repair lead. User explicitly
requested agent assignments with Astra guidance/review and authorized three
additional coordinated repair cycles. Preserve the six prior shared compiler
attempts and each feature lane's existing attempt ledger; this extension does
not reset them. Root alone starts builds, integrates changes, and lands the PR.

## Scope and ownership

| Lane | Agent | Writable scope | Acceptance boundary |
|---|---|---|---|
| Compiler | phase2_compiler_repair | src/compiler and compiler regressions | Original Result composition builds and executes all three assertions |
| MCP/LSP | phase2_mcp_lsp_repair | MCP, Simple LSP MCP, shared protocol, file text session and corresponding specs | Real native framing, envelope dispatch, IDs, text-I/O and server checks |
| T32/CMM | phase2_t32_cmm_repair | Physical examples/10_tooling/trace32_tools and corresponding specs | CLI/MCP/CMM link and actual behavior, including strict/tolerant parser recovery |
| Markdown | phase2_markdown_specs | Markdown LSP and corresponding specs | New code-fence exclusions and authored native SSpec execution |
| Guidance/review | astra_repair_lead | This coordination document only | Review actual diffs, evidence, semantic preservation and remaining gaps |

Materialized junctions/hardlinks and unrelated dirty files belong to setup or
other sessions. Never stage their apparent deletions or fold unrelated edits
into this change. Source owners freeze manifests before root builds closures.

## Shared interfaces and evidence

- Keep the original `result_payload.spl` fixture frozen; it is the acceptance
  test. `direct_payload_control.spl` already passed and must not be replayed
  unchanged as proof of Result correctness.
- Existing named helpers take precedence over new names. If required, use
  `expect_jsonrpc_error`, `expect_jsonrpc_id`, `exchange_stdio_frames`,
  `parse_cmm_fixture`, `expect_cmm_statement_kinds`, and
  `expect_cmm_recovery_after_error` consistently within their owning specs.
- Preserve the Markdown `md_stdio_*` helpers. New manual step labels may use
  `send Markdown request`, `check Markdown response`, `check server exit`.
- Unimplemented scenarios must fail with `assert(false)` or `fail(...)`;
  they cannot contribute passing execution counts. Native wire probes are
  focused evidence, not canonical SSpec runner qualification.
- Retain prior IDs, Unicode positions, header order, document state, fence
  symbols/folding, Hello and envelope greens. New binaries require their own
  relevant changed-input checks, but unchanged checks are not repeated for
  reassurance. All source-only regressions remain explicitly UNRUN.

## Compiler diagnosis sequence

1. Extension cycle 1: root traced the original Result fixture with the existing
   immutable Phase2 producer. It still exited 139 after MIR module completion;
   no object or assertion execution. Evidence:
   `build/tooling-phase2/result-owner-probe/astra-trace1/compiler.log`.
   This narrows the boundary, not its root cause. Two extension cycles remain.
2. Inspect the alternate admitted pure-Simple Phase2 producer discovered by
   compiler owner, including provenance and matching runtime capsule. Candidate
   SHA256: `17d1a40abc390c08c05cec3ba13db41eb12ee5709126c6636fe974f753f7e5ac`.
   Root qualified exact bytes with fresh compiled-and-executed Hello (PASS),
   then the frozen Result fixture again exited 139 after module MIR completion.
   Evidence: `build/tooling-phase2/astra-alt/{hello,result-original}`. Treat
   qualification and its component rows as one changed-producer cycle. One
   shared extension cycle remains, reserved for meaningful debugger evidence
   or a concrete changed compiler owner; no blind full rebuild is justified.
3. Only a newly successful original Result fixture justifies dependent shared
   text-I/O, production SSpec generator/runner and MCP/LSP/T32 retry. If it
   fails, retain the new boundary and use the remaining cycle only for a
   concrete changed owner or diagnostic with an explicit hypothesis.

Typed MIR diagnostic collection is currently a speculative hardening, not a
proven fix and is being removed after static crash mapping. Existing
current-source payload/provenance repairs are not evidence
that the immutable older compiler contains them. Do not erase errors, flatten
structured payloads, or replace the genuine SSpec runner to obtain a pass.
The preserved source manifests show both old producers already retain Result
array payload provenance and local HIR types. Neither contains the current
`enum_match_subject_type` declaration-ownership fallback; the alternate adds
Optional provenance and lambda ABI changes. Do not overstate this as all old
Result provenance being absent.

Extension cycle 3 captured a native null read (`C0000005`) in the alternate
producer at `0x7ff74f4aae60`; the instruction was `movq (%rax), %rdi`.
Evidence: `build/tooling-phase2/astra-alt/result-debugger-ready/compiler.log`.
The debugger's exit 0 records debugger completion, not compiler success. No
object/executable was admitted. A prior debugger setup refusal (missing DLL,
before compiler invocation) is separately retained. All three shared extension
cycles are now consumed; static symbol/instruction mapping may continue, but
no unchanged build or debugger replay is authorized by this plan.
Static PE mapping positively identifies the fault in
`mir_verify_type_unresolved_reason`, which dereferences a missing type before
reading its kind. The authorized source repair is a fail-closed diagnostic and
real-owner regression; it cannot make the malformed Result input valid. The
missing-type producer and rebuilt-compiler qualification remain outstanding.
Review found ordinary `MIRV-001` findings are warn-first, so merely returning a
new reason is insufficient. Root authorized the narrow rule-registry expansion:
`MIRV-001n` identifies a missing type declaration, defaults to error, and is
mandatory before warning-phase or per-rule suppression. Shared names are
`MIR_VERIFY_MISSING_TYPE_REASON_V1`, `mir_verify_type_reason_rule_v1`, and
`mir_verify_finding_is_mandatory_v1`. Report severity and driver consumption must
agree; existing unrelated unresolved-type warnings keep their current policy.
Final static review found and required repair of a masking path: a soft
unresolved Result/Tuple sibling previously hid a later missing carrier. Both
walks now prioritize mandatory absence while retaining the first soft reason
otherwise; a real-module regression covers both mixed forms. After inspecting
that repair, Astra found no remaining P0/P1 in the scoped verifier packet.
This is source review only: new compiler execution and canonical specs remain
unverified, and the existing bounded type-walk depth is not a claim of
arbitrary-depth structural validation.

## CMM design decision

The runtime and split parser extend the same `CmmParser` with 62 overlapping
methods. Owner review classified 22 differing bodies as 18 equivalent forms
and four material behavior differences. Preserve strict and tolerant callers:

- One split statement implementation owns parsing. Add explicit
  `recover_unclosed: bool` and `warnings: [text]` parser state, and
  `warnings: [text]` on `CmmProgram`; update explicit constructors rather than
  relying on uncertain default-field syntax.
- Export `parse_cmm_source_with_policy` with existing arguments and the final
  recovery flag. Public parser keeps strict behavior (`false`); runtime facade
  keeps tolerant behavior (`true`). Existing public entry signatures remain.
- Unclosed block/dialog recovery and runtime detailed diagnostics survive.
  Strict callers retain strict errors and diagnostic wording. Cursor recovery
  must make progress without consuming the next valid statement twice.
- Paired strict/tolerant regressions cover unclosed blocks, unclosed dialogs,
  detailed errors and valid-program equivalence before old duplicate bodies
  are considered safely replaced. Native execution remains required.

Review identified a cursor-ownership difference: split parser wrappers passed the parser
through free functions, while runtime methods called implementation methods on
`self`. The canonical route now directly calls `self.*_impl`, preserving mutable
receiver ownership. All genuine production-type constructors are updated.
Five apparent extra constructors belong to locally defined fake parser types
in historical test suites; adding production fields there would be incorrect.
The two canonical system parser suites have now been replaced with actual
production-parser imports and AST assertions, preserving 82 statement and 80
expression scenarios. They remain authored/UNRUN, not execution evidence.
Three separate facade-equivalence cases retain coverage of the file-facing
import paths while the pure source-owner cases avoid unrelated file I/O.
The original positive `--1` nested-negation scenario is retained as a genuine
assertion and a known unsupported grammar path, not flipped to a passing
negative case. Overall completion requires resolving that grammar issue too.
CMM extension cycle 1 passed HIR and reported zero ambiguity, then failed with
14 MIR diagnostics: statement payload mismatches plus the known shared
text-I/O payload family. No executable or test execution. Evidence:
`build/tooling-phase2/astra-cmm/probe-run/compiler.log`. Two CMM extension
cycles remain, but retries require a concrete changed input; the compiler
owner failure is not repaired by repeating this closure.

Root subsequently authorized a genuine source/file ownership split to collect
independent parser evidence. Move the existing source parser implementation to
`cmm_parser_source.spl`, exporting `parse_cmm_source` (strict) and
`parse_cmm_source_with_policy`. Existing public/runtime facades retain their
source/file signatures and `read_file` behavior, delegating to the same source
owner. Native source-parser fixtures may import that production owner; they
cannot qualify file APIs, CLI, MCP or LSP while shared text I/O remains blocked.
Do not clone the parser, substitute a fake wrapper, or replace file I/O with
raw FFI. Preserve the original positive nested-negation (`--1`) requirement as
a real assertion unless an authoritative language contract establishes that it
is invalid; a lexer limitation alone cannot justify flipping expected success.

Conservative combined T32/CMM extension cycle 2 compiled and linked the
independent two-module state-owner probe, then the executable failed an
assertion (exit 1). Its eleven authored assertions have no per-assertion
progress labels, so neither the first failing check nor an executed-pass count
is proven. Evidence: `build/tooling-phase2/astra-cmm/state-run` and
`state_probe.spl`. No unchanged rerun. The final combined extension cycle 3 is
reserved for the reviewed pure source-parser fixture. The state failure remains
an independent blocker, even if the parser fixture succeeds.

Astra's final static review found no remaining introduced P0/P1 in the scoped
T32/CMM packet after direct mutable receiver dispatch, constructor coverage,
source/file owner separation and original positive grammar-test preservation.
This approves the frozen source for the final bounded probe, not release or
runtime acceptance. The nine guarded expression-extraction workarounds retain
the original Err returns and use the existing concrete expression helper;
their removal still requires the original form under a repaired producer.

Final combined T32/CMM extension cycle 3 compiled the real pure source-parser
closure through all eight MIR modules, then exited 139 before object emission.
Peak RSS was 234060 KiB; no runtime assertions executed. Evidence:
`build/tooling-phase2/astra-cmm/pure-source-run`. This closure has no file-I/O
dependency, so the compiler blocker is independent of shared text I/O. All
three renewed combined T32/CMM cycles are consumed. No further build or
unchanged probe retry is authorized by this plan.

## Reviewed independent Markdown result

The changed native Markdown server compiled, linked and passed exact fenced
hover=`null`, definition=`null`, codeAction=`[]`, and outside-heading hover
responses, including full framing, correlated IDs and process exit 0.
Evidence: `build/tooling-phase2/astra-markdown/code-guards`.
Authored canonical SSpec suites remain unexecuted while the runner is blocked.

## Admission and completion

Source review alone cannot admit this change. Required native binaries, actual
SSpec execution, repository gates and generated-manual quality must pass under
qualified producer/runtime identities before overall PASS and PR landing.
Replace scoped historical fake parser suites with imports and assertions
against the real production parser. Placeholder passes, local parser copies,
fabricated statement counts, and duplicate fake wrappers are merge-blocking;
source replacement alone remains UNRUN until canonical execution succeeds.
Root reads PR findings and lands only the reviewed changes. No release tags or
publication are authorized by this coordination plan.

## Final review handoff and outstanding gates

Source review is complete for the Markdown, MCP/LSP, compiler-verifier and
T32/CMM packets. Root owns commits and integration, preserving the externally
updated PR branch through a separate integration checkout. Conflict resolutions
and the exact integrated diff require review; source approval does not admit
the PR for merge.

Remaining gates:

- Rebuild/qualify a repaired pure-Simple compiler and execute the original
  valid Result fixture; the new mandatory diagnostic is not a payload fix.
- Execute the new verifier and driver-route regressions, including mandatory
  behavior under warning/off overrides and mixed unresolved/missing siblings.
- Repair the independent T32 state assertion failure with identified checks.
- Compile/link/run the real CMM source parser; resolve the retained positive
  nested-negation grammar requirement and run canonical parser/facade SSpec.
- Build and exercise full MCP, LSP, T32 CLI/MCP, CMM LSP and file APIs with
  structured text-I/O payloads intact. Narrow helper/transport probes do not
  replace these product gates.
- Execute canonical Markdown/MCP/LSP/T32 SSpec through the production runner,
  generate current manuals, and complete required compiler/lib/MCP/LSP checks,
  environment-owner audits, core/native smokes and integrated PR review.

Known successful narrow evidence remains valid: prior native Markdown
IDs/Unicode/header/state/fence checks, the newly changed Markdown code guards,
qualified Hello controls, and retained production-envelope probes. None turns
the failed Result, state, parser, runner or full product rows into PASS.

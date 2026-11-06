<!-- codex-design -->
# Release 1.0.0 memory and MCP/LSP verification plan

Status: **NOT_RUN**. No executable or generated-manual result is asserted here. The complete test obligation inventory is [feature requirements](../../02_requirements/feature/release100_memory_mcp_lsp.md), containing all 44 memory ACs, 12 formal obligations, 69 MCP/LSP acceptance rows, numbered sections and release checklists. [NFR requirements](../../02_requirements/nfr/release100_memory_mcp_lsp.md) preserve measurement targets and undecided host-specific caps.

## Evidence binding

For each requirement record implementation owner/path, executable scenario, actual public front door/route, producer/compiler hash and provenance, source revision, runtime/provider/target/config identity, command, exit/result, executed assertions/cardinality and retained receipt. Status is PASS, FAIL, BLOCKED/UNAVAILABLE or NOT_RUN with reason. Missing evidence, zero scenarios, failed compile, timed-out reporter, fake empty result and unsupported backend cannot be PASS. Source inspection is useful diagnosis, never runtime parity.

Use `test/` for executable `.spl` scenarios and mirrored Markdown under `doc/06_spec` after removing the `test/` prefix. Retained plan §20.1's conflicting executable placement suggestion is overridden by repository policy. Generated manuals require docgen, zero stubs, seven-score `sspec-maintain` review and root's operator-readable review; authored mirrors are not generated PASS.

## Scenario groups

| Group | Obligations and oracle |
|---|---|
| Mandatory ownership | AC-OWN/AC-BOR plus strict no-GC bypass negatives; valid exclusive paths and CFG permutations; real source-to-execution routes |
| Resource lifetime/failure | AC-DROP/FAIL/CONT/REG/HANDLE/CYCLE, exact initialized cleanup counts/order, failure injection and nonwrapping owner-bound handles |
| Pipeline/cache/identity | AC-PIPE/CACHE/HASH, fused/split equality and counters, collision injection, immutable publication, actual sharing and read-quiescent eviction |
| Supervision/metrics/tracking | AC-PROC/BUDGET/METRIC/DB/GATE, no descendant/reservation leaks, calibrated units, lossless SDN migration and independent false-green rejection |
| Proof/refinement | All FV roots, pinned Lean versions, transitive axiom/contract audit, finite-width/failure transitions and implementation-linked events |
| Viewer/languages | VIEW/LANG rows, real MCP first/second/concurrent opens, versioned preferences, exact Unicode/range/overlay behavior and provider truthfulness |
| Diagnostics/edits | DIAG/FIX rows, successful-exit warning, timeout/crash payloads, Windows paths, empty deletion/multi-file edits, conflicts and actual post-edit analysis |
| Semantics/history/environment | SEM/HIST/ENV rows, symbol identity, unresolved effects, frozen history predicates, actual consumer config and pre-index redaction |
| Debugger | DBG rows, actual pre-unwind worker/fiber stop, shared target/epoch, real write event, dump/build mismatch and replacement receipts |
| Protocol/security/performance | CACHE/PROTO/SEC/PERF rows, framing/cancel/restart/permissions, 3,000 distinct-key stress, warm latency/RSS and honest limits |
| End-to-end/experiment | MCP scenarios A/B/C; A–E paired representations with fixed tasks/models/revisions/budgets and confidence intervals |

Every supported row has positive and rejecting controls where applicable. Mutation families from memory §12.3 must independently fail for checker bypass, owning-copy substitution, missing cleanup/scope end, borrow extension, linear CFG order, orphan worker, missing cap, collision/dependency omission, fabricated zero metrics, removed test/wiring and weakened proof root. Mutations run only in isolated bounded builds, not the shared worker.

## Required matrix

Preserve seed interpreter as an explicitly labeled product-route row where the selected plan requires it; it is not fallback authorization or pure-Simple release evidence. Separately qualify self-hosted interpreter, JIT, native Cranelift, native LLVM and every production runtime provider. Include x86-64/ARM64 and applicable Windows/Linux/macOS/FreeBSD adapters, supported 32-bit/RISC-V and applicable GPU/VHDL/bare-metal ownership/transfer rows. MCP external providers and stopped-target debugger backends each need individual admission. Missing hosts stay BLOCKED/UNAVAILABLE with owner/prerequisite/resume command, never silent exclusions.

## Integration gates after runtime admission

Root resolves `<runtime>` to an exact provenance-admitted pure-Simple binary and records its hash. No directory-name assumption, deployed stale binary or Rust seed substitutes for admission.

```text
<runtime> check src/compiler
<runtime> check src/lib
<runtime> check src/app/mcp
<runtime> check src/app/simple_lsp_mcp
SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-core-runtime-smoke.shs <runtime>
SIMPLE_BINARY=<runtime> MCP_SERVER=<fresh-mcp> LSP_MCP_SERVER=<fresh-lsp> sh scripts/check/check-mcp-native-smoke.shs
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
bin/simple test test --whole --mode=interpreter
find doc/06_spec -name '*_spec.spl' | wc -l
```

Last command must print 0. Run changed-file lint, owned-directory duplicate-check, focused scenarios, generated-manual checks and actual performance evidence under the admitted runtime. If packaging changes, also build both MCP entry closures and run isolated npm package smoke. The whole-suite wrapper must resolve to the admitted binary; do not infer that from the command spelling.

## Current prerequisites and stop conditions

Runtime admission remains BLOCKED: the inspected PID 25734 is absent and its full-CLI HIR build failed on unresolved `exit` in an older worktree. The release base already has the import but no newly admitted runtime is established. This is a terminal build result, not an active wait. Source audit findings do not satisfy execution gates. Root assigns unresolved matrix rows and pins numeric host/product caps before acceptance. Each unchanged successful criterion runs once; fix retries produce new evidence and obey bounded cycle rules. Only full requirement-by-requirement review plus merged release-targeted PRs can close the overall goal.

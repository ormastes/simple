# Item 6 release_phase3 readiness — 2026-10-11

STATUS: BLOCKED. This report does not admit a Phase 3 runtime or mark Item 6 complete.

## Source and ownership

Integration target: `release_phase3`, revised from `20f619fe31b` to
`9434873b8d3` (PR #3074, cold HIR diagnostic dictionary lookup).
Owned worktree: `C:/dev/simple-item6-phase3-validation-20261011`.
Owned branch: `work/item6-phase3-validation-20261011`.
The existing Item 6 fixes from PR #2860 are already ancestors of this target.
Other sessions' dirty files, processes, outputs and caches were preserved.

## Fixes retained locally

- Normalize the directory returned by Git for Windows through `cd` and `pwd -P`
  before comparing it with the shell's canonical source root. Both readiness and
  recovery authority still reject Git errors and non-root paths.
- Restore `compile_specialized_template`'s declared `text` return by returning
  its computed mangled symbol. Both concrete compiler/linker callers and the
  default/release wrappers require `text`; the previous `Ok(CompiledUnit(...))`
  body violated that signature and fabricated an empty compiled artifact.
- Align readiness assertions with the current diagnostic disclosure, bounded
  diagnostic range filter, and full-`src` source snapshot. Keep the Stage 3
  command/provenance assertions; do not remove them to obtain a green result.

The separate `CompilationContext` trait still declares a
`Result<TemplateCompiledUnit, text>` interface. Its relationship to the concrete
`text` implementations requires runtime verification and is not resolved here.
The specialization helper does not itself implement native code generation.

## Evidence and remaining admission blockers

Windows root fix: shell syntax, whitespace, dirty-root refusal, nested-root
refusal and working/staged environment-boundary guards passed. Smaller-model
and primary review found no P0/P1 in that root fix. These passing checks were
not repeated without changed inputs.

The clean static readiness attempt after that fix refused
`diagnostic-transport-disclosure-missing`, exposing the stale source assertions
addressed above.

An actual bounded invocation of the receipt-matching pure-Simple Stage 2
compiler (`1d18beed32d7156d9dc0ed2025ed6da77af289778f97632b8f57e07e5a7137b8`)
with `check src/compiler/80.driver/pipeline_fn.spl` exited 1 with
`error: unknown command 'check'`. The compiler-only capsule cannot supply the
required compiler/core/MCP/LSP checks. The diagnostic corrected Phase 2 hello
producer is bound to another source revision and is explicitly unqualified.

The provenance verifier still reconstructs an older Stage 3 command: its
Stage 3 argument hash and transcript omit the focused-route marker and
composition selection, and use the old positional entry/cache policy. The
current bootstrap command includes `SIMPLE_BOOTSTRAP_STAGE3=1`, explicit entry,
composition sources and enabled retained frontend/HIR caches. Updating only the
readiness assertion would hide a genuine exact-transcript admission mismatch.

No source-bound Phase 3 PASS or full Item 6 runtime/performance acceptance was
established. Clean/warm/no-op/edit time and RSS evidence, semantic invalidation,
corrupt-cache recovery, equivalent executable behavior and applicable
bootstrap/core/MCP/LSP acceptance remain required by the canonical Item 6 plan.
No new fix was pushed or merged, and no tags/publication were performed.

Local bounded process evidence is retained under
`C:/dev/simple-bootstrap-storage/item6-phase3-validation-20261011/`.

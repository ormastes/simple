# Stage 3 ZeroKind root-cause evidence and provenance gate (2026-09-02)

## Scope

This assessment inspected preserved logs, snapshots, receipts, and source only.
It did not restart bootstrap, build a compiler, deploy a binary, or replace the
admitted parent. The preserved Sep-2 run is authoritative; older `s3i` and
`wt_s3_full` attempts are historical context only.

## Exact terminal failure

The preserved transcript `r3_full.log` has SHA-256
`9f852425c6f6df3ef8afe53737e4886bd02ebb8d6448ccea556e5dd2d73b561f`.
It records successful HIR type checking and monomorphization, followed by MIR
lowering. The worker then exits 1 on:

`E-MIR-TYPE-ZeroKind: lower_type received a well-formed HirType whose kind field is raw 0 (never written) while lowering compiler.driver.pipeline_fn.compile_specialized_template_release`

This rules out timeout, signal termination, linker failure, and a HIR-stage
fatal for this run. The failure is the pure-Simple MIR fail-closed guard in
`src/compiler/50.mir/_MirLowering/function_lowering.spl`.

The function suffix in that old message is not reliable attribution.
`current_function_names[len-1]` is the fixed tail of a module/program name
list, not the currently lowered function. Therefore the exact active function
was lost; `compile_specialized_template_release` is only the preserved scope
tail. The diagnostic now tracks and reports `active-function:<name>` directly.

The native-build parent captured 1,110,284 stderr bytes. It preserved the exact
fatal in its bounded transcript, but wrote the full stream under cleanup-owned
`stage3-tmp`; that spill no longer exists. Worse, a later 481,412-byte bounded
print in the same PID reused the identical `native-build-stderr-15834.log` path,
so it overwrote the first full stream before cleanup. The preserved diagnostic
block was sufficient for this root, but raw ordering and non-diagnostic context
were lost. Spill names now include a per-process sequence and prefer the
provenance-bound native cache's durable `diagnostics` directory.

## Root-cause boundary

`HirType` is a two-field aggregate (`kind`, `span`). Publication-time and
initial-consumption evidence in the existing bug record found valid type data;
the raw-zero field appears during MIR lowering. Existing comments in
`mir_lowering_types.spl` also document admitted native-ABI corruption when a
`HirType` aggregate crosses a by-value method boundary.

That mechanism is the leading hypothesis, not yet a proven conclusion. The
remaining competing explanation is that the aggregate is already dead before
the call. Source-shape edits that merely moved the victim function are not
evidence of progress and must not be repeated.

The default-off `SIMPLE_MIR_TAG_PROBE=1` probe stores caller state without
printing and emits one record only when a callee observes raw-zero `kind`:

- caller nonzero, immediate callee zero: the by-value call minted the dead copy;
- caller zero and callee zero: corruption occurred upstream;
- `site=recursive-or-other`: the initial signature crossing was healthy and a
  recursive or body-level transport is the narrowed boundary.

The earliest boundary supported by retained evidence is therefore the
function-signature handoff from a completed HIR function into MIR
`lower_type`; the historical log does not prove a specific function or an
earlier HIR producer. The production path now materializes each `HirParam`
before reading its enum-bearing type, records owner/context/index plus caller
and callee discriminants, and caps invariant receipts at 16. The executable
regression is `test/01_unit/compiler/mir/stage3_hirtype_transport_spec.spl`
with its minimal source fixture under `test/fixtures/compiler/`.

The existing ZeroKind fatal remains unchanged and fail-closed.

## Provenance-safe prerequisites before any restart

1. Freeze a new source snapshot after these diagnostic changes and record its
   SHA-256 plus git state; do not reuse the Sep-2 source binding.
2. Build and admit a new Stage-2 parent from that frozen snapshot. Record the
   parent binary hash, source/runtime/tool snapshots, sanity receipt, and
   planner-v2 admission. The preserved admitted Sep-2 parent is
   `565514d3bfab849b705cd68941d19b966b0b68f9c278a24bfc9dd211be374cf7`;
   it predates this probe and cannot produce decisive probe evidence.
3. Use generation-isolated HOME, TMPDIR, output, and writable cache paths. Do
   not share a writable cache between Stage 2 and Stage 3.
4. Run Stage 3 with `SIMPLE_MIR_TAG_PROBE=1`; the allowlisted assignment must
   appear in both the args hash and command transcript.
5. Keep `SIMPLE_NO_STUB_FALLBACK=1`. Preserve the full stderr at
   `<SIMPLE_NATIVE_BUILD_CACHE_DIR>/diagnostics/native-build-stderr-<pid>-<seq>.log`,
   hash it, and copy it into immutable run evidence before cache pruning.
6. Do not deploy any Stage-3 candidate from this diagnostic run. Acceptance
   still requires a candidate provenance manifest and sanity receipt; Stage 4
   additionally requires its planner-v2 authorization chain.
7. Classify exactly one probe run. Do not repeat a green or identical command;
   choose the root fix from the caller/callee result first.

## Current decision

Implement diagnostics and evidence preservation only. A semantic ABI repair is
not justified until the two-sided probe separates in-flight aggregate transport
from upstream lifetime corruption. Bootstrap restart and deployment remain
intentionally blocked by the prerequisites above.

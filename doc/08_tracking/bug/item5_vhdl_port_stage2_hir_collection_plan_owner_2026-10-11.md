# Stage 2 HIR enum-owner failure while qualifying Item 5 VHDL port

Status: OPEN. The selected Item 5/6 branch contains the compiler-owned VHDL
output port at commit `e68c66ffcae`; its focused behavior spec has not run.

## Reproduction

- Worktree: `work/targets-release-20261010` at `e68c66ffcae`.
- Compiler: admitted pure-Simple Stage 2 under
  `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
  SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`.
  Its adjacent `admission.env` says `status=admitted` and binds that hash.
- Command: `SIMPLE_LIB=src timeout 600s <admitted-stage2> compile test/01_unit/compiler/driver/driver_vhdl_output_port_spec.spl --format=smf --output build/item5-vhdl-port-long.smf`.
- Exit: 1 after 367.152 s in phase 3 HIR. Parse and surface build reached
  525/525; HIR reached 525/525, then reported one poisoned module and four
  errors. Observed RSS during HIR 456/525 was 2,208,788 KiB; this is a sampled
  value, not peak RSS.
- Poisoned module: `compiler.semantics.perf.collection_plan`.
  Two occurrences each of `qualified enum pattern owner differs from subject
  owner` and `E-HIR-MATCH-UNHANDLED-PATTERN` are reported for
  `src/compiler/35.semantics/perf/collection_plan.spl`.
  The port and its spec were lowered before this module without an explicit
  diagnostic. The log does not identify which match arms have the mismatched
  enum owners.

## Impact and next action

The compile never reaches monomorphization or executable behavior. Source
closure and Phase 5 checks are green for the VHDL port, but native behavior,
provider demand-load, and size/startup evidence remain unqualified.

Inspect the subject and qualified pattern owner identities in
`expression_components.spl:226` at the error site, then repair the
canonical owner resolution or the actual mismatched enum projection. Add a
focused regression with the real `CollectionPlanFacts` enum cases and an
unrelated enum negative case. Do not replace qualified patterns with a broad
catch-all that could accept an incompatible owner. Rebuild an admitted
self-hosted compiler and rerun this spec in a fresh bounded verification cycle.

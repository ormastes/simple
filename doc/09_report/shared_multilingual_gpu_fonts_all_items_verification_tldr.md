# Shared Multilingual GPU Fonts All-Items Verification — TLDR

All 23 requirement/NFR rows are mapped, but the umbrella result remains
`STATUS: FAIL` until a fresh pure-Simple CLI runs the calibrated evidence.

## Current State

- source/spec lanes and reviewed GSUB/GPOS integration are checkpointed;
- HEAD `7a161abfabb` fixes impl accumulation; the final cycle-3 check reached
  15 functions and localized the remaining nil receiver inside HIR error
  collection;
- the typed-index collector, HIP-to-ROCm batch, fail-closed degenerate Web, and
  nested IMAGE changes are implemented but unverified;
- shared nested collection has source coverage for a valid collection and
  stale, duplicate, and orphan rejection, but remains runtime-unverified;
- the inventory is 32 changed/new specs: 13 mirrors missing, 19 stale, zero
  current, and all 32 require focused deployed-runtime docgen;
- Lane C resolved all 19 matcher findings; two short-expression parse repairs
  and selected-registry path/SHA/axis binder hardening are source-present but
  runtime-unverified;
- GPOS duplicate lookup indices now fail closed without publishing partial
  adjustments, and 3D Vulkan evidence records successful atlas/vertex upload
  counts and bytes; both changes are source-present and runtime-unverified;
- the lower executor now covers GSUB 1–8 and GPOS 1–9 generically; selected
  complex-script preprocessing remains fail-closed outside its pinned oracles;
- Lane F found 346 scenarios with real direct/helper assertions and all eight
  frozen steps; the deterministic 32-path docgen manifest is recorded but has
  not run;
- the synced checkout is detached at `397afaaee3bb`, matching the remote
  feature branch; `origin/main` continues advancing, so the final
  fetch/rebase/file-count gate remains open, while
  older static guard results remain historical evidence only;
- the latest three-cycle admission parsed all 1,190 files and retained 1,417
  objects, but cycles 2/3 trapped after `HirLowering.lower_module`'s diagnostic
  `eprint` with exit 132; no Stage4 ELF exists;
- the next fresh one-cycle owner preserves the cache and explicitly unsets
  `SIMPLE_COMPILER_PHASE_PROFILE`, `SIMPLE_COMPILER_TRACE`, and
  `SIMPLE_BOOTSTRAP_DIAG`;
- the three-cycle cap is reached; the compatibility bridge remains isolated
  and uncommitted, and no further build retry is permitted this session;
- an external compiler-only Stage3 was produced, but its Stage4 full-CLI build
  failed at `env/variables.spl:364`; no test/run/docgen runtime exists;
- the essential-tools gate for test, lint, duplicate-check, and its aggregate
  marker must pass once against the exact admitted CLI before runner calibration;
- all six production capability rows remain blocked: Engine2D/Vulkan,
  HTML/WebIR, GUI, hosted WM, x86_64 SimpleOS QEMU, and RV64 SimpleOS QEMU;
  their exact artifact paths and resume commands are recorded in the full
  report;
- Wave-0 host prerequisites, static x86 preflight, hosted-WM wrapper self-test,
  and RV64 wrapper self-test pass, but missing CLI/runtime/kernel/disk/crop
  artifacts prevent promotion;
- current GPU hardware exists, but native readback/performance remain blocked
  on focused runtime and device evidence.

## Open Next

- [full verification matrix](shared_multilingual_gpu_fonts_all_items_verification.md)
- [native evidence](shared_multilingual_gpu_fonts_native_lane_2026-07-26.md)
- [all-items plan](../03_plan/agent_tasks/shared_multilingual_gpu_fonts_all_items_2026-07-26.md)

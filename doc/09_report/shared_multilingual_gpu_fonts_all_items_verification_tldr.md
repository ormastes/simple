# Shared Multilingual GPU Fonts All-Items Verification — TLDR

All 24 requirement/NFR rows are mapped, but the umbrella result remains
`STATUS: FAIL` until the deployed pure-Simple runtime runs the focused evidence.

## Current State

- Current scoped admission: Stage2 attempt 24 and scoped-tool attempt 12 pass
  independent checks at `2a7e354c116`. RV64 attempt 25 compiles the canonical
  runtime object but cannot link: its pre-GC unresolved surface is 618 symbols,
  including 597 hosted/unrelated raw runtime APIs, with at least twenty proven
  live by lld. Reserve attempt 26
  for an owner repair; ELF/QEMU/exact-ten/manual evidence remains absent.
- source/spec lanes and reviewed GSUB/GPOS integration are checkpointed;
- compiler-enablement fixes do not promote font requirements; the focused
  runner contract remains in-scope evidence infrastructure;
- HIP-to-ROCm batch, fail-closed degenerate Web, and nested IMAGE changes are
  implemented but unverified on the deployed runtime;
- WM source tests now extend ancestor clipping across trait and concrete pixel
  buffers plus Draw IR/Engine2D and require full-buffer no-nesting parity;
- shared nested collection has source coverage for a valid collection and
  stale, duplicate, and orphan rejection, but remains runtime-unverified;
- the inventory is 42 changed/new specs: 19 mirrors missing, 23 stale, zero
  current, and all 42 require focused deployed-runtime docgen;
- Lane C resolved all 19 matcher findings; two short-expression parse repairs
  and selected-registry path/SHA/axis binder hardening are source-present but
  runtime-unverified;
- GPOS duplicate lookup indices now fail closed without publishing partial
  adjustments, and 3D Vulkan evidence records successful atlas/vertex upload
  counts and bytes; both changes are source-present and runtime-unverified;
- the lower executor now covers GSUB 1–8 and GPOS 1–9 generically; selected
  complex-script preprocessing remains fail-closed outside its pinned oracles;
- the historical Lane F scan found 346 scenarios with real direct/helper
  assertions and all eight frozen steps; the corrected deterministic 34-path
  docgen manifest is superseded by the current deterministic 42-path manifest,
  which is recorded but has not run;
- the corrected focused graph has 46 commands: one runner-contract preflight,
  B6, C18, D12, and E9. Focused failures return their real exit, while docgen
  retains immutable identity/command/streams/exit/manual-hash evidence and
  requires an explicit complete/`0 stubs` marker; the aggregate checker
  revalidates and seals the complete graph;
- implementation checkpoint `24a77be3c89a` has 75 current dirty paths; the
  origin comparison is 87 behind / 70 ahead. Final fetch/rebase/file-count sync
  remains open; the final 75-path/18-spec settled-overlay static gate passes;
- the final bounded retained-Stage3 cycle cleared the NUL environment panic,
  then trapped at RIP `0x88034b` because its obsolete iterable collector passed
  a lowering error with nil `span` to `_format_hir_lowering_error`; no candidate
  ELF exists; current source now formats a nil-span diagnostic without
  dereferencing it, but that repair is execution-unverified;
- this window has no eligible CLI, parent, or provenance-valid cache and permits
  no fourth producer/full bootstrap; a future fresh window must first prove an
  immutable pure-Simple parent/current source receipt and then use the cheapest
  adequate incremental build;
- Stage4 low-memory forwarding/restoration, per-invocation Stage3/HIR
  environment/profile hoisting, one direct sibling-owner index per lowering
  pass, and direct qualified-function lookup are source-fixed and independently
  reviewed; all four canonical prerequisite mirrors are missing;
- exact host-independent Rust diagnostics pass: runtime UUID/LUID identity
  (0.00s, 5,632 KiB max RSS) and compiler device-loss classification (17.84s,
  2,169,768 KiB max RSS); these are non-acceptance evidence;
- completed memory/performance source fixes reuse vertex-byte scratch, bound the
  completed vertex pool, retain one deferred-fallback snapshot, and clear
  Engine2D fallback pixels; runtime/profile acceptance remains blocked;
- the three-cycle cap is reached; the compatibility bridge remains isolated
  and uncommitted, and no further build retry is permitted this session;
- the latest external `c167e250` Stage4 ended `EXIT=143`/SIGTERM with no full
  output; older `env/variables.spl` failures are historical only, and no
  test/run/docgen runtime exists;
- the essential-tools gate for test, lint, duplicate-check, and its aggregate
  marker must pass once against the exact admitted CLI before runner calibration;
- compiler, lib, MCP, LSP, and MCP stdio integration pure-runtime gates remain
  mandatory because compiler and CLI source changed;
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

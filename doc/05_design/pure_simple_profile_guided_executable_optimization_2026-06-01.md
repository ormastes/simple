<!-- codex-design -->
# Pure Simple Profile-Guided Executable Optimization Detail Design

Date: 2026-06-01

Scope: persistent profile loader, native counters, pure-Simple BOLT-like
executable layout optimization, and bare-metal software-breakpoint counters.

## Design Principles

- Profile data is evidence, not semantic proof.
- The same `.sprof` profile model feeds interpreter/JIT, native executable,
  loader/startup, and bare-metal optimization.
- Pure-Simple executable optimization operates on Simple-owned metadata first:
  settlement/native metadata, symbol tables, relocation tables, and function
  layout manifests.
- Software breakpoints are a calibration/profiling tool, not a permanent hot
  loop counter.

## Persistent Profile Loader

### Data Structures

`ProfileLoadRequest`:
- `path`
- `module_identity`
- `workload_label`
- `schema_version`
- `mode`: `inspect`, `startup`, `optimize`

`ProfileLoadResult`:
- `status`: `loaded`, `ignored`, `invalid`, `incompatible`
- `summary`
- `diagnostics`
- `rss_bytes`
- `load_time_us`

`MergedProfileSummary`:
- function records keyed by `mir_hash` and `stable_name`
- edge records keyed by `(caller_key, callee_key)`
- block records keyed by `(function_key, block_id)`
- call-path records keyed by compact path hash

### Algorithm

1. Validate header, schema version, module identity, and workload label.
2. Parse records into a bounded staging arena.
3. Reject corrupt records independently when the container permits recovery.
4. Merge counters with saturating arithmetic.
5. Attach migration confidence to every reused record.
6. Publish an immutable summary for the current build/session.

### Hot Path Rule

Hot request handlers receive an already validated `MergedProfileSummary`.
They must not open `.sprof`, shell out, or scan the repository.

## Native Counter Feature

### Counter Classes

| Counter | Purpose | Default |
|---------|---------|---------|
| Function entry | hot function clustering | enabled in profile builds |
| Basic block | layout and fallthrough ranking | opt-in |
| Edge | call graph and branch direction | opt-in |
| Call path | inline/layout candidate discovery | sampled/bounded |

### Native Counter ABI

The native compiler emits a profile section or side table with:
- stable function key;
- counter slot index;
- counter kind;
- symbol/relocation mapping;
- profile build ID.

Counters are enabled only under an explicit profile build flag. Non-profile
native builds should either omit counters or keep them behind cold disabled
guards.

### Merge Path

Runtime counters are flushed into `.sprof` through the profile writer. Crashes
or partial writes must preserve the last valid profile and mark partial data as
diagnostic-only.

## Pure-Simple BOLT-Like Executable Optimizer

### Input

- `MergedProfileSummary`
- executable layout manifest
- symbol table
- relocation table
- function/block boundaries
- entry and exported symbol list

### Planner

1. Build weighted call graph from function and edge counters.
2. Identify hot clusters by call frequency and fallthrough probability.
3. Keep entry/exported functions stable unless relocation metadata proves safe.
4. Reorder internal hot functions for locality.
5. Reorder basic blocks when branch targets and relocation constraints allow.
6. Move cold blocks/functions to cold regions only when unwind/debug metadata can
   be preserved or explicitly regenerated.
7. Emit an optimization manifest mapping original offsets to optimized offsets.

### Output

- optimized executable or settlement artifact;
- layout manifest;
- before/after report: size, startup, representative runtime, cache-locality
  proxy, changed symbols, skipped candidates and reasons.

### Rejection Rules

Reject a layout transform when:
- relocation target cannot be updated;
- entry point would move without manifest support;
- unwind/debug/symbol mapping would become invalid;
- profile is stale or workload label mismatches;
- improvement is below threshold or measurement noise.

## Bare-Metal Software-Breakpoint Counters

### State Machine

```
candidate -> armed -> hit -> counted -> restore_original -> single_step
          -> rearm
          -> over_budget -> disarmed -> sampled_only
```

### Site Record

`BreakpointCounterSite`:
- `address`
- `original_instruction`
- `breakpoint_instruction`
- `hit_count`
- `trap_time_total`
- `trap_time_max`
- `budget_us`
- `state`
- `fallback`: `none`, `timer_sample`, `hardware_counter`, `manual_probe`

### Overhead Protection

The profiler removes or downgrades a breakpoint when any condition holds:
- per-site hit count exceeds calibration limit;
- trap time exceeds per-site budget;
- total trap time exceeds session budget;
- site is detected inside a hot loop;
- watchdog or scheduler latency degrades beyond limit.

After downgrade, the site becomes sampled-only. Its `.sprof` record includes
lower confidence and the reason.

### Cleanup

Every session owns a patch ledger. Cleanup runs on:
- normal profile stop;
- panic path;
- watchdog timeout;
- failed single-step;
- target reset notification.

Cleanup restores original instructions and invalidates instruction cache where
the target requires it.

## Call-Path Analysis

Call paths are captured with bounded depth and sampled frequency:

1. Record function entry counters.
2. Maintain a small rolling stack of stable function keys.
3. Hash call paths with depth cap.
4. Promote only repeated paths above threshold.
5. Feed path weights to native layout and inline-candidate planning.

Bare-metal breakpoint call paths use sparse probes only for calibration; after
the path is known, hot sites switch to timer/hardware/sample counters.

## Implementation Slices

1. `.sprof` loader and merge summary.
2. Native function entry counters.
3. Native block/edge counters.
4. Pure-Simple executable layout planner over metadata only.
5. Layout artifact writer with manifest.
6. Bare-metal breakpoint site table and patch ledger.
7. Bare-metal auto-disarm and sampled fallback.
8. Cross-mode report and verification harness.

## Open Risks

- Native executable metadata may not yet expose enough safe block boundaries for
  block-level rewriting.
- Bare-metal instruction patching is architecture-specific.
- Debug/unwind metadata may force function-only layout before block layout.
- Profile workload mismatch can make optimized layout slower.

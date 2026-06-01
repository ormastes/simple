<!-- codex-architecture -->
# Pure Simple Profile-Guided Executable Optimization Architecture

Date: 2026-06-01

## Goal

Build an MDSOC+ optimization capsule that uses Simple-owned profile data to
optimize interpreter/JIT planning, loader/startup, native executable layout, and
bare-metal call paths without depending on external BOLT.

## MDSOC+ Capsules

| Capsule | Boundary | Responsibility |
|---------|----------|----------------|
| Profile Store | `src/app/optimize`, future shared SMF/profile common layer | `.sprof` validate, load, merge, migrate |
| Native Counter | native build/runtime boundary | function, edge, block, call-path counters |
| Executable Layout | optimize app + settlement/native metadata | pure-Simple BOLT-like reorder/alignment/cold split |
| Bare-Metal Counter | OS/debug/bare-metal capsule | software-breakpoint counters, auto-disarm, sampling fallback |
| Verification | SPipe + reports | overhead, correctness, reproducibility, hardware evidence |

## Data Flow

```
instrumented interpreter/native/bare-metal run
    -> counters
    -> .sprof merge
    -> profile validation/migration
    -> optimizer plan
    -> native/executable layout transform
    -> verified executable
```

## Pure-Simple BOLT-Like Optimizer

The optimizer does not invoke BOLT. It consumes `.sprof` and Simple executable
metadata to perform:

1. hot function clustering;
2. hot fallthrough block ordering;
3. cold block/function separation when relocations allow it;
4. branch target locality ranking;
5. alignment hints for hottest entries;
6. reproducibility checks against symbol/relocation tables.

Initial target: Simple settlement/native metadata, not arbitrary ELF rewriting.

## Bare-Metal Breakpoint Counter Policy

Software-breakpoint counters are allowed only under a profiling session:

```
candidate site -> patch breakpoint -> trap -> increment -> restore/single-step
               -> rearm if below budget
               -> disarm and mark sampled-only if over budget
```

Rules:
- never arm breakpoints in known hot loops after the calibration window;
- cap hits per site and total traps per time window;
- remove all breakpoints before optimized/release execution;
- persist only counts and confidence into `.sprof`;
- use timer or hardware counters when breakpoint trap cost is too high.

## Loader Strategy

Profile loading is opt-in. Startup loads at most a validated summary keyed by
module identity, schema version, workload label, and executable build ID. The
loader must not scan the repository or reread `.sprof` during hot execution.

## Safety Gates

- Profile evidence never replaces typed-MIR, safe-deopt, semantic proof, or
  relocation validation.
- Executable layout transforms must be reversible or produce a manifest that
  can prove the original-to-optimized mapping.
- Bare-metal breakpoint sessions must have cleanup on normal exit, panic, and
  watchdog timeout.

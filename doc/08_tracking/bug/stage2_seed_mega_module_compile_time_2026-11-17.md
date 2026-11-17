# Stage2 seed native build dominated by single mega-modules (15-20 min each at 100% CPU, log buffered) (2026-11-17)

**Status:** OPEN (compile-time pathology; not memory, not a hang)
**Area:** seed (Rust) native-build of the stage2 compiler closure, single-module compile
**Evidence:** cycle-35 stage2 admission at f593c7123ca2 (MSVC, --jobs=1,
receipt lane). The stage2-native-build log exhibits a repeating pattern:
long plateaus where the log is byte-frozen while one simple.exe process
holds ~100% of a core (measured +15.3 s CPU per 15 s wall), followed by a
multi-KB burst of progress. At least two such plateaus of 15-20 minutes each
occurred within the first ~45 minutes of the module compile (log 241001
bytes frozen ~15 min at one module, then again at 248625 bytes). The build
is NOT hung: it is single-threaded in-process work (no llc child during the
plateaus), and the earlier c29-era build of a smaller closure took ~50 min
total where this one projects materially longer.

## Why this matters

- The stage2 admission latency gates the whole receipt lane; two to three
  mega-modules at ~20 min each add ~40-60 min to every admission cycle on
  this host class.
- The pattern (buffered log + one hot module) makes wall-clock estimation
  unreliable and looks like a stall to operators.

## Owner asks

1. Identify the mega-modules (the log does not name current= during the
   plateaus at this tip; the phase emits only seed aggregate-typing
   warnings). Candidates: generated codecs (hir_codec), the full driver,
   or a pathological single file whose aggregate typing is superlinear.
2. Consider per-module progress emission (current= + elapsed per module)
   for the seed native build, and/or splitting the worst modules.

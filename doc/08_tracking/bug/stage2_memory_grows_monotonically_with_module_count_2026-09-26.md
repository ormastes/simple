# Stage 2's memory grows monotonically with modules compiled, so the module it dies on is a function of host commit headroom

Filed: 2026-09-26
Host: DESKTOP-5A4V03J (Windows 11, `x86_64-pc-windows-gnu`, 15.7 GiB physical,
30.1 GiB commit limit = physical + a system-managed pagefile)
Severity: Blocking phase 1 on any host whose commit limit is near 30 GiB.

## Symptom

The Stage 2 self-host compile aborts with an in-process allocation failure,
never a kill:

```
  [400/901] compiled
memory allocation of 544 bytes failed
```

544 bytes is not a large request. The process had already exhausted what it
could commit; the next allocation of any size would have failed.

## Evidence that it is monotonic growth, not a fixed requirement

The same build, same flags (`SIMPLE_WINDOWS_ABI=gnu SIMPLE_NATIVE_LOW_MEMORY=1
SIMPLE_NATIVE_BUILD_THREADS=1`), on the same host, died at a **different module
count** depending only on how much headroom was free when it started:

| run | free physical at Stage 2 start | died at |
|---|---|---|
| 2026-09-26 ~15:15 | ~9 GiB | `[850/901]` |
| 2026-09-26 23:31 | ~4-5 GiB | `[400/901]` |

Pagefile peak usage across these runs reached 12366 MB of a 14836 MB allocated
file, against a 30.1 GiB commit limit. So the compile is consuming on the order
of 10+ GiB in a single process and still climbing at module 850 — it does not
plateau.

A fixed working-set requirement would fail at the same module every time. A
requirement that scales with modules-already-compiled fails wherever the
headroom runs out, which is what is measured. Something retains per-module
state for the whole run.

## Why this matters beyond one host

`--build-threads 1` and `SIMPLE_NATIVE_LOW_MEMORY=1` are already set; there is
no further knob. Raising the host commit limit moves the failure later but does
not bound it, so a large enough module count fails on any host. 901 modules is
today's count and it grows.

## Not yet established (state rather than guess)

- WHICH allocation is retained. No per-module RSS curve has been captured, and
  no allocator profile exists for the Stage 2 process on this host.
- Whether the retention is in the seed's own arenas, in the native-build object
  cache, or in accumulated diagnostics. Note the log emits per-module warnings
  (dynamic-receiver degradation, declared-return-type mismatches); if those are
  accumulated in memory rather than streamed, that is a candidate worth
  measuring first because it is cheap to check.

The honest next step is a measurement, not a fix: sample the Stage 2 process's
private bytes every N modules and report the curve. A straight line implicates
per-module retention; a step function implicates a specific phase.

## Related

- `stage3_walk_retains_handle_per_entry_2026-09-25.md` — same class (per-entry
  retention converting a bounded job into an unbounded one) in the Stage 3
  authority walk.

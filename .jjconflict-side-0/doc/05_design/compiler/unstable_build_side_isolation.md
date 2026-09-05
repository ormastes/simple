# Unstable Mode — Build-Side Process Isolation (design note)

Status: **BLOCKED, deliberately.** Recommendation: keep the honest printed
warning; do not build a half-isolated build path.

Companion: `doc/03_plan/infra/unstable_mode_build_side.md` (the plan and its
2026-08-17 P2 answer). This note is the *design* view: what the wall is made of,
what the minimum demolition order is, and what is already built but unwired.
Everything below was re-verified by reading code on 2026-08-18; corrections to
prior claims are marked **CORRECTION**.

## 1. What actually prevents a per-unit process today

```
 parent process                                     a child process cannot
 ─────────────────────────────────────────────      ─────────────────────────
 sources ──▶ HIR
              │
              ├─ (1) whole-program struct-layout PRESCAN ──┐   needs EVERY
              │      every module registered into ONE      │   module's HIR
              │      shared MirLowering                    │
              ▼                                            │
            MIR (per module, but field indices are a       │
                 function of the WHOLE program)            │
              │                                            │
              ├─ (2) whole-program post-passes mutate      │
              │      mir_modules (async SM, AOP)           │
              ▼                                            │
            freeze ──▶ capsule { MIR, storage snapshot,    │
                                 registry_identity } ──────┤   (3) no MIR
              │                                            │       reader
              ▼                                            │       exists
        compile_fn (IN-PROCESS closure)  ◀─ parallel.spl:424
```

Three independent blockers, each verified:

1. **Whole-program struct-layout prepass.**
   `src/compiler/80.driver/driver_pipeline_lowering.spl:202` builds one shared
   `MirLowering`; `:209-215` prescans *every* module's HIR struct layout before
   any module is lowered. The comment at `:203-208` says why: without it an
   imported struct's field order is unknown and `resolve_field_index` defaulted
   to 0 — a cross-module SEGV. So a module's field indices are a function of the
   whole program, not of its own source. A child re-deriving from a source path
   emits **silently wrong offsets**.
2. **Capsule registry identity is whole-program.**
   `_compile_frozen_module_capsule` hard-fails `capsule-registry-mismatch`
   (`driver_aot_native_output.spl:906`) unless the capsule's snapshot identity
   equals the batch identity. That identity is hashed over all modules' storage
   rows plus `self.mir_modules.keys()` (`driver_types.spl:806-823`). A child
   holding one module cannot reproduce it, and registration is refused once
   frozen.
3. **MIR has no deserializer.**
   `grep -rn deserialize --include=*.spl src/compiler | grep -i mir` → **0**
   (control: `serialize_mir_module` → 3 hits, `src/compiler/50.mir/mir_serialization.spl:13`),
   and that one serializer is an explicitly lossy functions-only shape that drops
   statics/constants/types. `FrozenStorageModuleSnapshotV1` has no serializer at
   all.

Consequence: there is nothing correct for `spawn_fn` to launch. The seam
`build_supervised(spawn_fn, artifact_fn)` (`parallel.spl:680`) is written and
uncalled; `build()` prints the non-activation warning at `parallel.spl:402-407`.

**Do not take the `capsule_identity`-on-argv shortcut** (rejected by the prior
lane, and this note concurs): the child would write a conforming
`.capsule-receipt` (`driver_aot_native_output.spl:186-198`) attesting an identity
it never verified, promoting a wrong-offset object into the cache as
authenticated. Green report, miscompiled binary — strictly worse than today's
loud SIGSEGV.

## 2. Minimum set of changes

Pick ONE of two real projects. Neither is small.

- **Route A — round-trippable capsule format.** Write a faithful MIR reader
  (every `MirInstKind`, terminator, type, const) plus a
  `FrozenStorageModuleSnapshotV1` (de)serializer, gated by an identity
  round-trip test (`serialize → deserialize → native_capsule_mir_identity_v1`
  must equal the original). Then the one-module CLI is genuinely small: read
  capsule, call `_compile_selected_module`, write object + existing receipt.
- **Route B — make lowering per-module pure.** Give imported struct layouts a
  stable, source-derivable field ordering, so the prescan becomes a *shareable
  artifact* rather than a shared mutable object. This is exactly the
  `interface_digest_of` work (`src/compiler/80.driver/cache/action_key.spl:199`).
  Route B also unlocks dependency-aware partial rebuild; Route A does not.

Not required for either: any dependency model. The parent already resolved
everything.

## 3. Ordering and rough cost

| # | step | depends on | rough cost | route |
|---|------|-----------|-----------|-------|
| 0 | confirm `ParallelBuildConfig` construction site `driver_aot_native_output.spl:667-672` still compiles after the struct gained `unstable`/`unit_timeout_ms` | — | minutes | both |
| 1 | flag plumbing onto `ParallelBuildConfig.bootstrap()` (`parallel.spl:113`) | 0 | small | both |
| 2 | MIR reader + identity round-trip gate | 1 | **multi-thousand lines, correctness-critical** | A |
| 2' | source-derivable field ordering; wire `interface_digest_of` | 1 | comparable, plus a cache-invalidation redesign | B |
| 3 | one-module CLI + `spawn_fn`/`artifact_fn`; switch to `build_supervised` when `cfg.unstable` | 2 or 2' | small | both |
| 4 | crash/timeout fixtures (segfault-on-demand, sleep-past-budget) | 3 | small | both |

Step 2/2' is ~90% of the cost and is a prerequisite for 3 and 4. Steps 0-1 are
landable now and change no behaviour.

## 4. Built but unwired (re-verified, with corrections)

| thing | state |
|---|---|
| `build_supervised` (`parallel.spl:680`) | fully written, commented, **never executed** — no caller, spec unrun. Correctness UNVERIFIED. |
| `interface_digest_of` (`cache/action_key.spl:199`) | one definition, **zero call sites**. Other two grep hits are a schema row (`cache/schema/cache_protocol.sdn:844`) and a comment (`cache/block/block_key.spl:10`) — so "one line in the tree" was slightly overstated, "zero callers" is correct. |
| `src/lib/simple.sdn` `dependencies:` | real edges; no build path traverses them (unchanged). |
| `SmfManifest` | **CORRECTION to CLAUDE.md.** "written but never verified on load" is wrong for the interpret path: `driver_api_interpret.spl:55` calls `smf_manifest_entry_matches_source`. What *is* unwired is `smf_manifest_entry_verifies` (`watcher/smf_manifest.spl:134`) — exported, zero callers. |
| `DependencyEntry.needs_recompile` | **CORRECTION:** now at `driver_build/incremental.spl:280`, not `203-226`. Still one-hop, still never called from a build path. |

## 5. Recommendation

**Leave it blocked.** Crash containment on the build side costs a new compiler
artifact format (Route A) or a lowering redesign (Route B); the run-to-end and
outcome-classification halves already work in-process, so the remaining prize is
only "the build survives one unit's SIGSEGV" — worth much less than a
miscompilation risk, and unmeasured against per-unit spawn cost on a host where
earlyoom already forces jobs=2.

Cheaper partial wins, in order of value per unit of work:

1. **Supervise the LINK step only.** Linking already consumes files, not
   in-memory capsules, so it needs no serializer and no identity reproduction.
   *Unverified* that link is a separate spawnable step here — verify by reading
   the link invocation in `driver_aot_native_output.spl`.
2. **Keep the printed warning and add per-unit progress breadcrumbs** so a
   whole-build death at least names the unit that was in flight. Cheap, no
   isolation claimed.
3. Do **not** crash-isolate "only the units that historically crash": selecting
   units by history needs the same child-compile capability as isolating all of
   them, so it saves nothing.

## 6. Unverified claims in this note

- Whether step 0 is a real compile break (not compiled — rebuilding `bin/simple`
  is forbidden in this lane). Verified by `bin/simple build bootstrap` on a lane
  that owns the binary.
- Capsule size / serialization cost. No capsule was measured.
- Per-unit spawn overhead vs. the in-process path. Unmeasured.
- Whether `build_supervised` is correct. Written, never run.
- Whether the linker step is independently spawnable (see recommendation 1).

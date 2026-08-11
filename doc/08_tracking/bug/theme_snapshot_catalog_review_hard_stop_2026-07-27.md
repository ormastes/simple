# Theme snapshot catalog review hard stop

**Status:** open / fail-closed — re-verified against `origin/main` 2026-07-27,
both P1 gaps still fire today  
**Iteration state:** three-cycle cap reached  
**Integration state:** rejected commits are not integrated. The three shas
below are **unrecoverable** — isolated worktrees, never pushed, and they no
longer resolve in either the git or the jj object store. Do not attempt
`git show` or a cherry-pick. No catalog landed by other means either: only a
single hardcoded `aetheric_dark` generated snapshot exists. See
[report](../../09_report/theme_hard_stops_unlanded_2026-07-27.md).

## Scope

An isolated lane attempted to remove hosted theme-package I/O from the
freestanding SimpleOS desktop closure and introduce one common generated
`ThemeRenderSnapshot` catalog. The source candidates are:

- `9f9a921689` — generated catalog and hosted/freestanding split;
- `d404042bc4` — registry-derived aliases, authority digest, full tuple keys,
  generator hardening, and recursive closure audit;
- `7ed0ae0a1a` — generated-default boot, animation/provenance binding, legal
  constructor symbols, and stricter closure checks.

None was integrated or pushed. No admitted self-hosted runtime was available;
no executable spec, entry-closure, first-frame, pixel, event, timing, or RSS
PASS exists.

## Candidate facts accepted statically

Final review found the series had statically implemented most prerequisites:

- all hosted aliases/defaults were authority-derived;
- catalog output used the existing `ThemeRenderSnapshot` model;
- tuple identity was bounded, hash-validated, versioned, and length-prefixed;
- the full tuple key reached Web cache/session/frame provenance;
- numeric revision was no longer the sole cache identity;
- generator output used real newlines, deterministic ordering, and safe symbol
  encoding;
- SimpleOS boot followed generated-default lookup rather than a direct
  Aetheric constructor;
- the closure audit used resolver-derived x86_64 and ARM64 entry closures and
  failed unresolved imports;
- hosted package source files were not modified.

These are rejected-candidate facts only, not landed behavior.

## Final rejection

The final cycle retained two P1 authority gaps:

1. hosted bootstrap validated registry/default catalog authority but returned a
   pre-existing non-default active snapshot without checking that active
   snapshot against catalog/hosted identity; stale or arbitrary active state
   could bypass parity;
2. external Web frame authorization stored the active theme key at
   registration, but frame acceptance did not recompare it with the current
   active snapshot. A theme change after registration left an old-theme frame
   authorized.

Per the mandatory cap, no fourth repair is permitted in this lane.

## Fresh-lane resume contract

Start from current `origin/main`, not a piecemeal cherry-pick:

1. validate any existing active snapshot against the authoritative hosted
   registry/catalog identity before returning it;
2. at every external-frame acceptance, compare the frame/registration key with
   the current installed active theme, or invalidate all registrations
   atomically when theme installation changes;
3. retain the full alias/default authority, generator validity, identity-key,
   animation reset, constructor-symbol, and recursive closure regressions from
   the rejected series;
4. keep freestanding x86_64 and ARM64 closures free of hosted package, session,
   file, environment, and process access;
5. preserve `Web -> DrawIrComposition -> Engine2D` and local CSS semantics;
6. obtain independent highest-capability review before integration.

Runtime completion still needs a permitted incremental entry-closure check and
focused specs on an admitted pure-Simple runtime, then live hosted/SimpleOS
theme/frame evidence.

# Stage 4 streaming lexer early-release SIGSEGV

## Status

Open after the bounded 2026-08-04 focused cycle.

## Reproduction

The strict LLVM 23.1 migration bootstrap completed source closure for 1,726
files, entered streaming Phase 2, emitted the release receipt for
`src/app/cli/main.spl` with sequence 1, and immediately terminated with
SIGSEGV. No Stage 4 candidate was produced and no fallback was accepted.

## Rejected hypothesis

The per-module transient-scope cleanup calls
`lexer_release_parse_source_globals()`. The lexer owner explicitly permits
that operation only after the caller has finished parsing every module. The
first repair attempt retained lexer globals between modules and released them
only after the loop. A refreshed, sanity-checked pure-Simple Stage 3 compiler
still crashed at the identical sequence-1 boundary, so early lexer release is
not sufficient to explain or repair this failure. The experiment was removed.

## Retained evidence and next owner

The strongest remaining hypothesis is a dangling nested carrier in the
promoted `ModuleSurface`/`ModuleSurfaceBuilder` graph after the transient
scope ends. The next fresh session must obtain a native stack trace or add
bounded markers around surface promotion, scope end, return, loop increment,
and the second `builder.has_path` call before changing ownership policy.

## Evidence

Cycle 2 log:
`build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`.
Refreshed-producer probe:
`build/focused/stage4-streaming-lexer-release/full-build-refreshed.log`.
Both completed the 1,726-file closure and terminated with SIGSEGV immediately
after `phase2:surface:file:released ... seq=1`. No candidate exists.

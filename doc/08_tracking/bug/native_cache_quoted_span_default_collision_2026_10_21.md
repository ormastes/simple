# Quoted Span-like defaults collide in native cache interface slices

Status: OPEN. Canonical ID: `native_cache_quoted_span_default_collision_2026_10_21`.
Bug DB reconciliation awaits a qualified self-hosted CLI.

`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`, owner SHA256
`e425a0afae279fbedaf8a6afe6b9031a23b5a0affe597291c7cf3bc80058923b`,
uses `span_free_debug` to remove source locations from interface defaults.
The scanner also removes `Span {...}` inside quoted default string values.
The Debug payloads `[Some(String("Span {a}"))]` and
`[Some(String("Span {b}"))]` therefore normalize identically. A caller whose
default is inlined can retain a stale dependency digest after that change.
This is a static algorithm reproduction; a native executable reproducer has
not been executed, and general cache correctness is not claimed.

Independent review of the Phase 2 recovery delta from `0bfa8039acd` through
`afb3b74059a` found no changed line containing `Span {`. Added defaults are
numeric, layout changes enter ordinary interface rows, and the enum, Lean and
JSON repairs change consumer bodies. Canonical source refresh admits this
owner only for the exact old snapshot and the exact reviewed new snapshot,
excluding exactly the wrapper's own record to avoid recursive hashing.
Producer, runtime, tools, cache binding and actual inner dependency keys remain
checked. Every other source transition fails closed. This scoped recovery
does not resolve the underlying normalizer bug.

Repair the normalizer to recognize quoted/escaped strings before general
admission. Regressions must show changed Span-like literal defaults invalidate
callers while source-location-only changes preserve reuse, and compare warm
objects/results with a cold build of the same input.

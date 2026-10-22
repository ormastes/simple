# Cache-HIR fixture overcaptures the Stage3 command

Status: OPEN. Severity: P2. GitHub: https://github.com/ormastes/simple/issues/3116.
Canonical ID: `BUG-HIR-FORWARDING-EXTRACTOR-20261011`.

The inherited `bootstrap_cache_hir_controls_test.shs` line 52 expects
`-o "${stage3_bin}" src/app/cli/bootstrap_main.spl` as the inline Stage3
command terminator. Candidate tree `9a95f2ae00ec3080ef9bbfaf9508e8a8d4fc2c56`
instead uses `--entry src/app/cli/bootstrap_main.spl` followed by
`-o "${stage3_bin}"` in `bootstrap-from-scratch.sh` lines 5100–5101.

An exact old-extractor control exits zero and captures 1,267 lines through
the end of the engine. Its HIR-enable count happens to remain one; this
evidence does not establish an immediate HIR-count assertion failure. The
defect is overcapture and accepting a missing command boundary.

The repair ends at the current output argument and requires a witnessed
terminator. A negative control mutates that exact terminator in the real
engine source and requires refusal. The full changed HIR forwarding fixture
passed with argument recorders and exact-base prerequisite sources, without
invoking a compiler. An initial isolated attempt refused before reaching
the extractor because an environment-field source prerequisite was absent;
the exact-base file was then supplied.

Related direct-worker fixture repairs provide the real source-policy helper,
typed RSS argument and explicit source tail for #3114. The ABI forwarding
fixture also supplies the real watchdog-policy helper and validates its one
owner-added positive reserved budget row before comparing the original
command vector. Duplicate, malformed, zero and argv-impostor rows refuse.
That changed fixture passed on its third/final targeted attempt; its two
earlier failures are retained in the external evidence.

Independent source review and final composition remain required. Native,
compiler and runtime qualification are UNEXECUTED. These shell controls
establish no cache-hit or Stage3 admission claim. No already-green suite
was rerun.

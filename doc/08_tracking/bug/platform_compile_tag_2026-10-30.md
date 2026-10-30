# Compile mode missing from platform tag matching

Status: source-reviewed candidate; native regression pending.

`TestExecutionMode` has five variants, including `Compile`, but
`platform_tag_matches` handled only Interpreter, Smf, Native and Composite.
Consequently an explicit `compile` platform tag did not have a matching branch.
The existing early `host`/`all` acceptance did not cover that case.

Add the explicit Compile arm with exact `tag == "compile"` semantics.
`platform_compile_mode_probe.spl` invokes the production matcher for all five
modes against eight tags (40 checks), preserving other modes, composite
matching and unknown-tag rejection.

The source-corrected attempt-8 runner log exposed this omission as a
non-exhaustive-match advisory. That advisory is nonfatal; it must not be
confused with the separate fatal E-RTI-006 module-alias registration failure.
The numerous textually-exhaustive advisories in the same log do not establish
actual enum-identity collisions. No wildcard suppression or compiler check
change is part of this repair.

# Native bootstrap schema-tool build times out

An isolated compiler explicit-call-types repair requires regenerating AST
fold traversal and semantic hashing after adding a real semantic Expr field.
The historical release-path executable is a Rust seed and rejects current
Windows process syntax, so it cannot provide normal-tool generation evidence.

The current Oct 10 bootstrap seed was used only to bootstrap a pure-Simple
compiler-schema executable: native-build with source roots src/compiler,
src/app and src/lib, entry-closure, entry src/app/compiler_schema/main.spl,
Cranelift, core-c-bootstrap runtime bundle, the canonical bound runtime path,
20 threads and a fresh dedicated schema cache. It exited 124 under a
180-second timeout and produced no executable. The retained log stops after
library family warnings and a canonical bug-database WAL refresh warning.
There is no successful generation, build or runtime evidence.

Evidence: build/native_probe/explicit-call-types/schema-build.log in the
isolated fix/bootstrap-explicit-call-types-20261010 checkout. Diagnose the
actual closure/load/typecheck bottleneck or build the fold-generator entry as
a bounded bootstrap product. Preserve the current compiler candidate; do not
hand-claim generated freshness, run ordinary tests through a seed, bypass
admission, or repeatedly launch the same timed-out command.

## Bootstrap dispatch correction

Static dispatch inspection confirms `driver/src/main.rs::dispatch_command`
uses the source-driven native-build route unless `SIMPLE_NATIVE_BUILD_RUST=1`
selects the Rust bootstrap handler. Canonical bootstrap stage-2 args explicitly
set that variable. The first auxiliary schema bootstrap command omitted it.
The corrected auxiliary bootstrap command uses that same setting, still
20 workers, the bound runtime and the same 180-second limit. It is a bootstrap
product build, not normal tests or generator execution through a seed.
The corrected build log is `schema-build-rust-bootstrap.log`; result pending.

## Corrected bootstrap outcome

The canonical Rust-bootstrap handler built the native pure-Simple schema tool
in 2.0 seconds: 65 compiled, zero failed. This resolves the auxiliary command
invocation error; it does not establish source-driven native-build performance.
The actual generator then revealed that the legacy field scanner retained
`= []` in the declared type. Fixing that scanner and rebuilding two modules
(63 reused) took 1.7 seconds. The generated fold output now walks explicit
call types as Type nodes and hashes them with the semantic Type encoder,
instead of silently omitting them or marking their syntax unsupported.
Native generation and these output assertions pass. No compiler or bootstrap
Phase 3/4 qualification is inferred from generator evidence.

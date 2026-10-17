# C34 source API regression

`main.spl` exercises both real LLVM+Cranelift composition entry points after
installing a valid, conflicting LLVM-only K1 table. It must exit 0, preserve
the installed `llvm` policy, and leave `rejected-policy-must-not-exist` absent.
Run it in a fresh process and private empty working directory: K1 installation
is process-global and deliberately immutable. A previous artifact must not be
mistaken for output of this case.

Compile this entry with an admitted pure-Simple producer and its matching
source/capsule identity, including `src` and `test` as declared source roots
and using entry closure. Its imported production composition includes the
Cranelift JIT lane, so qualification requires the actual linked Cranelift
runtime support; a core-only capsule or stubbed backend is not a valid runner.
No additional composition overlay should replace the explicitly named module.
An unsuccessful setup exits 10/11; incorrect admission results exit 12/13;
policy mutation exits 14. Inspect the output path in addition to the exit code.

The mono SSpec at `test/01_unit/compiler/mono/source_api_owner_spec.spl` checks
cross-module error-state updates, a genuine truncated read, clearing the error,
and the initialized tracker metadata. Both regressions are authored but not
executed; no build or runtime result is claimed.

# Phased Stage 3 omitted exact-candidate Hello gate

The `run_stage3_step` implementation in `build-phase3-phase4.sh` at
`9a1e4ea2bcc` verified dynlib policy, signed the candidate and checked its
banner, then printed PASS. `--phase=p3` and `--phase=all` could therefore
start a dependent producer without the mandatory exact-candidate native Hello
compile/run, even though path traversal advertised a `hello-smoke` action.

The phase now compiles the tracked `test/04_smoke/bootstrap_hello_world.spl`
with the new candidate and executes the resulting artifact before PASS.
The invocation binds `SIMPLE_BINARY` to that candidate, uses the selected
source checkout, host target/toolchain, backend and runtime, preserves the
static primitive policy and chooses one-binary Hello linkage. Independent
Hello caches prevent contamination by the producing compiler's cache.
The fixture remains in the frozen source inventory: a generated external
source would be refused by shard source authority.

The shared timeout helper bounds native compilation to 900 seconds and
execution to 30 seconds through guarded commands. Off Windows the gate
requires timeout/gtimeout instead of accepting an unbounded fallback.
The output must be executable, exceed 1024 bytes, exit successfully and
produce exactly `hello\n`. Failures explicitly propagate before dependent
phase dispatch. This is a sanity gate, not formal producer admission.

`scripts/bootstrap/tests/phase3-exact-hello-gate-test.shs` extracts the real
phase, Hello and guard functions. A padded shell fixture verifies successful
progress; version-only, failed compilation, missing artifact, empty artifact,
wrong output and failed execution each prevent the dependent-producer marker.
This is mock harness evidence only: no native compiler build, real Hello or
bootstrap qualification is claimed. The script regression passed, protected
script verification passed, and the protected manifest was resealed after
the final fixture-path adjustment. No live producer was rerun.

The legacy `--p2-bin` name accepts a compatible minimal producer from Phase 2
or later. Callers must bind its actual generation and immutable provenance;
the flag name does not reclassify a Phase 3 producer as Phase 2.

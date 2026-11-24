# Resume the canonical P3b operation without rebuilding P3a

The standalone phase owner previously offered `p3a`, `p3`, `p4`, and `all`.
An independently completed P3a could not continue to just P3b: `p3` always
built P3a again. Calling the P3a operation with a later producer also obscured
the phase label, output directory, and cache scope.

`--phase=p3b --p3a-bin=PATH --p3a-sha256=SHA256` now invokes the existing
`run_stage3_step P3b` operation, with its unchanged target/backend/link policy,
`phase3-b` output directory, `stage3-b` cache scope, version check, and real
candidate Hello. It neither rebuilds P3a nor reruns a previously verified P3a
Hello. The explicit producer digest is checked before and after the operation.
Standalone P3b requires a fresh build root and forbids an external output path,
so its cleanup cannot overwrite the parent product. The existing `p3` and `all`
routes remain unchanged.

The caller must first verify the parent's actual source, runtime, native Hello,
and artifact identities. A caller-supplied digest is an identity pin, not a
formal bootstrap admission. This command does not create planner, scheduler,
or lineage admission receipts.

For a source-frozen generation, a separately pinned control checkout may invoke
this wrapper with `--source-root` pointing at the frozen source. Record both
control and source revisions and verify the wrapper's policy/helper inputs;
never copy patched scripts into the frozen source or claim it contains the fix.
The wrapper and policy/run-timeout files at the starting release revision are
byte-identical to 93f7; the hash helper used here has the same implementation.

After the new P3b and its native Hello pass, the supported next command is
`--phase=p4 --p3b-bin=PATH` with the actual P3b identity. That path performs its
own producer gate and builds release/debug CLIs and the four essential tools.
A separately built full CLI must retain separate product and behavior evidence;
neither an early full CLI from P2 nor a banner substitutes for this lineage.

Regression: `scripts/bootstrap/tests/phase3b-continuation-test.shs` invokes the
actual public shell entrypoint with explicitly synthetic compiler processes.
It checks the P3b-only operation and Hello, wrong/missing parent identity,
existing output refusal, parent/output collision, parent mutation, candidate
Hello failure, and Windows `.exe` command generation. These are shell contract
checks, not evidence that a native P3b compiler has been built.

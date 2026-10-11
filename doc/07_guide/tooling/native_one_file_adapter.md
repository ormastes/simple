# Temporary native one-file test adapter

This explicit bootstrap workaround builds and runs exactly
`test/01_unit/compiler/interpreter/while_body_scope_spec.spl`. It preserves the
loop and its shadowed local, and compares the resulting integers against both
original expectations. A second native executable changes only the expected
loop count from 2 to 3; acceptance requires exit 1, one failed comparison and
the remaining comparison passing. Both executables enumerate exactly one case.

The source SHA and generated entry SHAs are fixed. Changed files, extra cases
and unsupported assertions are rejected. This is temporary restricted adapter
coverage, **not** a standard-library test framework pass, aggregate product
qualification, `SUBSET_PASS`, or full bootstrap qualification. No canonical
test is edited or skipped. The normal framework is still blocked by native
lowering errors and needs its separate repair before full inventories run.

Use an isolated physical checkout as `WORKSPACE`, the absolute path to a
Phase2 admitted compiler with adjacent `admission.env` and `runtime-capsule.env`,
and an unused absolute output directory:

```sh
sh scripts/bootstrap/run-native-one-file-adapter.shs \
  "$WORKSPACE" "$ADMITTED_COMPILER" cranelift "$NEW_OUTPUT"
```

Replace `cranelift` with `llvm` for the other backend. Each invocation owns its
workspace and output: do not run two invocations against the same workspace.
The wrapper validates compiler admission and the frozen runtime capsule,
generates positive/negative entries, and builds with `--entry-closure`. The
tested interpreter adapter has three closure modules. It requests 10 threads
while retaining the compiler's resource clamp, enforces a 6,835,937 KiB process
tree cap and a 1,800 second deadline, and prohibits unresolved stub fallback.
The process observer has a 5,000 ms budget; the memory ceiling is unchanged.

`SIMPLE_HIR_CACHE=0` avoids the recorded source-identity cache collision without
bypassing cold HIR receipts. `SIMPLE_SCV_INVENTORY_COLD_INIT=1` explicitly initializes
the source inventory in a fresh checkout. All caches, compiler logs, generated
source, line maps, runtime stdout/stderr and exit statuses remain in the output
directory. Separate cache names bind backend, producer SHA and variant; never
relocate or share them with another producer/workspace. A failed build keeps its
artifacts for diagnosis. The wrapper refuses existing output instead of
overwriting a previous receipt; a diagnostic retry must retain its original
log and record the changed configuration.

`result.json` is emitted only after strict comparison of both complete native
execution transcripts, owner hashes, entry hashes and exact exit statuses.
It records `RESTRICTED_NATIVE_GATE_PASS` and `formal_product_pass: false`.
This transcript checker is a local build companion, not a signed execution
attestation or the formal product verifier.

Generator regression checks:

```sh
sh scripts/bootstrap/tests/native-one-file-adapter-test.shs
```

Native acceptance on 2026-10-11 used admitted compiler SHA
`48975d35845f703116db796224c4c8cc13a8aa68dc0395664881f8594096fa6d`.
Cranelift and LLVM each passed the original case (2 assertions, exit 0) and
intentional failure (1 failed assertion, exit 1). The repository generator
reproduces both native-tested entry files byte for byte, and the repository
transcript verifier accepted the actual LLVM execution evidence. The assembled
shell wrapper has syntax and contract review; it has not repeated these native
builds end to end. This producer's later
required bootstrap matrix rejected configuration, so admission alone is not a
claim that the complete bootstrap passed.

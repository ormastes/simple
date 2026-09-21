# Phase 2 loader binary verification

Date: 2026-09-21. Source reviewed:
`6a68f7052d1dd55824557097e8bde94d4b1065b9`.

**STATUS: BLOCKED — admitted Phase 2 runtime execution is unavailable.**

## Evidence and changes

The former `test/02_integration/app/loader_exec_memory_spec.spl` shadowed six
production functions with local stubs, including a hardcoded host architecture.
It could not exercise executable memory. The updated spec imports the real
loader APIs, reads back bytes from a real mapping, checks deterministic invalid
inputs, and observes the Result-returning function-call contract. Its x86_64
scenario executes `mov eax, 42; ret` after the RW-to-RX transition. No runtime or
C toolchain implementation changed.

The former 1 TB allocation assertion was invalid on hosts that allow large
virtual mappings. Zero and negative allocation sizes replace it. No unsupported
architecture is reported as an execution pass: the actual-code scenario is
registered only on x86_64; both remaining scenarios use portable loader APIs.

## Existing coverage and gaps

| Spec | Evidence type | Remaining limitation |
|---|---|---|
| `test/02_integration/app/loader_exec_memory_spec.spl` | Real memory, readback, native entry point | Interpreter and compile runs await admitted command owners |
| `test/02_integration/app/loader_run_function_spec.spl` | Intended SMF load and symbol resolution | Still a placeholder: never writes its fixture and accepts load/symbol errors with `expect true`; cannot count as binary-load proof |
| `test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl` | Exact bytes and nonzero offsets | Requires runtime execution |
| `test/01_unit/compiler/loader/exec_memory_wx_lifecycle_spec.spl` | Mapping permissions and lifecycle | `/proc/self/maps` checks require Linux; not Windows proof |
| `test/03_system/feature/app/native_build_smf_spec.spl` | Mock configuration/output selection | Does not build or load an SMF artifact |
| `test/03_system/compiler/simple_smf_format_validity_spec.spl` | Parses pre-existing SMF files | Requires its two real build artifacts; does not execute an entry point |

## Admission blocker

The current authoritative bootstrap in `D:/wk-authoritative-sol` stopped in
Windows symlink receipt publication before Stage 2. Its owner confirmed that
no Stage 2 admission/runtime capsule or Stage 3 artifact/receipt was emitted.

The existing release executable at
`C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe`
is 16,347,136 bytes and was last modified on 2026-09-01. A bounded inventory
found no admission, provenance, or receipt files under `bin/release` or
`build/bootstrap`. It was not executed as Phase 2 evidence. No fallback to the
Rust seed was used.

## Resume after admission

Read `PHASE2_CLI` and `PHASE2_TEST_RUNNER` from the newly admitted command-owner
receipt and verify their hashes first. From the receipt-bound source root, run:

```sh
SIMPLE_BINARY="$PHASE2_CLI" SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 \
  "$PHASE2_TEST_RUNNER" test/02_integration/app/loader_exec_memory_spec.spl \
  --mode=interpreter --unstable --assert-ran --no-cache --no-db \
  --no-session-daemon --sequential --json
SIMPLE_BINARY="$PHASE2_CLI" SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 \
  "$PHASE2_TEST_RUNNER" test/02_integration/app/loader_exec_memory_spec.spl \
  --mode=compile --unstable --assert-ran --no-cache --no-db \
  --no-session-daemon --sequential --json
```

Retain both terminal JSON results and require three executed examples on
x86_64, zero failures, and no native stub fallback. Regenerate the mirrored
manual with the admitted doc generator. Until those steps pass, this change is
test repair awaiting verification; no bug DB status is closed and no Phase 2
completion is claimed.

## Checks completed in this lane

- Scoped and staged `git diff --check`: PASS.
- Staged direct environment/runtime facade guard: PASS.
- Staged numbered-artifact guard: PASS; zero numbered artifacts.
- Tracked executable `*_spec.spl` files under `doc/06_spec`: zero.
- Source scan: no local native-function stubs, hardcoded host architecture,
  `expect true`, `pass_todo`, or oversized-allocation assumption remains in the
  repaired spec.
- The working-tree guard could not complete because the MSYS shell cannot find
  `git-lfs` while examining unrelated tracked PNG assets. This is recorded as
  an unavailable check, not a pass.
- Runtime interpreter/compile checks and admitted doc generation: not run;
  blocked by the missing admission described above.

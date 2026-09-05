# SimpleOS aarch64 in-guest: two text defects that are NOT the `.len()` u32/i64 ABI bug

Date: 2026-08-31
Lane: aarch64 in-guest toolchain components (EDK2/AAVMF pflash -> BOOTAA64.EFI)
Gate: `scripts/check/check-simpleos-aarch64-components-in-guest-efi.shs`
Compiler: the RUST SEED (`src/compiler_rust/target/release/simple`, freshly built).
The pure-Simple self-hosted compiler cannot compile anything in this tree yet.

## Why this record exists

These two defects were initially assumed to be the freestanding `.len()` ABI bug
fixed on `fix/freestanding-string-len-u64-abi` (PR #173): `compile_inline_len`
expands `.len()` to an i64 load at object+8, while several baremetal runtimes
declared `uint32_t len`, so the high half of the loaded i64 is the first four
payload bytes.

**That is not the cause here, and the check was empirical, not inferential.**
PR #173's five runtime files were applied to this worktree, all four component
kernels were rebuilt from scratch (`rm -rf build/os/aarch64_components`), and the
gate was re-run end to end. The serial output was **byte-identical** before and
after, and the gate verdict was character-for-character the same.

Three independent reasons it cannot apply to this lane:

1. This lane compiles exactly one runtime C file,
   `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`
   (boot-object autodiscovery keys off the `--entry` file's own directory,
   `arch/aarch64/`). **None of PR #173's five fixed files is in that directory** —
   it fixes `arch/arm64/`, `arch/common/`, and three `arch/riscv64/` files. A
   grep of the component build log for `arch/arm64|arch/common|baremetal_stubs`
   returns 0.
2. That file's `RtString` already declares `spl_u64 len` at offset 8. The layout
   the fix installs is already present.
3. PR #173's own gate, `scripts/check/check-freestanding-string-len-abi.shs`,
   runs **8 checks and does not scan this file at all**.

Distinguishing symptom, worth keeping: on riscv64 this defect class made caret
and the test runner **STALL** (unbounded `while i < s.len()` over a garbage
length). On aarch64 both components **run to completion and return wrong
answers**. A stall and a wrong answer are different failure shapes.

### Incidental finding while verifying

Applying only PR #173's `arch/arm64` + `arch/common` + `baremetal_stubs` files
left its own gate RED:

    FAIL — 8 check(s) run, 1 failed:
      examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c
      (RuntimeString.len is uint32_t, must be uint64_t)

It goes green only once `arch/riscv64/boot/baremetal_runtime_core.inc.c` is also
taken from the branch. That file is part of the fix; anyone cherry-picking a
subset must include it.

## Defect 1 — `extract_json_string` returns empty for the FIRST key

Real product code: `app.llm_caret.json_helpers.{jo2, jp, js, extract_json_string}`.
Literal in-guest serial capture (unedited):

    [caret] built message: {"role":"user","content":"CARET_RTT_CONTENT"}
    [caret] extracted role=
    [caret] extracted content=CARET_RTT_CONTENT
    [caret] redacted: key [REDACTED:aws_access_key_id:] trails CARET_KEEPME
    [caret] FAIL role did not round-trip

The message is BUILT correctly by the real `jo2`/`jp`/`js` and printed in full,
so string construction and output are sound. The real `redact` is fully correct:
the secret is gone and the neighbouring `CARET_KEEPME` survives — the row's
two-directional redaction condition passes.

The extractor succeeds on `content` (the second key) and returns EMPTY for
`role` (the first key), on the same input string, in the same call sequence.
This is a positional defect, not a whole-function failure, which is why it
cannot be explained by a garbage length (that would break both keys).

## Defect 2 — `parse_test_output` returns wrong counts in-guest

Real product code: `std.nogc_sync_mut.test_runner.test_executor_parsing.parse_test_output`.
Fed a real 3-example spec transcript ending in
`test result: FAILED. 2 passed; 1 failed; 0 ignored`:

    [testrun] feeding a 3-example spec transcript to the real parser
    [testrun] FAIL parser did not report passed=2
    [testrun] FAIL parser did not report failed=1

Neither count came back right. Same class as Defect 1 (in-guest text scanning),
same evidence that it is not the `.len()` ABI bug.

## Defect 3 — warning `.message` interpolates as the literal `<value>`

The dev-tool row is GREEN and its rule genuinely discriminates (clean snippet
silent, dirty snippet flagged, both required for rc=0), but the finding's own
text does not render:

    [devtool] finding: <value>

`"[devtool] finding: " + w.message` emits the placeholder `<value>` rather than
the warning message. The riscv64 sibling row printed real message text, so this
is specific to the aarch64 freestanding runtime. Re-tested after the PR #173
rebuild: unchanged.

The gate row anchors on the `[devtool] finding:` prefix, so the pass is
legitimate — but the message text is not evidence of anything until this is
fixed.

## Not in scope of this record

MCP does not link on this lane: `undefined symbol: rt_closure_new`,
`undefined symbol: rt_closure_func_ptr`, needed for `DispatchEntry.handler`.
That is real missing closure functionality, tracked with the riscv64 lane. It
must NOT be stubbed — `SIMPLE_ALLOW_STUB_FALLBACK` would ship a dispatcher that
silently handles nothing.

## Reproduce

    sh scripts/check/check-simpleos-aarch64-components-in-guest-efi.shs --selftest
    sh scripts/check/check-simpleos-aarch64-components-in-guest-efi.shs

Current verdict (unchanged across the PR #173 rebuild):

    FAIL — 4 component(s) evaluated in-guest on SimpleOS aarch64 under EDK2/AAVMF
    pflash -> BOOTAA64.EFI (no -kernel, no isa-debug-exit), 1 completed a real
    round-trip; offenders: caret(...) testrun(...) mcp(link: undefined symbol:
    rt_closure_func_ptr undefined symbol: rt_closure_new)

`COMPONENTS=devtool` gives `PASS — 1 component(s) checked`, exit 0.

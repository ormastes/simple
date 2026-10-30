# Doctest native provider contract and invocation ownership

Status: repaired in source; rebuilt-runner native execution pending.

The attempt15 source-route calibration used admitted bootstrap compiler
SHA256 `2ec06bb53fd2c1c40dc975c6bd6e667e6ef8af9557af221d94d0c83439432266`
as `SIMPLE_PHASE2_FULL_CLI`. Markdown and source-comment extraction each found
one block, but passed the generated source path directly to this compiler.
The bootstrap entry supports `compile --format=smf` and `native-build`, not
general source execution. An actual `--help` invocation confirmed that contract;
an actual `run <existing source>` invocation also returned unknown command.
The full CLI's separate `run` implementation is not evidence that this bootstrap
artifact supports it. Adding `run` to argv would not repair the failure.

Retained evidence: `/tmp/source-doctest15-markdown-out` (child execve at
`strace.log:18`) and `/tmp/source-doctest15-comment-out`; source, runtime, tool
and binary audits matched. These failures remain failures.

REQ-DOCTEST-NATIVE-CHILD: an explicit `native_backend` selects native compilation
and artifact execution for Markdown and source-comment blocks. Empty backend
retains the full CLI positional source contract. No executable probing or
producer fallback is introduced. The shared child owner uses the existing
native compile argv and admitted generated-source staging, with the selected
binary and inherited runtime/tool authorities. Native run-config is rejected.
The existing library-mode lane gate remains unchanged; configured doctest
qualification is outside this repair.

Compilation/staging/transport errors are separate from body exit status and
cannot satisfy `should_fail`. Successful native execution requires the existing
plain-program completion receipt, so early exit zero cannot qualify. Compilation
and execution share the explicit CLI timeout. Output remains bounded.

The active routes now write checked source bytes to a fresh private invocation
directory under `.simple/doctest`, preserving repository-relative library lookup.
This removes Markdown's global `/tmp/sdoctest_block_LINE.spl` collision and the
source route's same-file/same-line concurrent collision. Native generated sources
use the existing owned `test/native-generated-*` staging. `keep_artifacts` keeps
both for inspection; otherwise the respective owners clean them up. Legacy
standalone extraction helpers are not the active routes and remain unchanged.

Verification: `test/01_unit/app/test_runner/doctest_child_execution_spec.spl`
covers CLI/native argv, run-config refusal, compile failure/artifact absence,
completion evidence and transport/body failure separation. Execution is pending.
The existing calibration fixtures `markdown_green.md`, `markdown_red.md`,
`comment_green.spl`, and `comment_red.spl` are the real snippet matrix for a
rebuilt runner with an admitted native compiler, explicit native backend and
finite source roots. Require one extracted block each, green 1 pass/0 failures,
red 0 passes/1 failure, and execve evidence for both compilation and artifact.
The added `markdown_compile_error_should_fail.md`, `markdown_should_fail.md`,
and `markdown_early_exit.md` provide native phase/completion negative controls.
Require compile-error plus `should_fail` to remain an error, native
run-config refusal, two concurrent same-line cases with distinct retained
invocation paths, and absent-completion zero to remain an error. No seed fallback
or new compiler generation is required by this source repair.

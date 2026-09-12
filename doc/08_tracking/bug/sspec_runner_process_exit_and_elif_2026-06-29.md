# Bug: sspec runner — process_run exit code unreliable + 3-way if/elif/else mis-evaluates

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Filed:** 2026-06-29
**Severity:** medium (both have workarounds; the elif one is a real codegen/interp defect)
**Found while:** writing subprocess sspec system tests
(`test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl`).

## 1. `process_run` exit code is not surfaced under the spec runner
Under `bin/simple test <spec>`, `val (out, err, code) = process_run("/bin/sh", ["-c", "test -f <absent>"])`
returns `code == 0` even though the child exited non-zero. So a spec cannot branch on the child's exit
status. Worse: under `bin/simple run` (not `test`), `process_run` captures **no stdout at all** and
returns `-1` — only the `test` runner captures child stdout, which is why these specs must be run via
`bin/simple test`, not `bin/simple run`.
**Workaround:** never branch on `code`; have the shell echo explicit stdout tokens and branch on
`out.contains("...")`, e.g. `sh -c 'command -v qemu-system-riscv32 >/dev/null && echo QEMU_PRESENT || echo QEMU_ABSENT'`.

## 2. 3-way `if / elif / else` mis-evaluates in the sspec interpreter
A three-branch `if cond1: ... elif cond2: ... else: ...` fell through to the `else` branch even when
`cond1`/`cond2` held, inside an sspec `it` block run by the test runner.
**Workaround:** rewrite as nested `if/else`:
```
if cond1:
    ...
else:
    if cond2:
        ...
    else:
        ...
```
This is a real evaluation defect (the `elif` chain is not honored on this path), not just a style issue.

## Impact
Both are worked around in the committed NVMe sspec system tests (the rv32 baremetal-boot spec branches
on stdout tokens and uses nested if/else). A correct runner would surface child exit codes and evaluate
`elif` chains.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.

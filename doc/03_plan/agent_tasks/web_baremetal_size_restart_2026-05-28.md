# Web and Baremetal Size Reduction Restart Plan — 2026-05-28

## Current State

Workspace for the latest unpushed slice:

```bash
/tmp/simple-size-next4.EEbaCI
```

Local commit in that worktree after adding this plan doc:

```bash
git log -1 --oneline
```

This commit is not pushed yet. The user interrupted the push/rebase flow and
asked for a restart plan document.

The shared checkout at `/home/ormastes/dev/pub/simple` is dirty and diverged.
Continue size work in clean temporary worktrees from `origin/main`; do not edit
or reset the shared checkout unless the user explicitly asks.

## Latest Completed Remote Commits

Already pushed to `main`:

- `ce24605a0f93 size: split static web and startup handoff lanes`
- `bc909332d11c size: shrink rv32 semihost hello elf`
- `502c9231617c size: share riscv uart stdout capsule`
- `1871fc9ebcec size: share riscv interrupt control capsule`

## Unpushed ARM PL011 Slice

Files changed in the unpushed local commit:

- `doc/03_plan/agent_tasks/web_baremetal_size_restart_2026-05-28.md`
- `examples/simple_os/arch/common/baremetal_pl011_uart_stdout.c`
- `examples/simple_os/arch/arm64/boot/baremetal_uart_stdout.c`
- `examples/simple_os/arch/arm32/boot/baremetal_uart_stdout.c`
- `scripts/check-web-baremetal-size-audit.shs`
- `doc/09_report/web_baremetal_size_audit_2026-05-28.md`

Intent:

- Share ARM32/ARM64 PL011 startup/stdout implementation in one common capsule.
- Keep ARM32/ARM64 files as thin target wrappers for baud divisors, entry name,
  halt instruction, and module-init behavior.
- Preserve binary output while reducing duplicated source.

Measured result before this plan doc was added:

- ARM64 stdout wrapper source: `1458 -> 252` bytes.
- ARM32 stdout wrapper source: `1375 -> 249` bytes.
- Shared PL011 capsule source: `1283` bytes.
- ARM64 stdout object stayed `1976` bytes.
- ARM32 stdout object stayed `2000` bytes.
- Full `scripts/check-web-baremetal-size-audit.shs` passed.

## Restart Commands

Resume the unpushed slice:

```bash
cd /tmp/simple-size-next4.EEbaCI
git status --short --branch
git log -1 --oneline
```

Then fetch/rebase/push with the file-count guard:

```bash
before=$(git ls-files | wc -l | tr -d ' ')
token=$(GITHUB_TOKEN= gh auth token)
basic=$(printf 'x-access-token:%s' "$token" | base64 -w0)
git -c http.https://github.com/.extraheader="AUTHORIZATION: basic $basic" \
  fetch https://github.com/ormastes/simple.git main:refs/remotes/origin/main
if ! git merge-base --is-ancestor origin/main HEAD; then
  git rebase origin/main
fi
after=$(git ls-files | wc -l | tr -d ' ')
echo "file_count_before=$before"
echo "file_count_after=$after"
test "$after" -ge "$before"
git -c http.https://github.com/.extraheader="AUTHORIZATION: basic $basic" \
  push https://github.com/ormastes/simple.git HEAD:main
```

## Required Verification Before Pushing Further Size Work

Run the full size audit after any follow-up size edit:

```bash
SIMPLE_BINARY=/home/ormastes/dev/pub/simple/bin/simple \
BUILD_TIMEOUT_SECS=120 \
sh scripts/check-web-baremetal-size-audit.shs
```

For capsule refactors, also compile the exact affected targets and inspect
symbols when symbol compatibility matters:

```bash
clang -target aarch64-unknown-none-elf -ffreestanding -nostdlib -fno-pie \
  -Os -ffunction-sections -fdata-sections \
  -c examples/simple_os/arch/arm64/boot/baremetal_uart_stdout.c \
  -o /tmp/arm64_uart.o
llvm-size /tmp/arm64_uart.o
llvm-nm /tmp/arm64_uart.o

clang -target armv7-none-eabi -ffreestanding -nostdlib -fno-pic \
  -Os -ffunction-sections -fdata-sections \
  -c examples/simple_os/arch/arm32/boot/baremetal_uart_stdout.c \
  -o /tmp/arm32_uart.o
llvm-size /tmp/arm32_uart.o
llvm-nm /tmp/arm32_uart.o
```

## Next Size Candidates

1. Web script-render closure:
   - Inspect `src/lib/gc_async_mut/gpu/browser_engine/browser_script_render.spl`
     and `simple_web_script_renderer.spl`.
   - Goal: keep script-enabled file rendering explicit while avoiding
     accidental retention of full BrowserRenderer/script subprocess machinery
     in tiny static/web facade paths.
   - Verification: full size audit plus script facade binary/retention markers.

2. Baremetal semihost/root API closure:
   - Inspect `src/lib/nogc_async_mut_noalloc/baremetal/__init__.spl`,
     `semihost_transport.spl`, `syscall.spl`, and `system_api.spl`.
   - Goal: keep pure policy imports separate from transport/syscall imports;
     avoid root re-export use in tiny examples.
   - Verification: pure policy native probe remains small and forbidden
     markers for `semihost_transport`, `syscall`, UART, and interrupt
     controller code stay zero.

3. ARM interrupt-control sharing:
   - ARM64 and ARM32 interrupt-control assembly are similar but not identical
     (`DAIF` vs `CPSID/CPSIE`, `ret` vs `bx lr`).
   - Only share if it is a net source reduction and keeps exact object symbols.
   - Verification: affected object sizes, `llvm-nm`, and full audit.

## Do Not Mark Complete Yet

The active objective is broader than the completed slices. Completion still
requires evidence that web rendering, SimpleOS/baremetal examples, semihost
stdout, startup, interrupt handling, pure Simple policy surfaces, and
multiplatform sharing are minimized enough and covered by stable gates.

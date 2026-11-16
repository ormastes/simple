# Resident handler call-boundary regression

PR #9240 structural run 43602614678 failed the existing no-call handler gate. A bounded Clang 18 AArch64 object-only diagnostic reproduced two real same-section calls: `simple_xray_thread_note_unattached_v1` and `simple_xray_channel_produce_selected_sequence_v1`. Ordinary `inline` was insufficient after adding resident dispatch. The failure diagnostic printed only relocations, so it omitted these call targets.

The two audited hot leaves now require `always_inline`. The gate remains strict and additionally prints offending call instructions. No call whitelist or vector-state relaxation was added.

The changed object was compiled once with `-O2 -Wall -Wextra -Werror -mgeneral-regs-only -mno-outline-atomics`, Clang 18, under required 256 MiB cgroup and 15-second timeout. A fresh preflight showed 62,672,984 KiB available. Its 1,424 handler instructions contain zero calls, zero external branches, and zero FP/vector-register operands. The first ad-hoc disassembly assertion mistakenly scanned hexadecimal address/encoding columns as operands; correcting it to the existing gate's instruction-only extraction passed on the same object, without recompilation. The initial diagnostic's versioned objdump executable was unavailable; the installed LLVM objdump read the already-produced object.

This proves only the AArch64 Clang 18 object discipline. No executable was linked or run, no x86-64 result is inferred, and resident session/ABI/public-facade qualification remains pending. CI must exercise the retained complete gate on its actual target.

Local retained evidence: `/tmp/xray-shim-call-diagnostic-20261114`.

- `adapter.o`: `cc627b89e397ba49e6d30886c6358af46df0720db3ffbf2ee0bda6f8ab409cea`
- `handler.dis`: `dfffcc08466c0a89e8eaa4d48fd4bcaf1f84aa84912b80a66e1e3d947e714394`
- `adapter-fixed.o`: `b2f04e128dfcec1030d7552b572ed082ea38fa423acfdac222f533541fadaea5`
- `handler-fixed.dis`: `e0a90e96fa61b288acb1a899d4289c6883ff630df8f504646de7bdb3372d436f`

The changed head `92d27334df47250e8b821537a1952cb35904bbfd` subsequently passed [structural run 43603400019](https://github.com/ormastes/simple/actions/runs/43603400019): `local-xray-llvm-adapter-e2e pass`, all 78 rows passed. This is the complete existing gate's CI outcome, separate from the local object-only proof. It does not establish public Simple-provider or new startup-ledger qualification. Retained aggregate log: `/tmp/xray-ci-43603983255/shim-correction-structural.log`.

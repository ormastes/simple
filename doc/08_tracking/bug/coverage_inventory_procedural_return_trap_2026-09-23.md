# Coverage inventory mutator early-return trap

Baseline: `09837db049777774a61fade41e05895d613fe2ff`.
Status: scoped return-ABI correction reviewed; complete fixture **FAIL** on a
separate disabled-inventory bug. Bootstrap admission is not established.

`inventory_add_decision` and `inventory_add_condition` are statement-only
mutators. Their terminal array pushes caused the bootstrap producer to infer
value-returning signatures, although duplicate, invalid and excluded-source
branches return without a value. Explicit `-> ()` annotations preserve the
intended ABI and avoid the generated `udf #0xc11f` early-return traps.
The change adds no loops, scans, allocations, or runtime policy changes.

The native fixture imports the actual flat-AST and inventory modules. The
original native build compiled 54 modules with zero failures; execution exited
132 before its excluded-source marker. After the annotation, execution passes
excluded-source row retention, no excluded MC/DC obligations, duplicate-row
idempotence, and included-source obligations. Retained condition disassembly
shows normal returns where old code had `udf` traps.

## Retained evidence

Worktree: `/Users/ormastes/simple-tmp/compiler-coverage-inventory-return-20260923`.
Directory: `build/native_probe/coverage-inventory-return/`.
The `build-probe.shs` wrapper and `*-inputs.sha256` retain commands, exact source
and fixture hashes, pinned LLVM23 tools, and bootstrap producer/runtime hashes.
Producer SHA-256:
`da57f073ca4c9217bca520a2867bc3b8e669460043312c82ec00d43f77b1280a`.
This is an explicitly selected Rust bootstrap producer, not an admitted
pure-Simple compiler or general SSpec runner.

- `red`: 54 compiled, zero failed; build 6.38s, sampled peak 297,344 KiB;
  run exits 132 in 0.33s, max-process RSS 9,240,576 bytes.
- `green`: one rebuilt module, 53 cached; build 3.09s, peak 264,208 KiB;
  excluded/duplicate marker passes, then included-obligation check exits 22.
- `green2-run.log`: diagnostic fixture prints included-scope true, passes
  excluded/duplicate and included markers, then exits 32 at disabled inventory.
- `green3`: retained current fixture/source hashes match its input receipt;
  one rebuilt module, 53 cached; build 3.09s, peak 261,088 KiB; execution again
  passes excluded/duplicate and included markers, then exits 32 in 0.33s.
  Native executable SHA-256:
  `37f1aabcaad5f53f80bb281928804421d2f70dd2a988e8b52050972482d84278`.

All inspected build/run receipts report zero observer errors and quiescence,
with sampled RSS enforcement at 5,859,375 KiB. They report no kernel hard
memory limit. Cold-red versus cached-green build timings do not prove a
performance improvement. Native runtime samples are too small for a precise
performance claim.

## Remaining failure and review boundary

The complete regression checker deliberately requires every marker and exit
zero. It currently fails at disabled inventory, a separate boxed-global/default
value issue assigned to `coverage-global-bool-defaults-20260923`. The invalid
span assertion before that point executes, but the combined invalid/disabled
PASS marker is not reached. Collision and 1,000-repeat checks follow the
failure and have **not executed** successfully. No complete fixture PASS,
branch-coverage target, compiler-suite PASS, or bootstrap PASS is claimed.

Independent recovery review inspected the exact two-signature source diff,
all statement-only call sites, retained disassembly and logs, and current
source/fixture hash matches. Result: PASS for the narrow return-ABI correction,
with the full fixture explicitly remaining FAIL. The review performed no
test reruns or builds. Existing evidence and caches are preserved; the next
owner must fix the separately assigned failure before claiming full coverage.

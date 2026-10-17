# I/O debug facade re-exports itself instead of its concrete owner

Status: original export error cleared in actual focused HIR; native build timed
out before an executable or state-transition run. No compiler, smux, library,
MCP/LSP or release PASS is claimed.

## Original observed failure

The immutable product checkout `D:/dev/simple-smux-product-270d5b30a1a`, commit
`270d5b30a1acc77fc6157e6202dd1d48934948a7`, failed its actual smux native build
under the separately frozen f612 compiler cohort. The first fatal HIR error is
retained at `build/smux-diagnostic-phase2/smux-build.stderr.log`, source index 13:

```text
module std.nogc_sync_mut.io has no exported item rt_debug_set_active
```

Its Windows Job receipt records complete, exit 1, quiescent termination; the
error is independent of nonterminal Option/Result chase warnings. The producer
is `simple-smux-bootstrap-20261016/build/smux-windows-bootstrap/diagnostic-relink/simple-diagnostic.exe`,
SHA-256 `bad4c7fced5d4c945a24a3deb8f601685446a76dbe2ace5938feeccaea1b04a9`.
That diagnostic producer compiled and ran real Hello with a private reviewed
tagged-print forwarding shim. This is diagnostic qualification, not admission.

## Owner analysis and narrow repair

The existing ffdb0bc7f50 change imported the leaf implementation, but left
`rt_debug_set_active` inside `export use std.nogc_sync_mut.io.{...}`. That module
spelling resolves to the same facade file, so export validation still asks the
facade to supply an export whose only declaration belongs to `debug_stubs`.
The debug implementation itself already delegates to the real debug-state owner.

A fresh fetch of `origin/release_phase3` at `f6fa73977316982468407da469ec632f23332b3e`
confirmed the same pattern, rather than an already available upstream repair.
In the new editing checkout based on `5be1e7e7578`, export this one symbol directly
from `std.nogc_sync_mut.io.debug_stubs` and remove only its self-package export.
Do not change configured family selection, global resolver behavior, unrelated
facade symbols, the frozen product or the frozen compiler source.

Add `ds_is_active` to the canonical debug-state owner so the focused native
fixture can observe actual `_is_active`, not infer success from a void call.
The fixture imports that same physical/logical owner used by `debug_stubs`.
It sets false, true, then false through the public facade, checking each actual
owner value before printing its successful result. No runtime extern status,
hardcoded return or test-local substitute supplies the state.

## Focused evidence and remaining gates

Fixture: `test/fixtures/compiler_entrypoint/io_debug_facade_owner/main.spl`.
Its `expected.stdout` is a golden oracle, never an execution claim.
Private attempt: `build/io-debug-facade-20261017/`. `build.sh` records the exact
Hello-tested diagnostic producer, existing runtime authority, shim/import-library
composition, LLVM backend, source roots (`src/lib` and the fixture), entry
closure, one compiler worker, supported cold inventory setting and private cache.
`input.sha256` binds producer, shim and changed source bytes. The build has a
180-second Windows Job watchdog and, if successful, a separate 30-second run
watchdog. Original failure evidence and successful caches remain intact.

The single bounded attempt ended with watchdog status `timeout`, exit 124,
`quiescent=1`, and peak RSS 2,958,168 KiB. Its actual current-source closure parsed
and lowered 76/76 modules; final HIR ledger reports `failed_modules=0` and
`unfinished=0`. The original `rt_debug_set_active` export error is absent. The
SCV source snapshot is
`scv-revision-v1-cd3da4f47a107df1053c1205ba45d7fb2f29b0ce8e9e130f3d803fb029537df6`.

Scoped row inspection, including ignored files, found 240 files: 76 `.fpc`
frontend capsules, 76 `.terminal` receipts and 76 `.claim` records, plus the row
metadata/log/queue files. There were zero `.o`/`.obj`, backend MIR/bitcode capsules,
generated LLVM modules or diagnostic-message/ICE files in this private row.
The last recorded phase is HIR, done 76/76, task 2/6; its cache records 76 stores
and sampled selfcheck failures zero. No backend phase or deterministic codegen
error is recorded in the retained row logs. This scoped observation does not
claim backend success or exclude unrecorded failures outside these artifacts.
No executable was published and the conditional run step did not execute.

No unchanged retry was started. A cleared export diagnostic alone cannot
establish runtime state transitions. Broader library/compiler and MCP/LSP checks,
actual smux product rebuild and phase qualification remain separate required
gates. Source changes to the editing tree do not alter the frozen build cohort.

Astra accepted the narrow source/fixture review with no demonstrated P0/P1:
the direct export preserves the concrete owner, the getter observes the same
state written by the setter, and the fixture checks false/true/false with
distinct failures. This accepts scoped source quality only, not execution or
state-runtime PASS. No build was rerun for review.

Provider input/output/cache-read/cache-create usage: unavailable. Comparable
cohort average and usage ratio: unavailable; no zero-filled or guessed values.

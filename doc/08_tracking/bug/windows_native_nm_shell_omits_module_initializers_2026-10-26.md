# Windows native symbol discovery omits module initialization

Status: source repair prepared; verification BLOCKED at the six-cycle limit.

The actual Phase 2 producer SHA-256
`13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`
built a two-module native witness. Its entry-module `val LIMIT: i64 =
128 * 1024 * 1024` reads as zero; an equivalent literal and inline arithmetic
both read as 134217728. An imported provider function reads the correct value
because its generated guard initializes that provider. Imported-global tests
alone therefore miss the broken startup path.

`extract_symbols_nm` passed `nm 'object' 2>/dev/null` to
`backend_shell_tuple`. On Windows that owner uses `cmd.exe`, which does not
implement the POSIX quoting and redirection. The scan returned nonzero, which
the caller interpreted as an empty symbol list. The native entry shim then
omitted every module initializer. The exact witness COFF returns exit 1 through
that shell command and exit 0 through the pinned tool's direct argument call,
which reports `__module_init_src_app_main_spl_dynamic`.

The retained generated-codec probe independently contains a correct initializer
body at `0x14104c3c0`: it computes and stores the intended 8 MiB output and
128 MiB allocation limits. Its C `main` at `0x1400c37e0` invokes the runtime and
user entry without invoking module initializers. `create_canonical` loads those
zero globals and valid text is consequently refused. This explains that focused
probe's zero limits; it does not establish the cause of every historical codec
refusal or the phase of the hour-long full Phase 3 timeout.

The repair invokes the existing `process_run("nm", [object_path])` API directly. Symbol parsing, strict admitted-tool
selection, codec budgets, startup ordering, and cache identities are unchanged.
The native regression checks its entry global before calling provider functions.

Retained evidence: `C:/dev/simple-hir-global-witness-astra-20261026`.
The baseline program hashes to
`c97f5b40c54316cc94fd3b53daa7af3af4eda62a90023ca84b2da1d6a46f3b17`
and exits 12. Its compile monitor records peak RSS 594520 KiB and quiescent exit.
The fixture-only BOM parse failure is retained as renewed cycle 1; the native
baseline is renewed cycle 2. Neither resets the historical six codec attempts.
No Phase 3 compiler or full test-runner qualification is claimed.

## Renewed cycle results and resume boundary

The proposed production change is one call-site replacement in
`llvm_backend_tools.spl`; no helper or runtime changes remain. Cycles 3 and 4
built the actual process owner with a temporary forwarding helper, but native
execution returned invalid text lengths and status 4. The helper was removed.
Cycle 5 called the exact existing `std.nogc_sync_mut.io_runtime.process_run`
API directly and reproduced status 4 with stdout length -1, before any positive
symbol assertions passed. All failed receipts remain under
`C:/dev/simple-hir-nm-helper-astra-20261026`.

This secondary boundary is the already documented Cranelift process result ABI:
`rt_process_run_bounded` returns a `SplArray`, while the generated tuple read
loads header words and mistakes capacity 4 for the exit status. Current release
commit `2add6be09ff36ad226335e8ae2c963a4290c9e0d` already routes that call through
`rt_process_run_bounded_tuple`. The immutable P2 executable used here predates
that repair. It is not evidence against the current source repair and does not
justify duplicating or weakening the runtime boundary.

Cycle 6 kept the same fixture/source and P2 bytes but selected LLVM, whose source
already uses the tuple facade. It collected 50 code-generation failures with
`llc not found`, produced four cached objects, skipped linking, and terminated
quiescent with exit 1 (peak RSS 1164888 KiB). There is no LLVM test binary.
A separate 30-second bounded LLDB attempt could not start because of missing
DLLs (`0xc0000135`); it executed no initializer and proves no repaired behavior.

No further repair cycle was started. Resume needs a genuine producer containing
`2add6be09ff` or a working pinned LLVM tool-discovery lane. Then execute the exact
process-call regression (plain/spaced/missing object), verify the generated
entry invokes its discovered initializers, and run the six-assertion arithmetic
global fixture plus the original HIR codec probe. A focused before/after
performance comparison, full compiler/core smoke checks, and merged PR remain
pending. The authored native fixture is UNRUN. There is no verification PASS,
P3 compiler, cache admission, publication, or release claim.

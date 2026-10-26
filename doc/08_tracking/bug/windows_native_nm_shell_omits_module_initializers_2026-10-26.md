# Windows native symbol discovery omits module initialization

Status: source repair prepared; verification blocked by the immutable P2 producer ABI.

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

At that stop, no further repair cycle was started. The recorded resume needed a genuine producer containing
`2add6be09ff` or a working pinned LLVM tool-discovery lane. Then execute the exact
process-call regression (plain/spaced/missing object), verify the generated
entry invokes its discovered initializers, and run the six-assertion arithmetic
global fixture plus the original HIR codec probe. A focused before/after
performance comparison, full compiler/core smoke checks, and merged PR remain
pending. The authored native fixture is UNRUN. There is no verification PASS,
P3 compiler, cache admission, publication, or release claim.

## Explicitly renewed object-generation diagnostic

After the six-cycle stop, the user explicitly authorized one additional bounded
attempt to start object generation. No historical attempt was discarded or
renumbered. The material change was a different, healthy `llc`, not the mere
presence of the prior MSYS executable. MSYS llc/clang/lld still fail to load with
`0xc0000135`. LLVM 18.1.8 `llc.exe` at
`C:/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin` runs successfully;
its SHA-256 is
`7d900ddc6e17ebc4438a39589e4319cc80fc019ae2f189fb52afd5370f1948e7`.
The executable package name does not select MSVC ABI: the target remains
`x86_64-pc-windows-gnu`, with the pinned MinGW Clang/LLD 23.1.2 first on PATH.

An independent envelope review admitted only this diagnostic: all 55 source
files and the clean project HEAD were pinned, argv/tool hashes enforced,
physical memory and free commit measured through the exact Win32 APIs, and the
600-second watchdog/8 MiB log bound retained. A 30-second tool preflight emitted
valid AMD64 COFF. No warning, source/cache integrity, or diagnostic checker
bypass was required.

Attempt 7 then completed real P2 LLVM compilation and linking, with 54 user
object files in the actual link argv. The guard exited zero and quiescent;
peak RSS was 2038704 KiB and peak job commit 2050868 KiB. The executable hashes
to `5cfcee30fad1fff8700593a0e184aa9c77a01a7465f7d1cb11053e7cb703c938`.
These are focused diagnostic objects, not full P3 compiler objects.

Executing that binary failed the first positive process assertion. Both plain
and spaced object paths return status -1, empty stdout, and `missing command`.
Unlike the Cranelift capacity-4 result, the tuple is well formed. Disassembly of
`_process_run_bounded_raw` at `0x140001890` shows the call at `0x140001949`
passing only four words to `rt_process_run_bounded_tuple`: command pointer,
argument-array pointer, timeout, and output cap. The actual C facade requires
five words, including command length. Thus the argument-array pointer becomes
`cmd_len`, and the process owner rejects it before invoking nm.

Current release already repairs that split in `8f13b29892d`
(`text_extern_abi.spl`). A rebuilt producer must contain that fix as well as
`2add6be09ff` before the process regression can qualify this nm call-site repair.
The source fixes were not duplicated, and no subsequent attempt was started.

The original POSIX shell command and direct pinned nm also produced identical
symbol output and exit zero for the actual object path containing spaces under
Windows Git Bash. This is POSIX-shell transport evidence, not a native Unix
compiler test. Native Unix verification remains unrun.

Retained receipts, source/tool pins, actual link argv, executable, disassembly,
and POSIX-shell parity evidence are under
`C:/dev/simple-hir-nm-helper-astra-20261026`, especially `compile7`, `run7`, and
`evidence/attempt7-process-bounded-disassembly.txt`. PR #4862 remains draft;
actual fixed startup, original codec regression, performance comparison, and
full compiler qualification remain pending. No P3, release, or admission PASS
is claimed.

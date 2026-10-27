# GNU Phase2 link retains unavailable host aliases

Tracking key: BUG-GNU-PHASE2-HOST-ALIAS-LINK-20261027.
Status: OPEN, claimed by phase2-test-runner parent. Canonical BugDB insertion
is pending writer verification; this Markdown record is not a DB write.

## Reproduction

Source 69dfacbee15d3136f10f0b8108e3f3eac7ebc9fd; GNU-only bootstrap attempt4
at D:/dev/simple-phase2-test-runner-20261027. Seed/runtime/preflight succeeded,
but Stage2 native-build exited 1 in ld.lld with unavailable runtime imports
from libspl_objects.a(mod_1498.o), lib.nogc_sync_mut.sffi.host wrappers.
Examples: rt_arm_elf64_direct_entry, rt_baked_fs_byte, rt_byte_char,
rt_bytes_concat and debugger hooks. The error limit hid further diagnostics.
No Phase2 executable, runner executable or executed test assertions resulted.

Logs: build/phase2-runner-gnu-bootstrap/logs/x86_64-pc-windows-gnu/
stage2-native-build.log and D:/dev/simple/build/
phase2-runner-gnu-bootstrap-attempt4.log. Preserve all native object caches.
Seed authority key: f26fe1854126a3214fe2e7fbfa814b7c29947d4f7447e426a37ea047b7037b3a.

## Boundary evidence

Pure-Simple host.spl contains typed thin wrappers over rt_* functions. Missing
platform APIs are retained in the same generated COFF module as used wrappers.
Seed LLVM backend_core.rs:1949 enables per-body sections only for ELF-like
targets, and native_project/linker.rs:2390 adds --gc-sections only under a
Linux/FreeBSD host cfg. This is evidence for a COFF liveness hypothesis, not
proof that every missing symbol is unreachable. Do not add dummy functions,
ignore unresolved symbols, disable no-stub guards or claim successful linkage.

## Workaround investigation and removal condition

User explicitly requests a tagged workaround and canonical bug registration.
Investigate a scoped alternative backend/object-retention route using strict
linking and real Hello execution before any full rebuild. Preserve the original
LLVM/GNU failure. Cranelift emits per-function sections, but its COFF behavior
must be proven, not assumed. A backend workaround stays provisional until it
builds the actual Phase2 compiler, runs its Hello output and builds/exercises
the real runner. Remove the tag only after the intended LLVM/GNU path passes
the exact dead-reference and required-reference regressions plus real products.

## BugDB integrity

The inspected D:/dev/simple/tools/bug-cli/bin/bug is a literal exit-zero stub.
It must not be used as a writer or counted as registration evidence. Locate
and invoke the canonical real writer, then read back this row. If the writer
is unavailable, retain explicit pending intake and report zero DB writes.

## Scoped diagnostic result and tagged source workaround

Original LLVM and Cranelift tiny COFF probes both failed strict linking of an
unreachable rt_phase2_coff_probe_missing call. A retained Cranelift relink with
--gc-sections also failed; backend switching alone is not a workaround.
LLVM object inspection shows one .text body section. Cranelift has per-function
sections but no COMDAT flags. Probe receipts remain under
build/phase2-coff-workaround; no probe executable ran successfully.

Tagged seed changes now emit per-function Windows COFF COMDATs with unique
function-name keys and NoDuplicates selection (preserving existing COMDATs and
explicit section placement), and add --gc-sections for the GNU Windows link.
No runtime function bodies, unresolved-symbol overrides or stub bypasses were
added. This Rust-seed boundary is below the pure-Simple typed wrappers; its
limited bootstrap purpose is explicit. The new Windows regression inspects
COMDAT flags, links/runs a live=7 control and requires failure when the missing
call is live. This regression and the changed producer are UNRUN at this point.

User-directed workaround build uses build-phase2-runner-coff-workaround.sh,
with new output build/phase2-runner-gnu-coff-workaround, retaining the original
failed seed/runtime/object lineage. Scope remains GNU Clang/LLD only.

Read-only current DB diagnostics found the same 20 potential field-count
mismatches in both main and this worktree, despite changed file hashes and
different table totals. Parent reviewed the diagnostic source; this is not
CRC validation or qualified logical loading. Exact summary and pending intake
are under build/phase2-coff-workaround. Canonical writes/readback remain zero.

## Updated evidence: 2026-10-27

The tagged COMDAT/GC candidate was rebuilt but still failed the same strict
GNU Phase2 link. Its regression remains UNRUN; the workaround is not accepted.
The new producer SHA256 is
be4d64a5f6bbc1ea656239dde36b87c286509c1a32cbee6825267ee0b83f3c16.
Both its COMDAT probe and a MinGW Clang C control fail strict dead-reference
linking with section GC. Do not repeat this candidate unchanged.

The original archive has zero undefined references matching __sffi__host__
from other modules (llvm-nm exit zero), while the GNU linker forces the whole
archive. Selective retention remains an investigation: initializer and other
export obligations must be checked before omitting any member. Preserve the
original archive and keep required unresolved references fatal. Real Hello
execution is required before compiler qualification.

Two cached diagnostic replays reused 1605 objects and compiled two, then failed
to locate clang before final linking. These are replay environment failures.
No Phase2 compiler or test runner is admitted. Canonical BugDB writes and
readback remain zero. Current field-count diagnostics found 20 potential
mismatches; this is not a qualified logical-load or data-repair result.

## Strict copied-archive experiment

The canonical cached replay completed with 1605 reused and two fresh modules,
then reproduced the original strict GNU link failure. Exact command and
transcript are retained in build/phase2-coff-workaround/
cached-link-diagnostic-transcribed-final. The original compiler output was
not overwritten.

A local-only diagnostic audited all 157 host-member exports, archive/shim
undefined references and COFF sections, then deleted mod_1498.o from a COPY
of the cached archive. Original archive was hash-checked unchanged. In the
selected GNU environment this removed the host missing-import errors but
strict linking still failed on wasm_rt_load, wasm_rt_parse_all and wasm_rt_free
from mod_1552.o (lib.scv.wasm_executor). Logs/argv/audit remain under
build/phase2-coff-workaround/strict-host-omission-gnu-env.
The preceding direct-PowerShell launch failed in watchdog helper setup before
linking and is retained separately; it is not compiler/linker evidence.

Selective host omission is insufficient. No unresolved-symbol override was
added, no fake implementation was supplied, and no compiler executed. The
remaining investigation is GNU archive root selection versus required Wasm
runtime composition. Do not iteratively delete additional modules without
proving their entry, initializer and export obligations. No working Phase2
compiler or runner, verification PASS, canonical BugDB registration or PR
merge is claimed.

## GNU archive roots and non-vacuous entry gate

A strict cached relink using -u,spl_main plus the 278 initializer names from
_init_all.c exited zero. Parent and small-worker review identified a COFF
weak-alias trap: all 279 requested root symbols in that executable were
absolute A symbols, not code definitions. The exact compiler hash was
2d1bb37fd6afaccf5ac02180e4f9a0ca3497b8905011d20e60d632dccbdcd16a.
Its bounded Hello invocation exited zero with zero captured bytes and created
NO hello.exe. Qualification FAILED. Never use that vacuous executable as a
tool, compiler producer, evidence writer or successful Phase2 artifact.
Receipts: build/phase2-coff-workaround/roots-hello and
build/phase2-coff-workaround/strict-gnu-archive-roots.

The worker independently mapped the real entry and initializers to 243 unique
existing object members (242 initializer owners plus mod_10.o for spl_main),
with no missing objects or duplicate root definitions. A subsequent strict
relink supplied those original objects directly before the weak shims and
left the original source archive lazy. It retained all other inputs and runtime
roots. This reached the linker and FAILED on the same three wasm_rt_* imports
from mod_1552.o; evidence is under strict-gnu-archive-roots-direct-native-response.
Direct-member launch attempts first hit Windows command length in the wrapper;
a native Python launcher with Clang response file reached the actual linker.
Those earlier launch errors are not compiler/linker results.

## Wasm provider boundary

src/lib/scv/wasm_executor.spl claims runtime DynLib loading, but declares and
calls static wasm_rt_load/free/parse_all externs. A runtime availability check
cannot satisfy native link requirements. src/runtime/scv_wasm_shim.c labels
itself a DESIGN ARTIFACT, not an admitted production provider; compiling it
merely to satisfy imports would not establish correct Wasm execution.
The intended fix must use a real qualified provider/composition or a correctly
typed dynamic boundary preserving unavailable errors, handle lifetime, void
free ABI, bounded output and copying before handle destruction. Do not replace
these symbols with success/empty stubs or cast a void call as integer ABI.

No compiler has passed Hello; no test runner execution or release qualification
is claimed. The archive-root experiments are diagnostic and UNACCEPTED as a
production workaround. Canonical BugDB registration remains pending.

## BugDB audit correction

Small-worker review of current database/core.spl found SdnTable.parse silently
continues on field-count mismatch; it does not fail closed. The previous raw
audit's 20 counts therefore denote possible dropped rows, not a proven loader
rejection. Its section splitting differs from the canonical literal LF/LF
split, and CRC validation/logical loading remain unperformed. Do not label
those records definitively malformed from this audit alone. A canonical
load/add/save may silently lose rows, so it is unsafe to register this bug
until preservation is qualified. Zero canonical writes/readback still holds.

## Typed Wasm boundary investigation

Small-worker read-only audit found no existing admitted dynamic dispatcher for
all three Wasm shim ABIs. Integer-only DynLib.call_checked cannot implement
free(i64)->void. Existing cstring_to_text copies provider bytes into Simple
storage but does not supply the missing typed call. A proper boundary needs
managed NUL-terminated path/source storage, exact typed load/parse/free calls,
copy-before-free, and retained DynLib mapping throughout the transaction.
Do not replace the provider with success/empty stubs or claim installation of
wasmtime alone resolves this source-level ABI/composition problem.

Independent shared-scheduler work progressed: interpreter async receipt wiring
and six collection regression cases were authored in the separate scheduler
worktree. No new executable tests ran; no qualified Phase2 exists. Full native
runner, full CLI, parallel green/red/empty, verification and merged release PR
remain required. Existing repair attempts must count toward the repository's
six-cycle feature cap; no unchanged diagnostic should be repeated.

## 2026-10-28 renewed repair campaign (three cycles)

User renewed up to three cycles and requested landing. The first canonical GNU
build compiled all 1608 modules and linked Phase2 (64450560 bytes) with zero
module failures in 770.8s compile + 8.4s link. Compiler SHA256:
fa125f8532b6fce88ed50990ae9da98d3cdcb88019c989340290a401fc6f6abe.
It is NOT admitted: canonical sanity refused 22644 MiB free below its default
24576 MiB reserve and quarantined it as simple.exe.rejected. Original output,
logs and authority remain intact under build/phase2-runner-gnu-typed-provider.

Second cycle copied that exact rejected image privately (byte-compared), set
an explicit 8 GiB memory reserve with a 6 GiB enforced cap and one worker, and
attempted Hello outside the source inventory. It refused the untracked entry;
no unfrozen fallback was enabled. It also found a malformed workaround tag.

Third cycle corrected production tag grammar and used the tracked
windows_native_hello.spl fixture. Source freezing and object compilation
succeeded (4.2s), but linking failed on ___chkstk_ms and LLVM C API references.
The full worker stderr is preserved at
C:/Users/ormas/AppData/Local/Temp/native-build-stderr-50020-1.log; copy this into
lane evidence before cleaning temp. The compiler-rt archive does define
___chkstk_ms; pure GNU link selection/order requires investigation. The pure
link command supplies compiler-rt/unwind but no LLVM import library despite
using the aggregate archive containing Rust compiler LLVM functions.

No Hello executable ran. No runner, full CLI, release verification or merged
PR is claimed. All three renewed cycles are consumed; do not launch another
compiler/link repair probe without renewed scope. All processes are terminal.

Reviewed implementation replaces static optional Wasm imports with a leased,
exact-ABI dynamic transaction; native bridge calls real load/parse/void-free,
copies bounded output before releasing a handle, and leaves absence an error.
A GNU focused harness passed; an expanded single instrumented harness also
passed allocator-failure cases with bridge-only 100% line/81.25% branch coverage.
This is not evidence of a real installed Wasm parser or whole-runtime admission.
The failed COMDAT-only experiment was removed from production source and saved
under build/phase2-coff-workaround/rejected-metadata-source.

Parent review additionally limited lazy source-archive extraction to actual
GNU Windows targets (the surrounding cfg is host-only). Other Windows-host
cross-targets retain their original archive policy. Generated GNU entry/init
references are strong; no empty/zero fallback or unresolved override is used.

BugDB source-matched read-only audit confirms CRC32 but predicts loader failure
on headerless section6; 20 balanced-quote rows also have excess fields. They
are not valid multiline quoted records. Intended values require disposition;
no payload was guessed/discarded and canonical writes/readback remain zero.

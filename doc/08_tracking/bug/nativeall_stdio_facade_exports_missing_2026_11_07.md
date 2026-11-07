# Nativeall omits binary stdin and terminal status facade exports

- Severity: P1; status: open, fix implemented with broader verification pending.
- Source owner: `src/compiler_rust/runtime/src/value/sffi/io_print.rs`.
- Session: `01a1afac/nativeall-stdio`; target: `release/1.0.0`.

## Proven defect and boundary

At release base `5dba5390b5892dafb363e670aed11acb7741480c`, canonical callers
require `rt_stdin_read(i64)->[u8]`, `rt_stdin_read_all()->[u8]`,
`rt_term_write(text)->i64` and `rt_term_flush()->i32` (`io/pipe.spl`,
lines 185, 186, 192 and 193). No corresponding Rust definition exists in the
runtime/compiler/native_all owners at that revision. The canonical C provider
implements their scalar contracts in `runtime_core_io_exports.c`, but that TU is
not selected by the Windows/default or native-all-provider runtime build list.

The existing unconditional `io_print` module is the Rust owner. The native_all
crate reexports simple_runtime, with no second provider for these names. The
physical Rust signatures use an eight-byte transparent RuntimeValue for managed
arrays/text, matching the four callers and C scalar signatures. This source
ownership proof does not establish a nativeall aggregate link result.

## Repair

Add the four exports to io_print without changing existing I/O functions. Binary
reads use the same Rust stdin lock as `rt_stdin_read_byte`. A nonpositive request
returns an empty managed byte array without reading. Positive requests cap at
16 MiB and stop after one successful, possibly partial read, retrying Interrupted.
Read-all continues to EOF without that total cap, retaining accumulated bytes on
read or fallible growth failure. The existing bulk managed-byte constructor
copies bytes before the temporary Vec is dropped.

Terminal writes validate and copy typed UTF-8 text under the allocation registry
lock, release it before capture/stdout I/O, preserve the existing capture cohort,
and return the number of bytes written, including partial progress before error.
Invalid values return zero. Flush returns zero or minus one from the actual Rust
stdout flush result. No C FILE state, alternate stdin owner, or capture policy is
introduced.

## Executed owner verification

One guarded Cargo attempt ran on Windows using pinned nightly 2026-09-15,
x86_64-pc-windows-gnullvm, the default cpu-simd runtime profile, offline locked
inputs and filter `nativeall_stdio_` with one test thread. Result: **9 passed,
0 failed, 0 ignored, 1,414 filtered out**. Build took 2m18s; tests took 0.07s.
The compiler emitted 34 warnings, including existing clashing Windows extern
metadata; the build/test exit status was zero. No warnings were suppressed.

The nine real tests cover the physical function types, nonpositive requests,
16 MiB request cap, partial reads, Interrupted retries, prefix retention after
errors, read-all exceeding 16 MiB, managed copy ownership, partial/zero writes,
flush success/failure, capture byte counts and invalid values. The actual binary
pipe test spawns this Rust test executable, mixes new reads with the existing
stdin-byte export, and verifies 0xff, CRLF, Ctrl-Z, NUL, UTF-8 and invalid UTF-8
bytes through EOF. Its child writes an exact UTF-8/NUL/CRLF frame and flushes;
the parent requires child success and exactly one matching output frame.
Deterministic allocator failure injection and branch coverage measurement were
not performed.

Frozen guard SHA256:
`3c72d99ecbbaf704749261e23ebc4865fbf8f4b4f6252614fab0ce003c442293`.
Limits were 8 GiB job/RSS, two CPUs, 1,200 seconds, 32 MiB log and 3 GiB private
target with 2 GiB disk reserve. Receipt: native exit 0, no resource error or job
remnants; RSS peak 1,169,887,232 bytes, target peak 279,420,928 bytes, minimum
free disk 6,579,818,496 bytes. Attempts consumed: **1/6**; green tests not rerun.

Reviewed/tested source Git blob:
`ddf590d3b17a930fe24fbc183e8d180a2967ee53`.
Source SHA256:
`e050ebd0d07720ed8d3ab0a8b30446552016d4756810489f9305ca569f098893`.
Log SHA256:
`83a70169e25e095d80f78c1157def06b9f36c08938d4adf1835278b3b325e126`.
Source and index were frozen throughout execution; source hash matched afterward.
Root independently reviewed the source, correction, actual nine-test log and
resource receipt before publication.

## Outstanding qualification and retained evidence

**Nativeall composition, rebuilt Simple callers, P2 SSpec and core/MCP gates are
UNRUN.** This is Rust runtime-owner evidence, not seed behavior qualification or
completion of the MIR/codegen campaign. This PR remains genuinely unfinished
and draft; the bug stays open.

The full SPL source-only unsafe audit remains **FAIL**, source variants 400/399
and migration 3764/3546. Its previous result is reused, not rerun: 44,954 owned
src/test SPL Git path/mode/blob entries and both audit script blobs match base
5dba, with zero modified or extra SPL inputs. This audit excludes C/Rust inputs.
The complete sparse source set was not materialized to repeat this known failure.

Local immutable evidence is retained under
`C:/dev/simple/.git/worktrees/nativeall-stdio-d88f/evidence/`:
`stdio-contract-source-review.sdn`, `runtime-owner-attempt1-command.json`,
`runtime-owner-attempt1-source.diff`, `runtime-owner-attempt1.log`,
`runtime-owner-attempt1.receipt.env`, `stdio-owner-result.sdn` and
`stdio-unsafe-input-equality.sdn`. The command JSON is an explicit external
process argv/environment interoperability receipt. The authoritative reused
audit artifacts remain in the sibling scalar worktree evidence directory.

Provider input/output/cache-read/cache-create token counts, comparable cohort
average and ratio are unavailable; no estimated or zero-filled usage is claimed.

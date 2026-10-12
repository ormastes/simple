# Regular bounded reads allocate the policy ceiling

Status: focused Linux owner1 repair qualified; compiler integration and the larger runner OOM remain OPEN.

## Reproduction and scope

A real self-hosted P2 native-codegen worker was sampled in `read` called by
`rt_file_read_regular_no_follow_bounded_bytes` during
`cold_hir_native_objects_persist_v1`. The cache limit is 1 GiB. Both bounded
regular-file readers allocated `max_bytes + 1` before opening/statting the file
and passed that remaining capacity to `read`. A separate nine-module native
fixture produced a 45,120-byte object, passed strict linking and executable
assertions, but peaked around 1.2 GiB during cache persistence. This establishes
a concrete allocation defect, not the complete cause of the separate 29.2 GiB
runner OOM. No aggregate runner retry was used to qualify this repair.

Source base: `54a1397eb`. The historical P2 bounded-byte reader matched this
base byte-for-byte. Historical source already includes the separately qualified
empty-transient-scope guard; that guard is preserved.

## Repair and contract

Both public result forms use one handle-based reader. Open and validate the same
regular no-follow handle, allocate observed size plus one sentinel byte, and grow
geometrically only if that opened file grows. Growth never exceeds the caller's
limit plus sentinel. Each actual read request is at most 1 MiB, including after
concurrent truncation. The separate procfs-capable streaming reader is unchanged.

Negative/path/`SIZE_MAX` validation remains code 2, open failures 4, invalid
regular-file metadata/initial oversize 5, post-stat oversize 7, and allocation
failures 9. POSIX EINTR retries; POSIX read errors remain 9 and Windows read
errors remain 5. Windows reparse checks and handle sharing flags are unchanged.
The validated size is at most max before narrowing; `capacity > limit / 2`
avoids overflow while doubling. Zero limits still admit empty files. Every
post-open error closes the handle and frees the temporary buffer. Final array
copy/string construction retain their existing ownership contracts.

## Executed regression evidence

`src/runtime/test/rt_bounded_read_allocation_selfcheck.c` links the real public
runtime functions and uses real files. Linker wrappers inject named error edges
and deterministic mutations after stat; fortified reads still call real
`__read_chk`, retaining its bounds check. Assertions cover exact bytes including
embedded NUL, exact/negative/zero/very-large limits, empty files, directories,
missing/permission-denied/symlink paths, opened-path replacement, stat/read errors,
EINTR, truncation, growth within/past limit, malloc/realloc failures, descriptor
balance, temporary-buffer release, and owned-result cleanup. Shared empty strings
correctly refuse explicit free.

Final cycle: baseline **38 cases PASS**, candidate **42 cases PASS**. This was
cycle 3 and the final logic run. Cycles 1 and 2 exposed harness assumptions on
both binaries: existing path conversion permits an embedded NUL (OS sees the
prefix), and production fortify dispatches to `__read_chk`. Those are recorded,
not represented as runtime failures. Path-NUL semantics were not changed.

Both complete historical and current-source runtime translation units compiled
with admitted Linux owner1 flags. The only warning was an existing unrelated
ignored `write` return. The historical executable archive contains 40 members;
only `runtime_native.o` changed and defined global symbols are identical.

## Representative performance and memory

Each row uses real content equality and release assertions. Same 1 GiB bound,
separate processes, eight reads of 4 KiB or three reads of 4 MiB. Times are batch
means, not percentile claims. Peak is `/usr/bin/time -v`; after-batch RSS is
`/proc/self/status`. Small discrepancies between peak/after readings reflect the
kernel accounting interfaces; they are not leak estimates.

| Filesystem | Bytes | Mean ms before → after | Peak KiB before → after | After-batch KiB before → after |
|---|---:|---:|---:|---:|
| ext4 | 4,096 | 0.142 → 0.095 | 2,416 → 2,384 | 2,456 → 2,368 |
| ext4 | 4,194,304 | 3.212 → 2.719 | 14,480 → 14,480 | 10,572 → 14,708 |
| SOSIX Windows-backed | 4,096 | 224.440 → 1.853 | 1,050,844 → 2,236 | 2,360 → 2,344 |
| SOSIX Windows-backed | 4,194,304 | 215.557 → 18.158 | 1,059,008 → 14,192 | 10,672 → 14,708 |

Temporary allocation request: 1,073,741,825 bytes before versus 4,097 or
4,194,305 after. Read request: 1,073,741,825 before versus 4,097 or 1,048,576
after. Candidate observed RSS stayed below 15 MiB on these fixtures. The 4 MiB
candidate retains about 4 MiB more after the batch; this is consistent with the
smaller malloc allocation being retained by the allocator instead of the former
large mapping being returned. There is no claim of lower steady RSS for every
allocator or input, nor of a general leak fix.

## Replay and artifact authority

Artifacts: `/mnt/c/Temp/simple-bounded-read-contract-20261012/` contains exact
commands and stdout/stderr in `link-cycle3.json`, `logic-cycle3.json`,
`perf-memory.json`, `candidate-object-build.json`, `current-object-build.json`,
and member/symbol comparison `archive-audit.json`. Earlier failed harness cycles
remain in `logic-cycle1.json` and `logic-cycle2.json`.

Baseline archive SHA-256:
`594f02374b6a9d7ef3dfd5ec57bc937d6ca9ca47b4908f6683a4d401532ea0f9`.
Candidate archive SHA-256:
`07a41f222989ede29bb472d1826627189151e6829f35f491f8c4d4ca2198c0fb`.
Paired compiler backfill SHA-256:
`935f72674326bbf1042d4c4ce8bfdb1fccf4796242e8a418db65d7744a3ac723`.
No stale artifact admission, symbol renaming, duplicate-symbol suppression, Rust
seed fallback, or full compiler rebuild was used.

Representative invocation after the exact recorded link:

```sh
mkdir -p /tmp/bounded-read-contract
candidate logic /tmp/bounded-read-contract bounded
/usr/bin/time -v candidate bench /tmp/bounded-read-contract 4096 1073741824 8
```

Link the selfcheck with `-O2 -g -Wall -Wextra -Werror`, GNU ld wraps for
`malloc,realloc,free,open,close,fstat,read,__read_chk`, the paired runtime and
compiler backfill in a start-group, and the recorded system libraries. The
fixture is deliberately Linux/GNU-linker focused, not a portable test claim.

## Qualification boundaries

Native Windows, macOS, BSD, SimpleOS, 32-bit execution, owner0, full compiler
relink/Hello, MCP/LSP smoke and whole suites are UNEXECUTED for this candidate.
SOSIX Windows-backed reads above execute Linux code, not the Windows branch.
No MinGW compiler was available. Root source review found no P0/P1 in arithmetic,
handle admission, cleanup, or result ownership; final acceptance remains bounded
to the executed focused contract. The larger native-codegen OOM and cache-scope
questions still require independent evidence after compiler qualification.

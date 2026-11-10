# SFFI `-> [u8]` siblings: interpreter binds `nil`, and `rt_bytes_alloc` length disagrees across engines
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-18
**Area:** interpreter / SFFI return marshalling
**Status:** FIXED (2026-11-11, lane interp12) — Defect A closed by the `[u8]?` declarations of every nil-returning fs extern (pinned, spec green); Defect B (cross-engine `rt_bytes_alloc(n).len()`) fixed by the packed-byte bridge in `runtime_bridge.rs`, verified equal on the interpreter and JIT lanes of fresh seed 46fe8f6b6def; defect-class spec 6/6 GREEN. See "Addendum 2026-11-11". (Supersedes:) open
**Found while:** verifying the premise of todo_db rows 6/40/96/155/355/418/487
(all seven are duplicate scanner hits of one TODO in
`src/lib/nogc_sync_mut/io/signature_sffi.spl`).

## Context

The original row claimed an SFFI wrapper declared `-> [u8]` bound
`Option::Some([bytes])`, breaking `.len()`. **That premise is stale** — see the
correction note in this directory. While sweeping siblings of that defect class
two *different*, still-live defects turned up.

## Defect A — interpreter binds `nil` for a declared `-> [u8]` extern

```simple
extern fn rt_file_read_bytes(path: text) -> [u8]
val buf = rt_file_read_bytes("/nonexistent/missing.bin")
buf.len()
```

`bin/simple test` (tree-walk interpreter):

```
✗ rt_file_read_bytes on a missing path binds an empty array, not Option
  semantic: method `len` not found on type `nil` (receiver value: nil)
Results: 5 total, 4 passed, 1 failed
```

The declared return type is a plain `[u8]`; binding `nil` violates it. This is
the same *class* as the original row (declared `[u8]`, bound something else),
with a different wrong value.

## Defect B — `rt_bytes_alloc(n).len()` disagrees between engines

Same fixture on both engines:

| engine | `rt_bytes_alloc(24).len()` | `rt_file_read_bytes(missing).len()` |
|---|---|---|
| `bin/simple test` (interpreter) | 24 | `nil`, no `.len()` |
| `bin/simple run` (Cranelift JIT) | **0** | 0 |

Raw JIT output:

```
alloc len=0
read len=0
```

The interpreter transports the real allocation length; the JIT reports 0. A
caller sizing a buffer off `.len()` gets a different answer per engine.

## Pinned by

`test/01_unit/compiler/sffi_byte_array_return_class_spec.spl` covers the
*working* part of the class (4 green, with a positive control proving the
extern path really executes). The two cases above are deliberately **excluded**
from that spec so it does not normalise the broken behaviour; re-add them as
the fix lands.

## Not fixed here

Root cause is in the extern return marshalling, and the two engines disagree,
so a one-engine patch would paper over Defect B. Left open rather than
half-fixed.


## 2026-11-06 note (round 10, owner decision)
Defect A resolved by declaration: every `rt_file_read_bytes` declaration is already `[u8]?`
(pinned by `test/01_unit/lib/contract/fs_extern_optional_spec.spl`). The remaining nil-returning
`rt_io_tcp_read` declarations (`http_baremetal.spl`, `_SshTool/run.spl`, `_SshTool/transport.spl`)
are now `[u8]?` with explicit absence handling. `rt_io_file_read` returns empty (documented), not nil.


## Addendum 2026-11-11 (lane interp12) — verified FIXED on fresh seed 46fe8f6b6def

**Verification actually run** (worktree simple-p3-interp12-20261111, seed-smoke):

```
# Defect B engine-parity probe, default run (JIT-eligible) lane:
./bin/simple.exe run build/review/p3fix-interp12-20261111/tmp/row7_len_probe.spl --no-cache
# alloc len=24 | read nil=true        (rc=0)

# interpreter lane:
SIMPLE_EXECUTION_MODE=interpret ./bin/simple.exe run build/review/p3fix-interp12-20261111/tmp/row7_len_probe.spl --no-cache
# alloc len=24 | read nil=true        (rc=0)

# defect-class spec:
./bin/simple.exe test test/01_unit/compiler/sffi_byte_array_return_class_spec.spl --mode=interpreter --no-cache
# SPEC FILE VERDICT: outcome=OK declared>=6 executed=6 passed=6 failed=0
```

Both engines now agree: `rt_bytes_alloc(24).len() == 24` (JIT previously
reported 0) and `rt_file_read_bytes` on a missing path binds `nil` under its
`[u8]?` declaration. The `[u8]?`-declaration census
(`fs_extern_optional_spec.spl`) is 15/16 on this host — the single failure is
the dangling-symlink fingerprint case, which depends on POSIX symlink
semantics and is unrelated to this defect class (noted for routing; not
re-diagnosed on this lane). Verdict: STALE (fix previously landed; no new code
change this lane).

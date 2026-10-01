# Stage 2 empty MIR audit — 2026-09-22

Status: **WARN — historical root fix confirmed in main; current-source execution unverified.**

Scope: `bootstrap_stage2_empty_mir_bodies_2026-07-05`, audited against
`origin/main` `e0dd873da1b7828389db4eb60e82972cc8245313`. No compiler or runtime
implementation was changed. The bug remains `IN_PROGRESS` because the available
admitted executable was built from an older source snapshot.

## Root fix already present

Commit `3edcb8c2605d4d9c52e371c16923054d18236a57` (2026-08-25) is an ancestor
of main. It fixed the exact empty-list dispatch defect diagnosed after the
current report's final August 24 entry. Native project name resolution discarded
the builtin receiver qualifier and resolved `Array.is_empty` to a user method
such as `Sp.is_empty`. The wrong predicate returned false for the empty pending
instruction array, so `MirBuilder.finalize_block` overwrote finalized instructions.

Both parts remain in current source:

- `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs` excludes
  builtin receiver types from the bare method-name fallback.
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs` lowers builtin
  `is_empty` through `rt_len == 0`, and supplies the related pointer and byte
  conversion lowerings. A genuine user method retains priority.

The original commit records a fresh admitted macOS Stage 2, correct empty and
nonempty collection results with a colliding imported user method, the absent
collision control, and genuine user-method dispatch. Those are historical
claims from the commit, not tests repeated in this audit. The current bug record
omits that later result. Open PR search found no focused pending empty-MIR fix;
PR #1207 covers broader macOS Stage 3 ownership and bootstrap work and does not
establish current-source completion for this report.

## Artifact identity and receipt validation

Windows x86_64 artifact:
`D:/simple_build/bootstrap-msvc/stage2/x86_64-pc-windows-msvc/simple.exe`

SHA256: `4a8dd3eb3887b9cb61608dd6cc668dafa18bbd75bd0d98326328df48c6d54db5`.
Its `--version` prints `simple-bootstrap 1.0.0-rc.1` and exits zero.
The release-path executable instead identifies itself as a Rust seed and was
not used for the reproduction.

The candidate, source snapshot manifest, runtime snapshot manifest, tool authority
manifest, sanity evidence, and admission receipt hashes all match their recorded
values. See [receipt validation](evidence/stage2_empty_mir_20260922/receipt-validation.json).
This validates the retained receipt chain, not the source identity of today's
checkout or every file named inside those manifests.

The admitted source manifest records `src/compiler/50.mir/mir_data.spl` as
`f945e67813917b54534db32361c4022e4830c26e98f528a89ff71adbe5bf4d8f`;
the isolated current-main checkout is
`fc43dc4a878ac3bfbe8af4281c49e1b841a980ed193dc97e3644df45575dc64f`.
This mismatch prevents a current-main runtime PASS.

## Bounded Windows measurements

Each case ran once, sequentially, with `SIMPLE_MIRB_TRACE=1` and
`SIMPLE_PROJECT_ROOT` set to the isolated worktree. The command was the admitted
artifact followed by `native-build <fixture> --backend <request> -o <output>`.
Fixtures lived under `.simple/stage2-empty-mir-evidence/`; source copies
are retained as `.spl.txt` files with repository-normalized line endings.

| Fixture | Requested backend | Finalized main instructions | Elapsed | Peak working set | Exit |
|---|---|---:|---:|---:|---:|
| `fn main() -> i64: return 7` | LLVM | 1 | 32.600 s | 132,968,448 B | 1 |
| `fn main(): "abc".len()` | LLVM | 2 | 20.275 s | 133,423,104 B | 1 |
| Same return fixture | Cranelift | 1 | 5.577 s | 132,476,928 B | 1 |

All three trace a nonempty pending block, then `pending_len=0 is_empty=true`,
`early-return-taken`, and an `end main` with preserved nonzero instructions.
The method fixture is the shape used in the report's August 24 localization.
The return fixture covers its adjacent silent-emission case.

All builds then fail with `AOT compile error ... <invalid-heap:...>`; none
produces an executable. Backend selection requests are controls only: these
runs do **not** prove either backend generated valid native code. The later
failure is outside this audit's empty-MIR scope.

Metrics use a stopwatch around process execution and the Windows process
`PeakWorkingSet64` counter sampled every 50 ms until exit. They are process
working-set measurements, not aggregate child-process RSS. Cache/startup state
and fixture work differ, so their elapsed times are not a backend benchmark.
The unchanged artifact is the baseline; no compiler change or claimed speedup
is proposed, and no before/after performance or memory regression claim is made.
Raw stdout, stderr, and per-case measurements are retained under
[`evidence/stage2_empty_mir_20260922`](evidence/stage2_empty_mir_20260922).

## Remaining acceptance work

Build and admit current-main Stage 2, then run the return, method-call, imported
user `is_empty` collision, absent-collision, and genuine-user dispatch controls.
Compare candidate and baseline elapsed time and peak RSS using identical
fixtures and cache policy; reject regressions. Complete native executable
behavior checks after the unrelated AOT blocker is resolved.

This audit executed Windows x86_64 only. Linux/macOS and ARM64 were not run;
the original fix addresses common seed name resolution and LLVM lowering, but
that source scope does not certify other platforms or CPU targets. No broader
compiler/lib/MCP gates were run because this change only restores evidence and
tracking. The tracked `doc/06_spec` tree contains zero executable `_spec.spl`
files. No unrelated worktree edits are included.

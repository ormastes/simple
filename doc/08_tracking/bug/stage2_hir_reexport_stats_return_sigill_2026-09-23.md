# Stage2 re-export statistics reporter traps on both early returns

Date: 2026-09-23. Base: `2710d948270316e156a0f90380b28adedb2e801f`.
Status: scoped bootstrap-producer native regression PASS; rebuilt Stage2
admission and the original pure-Simple comprehension probe remain pending.

## Exact failure and producer cause

The admitted macOS Stage2 compiler, SHA-256
`fc2fc3a280ed6afc056ac766a7561a0ba5d6d57038bc8bbb33ea474d9f6a4930`,
exits 132 while lowering the first of 296 modules in the pure-comprehension
production-owner probe. This failure precedes comprehension expression lowering.
LLDB identifies `HirLowering.report_reexport_chase_stats+736`; the stack is
`find_reexport_source_walk -> register_imported_symbol_inner ->
materialize_imported_field_dependency -> resolve_import_symbols`.

Existing dynamic evidence is retained in P0
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/evidence/macos-enforced-bd544/pure-comprehension-2710d94/`:
`main.spl`, `run.shs`, `build.log`, `build-rss.env`, `debug.log`,
`debug-rss.env`, and `RESULT.md`. No evidence there was modified by this lane.

Static LLDB disassembly of that exact admitted binary establishes:

| Source path | Branch | Target |
|---|---|---|
| Counter not divisible by 20000 | `b.ne` at +52 | `udf #0xc11f` at +736 |
| Environment value differs from `1` | `b.ne` at +244 | `udf #0xc11f` at +732 |
| Enabled reporting boundary | `rt_eprint_value` at +700 | zero return value at +704; `ret` at +728 |

Thus the first early return traps before any environment read or memo formatting.
The second early return is independently emitted as a trap. This is a procedural
return ABI defect, not evidence of a corrupt re-export cache.

The bootstrap producer sources explain the mismatch:

- `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs` lowers `eprint`
  as a builtin with `TypeId::NIL`.
- `hir/lower/module_lowering/function.rs` treats a terminal expression whose
  type differs from `VOID` as value-producing, then assigns an unannotated
  function `TypeId::ANY`. NIL is not VOID.
- `codegen/instr/body.rs` deliberately traps on a valueless return in a
  non-VOID function. The enabled path can return its nil value normally.

## Scoped source correction and open producer defect

Declare `report_reexport_chase_stats() -> ()`, its intended side-effect-only
contract. Its production caller in `module_reexport_materialization.spl`
discards the result. Both early returns, the modulo boundary, environment
policy and exact output remain intact. The docstring's stale 200k claim is
corrected to the existing 20k behavior. No runtime work or allocation is added.

The general producer inference defect remains OPEN: terminal NIL-valued I/O
combined with an early bare return must not silently produce a nonvoid ABI
and runtime trap. The explicit annotation corrects this production API; it
does not establish that unannotated user procedures compile correctly. Do not
remove the backend trap or manufacture return values for nonvoid functions.

## Focused production-owner regression

`test/fixtures/native/hir_reexport_stats_return.spl` imports the real
`HirLowering` type and reporter, initializes a nonempty memo and memo-hit count,
then calls it at 1, 19999, 20000, 20001 and 40000. After every call it checks
the counter, hits, memo length and memo value remain unchanged. Completion
alone is insufficient: require all five `reexport-stats-returned-N` markers
and `reexport-stats-state-preserved`, exactly six stdout lines, exit zero.

Run the compiled native fixture in separate subprocesses with
`SIMPLE_HIR_REEXPORT_STATS` unset, empty, `0`, and `1`. The first three must
have empty stderr. The `1` case must have exactly these two nonempty stderr
lines and no other nonempty lines (blank lines from the eprint facade may
differ by producer):

```text
[reexport-chase] calls=20000 memo_hits=17 memo=1
[reexport-chase] calls=40000 memo_hits=17 memo=1
```

Compilation must retain producer/runtime digests, frozen source hashes,
`SIMPLE_NO_STUB_FALLBACK=1`, a phase-bound private cache, and the parent's
unchanged RSS/deadline guard. The existing Stage2 binary cannot consume its
own source fix; the parent must select and authorize the producer/rebuild
boundary. A bootstrap-producer mini-build is bootstrap evidence only, never
admitted pure-Simple evidence. Then inspect emitted reporter disassembly to
confirm both early returns have normal epilogues. Parent-owned Stage2
admission and the original comprehension probe remain required afterward.

## Authorized bootstrap-only native evidence

After static review the parent authorized one focused green build. Preflight
rejected the stale historical producer digest `3ff20095...7c0a6`; the current
frozen producer was separately authorized after verifying all manifest hashes:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`

SHA-256 `69b67b26e965e7fa3de2d292c2774980be15e84625dd382708092f848241dfce`.
This is a Rust bootstrap producer used only for the scoped regression; it is
not admitted pure-Simple evidence. The original admitted Stage2 failure above
is the retained baseline, not a same-producer red/green comparison.

Evidence in worktree
`/Users/ormastes/simple-tmp/reexport-stats-trap-20260923/build/native_probe/reexport-stats/`:
`build-fixture.shs`, `run-cases.shs`, `recorded-build-command.shs`,
`green-inputs.sha256`, `green-build.log`,
`green-build-rss.env`, each case's stdout/stderr and RSS receipt, and
`green.disasm`. The wrappers preserve complete commands, the verified frozen
runtime stamps, LLVM/LLD 23.1.1 hashes, source/fixture hashes, private cache
bound to the producing hash, one worker, and `SIMPLE_NO_STUB_FALLBACK=1`.
`recorded-build-command.shs` was written after execution from the exact outer
watchdog invocation, retaining the build deadline absent from the RSS receipt;
that recorded wrapper itself was not rerun.

- Build: 282 compiled, 0 cached, 0 failed; 75.18 seconds.
- Sampled tree peak: 721,248 KiB; process max RSS: 598,573,056 bytes.
  Both are below the ordinary 1 GB compilation target for this sample.
- Guard: unchanged 5,859,375 KiB sampled cap, 100 ms interval, 180-second
  build deadline and 20-second per-case deadlines. This is not a kernel hard
  memory limit. Build and all four runs report zero observer errors/restarts
  and quiescent cleanup. Very short run samples are not exact RSS peaks.
- Unset, empty, `0`, `1`: all PASS, exit zero, exactly six expected stdout
  markers each. The first three have empty stderr; `1` has exactly the two
  expected nonempty reporting lines. State assertions execute after all calls.
- Emitted disassembly: nonboundary branch +52 targets the normal return
  epilogue +760; disabled-environment branch +244 targets epilogue +732.
  The reporter contains three normal returns and no `udf`.
- Fixture executable SHA-256:
  `e3f57ad081699ad47cb13b54337577f27505768628a42ba986697a154e3bbca4`.

One build and one execution of each environment case were performed; no
passing test was repeated. The shared heavy slot was released immediately
after the four cases. No full bootstrap, Phase2, publication, or shared-P0
mutation occurred. No speedup or broad no-regression claim follows from one
green build. Rebuilt Stage2 admission, broad compiler/core/MCP verification,
and the original comprehension production-owner probe remain parent-owned.

Independent Astra-high static review found no actionable findings: explicit
unit resolves to VOID, survives return inference, accepts the NIL tail, and
selects the normal valueless-return backend path. The unchanged predicates,
documented environment matrix and fixture state assertions were accepted.
The subsequent independent Astra-high evidence review accepted all four
native cases, matching source/binary hashes, emitted returns, and resource
claims. Its minor request to retain the outer build-watchdog command was
addressed by the explicit post-execution record above, without rerunning any
check. No compiler admission PASS is claimed.

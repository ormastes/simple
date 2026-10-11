# Phase-2 verification matrix: strict stage-2 compiler error family (2026-10-09)

Batch record for the phase-2 verification matrix failures of the self-hosted
(stage-2) compiler on worktree `release-llvm-20261007` (branch
`work/rel-phase2-matrix-fixes-20261009`, stage2-admitted compiler sha
`17133b7019…`, snapshot `scv-revision-v1-cbb5b270…` == src/ at the time).

Evidence logs:
`.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/test_runner_build.log`
and `compiler_cli_build.log`.

Local reproducers live under `build/matrix-probes/` (gitignored, kept for the
compiler lane). Seed = `src/compiler_rust/target/bootstrap/simple` (accepts
every construct below; verified by running the probe programs where the
construct is runnable). Stage-2 = the admitted stage2 binary.

## Source bugs fixed in this batch

### S1. Bare enum variant `Composite` in test-runner matches (error classes 3, 4, 5)

- **Errors**: `enum match: bare variant 'Composite' is ambiguous (declared in
  multiple enums)` (5x), paired 1:1 with `enum construction: missing runtime
  identity for ''` (5x) and with `unresolved method call: contains` /
  `find` at `test_runner_types.spl:8:38` (bogus span; real sites are the
  `spec.contains(layer)` / `spec.find("(")` arms).
- **Root cause (source)**: five match arms used the bare variant
  `case Composite(spec):` in a build where several enums declare `Composite`
  (`lib/*/compositor/frame.spl`, `lib/*/message_transfer.spl`, plus
  `TestExecutionMode` itself). The strict compiler rejects the ambiguity; the
  failed pattern leaves the `spec` binding untyped, which cascades into the
  `contains`/`find` "unresolved method" errors, and the enum-construction
  identity errors pair with the same five sites.
- **Fix**: qualify all bare arms as `TestExecutionMode.Composite(...)`:
  - `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:460,470,476,494,511`
  - `src/app/test_runner_new/test_runner_types.spl:192,202,208,226,243`
  (Sibling modules `test_runner_config.spl` / `test_runner_files.spl` already
  use the qualified form — this matches the established style.)
- **Validation**: stage-2 now lowers a probe copy of the fixed module with
  zero MIR errors (previously reproduced `contains`/`find` at the phantom
  8:38 span); seed runs both modified modules correctly
  (`build/matrix-probes/seed_check_types.spl`, `seed_check_app_types.spl`
  print OK). Repro pair: `build/matrix-probes/p7/main.spl` (`f` qualified
  passes, `f2` bare fails).

## Compiler bugs (NOT patched in source; reproducers in build/matrix-probes/)

### C1. Unresolved primitive text methods on non-trivial receivers (error class 1, and `trim`)

`to_int`, `contains`, `find`, `lower`, `trim_start`, `last_index_of`,
`split`, `trim` fail MIR method resolution when the receiver is not a plain
local val:
- array index: `args[i].to_int()` — `p3c.spl` (stage-2 errors; seed runs it,
  prints RESULT=3).
- field of an imported struct (`C2` family below).
- nil-guarded `text?` receiver: `env_env.lower()/trim` at
  `src/app/io/mod.spl:123` (cranelift-matrix data point; same family as the
  recently landed `f87ed657830` / `cb2bed7ddff` narrow-nil-receiver fixes, so
  the admitted compiler still misses some receiver forms).
Error spans are misattributed (e.g. every `to_int` in
`test_runner_args.spl` is reported at `57:8`, a fn-declaration line).

### C2. Enum / struct equality through IMPORTED struct fields (error class 2)

`r.packet.packet_kind != KindV4.Frozen` fails with "operator overload for
struct KindV4" when `Receipt`/`Packet` come from an imported module
(`p6/t1.spl`, `t2`, `t4`, `t6`, `t8`, `t10`, `t11`, `t14` fail), while the
identical code with a LOCALLY declared struct passes (`p6/t12`, `xmod`
probes). Bare enum parameters compare fine (`p6/t5.spl`). This is the root of
the `ProcessObservationPacketKindV4` errors at
`src/lib/nogc_sync_mut/io/process_ops.spl:1096,1119` (reproduced via
`build/matrix-probes/pb/` copy of the real module) and of the whole
`WalEntryType` / `TerminationCause` / `BlockStatus` / `FeatureStatus` /
`DecisionStatus` / `ResourceEvidenceQuality` / `McdcMode` operator-overload
error family in the matrix log.

### C3. Generic type parameter named `Id` is not resolved (CLI HIR failure, module 1 of 2)

`lib.common.search.ranking` + `lib.common.search.types` poisoned with
`unresolved type: Id` where `Id` is the type parameter of
`struct PostingList<Id>`. Minimal repro: `p10_generic.spl` / `p10b.spl`
(stage-2 HIR rejects; seed runs fine). Renaming the parameter to `T` passes
HIR (`p10c.spl`), so the strict type table mishandles the name `Id`
specifically.

### C4. CLI HIR failure, module 2 of 2: `compiler.backend.backend.backend_types`

`unresolved type: BackendKind` reported inside the very file that declares
`enum BackendKind` (line 22). Not reproduced standalone (needs the large CLI
closure); the module is poisoned wholesale in the module-diagnostics sweep
(attempt `…/module-diagnostics/attempt.sLaYUC/36`). Treat as a strict-HIR
module-registration bug pending a minimal repro.

### C5. Diagnostic-storm "hang" on the error path

The cranelift-observed "100% CPU after printing a MIR error" reproduces on
the llvm lane as pathological slowdown, not an infinite loop: per-module
diagnostics attempt 36 (`src/app/bootstrap_builder/main.spl --emit-object`)
ran 1489 s at 100% CPU and exited FAIL, emitting a 43 MB log dominated by
`hir-reexport-chase-unresolved` lines (quadratic in closure size; 118k lines
for one module). Small closure repro of the spam multiplier:
`build/matrix-probes/p5_process_ops.spl` (tiny entry, dozens of chase lines).
Seed has no equivalent pass. Suspect: the chase-unresolved diagnostics loop;
needs a compiler-lane fix (cap/dedup), not a source change.

## Remaining unknowns

- **B5b "match has multiple wildcard/binding default arms"** (3 unique sites):
  no match in any failing source actually has two wildcard/binding default
  arms (scanned all runner modules cited in the log). Likely a cascade of the
  bare-variant/identity failure path in the same module cluster (it sits
  inside the `test_runner_types` error group), but it was NOT reproduced
  standalone — the small-closure copy of the module emits only the
  contains/find errors. Needs re-check after the S1 fix lands in a full
  matrix run.
- The `for-in over non-array iterables (collection mir type: I64)` family
  (e.g. `test_runner_args.spl:761` `for i in s.len():`) and the
  `unresolved method call: set/get/valid_rows/…`, `infer-arm`, and
  `enum match: unsupported arm pattern` masses in the same logs were not
  bisected in this batch; several are likely C1/C2 cascades but that is
  unproven.

## 2026-10-11 addendum: valid_rows / for-in I64 family bisected (release-llvm-20261011 lane)

The previously unbisected `for-in over non-array iterables (collection mir type:
I64)` + `unresolved method call: valid_rows` family is a C1 receiver-identity
cascade: in `database_queries.spl` and `factory.spl` the table receiver is a
`case Some(table):` match-arm binding from `SdnTable?`. Strict HIR fails to
propagate the arm payload type, `SdnTable.valid_rows() -> [SdnRow]`
(core.spl:408) fails to resolve, and the fallback names a same-shaped `i64`
symbol — the unrelated `valid_rows: i64` parameter in
`src/lib/gc_async_mut/slang/model_executor/backend.spl:742,767` — so the for-in
collection lowers as I64. Paired `enum match: unsupported arm pattern` is the
same arm-pattern typing failure.

Workaround landed on `work/release-llvm-fixes-20261011` (PR #2999): bind match
results and arm payloads to explicitly annotated `SdnTable` locals before
calling `valid_rows()`. Probes for re-verification:
`build/matrix-probes/dbq/` (minimal MiniDb repro + annotated-local variant) and
`build/matrix-probes/c4_backendkind/`. Compiler-side fix still required for the
receiver-identity family itself; PR #2967 (HIR cache/receiver identity,
e650ad19d67) may cover part of it.

## 2026-10-11 addendum 2: std.crypto.sha3 module-index registration gap (C6, release-llvm-20261011 lane)

Stage-2 matrix `test_runner_build` (admitted compiler 85fc943a, post-PR-#2967)
fails in `src/lib/common/crypto/hmac.spl`:

    module std.crypto.sha3 has no exported item sha3_384_bytes
    module std.crypto.sha3 has no exported item sha3_512_bytes
    unresolved name: sha3_256_bytes / sha3_384_bytes / sha3_512_bytes
    (12 errors; module lib.common.crypto.hmac poisoned)

The functions ARE declared in `src/lib/common/crypto/sha3.spl:341,347,353` with
the same plain `fn` style as `sha1.spl:251` (`sha1_bytes`), which imports fine.
So the compiler's module-index registration silently drops std.crypto.sha3's
exports. Same family PR #2967 chased ("failed one HMAC module importing SHA3
functions; module-index registration under investigation") but the failure
persists WITH #2967 merged (e650ad19d67 in tree). Suspect visit/declaration
order sensitivity (cf. robust-5a test 2b284af6820 pinning module typing
against declaration/name/visit order). Needs a compiler-lane fix; probes under
`build/matrix-probes/sha3reg/`.

## 2026-10-11 addendum 3: C6 root cause — missing std.crypto.sha3 facade (source gap, not a registration bug)

Bisect (probes `build/matrix-probes/sha3reg/`, minimal-shard-repro) corrected
addendum 2: `std.crypto.sha3`'s exports are NOT dropped by a registration bug.
`src/lib/crypto.spl` declares `mod crypto.types/sha256/sha512/hmac/legacy_hash/
sha1` but no `mod crypto.sha3`, and `src/lib/crypto/sha3.spl` did not exist —
sha3 was the only `common/crypto` module missing its `src/lib/crypto/*`
re-export facade. The sequential compile path falls back to the real file, so
only the `--low-memory` HIR-shard path (used by the stage-2 matrix builds)
fails: item lookup chases facade `lib.crypto`, which declares no sha3 names.

Fix (PR on work/rel-c6-sha3-facade-20261011): add `src/lib/crypto/sha3.spl`
re-export facade + `mod crypto.sha3` in src/lib/crypto.spl (matches the
`crypto/hmac.spl` idiom; validated 0 hir-fatal on a 256-module shard repro).

Latent same-family gaps (NOT in today's closures; fix when imported):
`std.crypto.md5` (src/os/crypto/pbkdf1.spl:15) and
`std.crypto.entropy_platform` (src/os/crypto/entropy.spl:5) also lack
`src/lib/crypto/*` facades.

Related open infra failure (NOT source): `compiler_cli_build` shard owner went
`status=BLOCKED exit=-2 claimed=0 sealed=-1 inventory incomplete rows=-1` after
clean parse (2204/2454 files, zero module errors) — same family as the wrapper
receiver-proof `cannot establish invocation ledger` failures on 2026-10-11
runs 2-4. Nondeterministic shard-owner startup under multi-lane host load;
needs compiler-lane diagnosis of the shard owner startup/claim path.

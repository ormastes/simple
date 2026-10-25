# release_phase3 Stage2 reverse-reference publication SIGSEGV

Status: scoped repair verified for the original p2_add failure; full admission
remains unverified. A separate HIR crash remains open below.

## Bound reproduction

Source: `9929e6f62a0`, immutable build directory
`/tmp/phase3-releasephase3-stage2-admission-9929e6f62a0-20261025`.
The terminal harness renamed the candidate to
`stage2/aarch64-unknown-linux-gnu/simple.rejected` (SHA256
`0accdb54460a8360508824d0042bc84857552718cd037a4159ab5c5fea6f12d9`).
Its Stage2 sanity receipt reports `frontend_smoke_status=117`; the actual
native-build worker died with SIGSEGV while compiling
`src/compiler/bootstrap_admission/p2_add.spl`.

The diagnostic worktree is `/tmp/simple-releasephase3-p2add-fix`.
All diagnostic outputs are under `/tmp/releasephase3-p2add-debug`.
The original candidate, runtime authority, source checkout and caches were
preserved. The failed admission harness had removed its probe temp directory,
so its `candidate_frontend_admission.shs` arguments were reconstructed with
private output/cache paths. Direct worker diagnosis supplied the standard
validated default environment-policy handoff; no checker was suppressed.
HIR/MIR sharding was disabled for the single-process diagnostic replay.

`gdb-direct.log` captures the failing instruction at
`reverse_reference_module_publish_v1+1648` (`ldr x0, [x6, x3, lsl #3]`), called
by `MirLowering.lower_module_transient_scoped` after transient scope end.
The old seal promotes only the optional batch carrier; publication subsequently
reads the batch's array limbs after reclamation. The exact generic/runtime
mechanism by which carrier promotion misses the owned graph is not established
by this backtrace.

## Repair and evidence

Ported only `src/compiler/00.common/cache/reverse_reference_facts.spl` from
the refreshed `release/1.0.0` head `5e8ad7e3638`; its contents match that branch
exactly. This carries the existing explicit promotion of the batch, array
limbs, element strings and phase-owner roots, typed generic arguments, and
persistent array mirrors. Related upstream commits include `2b996fbc6f7`,
`ff1f69fd931`, `3159810d701`, `9a79de084e9` and `8511efb3598`.
Existing token, generation, sealing and invalid-registration checks remain.

The recorded bootstrap producer/runtime from
`stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority` rebuilt the candidate
using a private copy of its object cache: **3 compiled, 1484 cached, 0 failed**,
42.7 seconds. `rebuild-argv.txt` and `rebuild.log` retain the invocation/result.
This was a scoped candidate rebuild, not a full bootstrap or admission run.
The resulting `simple-patched` SHA256 is
`38ffa978a5eb956cdaca86ca3488cc52db307ed69e9b423b6d21447cfb054242`.

| Check | Actual result |
|---|---|
| Original p2_add with rejected candidate | SIGSEGV in reverse-reference publication |
| Same p2_add with patched self-hosted candidate | Compile 0; executable 0; stdout `5\n` |
| Hello World with patched self-hosted candidate | Compile 0; executable 0; stdout `hello\n` |
| New native scope-survival fixture, recorded bootstrap producer | 42 modules compiled; executable 0; PASS |
| Same narrow fixture against old owner source | Also PASS; adjunct coverage, not causal negative control |

`patched-p2add-argv.txt`, `patched-hello-argv.txt` and their corresponding
`.log`/`-run.txt` files retain the actual self-hosted checks. The new fixture
`test/fixtures/reverse_reference_scope_survival/main.spl` checks all four batch
arrays across two consecutive scopes, dynamic fact fields and evidence digests,
alias order, incomplete-family filtering, duplicate seals and wrong/stale tokens.
The exact p2_add before/after result is the causal regression evidence; the
standalone fixture does not reproduce the full compiler's original corruption.

## Open qualification blocker: custom primitive registry HIR crash

Compiling the new 50-module fixture closure with the patched self-hosted
candidate exits with SIGSEGV during HIR of `reverse_reference_facts`, before MIR.
`patched-fixture-argv.txt`, `patched-fixture.log`, and `gdb-fixture-hir.log`
retain this separate failure. The GDB chain is:

```
custom_primitive_find
custom_primitive_is_name
HirLowering.lower_named_kind
HirLowering.named_instance_kind_or_any
HirLowering.lower_named_instance_kind
HirLowering.lower_type
HirLowering.declared_callable_type
HirLowering.declare_module_symbols
```

The failure's presence before this patch has not been established. It is not
treated as a passing test or repaired in this scoped change. Full compiler/lib,
MCP/LSP checks, Stage2 admission and dependent phases remain outstanding.

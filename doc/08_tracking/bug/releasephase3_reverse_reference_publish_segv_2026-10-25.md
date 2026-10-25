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

Initially ported only `src/compiler/00.common/cache/reverse_reference_facts.spl`
from the refreshed `release/1.0.0` head `5e8ad7e3638`; that initial port matched
the branch exactly. The review correction below subsequently changes the
promotion schedule and failure result. The port carries explicit promotion of the batch, array
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

## Review correction: bounded phase promotion and truthful seal failure

Review of `d8b185ab2bf` found that promoting the accumulated phase containers
on every module seal repeatedly walks earlier facts and aliases. Persistent
array/dictionary roots still undergo child traversal in the native runtime;
being persistent does not make their promotion a constant-time operation.

The corrected owner retains phase containers once per owner generation. The
readiness flag resets with `reverse_reference_owner_clear_v1` and is set only
after all four initial promotions succeed. This supports owner initialization
inside the first allocation scope. Each later module promotes its own batch;
publication then appends after scope end, where container growth and newly
allocated alias lists are persistent. Direct registration without a module
batch is an unscoped operation. The audited HIR/MIR/selective/archive paths
start their batch immediately after entering their transient scope.

The seal now returns the conjunction of initial ownership, element ownership,
and phase-root ownership. It publishes its sealed mirror and batch handles only
after all succeed; an unsuccessful seal remains invalid and requires abort
before scope reclamation. No accumulated phase graph is promoted repeatedly.
This removes the newly added repeated traversal by construction; no whole-build
time or RSS improvement is claimed from the small fixtures.

Ordinary native checks of this correction used the recorded bootstrap producer
and `core-c-bootstrap` runtime authority, with `SIMPLE_NATIVE_BUILD_RUST=1` and
`SIMPLE_NO_STUB_FALLBACK=1`. They are bootstrap-produced fixture evidence:

- The revised scope-survival fixture passed owner creation both inside and
  outside an allocation scope, then passed 32 batches per generation (64 total),
  checking retained dynamic facts, aliases, digests, filtering, and tokens.
  Binary SHA256: `82efb0203d6ad68287b397e0275e8ad2920fa0cc055520e464efa8b47c0806f9`.
- `abort.spl` deterministically attempts sealing before pause, requires refusal
  and refusal to publish, then pauses, aborts and ends the scope. It verifies
  that no facts/families/aliases escaped. Compilation was 1 changed module,
  41 cached, 0 failed; executable exit 0 and the PASS marker were observed.
  Binary SHA256: `517a5144b0f4f08bb684a57a476a78983ad9a04fd9c655268221312fc1124180`.
  Logs: `/tmp/releasephase3-p2add-debug/review-fix/abort-deterministic-authority-build.log`
  and `abort-deterministic-run.log` in the same directory.

An initial fixture compile omitted the recorded native-build authority flag
and exited 1; its `abort-deterministic-build.log` is retained separately. The
ordinary deterministic test covers early promotion refusal, not a failure
injected after some element promotions. No debugger-injection result is claimed.
The p2_add and Hello receipts above belong to the initial port; a compiler
rebuilt with this review correction and full admission remain pending.

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

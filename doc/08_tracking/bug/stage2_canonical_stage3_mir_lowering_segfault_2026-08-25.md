# Canonical pure-Simple Stage-3 build crashes entering MIR lowering

Status: root cause fixed in source; admission retry pending and blocked by the
current session's three-cycle cap.

## Exact evidence

- Producer: admitted pure-Simple Stage 2 at
  `/mnt/data/worktrees/lane-bootstrap-s4/build/bootstrap/s4run/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`, SHA-256
  `112a11f6e9e0076ff44e164aabaf14069aa51e91d2bc0f6af4076e59e55d7004`.
- Invocation: the canonical Stage-3 environment and positional
  `src/app/cli/bootstrap_main.spl` contract from
  `scripts/check/lib/bootstrap-stage3/manifest-verify.shs`, with
  `SIMPLE_NO_STUB_FALLBACK=1`, Cranelift, `core-c-bootstrap`, and the admitted
  runtime authority.
- Retained cache:
  `build/bootstrap/abnormality-source-stage3/x86_64-unknown-linux-gnu/native-objects-LAU8Q9`.
- Final log:
  `build/native_probe/abnormality-source-stage3-canonical-retry.log`.
- Terminal result: exit 139 (`Segmentation fault`, core dumped).
- Last successful phase: all 687 surface files released, parse/HIR completed,
  monomorphization and post-mono verification reported zero diagnostics; the
  process crashed immediately after `mir ... lower_to_mir` began.
- Elapsed before crash: 772,383 ms. Peak live RSS observed shortly before the
  crash was approximately 1.7 GiB.

## Root cause and source correction

The kernel fault address was `0x28` at executable address `0x81a5bd`.
`addr2line` mapped it to
`bootstrap_lower_hir_globals_to_mir_module_for_target`; disassembly placed the
fault at the first `HirModule` field load. Immediately before it, generated
code called `lib.nogc_async_mut.async.poll.Poll.unwrap` for
`_bootstrap_entry_hir_module.unwrap()`.

The driver had already extracted `ctx.bootstrap_entry_hir` through the same
ambiguous `.unwrap()` twice, then stored the invalid tagged result in the MIR
global. The first source correction used only
`ctx.hir_modules[entry_module_name]`, but the canonical bootstrap shape does
not populate that map key and therefore failed closed with zero MIR
instructions. The corrected source now pattern-binds `Some(entry_hir)` and
retains the map only as the absent-option fallback. The MIR global extraction
likewise uses a pattern-based helper instead of `.unwrap()`.

A hash-recorded diagnostic copy of the admitted producer retargeted exactly
three bad call sites from `Poll.unwrap` to the existing `rt_enum_payload`:
SHA-256 `7373f609508312cd2dabe2979a19044d4bfb4c9ec0eaecd9eaf0ff857e3ac193`.
It eliminated the SIGSEGV and reached the intentional zero-instruction guard,
proving the crash diagnosis while preserving the admitted original unchanged.
The three-cycle cap expired before the pattern-based correction could be
admission-tested.

A fresh admission session proved the patched producer no longer crashes. The
minimal canonical shape reaches the zero-instruction guard because the legacy
producer supplies no entry bodies in that mode. The supported full-closure
bridge then reduced to one 600-second compile timeout in
`src/compiler/10.frontend/core/__init__.spl`; that independent remaining
blocker is tracked in
`stage2_frontend_core_init_compile_timeout_2026-08-25.md`.

## Attempts and exclusions

The first canonical attempt was bounded to 600 seconds and timed out while
still making surface progress. The cache-preserving final attempt used an
1,800-second bound and reached MIR before SIGSEGV. An earlier broad-source
command compiled 2,179 artifacts but linked against the intentionally limited
core bundle, so its missing-symbol link result is not treated as this crash.
No Rust/hosted fallback, stub fallback, cache deletion, or fourth retry is
permitted.

## Resume plan

Owner: self-host compiler MIR pipeline maintainer.

After the session retry budget resets, rerun the canonical Stage-3 command with
the retained cache and confirm the MIR field read no longer faults. Do not
restore `HirModule?.unwrap()` at this boundary. Acceptance requires a no-stub admitted Stage 3, then an
admitted Stage 4 that runs the feature's focused tests, doc generation, and
production-readiness verification with `STATUS: PASS` before commit/push.

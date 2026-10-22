# Imported libc `free` rebinds to RtStringBuilder.free in seed native builds (2026-10-12)

Bug db: `bootstrap_imported_free_method_rebind_2026_10_12` (issue #3352).
Symptom (cycle 11): stage2 sanity gate rejected the freshly built stage2
candidate: `candidate_frontend_smoke: p2_add-build failed (raw rc=139)`.
Reproduced 3/3 against
`.simple/storage/build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple.rejected`
with the exact smoke invocation from
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`; gdb batch
backtrace: SIGSEGV in `rt_string_builder_free`, x0 = ASCII "/home/yo..." — a
path text pointer passed as a string-builder handle.

## Mechanism

`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`
(`build_import_map`): every class method registers its BARE method name into
`raw_to_mangled` (`free` -> `...RtStringBuilder.free`), and every `extern fn`
registers an IDENTITY mapping (`free` -> `free`). With both present the bare
name is ambiguous, and the ambiguity rule was pure first-wins by module
processing order. When `src/lib/common/string_builder.spl` sorted before
`src/lib/nogc_sync_mut/io/path_identity_abi.spl` in the stage2 closure,
`import_map["free"]` bound to the builder method; `_path_final_existing`'s
`free(input)` (libc, for the realpath input buffer holding "/home/...") then
called `rt_string_builder_free` and crashed at candidate startup during SCV
cache init. Cycle 8 passed only because closure order happened to favor the
extern. The local-extern workaround (36e17744f8a, reverted by 2a6cf083251) was
disproven because the call site resolves through this global import map, not
through per-module extern identity.

## Fix

In the ambiguous-name branch of `build_import_map`, prefer an extern identity
candidate (`mangled == raw`, which only `Node::Extern` registers) over
first-wins file order; keep historical first-wins when no extern identity is
among the candidates. An explicit extern declaration is stronger evidence than
a same-named class method's bare-name fallback, and the fix is order-
independent. This covers the whole collision class (`free`, `malloc`, ...).

## Verification

- Rebuilt the Rust seed (canonical cargo recipe, profile bootstrap,
  `--features llvm`) with the fix.
- Rebuilt the stage2 candidate from the fixed seed (stage2-command.transcript
  invocation) and reran the p2_add frontend smoke (`SIMPLE_BOOTSTRAP=0`):
  passes (see cycle-12 evidence / build/repro-stage2-fix/freefix/).
- The interpreter-mode repro fixtures under
  test/fixtures/repro/compiler/bootstrap_imported_free_method_rebind/ pass
  under the fixed seed's native build.

Cycle 8's stage2 (cbf3d3facb5 + 610110c1975) passed this same sanity gate, so
610110c1975 (MIR erased-receiver/for-in fixes) is exonerated; the trigger was
closure-order drift from the intervening commits exposing the latent
first-wins ambiguity.

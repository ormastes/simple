# Literal nil is compatible with a declared optional enum payload

Status: focused native positive and both negative compiler regressions PASS; broader compiler/app/bootstrap matrices UNRUN for this isolated patch. This is not whole-compiler or vector completion.

The MIR payload validator rejected `OptionalTextCarrier.Payload(nil)` despite the declared `text?` slot. The old qualified Phase2 744f90 rejected the positive entry at line14:55 with payload type mismatch; retained evidence is `/var/tmp/simple-item5-phase2-20261005/build/item5-optional-nil-baseline/`. The range-checker closure exposed the same boundary at `HirExprKind.IntLit(7, nil)`, whose suffix is declared `text?`.

The eight-line change in `enum_payload_local_compatible` accepts exact `HirExprKind.NilLit` only when the expected type is `HirTypeKind.Optional`. It neither treats arbitrary erased I64 as optional nor mistakes integer3 for nil. Existing checks still handle nonnull typed optionals, nominal/container payloads and nonoptional requirements. No runtime representation, record owner, early-let or code-point change is included.

## Actual focused evidence

Producer SHA256: `afaa53e061807d11b0e36b79088c3af3a4e51c5dc3d224f6b5683f181af49f4c`; parent qualified its actual LLVM Hello build/run. This producer contains separately reviewed compiler overlays in addition to this change; the focused results do not qualify every overlay.

Positive source `test/fixtures/compiler/enum_optional_nil/main.spl` constructs and matches absent, present text and present empty text. Build exit0, native run exit0, `checks=3 failures=0`. Native binary SHA256 `b04ffc7a6324cf2fca4d0fa7da2cb877f269df84dfcd4c8153799eb5af1aab7a`. Evidence: `/var/tmp/simple-item5-phase2-20261005/build/item5-owner-nil-core-runtime/optional/` (build/run logs, source/binary hashes, status and watchdog receipts). Build peak560328 KiB, run peak8496 KiB; both quiescent1.

The successful attempt explicitly selected `SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap` in the environment as well as the requested CLI profile. This is a recorded diagnostic workaround for a separate positional CLI forwarding defect, not a claim that the positional flags are repaired here. The exact parent launcher and retained logs define the attempt; no seed was substituted for application execution.

Both intentionally invalid files compiled independently and exited1 for the expected MIR payload mismatch at line6:47:
- `negative_integer.spl`: integer3 into OptionalTextCarrier.Payload(text?), evidence `build/item5-owner-nil-negative/optional-integer/`.
- `negative_nonoptional.spl`: literalnil into RequiredTextCarrier.Payload(text), evidence `build/item5-owner-nil-negative/optional-required/`.

No binaries are expected or claimed for the negative entries. These are semantic rejection results, not generic failed builds.

## Separate failure retained

The initial positive compile succeeded but execution failed under the accidentally selected ordinary runtime (`build/item5-owner-nil-tests/optional/`). Its binary mixed tagged native enum construction with a legacy raw-pointer enum checker. The five-case diagnostic also failed ordinary integer enum matching (`build/item5-optional-nil-diagnostic/diagnosis.md`). Current runtime_native.c already has the correct checker. Positional CLI option forwarding and ordinary runtime symbol ownership are separate repairs; neither is hidden by this focused core-C pass.

Landing scope: one eight-line production change, these three fixtures and this evidence note. Static landing gates are recorded separately by the landing owner. No rerun of the unchanged green native evidence is needed. Broader compiler/lib/MCP/LSP checks, full range closure, DB/live HTTP, LLVM/Cranelift subsystem matrices and complete bootstrap remain unrun or independently failing; no broader PASS is implied.
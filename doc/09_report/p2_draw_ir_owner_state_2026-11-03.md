# Draw IR execution owner candidate

Bug: `engine2d_draw_ir_free_function_state_visibility_2026-06-05`.
Claim: `p2-draw-ir-20261103`; canonical helper admitted the claim on
2026-11-03T08:04:50Z. Base: `89d4e41ec88`, fetched `release/1.0.0`.

The batch and composition walkers already returned their updated Engine2D
internally, but ordinary public results discarded it. The composition path
copied CPU framebuffer pixels into the argument for legacy compatibility;
that copy cannot convey general backend/font/frame state.

The new `Engine2dDrawIrAdvOwnerResult` returns the actual final engine with the
unchanged receipt. `engine2d_draw_ir_adv_batch_owner_with_images` and
`engine2d_draw_ir_adv_composition_owner_with_images` expose this boundary.
The composition owner path presents its own final engine without legacy CPU
writeback. Existing receipt-only entrypoints preserve their signatures and
behavior. Both Screen2d showcase hosts commit the returned engine before
checking receipts, including rejected partial frames.

No renderer substitute, fabricated framebuffer or compiler semantics change
is introduced. Native-handle ownership is the existing engine contract; the
caller must continue with and shut down the returned owner, rather than also
using the pre-execution value.

`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_owner_state_spec.spl`
authors three real scenarios:

- Exact: batch owner readback, sequential disjoint draw, immutable prior
  receipt pixels.
- Adjacent: multiple composition batches, then exact retained damage with
  untouched pixels preserved.
- Adjacent: legacy receipt readback and empty composition owner continuation.

Behavioral status: **TEST_BLOCKED**, zero executed cases. `bin/release` is
absent; the tracked Rust seed is bootstrap-only. No interpreter, LLVM native,
Cranelift native, core/MCP smoke or library checks are claimed as passing.
Required resume gates include the new focused spec and existing Draw IR and
showcase host specs through a qualified self-hosted producer, followed by the
required compiler/lib/MCP checks and native smoke gates. Keep the PR draft.

Static checks are recorded separately in the PR receipt; they cannot admit
behavioral correctness or prove configured-family/native backend parity.

Static evidence: working-tree direct env/runtime guard PASS; whitespace diff
check PASS. Tracked `doc/06_spec` executable `_spec.spl` count is zero.

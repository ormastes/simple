# Stage2: UFCS method result leaves match scrutinee untyped

- **ID:** stage2_ufcs_method_result_untyped_match_payload_2026-11-07 — status open.

## Re-check 2026-11-08 (lane bootp2)
The run13 failing site no longer exists: commit `74d077aafda` ("align trait impls and stale
method callers with Stage 2 MIR") rewrote `src/compiler/99.loader/loader/module_loader.spl:747`
to the direct call `objtaker_take_with_types(moduleloader_ensure_obj_taker(self), ...)`, so the
stage3 closure no longer contains the UFCS shape. The compiler root (a UFCS-alias method's
declared return type not propagated to a `match` subject in 50.mir) was not reproduced or fixed
here; it belongs to the unresolved-method-call cluster. Re-confirm with an in-process HIR+MIR
probe of `x.take_with_types(...)` matched by `case Code(..)` before closing.

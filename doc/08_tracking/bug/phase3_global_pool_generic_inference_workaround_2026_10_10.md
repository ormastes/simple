# Global pool generic inference diagnostic workaround

Status: OPEN (P1)

Nine calls in core/types.spl use explicit type arguments for diagnostic continuation. This does not repair inference. Tiny explicit-argument control compiled and linked but runtime SIGSEGV; no runtime qualification. Original reproduction and control: test/fixtures/compiler/phase3_global_pool_typeargs_workaround_probe/. Native18 continuation achieved seven source-module HIR receipts; no object was produced.

**Revalidated 2026-11-02: still plausible because OPEN (P1); no merged fix commit with a passing regression is cited in this doc.**

## WA-P5 Update (2026-11-26)

- Status: `ROOT-FIXED+STAGE2-GATED` (closed-obsolete in `bug_db.sdn` via `ee4a0a0f714` after `56c0499ebd1` retired `40.mono` / `E-MONO-032`; module-global constant binding gap fixed in `src/compiler/30.types/type_infer/inference_control.spl`).
- Root fix in `30.types`: `HmInferContext.infer_module` (`inference_control.spl`) previously never bound `module.constants` into `self.env` (neither annotated module globals such as `var pool: [i64] = []` nor unannotated globals), causing generic pool-promotion calls over module globals (`phase3_global_pool_typeargs_workaround_probe` shape) to fail HM type inference with `Undefined`. `_bind_module_constants` now binds annotated module constants and synthesizes/unifies unannotated module constants before refreshing `self.module_env_vars` and running `infer_function`.
- `src/compiler/10.frontend/core/types.spl:1826`: updated `@workaround` tag to `status=ROOT-FIXED+STAGE2-GATED recover=28df8ceac42095edcc1d37c53c127271ea938bcb` (retaining concrete `_type_pool_promote_root_{text,i64,arr_i64}` for frozen Stage-2 native runtime qualification and keeping `53afb8c62cb` reference intact for `wa_src_lane3_workarounds_spec.spl`).

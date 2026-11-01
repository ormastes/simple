# Seed accepts enum-variant construction with extra payloads (2026-11-01)

**Status:** OPEN (seed only). **Found by:** generics-coverage-mcdc wave 2.

## Symptom

`test/01_unit/compiler/type_infer/method_call_inference_spec.spl` failed 4/4
on the Rust bootstrap seed with `unsupported expression kind`.

## Root cause

It was a real spec bug, not a seed limitation in inference. The spec built
`HirExprKind.MethodCall(receiver, name, args, MethodResolution.Unresolved, [])`
with **5** payloads, but the variant has **4** fields
(`hir_definitions.spl:635`: `receiver, method, args, resolution`). The seed's
interpreter constructed the 5-payload value without error. The 4-binding
pattern `case MethodCall(receiver, method, args, resolution):` in
`inference_expr.spl` then did not match it, so the value fell through to the
`case _` arm, which reports "unsupported expression kind".

## Fix

The spec now builds the variant with 4 payloads. After the fix it passes 4/4 on the seed.

## Remaining seed gap

The seed's interpreter does not check the payload count when an enum variant
is constructed. A wrong-arity construction should be a compile error. This is
recorded here and not fixed, because the seed is bootstrap-only. The self-hosted
type checker should reject it; re-check that once a self-hosted binary is
available.

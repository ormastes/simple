# `"lit".to_bytes()` — method not found on `text`

- Date: 2026-09-06
- Status: OPEN
- Severity: low (a compact, obvious form fails; a free function exists)

## Symptom

A `text` receiver has no `to_bytes` method. Under the seed interpreter:

```
semantic: method `to_bytes` not found on type `str` (receiver value: ok)
```

## Reproducer

`test/03_system/plan_acceptance/cuda_host_validation_spec.spl`, example
"Use cuModuleLoadDataEx; archive bounded JIT logs." (REQ-CUDA-VALIDATION-03):

```simple
val ptx: [u8] = "ok".to_bytes()
```

The example fails at that line, before reaching its own oracle.

## Expected

Either `text.to_bytes()` resolves to the same conversion the stdlib already
exposes as the free function `text_to_bytes`
(`src/lib/common/string_core.spl`), or the method form is rejected at parse
time with a message naming the free function.

## Notes

Recorded rather than worked around: per CLAUDE.md, a short, safe form that
fails must be fixed or filed, not silently normalised to the long form. The
spec line is left as written — REQ-CUDA-VALIDATION-03 is separately blocked on
a missing `rt_cuda_module_load_data_ex` extern (see the module TODO in
`src/lib/nogc_sync_mut/io/cuda_host_validation.spl`), so repairing only this
line would just move the failure to the `api_used` assertion.

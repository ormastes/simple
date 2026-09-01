# Stage 3 Resume Rejects Its Admitted Stage 2

## Status

Fixed on 2026-08-24; full bootstrap re-verification remains required.

## Exact reproducer

On a Linux host where bootstrap creates `stage3/<triple>/link-compat/libunwind.so`, a freshly admitted Stage 2 failed immediately:

```text
scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted=build/bootstrap-gpu --jobs=1 \
  --bootstrap-receipt=build/bootstrap-gpu/planner-admission-stage3.env
```

The admission recorded `build_args_sha256=8b8bb4...`; the old resume reconstruction produced `f21455...`.

## Root causes

1. Resume hardcoded `LIBRARY_PATH=` and `SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent` instead of consuming the immutable Stage-2 command transcript.
2. The primary Stage-2 admission hash placed `--cache-dir` before `--timeout`, while the executed/transcribed command placed `--timeout` before `--cache-dir`. The admission therefore did not describe the command it admitted.

## Fix and coverage

Resume now reads `RUST_LOG`, `LIBRARY_PATH`, and the link-compat digest from the canonical transcript. The producer hash uses the executed option order. `bootstrap_stage3_resume_source_spec.spl` pins both contracts.


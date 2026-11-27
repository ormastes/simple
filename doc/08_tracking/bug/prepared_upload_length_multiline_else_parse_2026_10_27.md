# Prepared upload chunk-length conditional parse failure

**Date:** 2026-10-27
**Status:** Minimal source syntax repair applied; validation pending
**DB registration:** PENDING

## Failure evidence

The pinned all-objects Phase2 collection recorded this failure:

`D:\dev\simple-all-objects-phase2-20261027\build\object-campaign\objects\c718ec0c9fbc4f25bdfe45181b7c4bc9\7617a5b36d226bd27037bf9eb389123ed3f1f618a9c193ddd1f4ee4d6b16b1b4\compiler.log`

It reports `src/app/build/scheduler/prepared_upload.spl:116:55`:
`unexpected token in expression: : ':'`.

## Repair

The conditional then-value had `else: remaining` appended on the same line.
The expression is now laid out with `else` aligned to the `if`:

```simple
        val length = if remaining > PREPARED_SNAPSHOT_COPY_CHUNK_BYTES_V1:
            PREPARED_SNAPSHOT_COPY_CHUNK_BYTES_V1
        else: remaining
```

Both branch expressions are unchanged. This is a source syntax correction.
Root owns changed-input validation; no compiler was launched in this repair
lane.

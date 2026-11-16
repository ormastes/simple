# Seed: f64 carried through `Result<f64, text>` and `?` is mis-unboxed

Found 2026-11-15 on the Windows Rust seed (`bin/simple.exe`) while writing the
pure-Simple Llama runner (`src/lib/gc_async_mut/slang/model_executor/pure/llama_forward.spl`).

## Symptom

A helper returning `Result<f64, text>` whose `Ok(v)` is unwrapped by `?` in the
caller yields a garbage f64. Storing that value in a struct field
(`LlamaConfig.eps`, `.rope_theta`) then crashed the process with
"Illegal instruction".

## Workaround in tree

`_json_raw` returns the numeric token as `Result<text, text>`; the caller parses
the number after the `?` (`_to_f64` / `_to_i64`). The comment above `_json_raw`
names this record.

## Not done

No minimal repro was reduced and the pure-Simple (self-hosted) lane was not
checked. When fixed, `_json_raw` can return the number directly.

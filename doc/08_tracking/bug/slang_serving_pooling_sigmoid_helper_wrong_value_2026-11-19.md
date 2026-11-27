# A local `_sigmoid` helper in serving_pooling.spl returned a wrong value

Date: 2026-11-19. Status: open (worked around in the same change).
Seed: `C:/dev/seeds/simple-release.exe` (interpreter lane).

## Symptom

`serve_rerank` computed `relevance_score` through

```
fn _sigmoid(x: f64) -> f64:
    1.0 / (1.0 + math_exp(0.0 - x))
```

and returned `2.19e-19` for logit `7.78` and `2.15e-19` for logit `-5.45`
(log `C:/dev/slang-logs/l4/serve_rr.log`). In the same response, the same
expression written inline (`math_exp(0.0 - scores[idx])`) gave the correct
`0.000417` / `233.76`, and the same arithmetic in a standalone probe gave
`0.99958` / `0.00426`.

## Cause

Not isolated. Renaming the helper to `rerank_relevance_from_logit` (and
binding `math_exp(...)` to a local first) gives the correct values, which
points at name resolution of a short private helper name across the
flattened module set, the class `backend.spl` already documents for
`_call1`. A minimal repro has not been reduced yet.

## Workaround

`src/lib/gc_async_mut/slang/entrypoints/openai/serving/serving_pooling.spl`
uses the uniquely named helper; the pooling live spec pins the scores in
(0, 1) with the relevant document first.

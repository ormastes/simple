# Type checker called a nonexistent value-kind accessor

- **Status:** fixed; strict incremental regression passed
- **Observed:** a focused pure-Simple test-runner build generated a weak `val_kind` fallback.
- **Cause:** type checking and evaluation called `val_kind`, while the interpreter value arena exports `val_get_kind`.
- **Fix:** use the existing canonical `val_get_kind` accessor at all nine call sites.
- **Regression:** a source contract rejects every `val_kind(` call in the affected owners, and a strict incremental runner link no longer reports `val_kind`. Other core-C hosted-runtime gaps still prevent that runner from linking and are not claimed fixed.

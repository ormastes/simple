/-
  CacheIdentity — root import for the global content-addressed cache identity model.

  Verifies the safety core of Option C (see
  doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md):
  the canonical encoding of an ActionKey is injective through its canonical form,
  every semantic input is present (no omitted-input false hit), a cache hit returns
  exactly what re-realization would produce, and the C fast-path SHA equals the A
  strict-path SHA whenever the file stamp is valid.
-/
import CacheIdentity.Model
import CacheIdentity.Theorems

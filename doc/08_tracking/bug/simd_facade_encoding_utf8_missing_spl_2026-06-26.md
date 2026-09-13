# Bug: simd_dispatch_facade_spec — encoding/utf8.spl source missing

## Closed 2026-09-13 — both fix items done: utf8.spl restored and cipher.spl imports modernised
- **measured**: `src/lib/common/encoding/utf8.spl` exists; `find src/lib -name '*.smf'` returns nothing, so the `.smf`-only state is gone.
- **measured** (`bin/simple run`): `use std.common.encoding.utf8.{text_codepoint_len, utf8_count_codepoints}` resolves and executes.
- **measured**: `grep '^import ' src/lib/common/aes/cipher.spl` returns no matches — fix item 2 (deprecated `import` keyword) is done.
- **inferred**: `simd_dispatch_facade_spec.spl` was not re-run; `bin/simple test` is broken on this Windows host.

**Date:** 2026-06-26
**Spec:** test/01_unit/lib/common/simd_dispatch_facade_spec.spl
**Status:** CLOSED 2026-09-13 (see Closed section above)

## Symptom

Spec reports Passed: 0, Failed: 1.

## Root Cause

The spec imports `std.common.encoding.utf8.{text_codepoint_len, utf8_count_codepoints}`. Only a compiled `src/lib/common/encoding/utf8.smf` exists; the `.spl` source was deleted. Additionally, `src/lib/common/aes/cipher.spl` (restored 2026-06-26) uses deprecated `import` keyword syntax instead of `use` for its internal imports (`import aes/utilities`, `import aes/types`, etc.) which produces warnings.

## Fix Required

1. Restore `src/lib/common/encoding/utf8.spl` from git history (commit 25a60a1eba5c92baabbfcedc1bfa985dd33ce1ed). **Scope: encoding agent.**
2. Update `src/lib/common/aes/cipher.spl` internal imports to use `use std.common.aes.utilities` etc. instead of `import aes/utilities`.

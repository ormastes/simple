# Bug: simd_dispatch_facade_spec — encoding/utf8.spl source missing

**Date:** 2026-06-26
**Spec:** test/01_unit/lib/common/simd_dispatch_facade_spec.spl
**Status:** Open (blocked on encoding agent scope)

## Symptom

Spec reports Passed: 0, Failed: 1.

## Root Cause

The spec imports `std.common.encoding.utf8.{text_codepoint_len, utf8_count_codepoints}`. Only a compiled `src/lib/common/encoding/utf8.smf` exists; the `.spl` source was deleted. Additionally, `src/lib/common/aes/cipher.spl` (restored 2026-06-26) uses deprecated `import` keyword syntax instead of `use` for its internal imports (`import aes/utilities`, `import aes/types`, etc.) which produces warnings.

## Fix Required

1. Restore `src/lib/common/encoding/utf8.spl` from git history (commit 25a60a1eba5c92baabbfcedc1bfa985dd33ce1ed). **Scope: encoding agent.**
2. Update `src/lib/common/aes/cipher.spl` internal imports to use `use std.common.aes.utilities` etc. instead of `import aes/utilities`.

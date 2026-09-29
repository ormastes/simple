# Fixed-width unsigned suffixes incorrectly use the signed decimal limit

## Exact incident

The admitted pure-Simple Linux producer SHA-256 `33b2dd65fde9f81f7d8520c6d3cea3706b1b2b11ee6e2cb35edfefb1eb7b87e4`, built from frozen source `668d2062b93f7a9755cea9c9c0c427c6feb329db`, rejected the dynlib lifetime maximum identity literal at line 12:64 with `integer literal out of range for i64: '18446744073709551615'`. The 1479-file next-generation closure stopped during parsing, before objects or a new executable. Evidence: `/mnt/simple-bootstrap-6b2/linux-668-early-nextgeneration-diagnostic-20260929/console.log` and its supervisor/source receipts. Frozen source and candidate outputs are unchanged.

## Current-main source and fix scope

This isolated fix starts at remote main `b05431d6537a0359e58473bc6cd791489e615133`, worktree `D:/dev/simple-parser-u64-literals-20260929`, branch `work/parser-u64-literals-20260929`.

At that exact revision, `src/lib/nogc_sync_mut/sffi/dynlib_lifetime_owner_v1.spl` already contains `const _DYNLIB_LIFETIME_MAX_ID_V1: u64 = 18446744073709551615u64`; its Git blob is `c3aed8560535b1c0bdfc560c251c396c5298ede2`. The last path commit visible in that revision is `bb3f6ab8ab29233fcc28f1fd4c239fe86aab8bf9`. This lane does not edit that library or replace its value with a cast/hex/negative workaround.

The primary parser previously used the same signed decimal decoder for ordinary and suffixed integer tokens. It therefore rejected the valid decimal `u64` maximum before retaining the suffix. Its radix-specific decoders could also silently truncate overflowing unsigned suffix magnitudes.

The new private decoder admits the exact declared ranges of `u8`, `u16`, `u32`, and `u64` in existing decimal/hex/binary/octal forms. Two base-2**32 limbs keep arithmetic intermediates below 2**36, and a final shift/or creates the existing i64 payload word. The existing suffix node and bridge Cast retain the unsigned type. No existing function signature, lexer/AST/HIR tag, field layout, serialization format, or runtime ABI changes.

Signed/default parsing and its existing minimum-magnitude convention remain unchanged. `usize`, signed suffixes, and custom unit suffixes keep their existing path. Leading zeroes do not cause false magnitude overflow. Malformed token errors take precedence over overflow.

## Separate existing limitation: bare annotated u64

The frozen 668 source already contains the explicit `18446744073709551615u64` literal: its library blob is identical to `c3aed8560535b1c0bdfc560c251c396c5298ede2` above. The parser diagnostic strips the suffix from its token text; it does not prove the source was bare. No constant transplant or library edit is required for a new 668-based candidate. This narrow suffix fix does not add contextual unsigned inference for unsuffixed literals: `const max: u64 = 18446744073709551615` remains unsupported by the pure parser's default i64 magnitude guard according to source analysis. That separate frontend representation/context limitation has not been executed in this lane and must not be reported as the observed 668 failure or as fixed by this patch.

## Regression and producer route

`test/01_unit/compiler/frontend/unsigned_integer_literal_suffix_spec.spl` checks declared unsigned width boundaries, u64 maximum/overflow, hex/binary/octal boundaries, malformed precedence, signed maximum/minimum magnitude preservation, and the real primary-parser bridge's u64 Cast/payload. `test/fixtures/native/unsigned_integer_suffix_boundary/main.spl` checks unsigned shift, division, comparison, preserved full-width bits, and signed boundary behavior through native lowering. Tests are authored but unexecuted.

The existing producer cannot acquire this parser behavior from a source copy. Rebuild the Stage2 producer through the canonical same-seed bootstrap route in isolated caches, then run the focused native fixture once and the failed next-generation parse once. The retained 668 cache has 1059 hashed objects but its incremental manifest contains only a header, without module-to-object or original link input mappings, so a selective relink is unproved. Keep producer/source/tool closure identity explicit; do not mix objects from another producer or silently change frozen 668.

Root/high-capability review is required before an expensive build. No test, producer build, successful bootstrap qualification, or memory fixture rerun is claimed. This feature has used zero verification/fix cycles so far; its cap is three.

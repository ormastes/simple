# text_to_bytes_pure indexed characters over a byte-length loop

- **Status:** fixed 2026-10-10 (same change)
- **File:** `src/lib/nogc_sync_mut/fs_driver/bytes_util.spl`

`text_to_bytes_pure` looped `i < s.len()` (BYTE length) and pushed `s[i] as u8`
(`s[i]` is CHARACTER-indexed; `as u8` on text is the code point). For any
non-ASCII text that is wrong on every lane, the seed interpreter included:
the loop runs past the last character (out-of-bounds index), and the values
pushed are code points truncated to 8 bits, not UTF-8 bytes
(`"é"` is bytes 195,169 but code point 233).

On the LLVM lane it was also the first module to abort stage2 codegen
(`unsupported LLVM value conversion from ptr to i8`).

Fix: `s.byte_at(i) as u8`. Seed-measured: `"aé😀".len()` is 7 and
`byte_at` yields 97,195,169,240,159,152,128.

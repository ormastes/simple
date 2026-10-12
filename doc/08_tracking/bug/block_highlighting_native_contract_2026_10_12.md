# Block highlighting bootstrap and raw-string comparison repair

Status: OPEN draft. Seven distinct focused native cases PASS on frozen f05 candidate across three bounded cycles. The final combined latest-release owner is UNEXECUTED. Full Stage2 compiler admission, SSpec runner, and Windows/macOS/FreeBSD/SimpleOS execution remain UNQUALIFIED. No fourth build is authorized by these results.

## Failure and source contract

Linux CI38172965677, exact b2b1fc2922630e756263ad421e4361ae072018cd, failed the highlighting owner with an LLVM undeclared `has_index` load and unresolved `text_len`. Other undeclared option guards and a providerless `text_index_of` call were in the same owner. Cycle1 of the focused real source closure exposed the additional unsupported native `str.is_hex_digit` method.

The candidate uses bounded keyword comparisons with cached lengths, skips empty keywords, restores declared optional binding and text.len(), and imports the canonical std.common.binary_inspect.is_hex_digit function. Comparisons preserve original offsets and overlap. Index+matched stays within text length. Worst-case keyword comparison work is O(text length * sum(keyword lengths)); there is no per-position remaining-text substring allocation. This is source reasoning, not a measured before/after performance claim. No allocation ownership or global frees are changed.

Cycle2 native execution passed cases1–3 and failed case4. Failed-only GDB observation found one actual Comment token(start2,end8) instead of end6 and the compared constant bytes5c6e. Single-quoted strings are documented RAW strings (syntax_quick_reference.md, Single quotes = raw string; Rust lexer strings.rs scan_raw_string preserves every backslash sequence except escaped single quote). Consequently '\n' and '\\' were incorrect source comparisons, not compiler literal defects. Cycle3 uses double-quoted escaped newline/backslash and tests the escaped quote path.

## Actual focused evidence

Recovered immutable bootstrap-only seed SHA445c9a1159b5187fd201a830ca9d52f072db0a7e34945f651c8f508399cad91d. Real frozen b2 source imports, actual highlighting owner candidate SHA f05c4562b801f6dc0b83736203c7702fc0a316b195baf3444144d5890c84eba5. Explicit SIMPLE_NATIVE_BUILD_RUST=1, LLVM, threads1, low-memory, private preserved cache,180s wall/4GiB process-tree bound. No production Rust-seed fallback or full compiler build.

- Cycle1:7 modules compiled, owner failed unsupported str.is_hex_digit;3.894s/250916864B peak treeRSS. Zero native cases.
- Cycle2:9-module archive93038B, compile0/4.352s/250855424B peak; strict link0; native exit4. Cases1–3 passed (keywords/empty searches/string spans); case4 line-comment span failed; cases5–6 were unexecuted.
- Cycle3:9-module archive93876B, compile0/5.242s/250859520B peak; strict link0/29.976s; native exit0/0.0441s/9172KiB peak, stderr empty and exact HIGHLIGHTING_REMAINING_NATIVE_CONTRACT_PASS newline. Cases4–7 passed (line comments, Some block delimiters, decimal/hex/signed-exponent spans, escaped quotes). Already-green cases1–3 were not rerun.

Strict link used the exact recovered paired libsimple_native_all.a SHA cc2840f9b92371e23bf048c49dabb247b5242de557535ffd4fb8c6263a49c3d1 and libsimple_compiler_backfill.a SHA eb46bacc9f8b95b90d70d9b3a616983133f542e0916f2720ae53ea65afc07484. The host startup C source was extracted from exact b2 compile_main_stub and preserves runtime init, argument setup, module initialization, and shutdown. Real spl_main is forced into strict link; no fake providers or duplicate-symbol suppression. Final ELF SHA5d27e48fe02e6ad1e5c7025bfc68c590c1ff2abfe9179d311b61ef5e213602f5.

Seven corresponding SSpec cases are authored but their runner is UNEXECUTED. The committed native fixture retains cases1–3 definitions but invokes only4–7, faithfully preserving the final tested bytes. The complete distinct-case evidence spans cycle2 andcycle3; it is not a fresh aggregate seven-case run. Timings/RSS characterize these diagnostics only, not optimization improvement or leak proof.

## Limits and concurrent upstream repair

Receipts, command/source/runtime hashes, archive, ELF, raw failed-case GDB evidence, and all caches are preserved under /mnt/c/Temp/simple-block-highlighting-repair-20261012. CI1248 successful object files were NOT collected (hyphenated stage2-native-cache collector defect); no full Stage2 cached relink is possible from that artifact. Focused symbol prefixes also differ from CI, so this archive is not a provider transplant.

Precommit latest-release check found concurrent df6494f18a in bed1ef92dd336f08c04005ee4536f08b6313f216. It adds a different keyword helper and optional tuple extraction. It retains raw newline/backslash comparisons and the missing native hex method. The exact qualified candidate is preserved separately; no automatic overwrite or unexecuted combined-source qualification is asserted. Merge review must choose a source integration explicitly.

Existing lexical policies outside this repair (underscore boundary and trailing escaped-character span) remain unchanged. General compiler/core/MCP/LSP gates and a complete new Stage2 Hello are not claimed by this focused bootstrap diagnostic.

## Final integration decision

The PR preserves df6494f18a keyword/helper/optional implementation exactly. Its production diff is only the canonical hex predicate import/call and escaped-text newline/backslash comparisons. Final source base bed1ef92dd336f08c04005ee4536f08b6313f216; combined owner SHA c7b0ceed957a5034826ff76cd0b51dda05f2801aa0d02b8c8ca43a9ec53a0fc2. The frozen native-qualified f05 owner remains in cycle3-owner.spl and the immutable diagnostic projection. No fourth narrow compile, green-case repeat, or combined-owner PASS claim. The next causally required full producer build must qualify this integrated source before this draft can become ready.

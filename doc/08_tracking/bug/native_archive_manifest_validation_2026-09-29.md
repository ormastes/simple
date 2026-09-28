# Native archive manifest validation blocks CAS publication

The Target 6 persisted archive fixture initially started a CAS transaction but aborted before the first `cas_put`. GDB showed `package_archive_manifest_v1` received an optional aggregate wrapper where it expected an entry and returned empty text. After explicitly unwrapping the aggregate, its digest validator still returned false for a valid 64-character lowercase SHA-256 digest; it compares one-character text values with native text relational operators. Other cache digest validators already use numeric `byte_at` checks because native text ordering can compare tagged addresses.

Correction to the earlier report: the raw `rt_file_create_excl` call returned `1`, and its Simple wrapper returned tagged `0xb`, which means **true**. File creation was not the failing step. The attempted wrapper changes were reverted without a commit.

The archive option bindings and byte checks moved execution to `cas_batch_stage_object_v1`, where GDB showed the compiler passed a null mutable reference. The function only reads the transaction, so its parameter now takes a value. CAS then rejected a mapping because a raw nullable file-read result was unwrapped as if it were a boxed Option; `cas_batch_read_v1` now normalizes that boundary to `Some(text)`.

The latest native spec reports **2 passes, 2 failures**. The graph and negative input examples pass. GDB showed `file_lock` returns `-1` because the linked ELF contains a weak `flock` body that returns tagged nil (`3`). `strace` showed the lock file opens but no `flock` syscall occurs. `SIMPLE_NO_STUB_FALLBACK=1` links libc's `flock` and allows CAS to write `CURRENT`. The Rust native-project system-symbol table now classifies `flock` as libc-owned; the bootstrap runtime needs rebuilding for that default-link fix to take effect.

After strict linking, the first archive lookup received tagged integer `0x4` instead of the package key. Explicitly unwrapping the aggregate entry before the call moved the lookup to the receipt read. GDB then showed that `receipt_digest!` passed an empty digest to `cas_get`: it tried to read `.../cas/sha256//`, a directory. The earlier quarantine contained that moved directory, not a corrupt receipt blob. Explicitly unwrapping the digest and receipt at the load boundary moved execution to receipt decoding. `cas_get` also returned bare text from a `text?` function; the decoder received tagged nil after the caller unwrapped it. It now returns `Some(content)` after digest validation.

The persisted receipt had `dependencies=Option::Some()` because canonical serialization interpolated an optional value. Explicit unwrapping corrected that field. The most recent native spec still reports **2 passes, 2 failures** with `archive-receipt-invalid`. GDB reconstructed the decoded receipt and found its member offsets/extents were pointer-like numbers (`3381553`, `3923265`, etc.) rather than the file's `0`, `92`, and other byte counts. The `to_u64() ?? 0` conversions were passing optional wrappers. They now use checked explicit unwraps, but that final edit has not been rebuilt or tested because this turn reached the three-cycle limit. The runner's zero exit status does not override its textual failure verdict.

## Follow-up native build boundary

The next full four-example spec build stopped before source parsing because this
worktree had no admitted SCV freeze inventory. With the tool's explicit
`SIMPLE_SCV_FREEZE_FALLBACK=1` diagnostic setting, it parsed 216 files, but
surface construction reached only 16/216 after about 16 minutes at roughly
4.7 GiB worker RSS. That diagnostic run was terminated; it is not a spec
verdict. A new direct native receipt regression probe under
`test/02_integration/compiler/cache/package_archive_receipt_native_probe_main.spl`
uses a 42-file closure and checks empty dependency encoding, numeric member
offsets/extents, digest roundtrip, and rejection of a malformed offset. Its
four-minute build bound expired at surface construction 14/42, before an
executable existed. The final decoder fix therefore still lacks native PASS
evidence. Use a longer bounded build or a smaller isolated decoder closure
next; then rerun the original publication spec before claiming the cold HIR
path works.

## Compiler-path check after the bounded build

The staged pure-Simple compiler at
`build/bootstrap-target56/stage4-sqlite-compiler/simple` (SHA-256
`f94f9f98dba65abb79491a84a30cc09aea86f4e1dc1c9bcb4ab35072fec19a3f`)
reached the 42-file receipt probe quickly but reported the existing flat-AST
empty-declaration-tag failure in several imported modules. An eight-file
decoder-only closure was tried by temporarily moving the decoder next to its
encoder; the installed `bin/release` compiler (SHA-256
`44a07ae51c5dd308553cb06203e3e92d0a468b68ffaa28773af0fde0c7ac2c2d`)
parsed and surfaced all eight files, then stopped in HIR with
`semantic: array index out of bounds: index is 3 but length is 3` after
reporting unresolved transitive `Option`/primitive type imports. That
unqualified refactor was reverted. Neither attempt produced a probe binary or
changed the 2/4 native publication verdict. The next diagnostic should
address compiler qualification or reduce the probe without moving production
code merely to shorten its closure.

## Stage2 native probe result

The immutable Stage2 pure-Simple compiler capsule
`build/bootstrap-target56/phase2-runtime-capsules/d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c/simple`
(SHA-256 `d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`)
compiled the unmodified 43-unit receipt probe with `--entry-closure`,
`--runtime-bundle host-gpu`, and no stub fallback in 2.24 seconds at
225,388 KiB peak build RSS. The resulting executable exited 1 with
`receipt-invalid-number-accepted`: native decoding accepted `bad` as an
archive member offset.

Two bounded repair builds used the same capsule. A digit check around
`text.to_u64()` made the valid receipt return nil; a manual decimal parser
then let decoding proceed but failed the combined digest/member roundtrip
assertion. Both candidate edits were reverted because neither passed the
probe. This points to native numeric/optional transport as a concrete next
diagnostic, but it does not prove which operation is at fault. A next repair
should isolate conversion and `Some(u64)`/unwrap in a tiny native executable,
then make malformed, overflow, and valid offsets pass before rerunning the
four-example archive publication spec. The latter still has only its earlier
2/4 failure verdict; no Target 6 completion or performance claim follows.

## Checked native decimal repair

A one-unit no-stub native probe confirmed that `text.to_u64()` and
`Some(u64).unwrap()` do not carry the numeric value correctly on this Stage2
binary; a plain `{valid: bool, value: u64}` struct and `(bool, u64)` tuple
both carried `92` correctly. The separate runtime defect is tracked in
`doc/08_tracking/bug/native_optional_u64_unwrap_2026-09-29.md`.

The archive decoder now parses canonical decimal bytes with an explicit
overflow guard and returns a plain checked struct, avoiding optional `u64`
transport. The 43-unit no-stub Stage2 build took 2.18 seconds at 226,860 KiB
peak build RSS. Its native receipt probe exited 0 with
`receipt-native-roundtrip-pass` at 3,376 KiB max runtime RSS, covering valid
offsets/extents, digest roundtrip, malformed offset/extent, overflow, and
noncanonical leading zero. This is a focused decoder PASS. The cold HIR
four-example publication spec and realistic time/RSS cohort remain pending.

## Full native publication retry

The immutable Stage2 pure-Simple capsule built the original four-example cold
HIR spec with no stub fallback: 323 units compiled in 21.27 seconds at
1,255,796 KiB peak build RSS. It reports **2 passes, 2 failures**; the first
publication case now reaches `cold-publish-archive-member-digest-mismatch`.
The runner exits 0 despite that textual failure. The persisted 542-byte
archive and 808-byte receipt each match their CAS SHA-256. Independently
slicing the archive by the receipt's three byte ranges yields the recorded
member SHA-256 for all three members, so stored bytes and offsets are sound.

A two-unit native probe found that `"abcDEF".bytes().slice(0, 3)` has length 3
but `validated_utf8_bytes_to_text_linear` converts it to empty text; copying
those same three bytes into a fresh array with `push` converts to `abc`. This
is tracked in `doc/08_tracking/bug/native_byte_slice_text_conversion_2026-09-29.md`.
A trial preallocated member copy built with 3 changed and 320 cached units
but the full spec stayed at 2/4 with the same digest mismatch; the trial was
reverted. The specific native operation losing bytes is still unproven. Do
not count this as a cold publication PASS or a memory/performance improvement.

The subsequent bounded native byte probe kept the same 92-byte and 88-byte
member lengths with both `push` and indexed preallocation, yet each decoded
member failed its expected hash and the action prefix contained control
bytes. The earlier three-byte copy passed. This rules out simply changing
the copy method as a qualified publication fix; the byte source and
conversion boundary need byte-by-byte diagnosis. The production code was
left unchanged after the failed trial.

## Cold publication PASS after byte-source repair

A byte-by-byte native probe found that the concatenated archive text matched
the source member through its first range, but `archive_content.bytes()` first
disagreed with `archive_content.byte_at()` at byte 10. The copied array and
decoded text preserved that wrong array byte. Direct `byte_at()` reads into a
preallocated member buffer produced the expected hashes for both 92-byte and
88-byte fixture members.

The cold publisher now uses the text's O(1) byte length and reads each
validated member range with `byte_at()`; it no longer allocates a full archive
byte array. The original no-stub Stage2 native spec then reported **4 examples,
0 failures**, including successful persisted-archive publication and rejection
of a mismatched payload before moving `CURRENT`. The changed build compiled
3 units and reused 320 in 6.83 seconds at 446,600 KiB peak build RSS; the
single spec run took 0.05 seconds at 5,536 KiB max runtime RSS. These are not
paired performance cohorts. The underlying native `text.bytes()` defect
remains open and Target 6 driver cutover is still incomplete.

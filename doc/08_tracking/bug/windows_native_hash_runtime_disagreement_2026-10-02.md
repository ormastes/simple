# Windows native hash target and text-method disagreement

Status: typed native text `.hash()` ABI mismatch FIXED in the 2026-10-11
candidate and verified with both backends. Mixed-import alias resolution and
literal-receiver interpolation remain OPEN; full bootstrap remains separate.

## 2026-10-11 owner claim and reproduced boundary

Windows bootstrap repair lane owns the typed text method lowering correction.
The newly built Rust seed from `release_phase3` reproduced the failure with a
single no-import module, Cranelift, one worker, and `core-c-bootstrap` runtime.
Direct `rt_hash_text` returned the expected empty/hello FNV values, while both
named receivers' `.hash()` calls returned `538079189680823091`. Build succeeded
in 11.6 seconds; execution failed. Evidence is retained under
`build/windows-phase4-logs/hash-seed-probe/` in the phase4 worktree.

Typed Rust MIR lowering selects `rt_str_hash`, whose C provider accepts a raw
C-string pointer. Its text receiver is a tagged runtime value. The correct
tagged ABI is `rt_hash_text`, also selected by the dynamic method backend.
The Rust runtime alias had masked this representation mismatch. Preserve raw
`rt_str_hash` callers and change only the typed text method lowering owner.
Pure-Simple MIR/backend sources contain no direct `rt_str_hash` dispatch.
This is seed bootstrap diagnosis, not Stage2/Phase4 qualification.

The corrected seed SHA-256 is
`b6ba9c9513f3e90e73bc4fdafbbe30329d785a8689aceec0ffa8d2455593d69b`.
The native fixture `test/fixtures/compiler/native_text_hash_method_abi_main.spl`
passed 14 outcomes through each of Cranelift and LLVM: direct runtime, named
method, and typed forwarding for empty/ASCII/embedded-NUL/UTF-8 text, plus a
literal receiver and an unrelated user-defined `HashBox.hash()` returning 73.
Both executables returned zero and printed `Results: 14 passed, 0 failed`.
Each backend compiled one module with one worker, in 8.5/8.3 seconds including
the C bootstrap runtime link. Evidence and exact commands are retained under
`C:/dev/simple-hash-verification/` (`probe-inputs.txt`, `verify-native.sh`,
`native-cranelift/`, and `native-llvm/`).

Both focused Rust MIR regressions also passed independently: one executed test,
zero failures each, with 4,416 unrelated cases filtered out. They verify the
typed text/ord shared-runtime targets, literal text dispatch, preservation of
the user-defined `HashBox.hash` static call, and absence of `rt_str_hash` calls.
Commands and complete logs are retained in the same evidence directory as
`verify-mir.sh`, `string_ord_and_hash_lower_to_shared_runtime_calls.log`, and
`string_literal_hash_uses_tagged_runtime_but_user_hash_keeps_static_dispatch.log`.

Verification was moved to C/NTFS after the private D/ReFS seed build stalled
in `File.sync_data -> FlushFileBuffers -> NtFlushBuffersFile`. The independent
host flush failure is not a hash/compiler defect. Synchronization was retained.
The old D worker remained pending kernel termination after cancellation; only
pre-worker stable cache files were copied with before/after SHA/size/mtime
validation. No later-phase admission is inferred from this diagnostic seed.

The focused Cranelift native executable built with the frozen bootstrap seed
and LLVM 23.1.1 MSVC tools returned these values for `hello`:

- `std.hash.rt_hash_text`: -6615550055289275125.
- `std.nogc_sync_mut.src.hash.rt_hash_text`: -6615550055289275125.
- Output labelled `runtime_hello`: 538079189680823091.

The two pure-Simple values match known FNV-1a. The initial comparison failed
with an assertion violation, but the label did not prove which symbol was
called. Subsequent object/disassembly evidence corrects the initial foreign
algorithm inference: the mixed-import object references `rt_str_hash`, not
`rt_hash_text`, and the observed call reaches the C-string hash path.

An independent LLVM native probe with no imports references the actual
`rt_hash_text` symbol and returns the known FNV-1a values for both empty text
(-3750763034362895579) and hello (-6615550055289275125). Its named text value's
`.hash()` call returns 538079189680823091, exactly the misleading original
`runtime_hello` output. Actual foreign ABI known-value checks PASS in this
diagnostic. Mixed-import alias/text-method resolution remains OPEN and FAIL;
this is not evidence that the foreign FNV-1a algorithm is wrong.

The explicit manual bytes-loop in the isolation fixture returned
4292782984883829272 and is unqualified; it is not a replacement oracle.
Do not infer production qualification from these bootstrap repair probes.

Local evidence is `C:/dev/simple-windows-hash-link-fix/build/native_probe/`:
`hash-alias.LiaUB8/results.log` preserves the initial assertion failure;
`hash-alias.lFLsT4/results.log` preserves all three observed values.
The final narrowed link probe checks six pure-Simple alias assertions only:
empty and hello known values through each public alias, alias agreement for
hellp, and discrimination between hello and hellp. It does not gate parity.

The LLVM native probe independently reproduced the same three observed values
and passed the same six narrowed pure-alias assertions. Its evidence is
`hash-alias.nCe1LD/{build.log,results.log,probe.exe}` under the local directory
above (five compiled modules, zero failures, LLVM backend, 80 workers).
The immutable LLVM-capable bootstrap producer was diagnostic-only and unadmitted,
SHA-256 `5494f30e0a9b3e2911d8b95d3a5640861d49c36aff1566674538f51f6c86dc37`.
This is real native alias evidence for both backends, not final qualification.

Isolation evidence: `C:/Users/user/.simple/worktrees/simple/runtime/`
`hash-abi-isolation/{main.spl,build.log,results.log,probe.exe}` and
`hash-abi-isolation/native-objects-tt1r1O/mod_0.o` (undefined `rt_hash_text`).
The producer receipt is `C:/Users/user/.simple/worktrees/simple-windows-phase2/`
`evidence/llvm-bootstrap-alias-producer-1ff/producer.env`: source 1ffaf797,
configuration 14b45b4246b4, admitted=false, diagnostic use only.
The original mixed-import object is
`C:/dev/simple-windows-hash-link-fix/build/native_probe/hash-alias.nCe1LD/cache/`
`scope-a3c3af57b694d7de/objects/e96ccfde3e2b2954.o` (undefined `rt_str_hash`).
The isolation directory's `investigation.md` preserves the target analysis;
its corrected fixture overwrote the original main/build log, while the original
failed object remains. Do not treat that failed object as execution evidence.

Separate OPEN compiler observation: the first isolation fixture's literal
interpolation `{"hello".hash()}` failed with `undefined global hello`.
Using a named text value allowed the diagnostic fixture to execute; this is a
fixture correction, not a language fix. The original failure is recorded in
the same `investigation.md`. Literal-receiver interpolation remains unqualified.

Run `scripts/check/check-native-hash-public-alias.shs PRODUCER RUNTIME` for the
narrow link probe. Full qualified runtime and method-resolution checks remain
required separately.

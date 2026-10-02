# Windows native hash target and text-method disagreement

Status: OPEN. Independent of the repaired pure-Simple public hash alias link.

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

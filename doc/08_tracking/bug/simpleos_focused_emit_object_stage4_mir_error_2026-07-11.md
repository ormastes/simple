# SimpleOS focused emit-object stage4 MIR diagnostic corruption

## Evidence

- Target Simple SHA before the diagnostic-only rebuild:
  `4f2b48b31c80e09ee3a6ca2cd2d0919faec0d8feff857e1bee11c1bfc40e784e`.
- Production QEMU opens and reads `/HELLO.SPL`, then exits 1 without writing
  `/HELLO.O`.
- Target RIP `0x204db2` is inside `simpleos_compile_native_file`, before
  LLVM/LLC object emission, while reading `mir_lowering.errors[0].message`.
- GDB proves `MirLowering.error`/the captured error-array `rt_array_push` never
  runs. `MirLowering.new` created `loop_stack` and `errors` as kind-6 Dicts;
  array length then misread Dict capacity `8` as an error count. Typed empty
  array locals are the source fix for both fields.
- The syscall return path separately misclassifies user RIPs near `0x200000`
  as kernel addresses because the kernel spans that numeric range; this leaves
  later user instructions at CS=8 and must be fixed independently.

## Next bounded proof

Complete a resource-stable target rebuild, then run one fresh emit-object gate.
Acceptance requires guest exit 0 plus a reconstructed ELF64 REL x86-64 object
containing `__simple_main`; no host-produced user object is accepted. The same
QEMU must also prove syscall return stays at CPL3 after the RIP-range privilege
heuristic was removed.

The first post-fix emit-object boot retained CPL3 but proved the next boundary:
external LLC requires fork/wait (`ENOSYS` 57/61), then faults without output.
The accepted path is now staged: Simple emits `/HELLO.LL` in-process; a fresh
filesystem boot runs `/USR/BIN/LLC` to emit `/HELLO.O`; another runs LLD. This
reuses the one-output RAM overlay and avoids adding a scheduler/fork subsystem.

## Focused HIR return-type follow-up (2026-07-12)

The staged emit-LLVM boot reaches CPL3 without host-process syscalls, but direct
push-time evidence reports `unresolved type: Option` twice. A flat-bridge marker
proves `main` still enters conversion with the correct `TYPE_I64` tag `2`; the
two errors are that one return type lowered in declaration and definition
passes after an untyped `HirLowering` local is ANY-erased. The focused facade now
uses the same explicit `HirLowering` local type required by the normal driver.

The apparent stale-cache diagnosis was disproved: the typed-local edit created a
new focused-pipeline cache key/object after the source mtime, but its bytes were
identical because that annotation is codegen-neutral in the proven stage2
producer. No cache entry needs deletion.

Three fresh, changed target ELFs then tested the actual TypeKind boundary. Early
Named extraction, raw multi-field payload slots, and frontend-owner typed
accessors all still decoded a correct flat return tag `TYPE_I64=2` as
`Named("Option", [Named("f64")])`. Final target SHA is
`ddab9e4ae824aec22a0c055010164966dd4274283883c45b6cb959bda04d25cb`;
final image SHA is
`dc7f6d4cd2e9381ceb17a400e864d6a8916b7333e9592be7a807159fabf25cae`.
This proves the corruption predates/underlies consumer-side TypeKind pattern
binding. The next bounded cycle must preserve primitive flat tags through a
non-enum owner boundary (or repair the stage4 enum-construction/payload ABI),
then require HIR Int64 and exact `i64 @__simple_main` evidence.
## Cycle 8 update (2026-07-12)

The raw-tag comparison repair is live-proven through HIR: `main` remains `i64` before and after flat function storage and in HIR, and lowering reports `phase=hir-ok`. The subsequent nil-receiver trap was symbolized to MIR expression fallback allocation; target disassembly shows `rt_alloc` returning zero after the 64 MiB user arena was exhausted.

A minimal loader-only experiment raised the existing eager arena to 65,536 pages. Its source contract passed 4/4, but the final 512 MiB QEMU run failed closed while allocating page 36,047, before CPL3 entry. Thus 256 MiB is not physically viable with the current kernel image. The three-cycle session cap is reached; next fresh verification should try 32,768 pages (128 MiB) once. Evidence is in `build/os/elfexec/emit_llvm_profile_run12.out`.

The failed experiment was reverted to the live-proven 16,384-page production baseline so the worktree does not retain a known-broken loader configuration.
## Cycle 9 update (2026-07-12)

The reviewed 32,768-page arena mapped successfully and reached the same CPL3 post-HIR nil-receiver trap. A second run with fail-only `_user_heap_bump` telemetry emitted no OOM marker. Therefore the immediate failure is not exhaustion of the bare-exec bump arena; the next diagnostic must distinguish a nonpositive `rt_alloc` request from a failure inside `simpleos_dlmalloc`.

Evidence: `build/os/elfexec/emit_llvm_profile_run13.out` and `build/os/elfexec/emit_llvm_profile_run14.out`.

# Windows snapshot sink: duplicate text expansion and linked failure stub

Status: caller repair implemented; native verification pending. The linked
Windows provider is a separate unresolved prerequisite. No native fix PASS.

## Reproduction and immutable evidence

The guarded Windows hello2 run reached HIR and failed with
`SIMPLE_MEM_SNAPSHOT_FILE could not be established safely`. The target leaf
was absent and its D: parents were real directories. The external Windows
Job observed approximately 3.34 GiB, below its unchanged 7 GB limit.

- Selective source commit: `6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`.
- Candidate: `D:/dev/bootstrap-memory-fix-validation-20261002/phase2-parallel4/output/stage2-fixed.exe`.
- Candidate SHA256: `e7ec89c1f106353cc8fdc792d5d41359336c72287f410aa039b57d8f6101dfdf`.
- Retained object: `D:/dev/bootstrap-memory-fix-validation-20261002/phase2/cache/scope-5b04df2992efbad8/objects/7a7c708365cf11c7.o`.
- Object SHA256: `72b4b076e5fc326ba29d2515109739cbcbb65442c18e63c5779a21d9b4d32deb`.
- Caller disassembly: `D:/dev/mem-snapshot-abi-probe-20261002/mem_snapshot_begin.disasm.txt`.
- Disassembly SHA256: `ebb422cf82456f68991a683f50de87c4413d21abdb1969b16e57bc1965e13aa0`.

## Two independent faults

Both `driver_mem_snapshot.spl` and `driver_log_helpers.spl` declared and
supplied raw pointer/length pairs. Both compiler routes already expand
semantic text: the seed's `text_arg_indices`/`expand_text_args` in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` and the self-hosted
`src/compiler/50.mir/text_extern_abi.spl`/`expand_text_abi_args` register open
argument 0 and record arguments 2, 3, 5. Raw caller pairs therefore expand
again. Open should have one logical/two physical arguments; record should
have 17 logical/20 physical arguments.

The actual retained object proves duplicate expansion: relocations at
0x319/0x324 call `rt_string_data`/`rt_string_len` on the path, then
0x32f/0x33a call them on the extracted pointer. The open call at 0x347 passes
the second pointer/length plus the original length as a third word.

Separately, the exact candidate selects an unconditional failure provider.
The read-only locator `D:/dev/mem-snapshot-abi-probe-20261002/locate_provider.py`
matches the object's function prefix uniquely in the PE and resolves the
call's signed rel32 displacement. `mem_snapshot_begin` is at VA
0x1409844d0; its open call at 0x1409845c7 targets VA 0x140c99390. The target
bytes `48 c7 c0 ff ff ff ff c3` decode to `mov rax,-1; ret`. This matches the
Rust non-Unix stub. A standalone core-C probe successfully opened the path,
but that does not establish that the candidate linked the core-C provider.

## Repair and acceptance

Both Simple owners now declare/pass semantic text and let the compiler
perform exactly one expansion. Runtime formatting, secure exclusive open,
error handling, cardinalities, and external guards are unchanged. The fix
removes redundant conversion calls without adding allocations or scans.

The updated registry spec lowers both real owner declarations through the
frontend, HIR, MIR and LLVM emitter, checking physical arities 2/20 and
exactly four data/length extractions. The standalone native fixture
`test/fixtures/native_memory_snapshot_abi/main.spl` invokes the actual owners,
checks flushed open/snapshot/terminal and phase records, every distinct
cardinality, disabled behavior, and refusal to overwrite existing evidence.
It fails with the old caller and also fails with a selected failure stub.

Native execution and the SSpec runner are UNRUN: no admitted full runner is
available and the current guarded hello run must not be disturbed. The
runtime/bootstrap owner must separately select the secure Windows provider.
Then compile the fixture through the pinned producer and run its native
binary in a fresh process with one absolute absent sink argument. Exit 0
and `NATIVE_MEMORY_SNAPSHOT_ABI_PASS`, together with retained producer/source
hashes and sink files, are required. C-only provider tests do not satisfy
this acceptance. No release merge is authorized by this source review.

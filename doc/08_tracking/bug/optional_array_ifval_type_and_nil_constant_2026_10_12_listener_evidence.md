# Optional byte-array payload: independent native listener evidence

Canonical OPEN bug: [optional_array_ifval_type_and_nil_constant_2026_10_12](optional_array_ifval_type_and_nil_constant_2026_10_12.md). This appendix adds an independent listener witness; it does not reset the original three-cycle stop or add a second bug ID.

The unchanged source reads one TCP byte through the SOSIX network facade, whose declared return is `[u8]?`. After `if val bytes = payload`, it checks `bytes.len() == 1` before constructing `[bytes[0], 0, 82]` and writing the counted response. The actual native object's `__simple_main` calls `io_tcp_read`, `rt_is_some`, and `rt_unwrap_or_self`, then calls **rt_string_len** on the unwrapped array word at relocation **0x1cd**. The emitted control flow compares that result to one and gates response construction/write on equality. This is a static array-metadata erasure diagnosis; no executed branch or write-callee trace was collected. The independent supervisor proves the child owns a live IPv4 listener, sends `Q`, and observes early EOF; the child exits **9**, proving its `written != 3` failure, with quiescence confirmed. The receipts do not prove which gated response instructions executed. No protocol PASS is claimed.

Relevant actual object excerpt:

```text
		000000000000017f:  R_X86_64_PLT32	lib.nogc_sync_mut.sffi.net.io_tcp_read-0x4
     183: 48 89 44 24 18               	movq	%rax, 0x18(%rsp)
     188: 48 c7 44 24 48 ff ff ff ff   	movq	$-0x1, 0x48(%rsp)
     191: 48 89 c7                     	movq	%rax, %rdi
     194: e8 00 00 00 00               	callq	0x199 <__simple_main+0x199>
		0000000000000195:  R_X86_64_PLT32	rt_is_some-0x4
     199: a8 01                        	testb	$0x1, %al
     19b: 74 11                        	je	0x1ae <__simple_main+0x1ae>
     19d: 48 8b 7c 24 18               	movq	0x18(%rsp), %rdi
     1a2: e8 00 00 00 00               	callq	0x1a7 <__simple_main+0x1a7>
		00000000000001a3:  R_X86_64_PLT32	rt_unwrap_or_self-0x4
     1a7: 48 89 44 24 40               	movq	%rax, 0x40(%rsp)
     1ac: eb 09                        	jmp	0x1b7 <__simple_main+0x1b7>
     1ae: 48 c7 44 24 40 03 00 00 00   	movq	$0x3, 0x40(%rsp)
     1b7: 48 8b 44 24 40               	movq	0x40(%rsp), %rax
     1bc: 48 89 44 24 30               	movq	%rax, 0x30(%rsp)
     1c1: 48 83 f8 03                  	cmpq	$0x3, %rax
     1c5: 74 7f                        	je	0x246 <__simple_main+0x246>
     1c7: 48 8b 7c 24 30               	movq	0x30(%rsp), %rdi
     1cc: e8 00 00 00 00               	callq	0x1d1 <__simple_main+0x1d1>
		00000000000001cd:  R_X86_64_PLT32	rt_string_len-0x4
     1d1: 48 83 f8 01                  	cmpq	$0x1, %rax
     1d5: 75 6f                        	jne	0x246 <__simple_main+0x246>
     1d7: 48 8b 44 24 30               	movq	0x30(%rsp), %rax
     1dc: 48 8b 38                     	movq	(%rax), %rdi
```

The original address-rendering criterion also remains FAIL: native cycle1 exited4 after3.026s, printing numeric `LISTENER:1041501185` instead of the concrete address. Its object routes the optional text payload through `rt_raw_i64_to_string`. That separate payload provenance witness is not repaired by socket discovery. Banner pre-accept flushing remains unqualified.

The [adjacent evidence](optional_array_ifval_type_and_nil_constant_2026_10_12_listener_evidence.json) binds source a21cbc83..., producer9fd9aaf8... (old-DAE literal-only facet), objectee6df1c0..., ELF ed7fcb9c..., same-core-C runtime4fbddc7e... and unchanged backfill935f7267..., plus exact local receipt/disassembly hashes. Actual strict link exits0 with no unresolved runtime/Simple strong symbols. This proves linkability and the specific native failure, not complete compiler/core/Redis behavior.

A typed-parameter helper workaround is prepared separately and unexecuted at this report's creation; it forwards the optional payload word into declared text/array parameters before operations. It is not an Optional compiler repair. No new compiler/whole-tree build, seed fallback, fabricated cache admission or runtime stub accompanies this documentation.

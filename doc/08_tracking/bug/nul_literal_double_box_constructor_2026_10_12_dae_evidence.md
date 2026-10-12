# Additional DAE evidence for nul_literal_double_box_constructor_2026_10_12

Existing authority: [PR3311](https://github.com/ormastes/simple/pull/3311), exact head 945990e5e68a4d0f14d4118ac5e70778232acc57, replacing closed PR3211. Its compiler/report/tests are another session's ownership. This appendix adds evidence only; no new bug ID or source repair. At historical release base 387702dc34d99e49fb7b872dad4603cd1d45e3b0, the database did not yet contain that pending PR's record.


Status: OPEN, actual native boundary failure; source prevention fixtures UNEXECUTED.

Qualified frozen Phase2 producer dae595a4 compiled the original exact Redis tagged-text boundary fixture once. Launch1 failed in watchdog setup before compiler spawn; corrected launch2 emitted x86-64 ELF object19c9e5bb (2512 bytes). Strong canonical entry strict-linked only C47 native archive plus935 backfill, binary26a7a2ff (2808464 bytes). Native exit2 with empty stdout/stderr means length3 passed but byte0 was not65. All later assertions remain unexecuted. No full Redis/RESP result exists.

Actual object relocation path: rt_string_new_literal at0x14 returns a tagged handle; rt_string_new at0x21 receives that handle as its raw pointer and length3. Later rt_string_data/rt_string_len/rt_string_new recopy this already corrupted string before the correctly registered tagged rt_text_to_bytes call. The genuine strlen negative control occurs later and was not executed.

Frozen compiler owner expr_dispatch.spl4987–5031 emits an Opaque(str) Const and then adds rt_string_new specifically for embedded NUL. LLVM core_codegen.spl1931–1938 already constructs this Const using rt_string_new_literal. Canonical C owner rt_string_new expects raw bytes, while rt_string_new_literal returns a tagged string. The repair belongs in compiler representation/provenance, not runtime decoder heuristics or replacing constructor contracts. The existing production repair is PR3311; Astra is reviewing frozen DAE integration only.

Retained reproducer is byte-identical to the original fixture. Additional empty, Unicode-plus-NUL and leading/trailing-NUL native prevention inputs are authored only. Their original counted bytes must survive; ordinary foreign strlen still uses a genuine C-string bridge. Backend and MIR prevention should establish exactly one literal construction plus correct counted extent, across custom callee and transport boundaries. No failed binary rerun or unchanged compiler rebuild is authorized. Original launch counters1/2 remain; no third compile until root reviews a genuinely changed, qualified producer containing the proper fix.

The final tagged-text boundary is correct in this emitted object; the compiler literal payload is corrupted earlier. This is additional evidence of the existing bug, not a runtime decoder defect or a separate bug registration.

# `hardware.rv32imac.*` modules gone; 6 specs orphaned (2026-08-18)

## Status
OPEN — reported, NOT fixed. Deleting the specs needs approval.

## Symptom
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_decode
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_regfile.Rv32RegFile
    error: semantic: Cannot resolve module: hardware.rv32imac.ext.rv32_muldiv.muldiv_execute
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_execute.alu_execute
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_compressed
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_pipeline_ctrl

Affected specs (all under `test/01_unit/hardware/rv32imac/`):
`rv32_alu_spec.spl`, `rv32_compressed_spec.spl`, `rv32_decode_spec.spl`,
`rv32_muldiv_spec.spl`, `rv32_pipeline_spec.spl`, `rv32_regfile_spec.spl`.

## Finding
There is no `src/lib/hardware/rv32imac/` tree and no retarget exists. The
surviving `src/lib/hardware/rv32gc/` holds only `top/rv32_machine.spl`; the
symbols the specs import are absent tree-wide:

    /usr/bin/grep -rn "fn decode_opcode|Rv32RegFile|fn is_compressed|fn decompress_rvc|fn alu_execute" src/lib/hardware/
    (only hit: rv64gc_rtl/mul_div.spl:373 fn muldiv_execute — rv64, different signature)

`src/lib/hardware/rv32i_rtl/` is a differently-shaped RTL library
(`decode.spl`, `regfile.spl`, `m_extension.spl`) with a different API, not a
rename of these modules. The same shape applies to the sibling
`hardware.rv64gc.*` / `hardware.riscv_common.pkg.*` unresolved imports in the
same shard logs.

## Required decision
Either the rv32imac RTL model is restored, or these 6 specs are retired. Both
need owner approval; this lane did neither.

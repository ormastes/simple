# x86_avx512_fma_encoding_spec

## Overview

Exact EVEX byte goldens for the fixed-width `VFMADD213PS zmm` emitter. The
unit lane is CPU independent and does not execute AVX-512 instructions.

**Requirements:** `doc/02_requirements/feature/x86_avx512_fixed_compiler_interpreter.md`

**Plan:** `doc/03_plan/sys_test/x86_avx512_environment_admission.md`

**Design:** `doc/05_design/x86_avx512_fixed_compiler_interpreter.md`

## Scenarios

### should encode an unmasked VFMADD213PS with k0 as the no-mask form

Checks the complete EVEX prefix, opcode, and ModR/M bytes for the canonical
f32x16 register form.

### should encode the opmask and zeroing fields in the EVEX P2 byte

Checks both a low mask with zeroing and a high mask without zeroing, proving
that mask bits and the `z` bit are retained together.

### should reject invalid ZMM and mask registers before emitting bytes

Out-of-range destination, source, and mask IDs produce an empty encoding.

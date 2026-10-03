# Explicit freestanding file linking

Authority: `test/03_system/app/compiler/feature/item4_freestanding_adapter_spec.spl`.
Requirements: ITEM4-REQ-002, 006, 007. Status: authored manual; SSpec execution
and canonical regeneration are **UNRUN**, not PASS.

1. Supply real ELF or Mach-O objects, an explicit entry and static configuration.
2. Link direct ELF inputs, a Mach-O archive provider, and RV64 archive inputs.
3. Inspect the actual output magic/machine/type and engine identity.
4. Place sentinel output bytes, then trigger unresolved input and image-size
   failures. Require the sentinel to survive unchanged.
5. Reject an empty entry before opening absent inputs. Reject normalized dot and
   absolute aliases of an owned input, preserving its bytes.
6. Remove task-owned output files after assertions.

The adapter is a resident fast path. An artifact-size limit is not a memory
certificate; these scenarios do not execute a Darwin or RISC-V image.

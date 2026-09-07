# runtime Layer Expert

## Role

Maintain process knowledge for the `runtime` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/runtime` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/runtime/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)

## Boundary Rules

- Pure Simple first: never a C implementation where pure Simple can do it; the C runtime is a boundary, not a place for logic. Bootstrap-required C keeps a pure-Simple twin (`scripts/check/check-dual-run-shadow.shs`). HAL code minimizes inline asm (typed register views > optimization-restraining tags > intrinsics > asm for irreplaceable ops only). Full policy: [pure_simple_hal.md](../../../07_guide/os/hal/pure_simple_hal.md).

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Session update 2026-09-06 — two heap tag spaces are overlaid on the same byte

**Hosted and freestanding number heap kinds differently, and they SWAP dict and
closure.** Both schemes live in the first byte of a heap object header, so a
reader that does not know which runtime allocated the object cannot tell them
apart:

| kind | hosted Rust runtime | core C / freestanding |
|---|---|---|
| String | `0x01` | magic `"STR1"` = `0x53545231` |
| Array | `0x02` | `0x02` |
| Dict | **`0x03`** | **`0x06`** |
| Closure | **`0x06`** | `0x03` |
| Enum | `0x07` | `0x04` |

- Hosted: `HeapObjectType` in `src/compiler_rust/runtime/src/value/heap.rs`
  — `Dict = 0x03` (`:11`), `Closure = 0x06` (`:14`).
- Freestanding: `src/runtime/runtime_native.c` —
  `RT_VALUE_HEAP_CLOSURE 0x03` (`:250`), `RT_VALUE_HEAP_DICT 0x06` (`:252`).

### Where it bites: the Cranelift inline `.len()` fast path

`src/compiler_rust/compiler/src/codegen/instr/helpers.rs` builds `.len()` inline
by loading the header byte and branching on it. It has BOTH numbering schemes in
one dispatch:

- `:74` `is_dict` — `object_type == 3`, documented as `RuntimeDict`, len at
  offset 8.
- `:81` `is_spldict` — `object_type == 6`, documented as
  "simple-core SplDict (freestanding / SimpleOS native-build)", len at offset
  **16**.

**The `:81` arm is scoped to freestanding IN ITS COMMENT ONLY.** Nothing in the
emitted code checks which runtime allocated the object, so a *hosted* closure
(`HeapObjectType::Closure = 0x06`) takes the SplDict arm. `RuntimeClosure`
(`src/compiler_rust/runtime/src/value/objects.rs:12-21`) is
`HeapHeader` (8 bytes: `object_type`, `gc_flags`, `reserved: u16`, `size: u32` —
`heap.rs:57-66`) + `func_ptr @8` + `capture_count: u32 @16`. So the offset-16
load returns **`capture_count`** — `0` for a non-capturing lambda — instead of
the contracted `-1` invalid sentinel. A `.len()` on a closure silently answers
`0` and reads as an empty collection.

Filed as PR <https://github.com/ormastes/simple/pull/403> (`docs(bug): Cranelift
inline len conflates hosted/freestanding heap tag spaces`). The record lands with
that PR as
`doc/08_tracking/bug/cranelift_inline_len_heap_tag_space_collision_dict_closure_2026-09-06.md`;
it is NOT on `main` yet, so do not follow that path until #403 merges.

### LANDMINE — the obvious fix is wrong

Gating the `object_type == 6` arm on `Target::is_baremetal()` (or any other
target-triple predicate) **regresses hosted-plus-C builds**. The axis is *which
runtime allocated the object*, not the target triple, and a single hosted binary
routinely contains both runtimes:
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` appends the
core-C runtime archive alongside the Rust `native_all` archive for the Stage-2
`bootstrap_main` link (`:1642`; the Stage-4 sibling supplement is at `:1587`).
Its own comments record that archive members resolve at OBJECT granularity, so
pulling `runtime_native.obj` drags in **~514 symbols `native_all` also defines**
(`:1649`), and `/FORCE:MULTIPLE` takes the first definition so `native_all`
wins (`:1654-1668`). (That block is the clang-cl/MSVC branch; the ~514 figure was
measured there, not on every platform — but the layering, and therefore the
mixed-runtime hazard, is not Windows-specific.)

A correct fix has to discriminate on the object itself — a per-runtime magic, a
disjoint tag space, or a header bit — not on where the code is being compiled to
run.

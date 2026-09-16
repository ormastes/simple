# Self-hosted parser has no `Variant = value` enum support — seed-only language feature

**Status:** open
**Found:** 2026-07-27 (bootstrap Stage 4 phase-2 parse, after device.spl entered the CLI closure)
**Area:** `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` (variant loop, ~:128)
**Severity:** high — a documented ABI pattern compiles under the seed but not the default toolchain

## Finding

`enum SyscallId: Exit = 0 ... Mmap = 10 ...` (explicit, non-sequential variant
values) parses under the Rust seed but the self-hosted parser rejects it:

```
[parser_error] line 8:10: expected enum variant name, got =
```

The variant loop handles payloads `Variant(field: type)`, pipe- and
comma-separated variants, but has no arm for `= <int>`. Deeper than parsing:
`decl_enum_def(enum_name, variant_names, 0)` stores **names only**, so even a
skip-the-value parser hack would silently assign ordinals — for
`src/os/kernel/types/syscall_types.spl` (gaps: 16→20, 38→44, out-of-order 43)
that would miscompile every syscall number. Do NOT "fix" this by skipping the
literal.

## Interim mitigation (landed 2026-07-27)

The only closure edge pulling the enum file host-side was
`os.userlib.device` → `new_device_info_buf`. Extracted `DeviceInfoBuf` +
factory to `src/os/kernel/types/device_info_types.spl` (enum-free), re-exported
from `syscall_types.spl` for kernel importers, repointed `device.spl`. The
guest kernel still compiles the explicit values via the seed cross-toolchain;
the host CLI closure no longer parses them.

## Real fix

Explicit variant values end-to-end in the self-hosted compiler: parser arm for
`= <int-lit>` (incl. hex/negative), value storage in the enum decl, HIR/codegen
using stored values, and cross-compiler parity specs against the seed on a
gap/out-of-order fixture. Until then any host-reachable module must not declare
explicit-value enums.

## Related

- `seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md`,
  `seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md` — same
  seed/self-hosted divergence family, all detonating at bootstrap Stage 4
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)

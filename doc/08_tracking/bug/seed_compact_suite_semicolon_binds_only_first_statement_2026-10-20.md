# Seed: a compact suite binds only the first `;`-statement (`while c: a; b` never advances)

- **Date:** 2026-10-20
- **Status:** open (the one site that blocked the internal ELF linker is rewritten to block form)
- **Where:** the Rust seed parser, `src/compiler_rust/parser/src/parser_helpers.rs:189`
  `parse_inline_or_block`. It parses ONE item after the colon. The block-level separator loop
  (`parser_impl/core.rs:399/430`) treats `;` like a newline, so `b` becomes the next statement
  of the ENCLOSING block.
- **Seen with:** `bin/simple` = `bin/release/aarch64-unknown-linux-gnu/simple`, the Rust seed
  (134525680 bytes, 2026-10-20 08:37).

## Repro (seed, `bin/simple run`)

```
fn main() -> i64:
    if false: print("A"); print("B")
    var i = 0
    while i < 2: i = i + 1; print("W{i}")
    print("end i={i}")
    0
```

The seed prints `B`, `W2`, `end i=2`, so `print("B")` runs even though the condition is false, and
the loop body prints nothing. `while index < n: emitted.push(false); index = index + 1` therefore
never terminates. It grows memory until the cgroup kills it: 2 GB in under 20 s.

## Impact

`src/lib/mdsocpp/seal.spl:129` had exactly that loop. Every `mdsocpp_seal_v1` call, and with it
`elf_builtin_file_operations_v1` and so every `SIMPLE_LINKER=internal` link, hung and then OOMed
(16 GB in 260 s; sampler: 76.7% self time in `mdsocpp_seal_v1`). That site is now in block form.

The same compact form is still used here, and under the seed each runs its second statement
unconditionally:

- `src/compiler/99.loader/parser_structural_guarded_scope_v1.spl:83`:
  `else: pending.windows = []; pending.affinities = []`
- `src/lib/nogc_sync_mut/composition/source.spl:126,141,156,171`:
  `if not inserted and ...: next.push(item); inserted = true`

## Fix wanted

The authors clearly meant Python's `;` rule (every statement on the line belongs to the suite).
Either make `parse_inline_or_block` (and the `if` inline paths at
`stmt_parsing/control_flow.rs:1385/1400`) consume `; stmt` up to the newline, or reject a `;`
after a compact suite with a diagnostic. Before landing either, check what the pure-Simple
front end does with the same form, so the two parsers agree. Do not keep the silent
mis-binding.

<!-- codex-design -->
# Detail Design: SFFI v2 Hardening P0/P1

## Shared interfaces

```text
ReturnOrigin = Explicit | Tail | UnitFallthrough | OptionalNoneExplicit |
               Foreign(contract_id) | ForeignError | Missing

SffiReturnContract = InfallibleValue | NullableValue | StatusOnly |
                     StatusOut | SentinelValue | TaggedResult

SffiFunctionContractV2 = identity + ABI + params + return contract +
                         ownership + validation + policy + hashes
```

Stable diagnostic allocation:

- `E-SFFI-001` unresolved symbol;
- `E-SFFI-002` raw call outside `unsafe(ffi)`;
- `E-SFFI-003` ABI mismatch;
- `E-SFFI-007` forbidden null;
- `E-SFFI-008` invalid sentinel;
- `E-SFFI-009` success with invalid output;
- `E-SFFI-010` invalid descriptor;
- `E-SFFI-011` invalid encoding;
- `E-SFFI-012` ownership/allocator error;
- `E-SFFI-014` unsupported signature;
- `E-SFFI-015` unvalidated foreign escape;
- `E-SFFI-016` missing return;
- `E-SFFI-017` cross-lane bridge corruption.

Other codes through `E-SFFI-020` remain reserved by the implementation plan.

## P0 algorithm

1. Execute a function body without creating a substitute value.
2. Classify the return origin.
3. Resolve the declared return contract.
4. Validate origin and value shape completely.
5. Only then construct/wrap the caller-visible value.

Extern dispatch resolves a typed handler or returns `E-SFFI-001`. Conversion
returns `Result`, never an integer fallback. Temporary C strings/buffers live in
a call frame and are released after invocation. Native closure resolution must
leave unresolved required symbols undefined and abort the build; it must not
emit weak, `ud2`, zero, nil, or empty stand-ins.

## P1 validation and lift

The resolver assigns a stable `contract_id`. HIR raw calls return a restricted
foreign state. Generated lift code performs, in order:

1. foreign status/tag validation;
2. null/sentinel validation;
3. overflow-safe pointer/length/capacity/layout checks;
4. encoding/discriminant checks;
5. ownership/allocator/provider-generation binding;
6. copy, scoped borrow, or resource construction;
7. typed `T`, `Option`, or `Result` publication.

On lift failure, generated cleanup follows the contract so live foreign output
is neither leaked nor published.

## Generation

The existing `src/compiler/90.tools/sffi_gen/` evolves to consume resolved
contracts and emit deterministic C headers, C++ exception shims, Rust C-ABI
shims, Simple raw declarations, Simple safe wrappers, provider registry entries,
and docs. Golden encodings prevent private per-lane schemas.

## Module interaction

- `00.common/sffi`: schema, canonical types, errors, encoders.
- `10.frontend`: attributes/declarations, no semantic inference.
- `20.hir`: contract IDs, raw/lifted operations, foreign state.
- `35.semantics`: ABI-safe types, lexical capability, escape/return checks.
- `70.backend` and Rust mirrors: typed lowering and closure enforcement.
- `90.tools/sffi_gen`: generated surfaces only.
- loader owners: planned P3/P4 atomic admission.

## Test helper contract

The primary system spec should define stable helper names before parallel test
work: `run_missing_return_fixture`, `run_missing_symbol_fixture`,
`run_null_on_success_fixture`, `run_value_category_fixture`,
`check_canonical_sffi_error`, and `check_no_fabricated_provider`. Any unavailable
lane helper must fail with `assert(false)`/`fail(...)`, never pass or skip.

Manual step text is frozen as: “Select the execution lane”, “Invoke the
contract fixture”, “Observe the typed boundary result”, and “Confirm no
fabricated value or provider was published”.

## Planned, not implemented here

P2 lexical enforcement completion, P3 provider registries/typed slots, P4
cryptographic evidence, P5 provider migration, and P6 full matrix/performance
remain planned. This design leaves extension fields but makes no PASS claim.


# Boxed enum instance methods resolve against the variant instead of the owner

- Priority: P1 — user enum methods fail, or an Option accessor silently wins.
- Status: source fix and focused native dispatch validation complete; full interpreter suite pending.
- Platform reproduced: macOS arm64.
- Requirement: REQ-INTERP-ENUM-METHOD-OWNER.

## Defect and change

`eval_enum_variant_call` and `eval_enum_variant_access` create boxed values named
`Type::Variant`, but impl methods are registered as `Type__method`.
`eval_method_call` previously looked up `Type::Variant__method`, which misses the
declaration. A user enum such as `Parcel.Some(7)` with an `unwrap` method returning
91 instead entered the built-in Option accessor and returned the payload 7.

The dispatcher now resolves the enum owner before considering built-in accessors,
and uses the resolved declaration for the ordinary struct-method call path. It
only removes the variant suffix for values identified as boxed enums. Built-in
Option accessors remain available when there is no declared receiver method.

## Focused validation

The admitted pure-Simple compiler was used, with no full bootstrap:

- Compiler: `/Users/ormastes/simple/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`.
- SHA-256: `e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`.
- Adjacent `stage2-provenance.receipt`: `pure-simple`, matching candidate hash.
- Runtime bundle: `/Users/ormastes/simple/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority`.

A temporary native probe embeds the exact live `eval_method_call` body, using
controlled expression/value/declaration tables. It covers payload and unit enum
variants, a user enum `unwrap`, boxed Options named `Option` and `Option::Some`,
and an ordinary struct's own `unwrap`. It also checks that method dispatch passes
the original receiver as its sole argument. All six cases pass (exit 0).
The identical probe with the pre-fix function body exits 11 on the first enum case.

Local artifacts: `/tmp/interpreter-todo3-dispatch-probe.spl`,
`/tmp/interpreter-todo3-dispatch-baseline.spl`, and corresponding native binaries
and build logs. The probes isolate dispatch; they do not establish parser, enum
registration, or complete interpreter integration correctness.

The durable behavioral spec is
`test/01_unit/compiler/interpreter/enum_instance_method_dispatch_spec.spl`.
It exercises `core_interpret` for enum methods, user accessor precedence, and
built-in Option accessors. Its execution remains pending a current working
self-hosted interpreter test runner. An installed release runner stopped after
setup and produced no case results, so it is not accepted as validation.

No full compiler/lib/MCP smoke or release readiness claim is made by this lane.

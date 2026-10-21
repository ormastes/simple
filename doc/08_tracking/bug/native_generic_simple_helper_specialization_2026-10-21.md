# Native generic Simple helper specialization is unresolved

## Evidence

The isolated native struct-carrier guard probe build 1 failed during LLVM linking. The retained log is `build/nogc-hardening/struct-carrier-guard-build-1.log`; its primary diagnostic is:

```text
ld.lld: error: undefined symbol: .home.yoon.dev.simple_nogc_short_borrow_completion.build.scv.snapshots.scv_revision_v1_4853ce6e029407e17a8cf75d0ff95784219a919a8a624bd1fe780776d66d594e.test.fixtures.compiler.nogc_struct_carrier_guard_probe.carrier_absent
```

The fixture defined `carrier_absent<T>` and invoked it with `LocalId` and `MirOperand`. The native producer emitted a call to the module-qualified generic function symbol but did not provide a matching specialization/definition at link time. This establishes a generic Simple helper specialization/linkage failure for this probe; it does not establish that the generic runtime extern declarations are unsupported.

## Bounded follow-up

The diagnostic fixture now uses two concrete helpers, `local_carrier_absent(LocalId)` and `operand_carrier_absent(MirOperand)`, with equivalent nil/integer-zero predicates. It retains the runtime classifier extern declarations and the raw-zero, nil, and constructed-record cases. The fixture-only revision is unverified pending the separately owned native build. No compiler product guard was changed, and no generic-helper fix or acceptance result is claimed.

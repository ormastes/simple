# Darwin host wrapper acceptance

One authored ITEM4-REQ-002/006 scenario, **UNRUN**, in
`test/03_system/app/compiler/feature/item4_macos_native_host_spec.spl`.
This is a manually authored companion, not generated runtime evidence.

Run separately on Darwin using an independently admitted self-hosted runtime:
`SIMPLE_LINKER=internal <runtime> test test/03_system/app/compiler/feature/item4_macos_native_host_spec.spl`

The test requires actual Darwin, a supported host CPU, externally selected
`internal`, and the ordinary unmanaged route. It changes no environment values.
Unmet prerequisites fail explicitly; there is no off-host skip-as-pass.
Real host-matching object fixtures flow through `link_to_native_with_engine`.
The returned route must be `internal:macho`; independent output checks validate
Mach-O CPU/type/local pointer and `/bin/test -x` validates executable permission.

Managed native authority remains separate and must not be disabled by this
adapter. This test does not fabricate managed receipts or prove managed
admission. It does not launch the generated image: dyld launch, full compiler
runtime/application execution and Darwin host qualification remain open gates.

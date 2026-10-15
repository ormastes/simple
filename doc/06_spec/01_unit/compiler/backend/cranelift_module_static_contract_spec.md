# Cranelift module static initialization contracts

Source: `test/01_unit/compiler/backend/cranelift_module_static_contract_spec.spl`.
Requirement: REQ-CRANELIFT-STATIC-001 — stored text and aggregate globals retain their initialized value and one defining storage owner.

The first scenario lowers an actual immutable public string declaration, checks its storage has runtime initialization rather than an unsupported constant payload, and requires an emitted store. The second lowers an aggregate factory and empty array and checks both resulting handle slots are accepted by the Cranelift declaration contract and initialized by emitted stores.

A third scenario rejects an imported initializer even when its value is Zero, accepts that import only after removing the initializer, and rejects a nonempty aggregate constant payload.

These scenarios cover the frontend-to-MIR/backend boundary. The native two-module fixture additionally checks initialized values and mutation across importers. The direct provider test checks actual owner data, undefined import symbol and relocation, and rejects import initializer bits. All three evidence layers are required; none is a substitute for the others.

Status: authored, UNRUN. Run SSpec/docgen on the admitted pure host, the native fixture with the rebuilt Cranelift provider and matching producer, and the direct provider AOT test through the provider build lane. Missing host/provider is BLOCKED, never a passing scenario. This manual is authored from the scenarios; generated docgen validation remains pending.

Native startup coverage additionally constructs an atomic during module initialization, checks value 23, and requires a positive recorded MC/DC count after configuration. The expected native receipt is `cranelift_module_statics=PASS text=present counter=7 registry=41 array=41 startup=23 mcdc=recording`. This check remains UNRUN until the matching native artifact executes.

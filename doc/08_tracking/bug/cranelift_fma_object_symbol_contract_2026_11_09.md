# Cranelift FMA object regression checks the symbol contract

Strict HIR unit run 42588612104 at 966ec47ee0ab5901977433506155cebd5331b201
reports 31 passing backfill tests, one failure and one ignored test. The FMA
probe successfully configures the ISA and defines a real function, then fails
because it requires an object section whose name contains `fma_probe`.
Cranelift ObjectModule can place the function in a shared `.text` section;
the exported function symbol identifies its actual section and byte range.

The regression now checks ELF/x86_64, a defined text symbol with a positive
size, a text section, and the bounded bytes belonging to that symbol. It
verifies a scalar F64 VEX-encoded FMA instruction in that range. A matching
module with the FMA feature disabled is the negative control: the same CLIF
operation must emit no native FMA and must reference the fused `fma` libcall
via a relocation inside that function range. Thus a lost ISA feature cannot
pass just because some object text exists.

No production lowering or ISA configuration changes. The existing vendored
Cranelift x64 lowering selects native FMA when `use_fma` is true and otherwise
uses `LibCall.FmaF64` for the scalar F64 operation.

## Evidence and limits

Source diff whitespace check passes. Local real-backend execution is UNRUN.
A bounded attempt to reuse the existing bootstrap cache failed before codegen:
the cached rlibs contain only metadata stubs and require the original rmeta
artifacts. No cold dependency build was started because free host memory was
about 2.6 GiB and the required reserve is 2 GiB. Retained attempted command and
diagnostics: `D:/dev/cranelift-fma-contract-evidence-20261109/`.

The next changed-graph CI run must execute the actual backfill regression;
source review and cache-unavailability evidence do not constitute a backend
PASS or Phase Ladder admission.

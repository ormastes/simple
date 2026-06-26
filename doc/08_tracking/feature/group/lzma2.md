# lzma2

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-LZMA2_FULL_LCLPPB_2026_05_01"></a>LZMA2_FULL_LCLPPB_2026_05_01 | LZMA2 — Full LC/LP/PB Property Support | `LC=3, LP=0, PB=2` (props byte `0x5D`). Full lc/lp/pb support landed 2026-05-10 via the restored `std.common.compress.lzma2` hosted XZ bridge. See `src/lib/common/compress/lzma2.spl`. ## Context | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |

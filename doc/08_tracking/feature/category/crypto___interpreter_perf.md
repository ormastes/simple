# crypto_/_interpreter_perf

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-CRYPTO-0001"></a>FR-CRYPTO-0001 | RSA-2048 modexp completes within interpreter test budget | PSS bigint micro-optimization. Current `HEAD` already contains the prior safe hot-path speedups in `src/os/crypto/rsa_pss.spl` (`_pss_bi_normalize` avoids copying already-normalized limb lists, `_pss_bi_get_bit` uses the same direct limb-ma | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |

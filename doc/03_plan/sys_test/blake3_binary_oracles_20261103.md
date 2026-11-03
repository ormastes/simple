# Independent binary BLAKE3 oracles — 2026-11-03

Status: Simple AUTHORED_UNRUN / BRANCH_UNMEASURED. No production edit. This closes an authored-test gap only: published upstream inputs repeat0..250 and never ff. The new pattern repeats exactly bytes00,7f,80,ff and reaches byte-word loading, block chaining and chunk trees in each separate owner. Common and OS scenario pairs intentionally exercise different implementations; neither owner's result is used as the other's oracle.

## Independent oracle provenance

These are upstream-reference-generated differential vectors, not published official test vectors. Reference source: https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/f55849f89cd85083c1c9daa2c5de20766f309c00/reference_impl/reference_impl.rs (official reference discussed in PDF section5.1). Apache2 license is cached as blake3-code-license.txt. Source SHA2566e89a18be72e3c4d838644e1796e04d896cb4a16bd7bb803d4380d7a363fbfd2.

Host toolchain: rustc1.101.0-nightly (92b5b8c87 2026-10-29). Standalone oracle compile only; no Simple bootstrap, seed, dependency rebuild or production execution.

Exact compile command: `rustc --edition=2021 -O C:/dev/p3new/hash-coverage-20261103/spec-cache/blake3_binary_oracle.rs -o C:/dev/p3new/hash-coverage-20261103/spec-cache/blake3_binary_oracle.exe`.
Run: executable stdout captured as blake3_binary_oracle.tsv via PowerShell Set-Content. Private source/artifacts remain in that spec-cache directory.

| Artifact | SHA256 |
|---|---|
| harness source | a106c69ed1a3c69949063c1c16920898593275b070d19961dbcdb9930809e089 |
| reference executable | 8e5a3d4e9cdea09783d24719614024f36c566f0f8f77860f2ff0c3037f25835a |
| stdout TSV | 3ddfcee9f807a02ba00fc89bea01cdd47f287e0b85b53c2dca0ef71fcf9547b4 |
| published vector JSON | dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624 |

Oracle qualification performed once: all131output bytes matched the published JSON for hash/keyed/derive at lengths0,1,63,64,65,1023,1024,1025,2048,3073 (30/30 exact comparisons). This validates the reference extraction/harness, not Simple. No production RED/GREEN exists.

Binary cases use the exact official key `whats the Elvish word for friend` and context `BLAKE3 2019-12-27 16:29:52 test vectors context`.

| Input length | Mode | Output length | Expected hexadecimal |
|---|---|---|---|
| 4 | hash | 32 | `7091ffa8ddb7544b67c09aefb51a256e8d839397288b3e1a7fee253c3395cc92` |
| 65 | keyed_hash | 32 | `8f3df3fa27a9508f7594becd14267c808507d3f21a93a4a722b30d96c81f8607` |
| 1025 | derive_key | 32 | `52068eb240cb42770be6fdbb20045cff386ced4e7f3f297facff60b11ef957e5` |
| 1025 | hash | 65 | `8d4295ba3c613f468fef5219df167e82c505bd466fb0890be046398d12ef962dd4d2f3c655902c1010868d92bf8268e9db8872e6cf82c8697c02f9e996fe130187` |

REQ-HASH-BLAKE3-001 maps binary hash4; -003 maps keyed65 and derive1025; -004 maps binary XOF1025/65. Common adds4scenarios; OS adds the same4against a distinct production owner plus published empty-input XOF0/31/33 and repository negative-length behavior (8OSscenarios). Existing sixteen common and twelve OS scenarios do not use this binary pattern; existing OS XOF65 positive uses the i%251 pattern, not this input. No existing case is duplicated on the same owner. API-invalid output behavior is a repo contract, not PDF mandated. No streaming API or seek API is invented.

Execution gate remains blocked: require admitted source-matched native runner for12newscenarios, actual docgen zero-stub receipt and per-owner branch inventory with zero-hit sites. No99% claim. Reuse prior static reviews; no seed fallback/bootstrap. Final reviewer Astra; landing owner /root/land_source_repairs; sidecars N/A.

<details><summary>Standalone oracle harness (not Simple test execution)</summary>

```rust
#[path = "blake3-reference_impl.rs"]
mod reference;
use reference::Hasher;
fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{:02x}", b)).collect() }
fn emit(pattern: &str, n: usize, mode: &str, out_len: usize) {
    let data: Vec<u8> = (0..n).map(|i| if pattern == "official" { (i%251) as u8 } else { [0,127,128,255][i%4] }).collect();
    let mut h = match mode { "keyed_hash" => Hasher::new_keyed(b"whats the Elvish word for friend"), "derive_key" => Hasher::new_derive_key("BLAKE3 2019-12-27 16:29:52 test vectors context"), _ => Hasher::new() };
    h.update(&data);
    let mut out = vec![0u8;out_len]; h.finalize(&mut out);
    println!("{}\t{}\t{}\t{}\t{}",pattern,n,mode,out_len,hex(&out));
}
fn main() {
    for n in [0,1,63,64,65,1023,1024,1025,2048,3073] { for mode in ["hash","keyed_hash","derive_key"] { emit("official", n, mode,131); } }
    emit("binary",4,"hash",32);
    emit("binary",65,"keyed_hash",32);
    emit("binary",1025,"derive_key",32);
    emit("binary",1025,"hash",65);
}
```
</details>

# bip39_kat_spec

> Purpose: Prove that BIP-39 wordlist integrity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bip39_kat_spec

Purpose: Prove that BIP-39 wordlist integrity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/bip39_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that BIP-39 wordlist integrity.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### BIP-39 wordlist integrity

#### is the official 2048-word BIP-39 English list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is the official 2048-word BIP-39 English list
- Verify: is the official 2048-word BIP-39 English list
   - Expected: bip39_word(0) equals `abandon`
   - Expected: bip39_word(2047) equals `zoo`
   - Expected: bip39_word_index("abandon") equals `0`
   - Expected: bip39_word_index("zoo") equals `2047`
   - Expected: bip39_word_index("notaword") equals `-1`
   - Expected: bip39_wordlist_self_check() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("is the official 2048-word BIP-39 English list")
step("Verify: is the official 2048-word BIP-39 English list")
# @req: REQ-OS-CRYPTO-001
expect(bip39_word(0)).to_equal("abandon")
expect(bip39_word(2047)).to_equal("zoo")
expect(bip39_word_index("abandon")).to_equal(0)
expect(bip39_word_index("zoo")).to_equal(2047)
expect(bip39_word_index("notaword")).to_equal(-1)
# 2048 entries, strictly ascending (implies sorted + duplicate-free)
expect(bip39_wordlist_self_check()).to_equal(true)
```

</details>

### BIP-39 entropy_to_mnemonic

#### TV1 00..00 (128-bit) → abandon×11 + about

- TV1 00..00 (128-bit) → abandon×11 + about
- Verify: TV1 00..00 (128-bit) → abandon×11 + about
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv1_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV1 00..00 (128-bit) → abandon×11 + about")
step("Verify: TV1 00..00 (128-bit) → abandon×11 + about")
val result = bip39_entropy_to_mnemonic(_tv1_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv1_mnemonic())
```

</details>

#### TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow

- TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow
- Verify: TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv2_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow")
step("Verify: TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow")
val result = bip39_entropy_to_mnemonic(_tv2_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv2_mnemonic())
```

</details>

#### TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above

- TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above
- Verify: TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv3_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above")
step("Verify: TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above")
val result = bip39_entropy_to_mnemonic(_tv3_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv3_mnemonic())
```

</details>

#### TV4 ff..ff → zoo×11 + wrong

- TV4 ff..ff → zoo×11 + wrong
- Verify: TV4 ff..ff → zoo×11 + wrong
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv4_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV4 ff..ff → zoo×11 + wrong")
step("Verify: TV4 ff..ff → zoo×11 + wrong")
val result = bip39_entropy_to_mnemonic(_tv4_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv4_mnemonic())
```

</details>

#### TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent

- TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent
- Verify: TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv5_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent")
step("Verify: TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent")
val result = bip39_entropy_to_mnemonic(_tv5_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv5_mnemonic())
```

</details>

#### TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art

- TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art
- Verify: TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `_tv6_mnemonic()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art")
step("Verify: TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art")
val result = bip39_entropy_to_mnemonic(_tv6_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv6_mnemonic())
```

</details>

#### invalid entropy length (15 bytes) → Err(InvalidEntropyLength)

- invalid entropy length (15 bytes) → Err(InvalidEntropyLength)
- Verify: invalid entropy length (15 bytes) → Err(InvalidEntropyLength)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("invalid entropy length (15 bytes) → Err(InvalidEntropyLength)")
step("Verify: invalid entropy length (15 bytes) → Err(InvalidEntropyLength)")
var bad: [u8] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val result = bip39_entropy_to_mnemonic(bad)
expect(result.is_err()).to_equal(true)
```

</details>

### BIP-39 mnemonic_to_entropy (round-trip)

#### TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e

- TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e
- Verify: TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e")
step("Verify: TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e")
val enc = bip39_entropy_to_mnemonic(_tv1_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("00000000000000000000000000000000")
```

</details>

#### TV2 round-trip

- TV2 round-trip
- Verify: TV2 round-trip
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV2 round-trip")
step("Verify: TV2 round-trip")
val enc = bip39_entropy_to_mnemonic(_tv2_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f")
```

</details>

#### TV3 round-trip

- TV3 round-trip
- Verify: TV3 round-trip
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `80808080808080808080808080808080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV3 round-trip")
step("Verify: TV3 round-trip")
val enc = bip39_entropy_to_mnemonic(_tv3_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("80808080808080808080808080808080")
```

</details>

#### TV4 round-trip (zoo×11 + wrong)

- TV4 round-trip (zoo×11 + wrong)
- Verify: TV4 round-trip (zoo×11 + wrong)
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `ffffffffffffffffffffffffffffffff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV4 round-trip (zoo×11 + wrong)")
step("Verify: TV4 round-trip (zoo×11 + wrong)")
val dec = bip39_mnemonic_to_entropy(_tv4_mnemonic())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("ffffffffffffffffffffffffffffffff")
```

</details>

#### TV5 round-trip (192-bit)

- TV5 round-trip (192-bit)
- Verify: TV5 round-trip (192-bit)
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `000000000000000000000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV5 round-trip (192-bit)")
step("Verify: TV5 round-trip (192-bit)")
val enc = bip39_entropy_to_mnemonic(_tv5_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("000000000000000000000000000000000000000000000000")
```

</details>

#### TV6 round-trip (256-bit)

- TV6 round-trip (256-bit)
- Verify: TV6 round-trip (256-bit)
   - Expected: dec.is_ok() is true
   - Expected: _bytes_hex(dec.unwrap()) equals `0000000000000000000000000000000000000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV6 round-trip (256-bit)")
step("Verify: TV6 round-trip (256-bit)")
val enc = bip39_entropy_to_mnemonic(_tv6_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("0000000000000000000000000000000000000000000000000000000000000000")
```

</details>

### BIP-39 error cases

#### unknown word → Err(UnknownWord)

- unknown word → Err(UnknownWord)
- Verify: unknown word → Err(UnknownWord)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("unknown word → Err(UnknownWord)")
step("Verify: unknown word → Err(UnknownWord)")
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon notaword")
expect(result.is_err()).to_equal(true)
```

</details>

#### invalid checksum → Err(InvalidChecksum)

- invalid checksum → Err(InvalidChecksum)
- Verify: invalid checksum → Err(InvalidChecksum)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("invalid checksum → Err(InvalidChecksum)")
step("Verify: invalid checksum → Err(InvalidChecksum)")
# Flip last word: 'about' (correct for 00..00) → 'ability' (wrong checksum)
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon ability")
expect(result.is_err()).to_equal(true)
```

</details>

#### wrong word count (11 words) → Err(InvalidWordCount)

- wrong word count (11 words) → Err(InvalidWordCount)
- Verify: wrong word count (11 words) → Err(InvalidWordCount)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("wrong word count (11 words) → Err(InvalidWordCount)")
step("Verify: wrong word count (11 words) → Err(InvalidWordCount)")
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon")
expect(result.is_err()).to_equal(true)
```

</details>

### BIP-39 mnemonic_to_seed

#### TV1 seed with passphrase TREZOR

- TV1 seed with passphrase TREZOR
- Verify: TV1 seed with passphrase TREZOR
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv1_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV1 seed with passphrase TREZOR")
step("Verify: TV1 seed with passphrase TREZOR")
val seed = bip39_mnemonic_to_seed(_tv1_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv1_seed())
```

</details>

#### TV2 seed with passphrase TREZOR

- TV2 seed with passphrase TREZOR
- Verify: TV2 seed with passphrase TREZOR
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv2_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV2 seed with passphrase TREZOR")
step("Verify: TV2 seed with passphrase TREZOR")
val seed = bip39_mnemonic_to_seed(_tv2_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv2_seed())
```

</details>

#### TV3 seed with passphrase TREZOR

- TV3 seed with passphrase TREZOR
- Verify: TV3 seed with passphrase TREZOR
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv3_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV3 seed with passphrase TREZOR")
step("Verify: TV3 seed with passphrase TREZOR")
val seed = bip39_mnemonic_to_seed(_tv3_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv3_seed())
```

</details>

#### TV4 seed with passphrase TREZOR

- TV4 seed with passphrase TREZOR
- Verify: TV4 seed with passphrase TREZOR
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv4_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV4 seed with passphrase TREZOR")
step("Verify: TV4 seed with passphrase TREZOR")
val seed = bip39_mnemonic_to_seed(_tv4_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv4_seed())
```

</details>

#### TV5 seed with passphrase TREZOR (192-bit entropy)

- TV5 seed with passphrase TREZOR (192-bit entropy)
- Verify: TV5 seed with passphrase TREZOR (192-bit entropy)
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv5_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV5 seed with passphrase TREZOR (192-bit entropy)")
step("Verify: TV5 seed with passphrase TREZOR (192-bit entropy)")
val seed = bip39_mnemonic_to_seed(_tv5_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv5_seed())
```

</details>

#### empty passphrase gives the BIP-39 no-passphrase seed, not the TREZOR one

- empty passphrase gives the BIP-39 no-passphrase seed, not the TREZOR one
- Verify: empty passphrase gives the BIP-39 no-passphrase seed, not the TREZOR one
   - Expected: _bytes_hex(seed_empty) equals `_tv1_seed_no_passphrase()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("empty passphrase gives the BIP-39 no-passphrase seed, not the TREZOR one")
step("Verify: empty passphrase gives the BIP-39 no-passphrase seed, not the TREZOR one")
val seed_empty = bip39_mnemonic_to_seed(_tv1_mnemonic(), "")
val seed_trezor = bip39_mnemonic_to_seed(_tv1_mnemonic(), "TREZOR")
expect(_bytes_hex(seed_empty)).to_equal(_tv1_seed_no_passphrase())
assert_not_equal(_bytes_hex(seed_empty), _bytes_hex(seed_trezor))
```

</details>

#### TV6 seed with passphrase TREZOR (256-bit entropy)

- TV6 seed with passphrase TREZOR (256-bit entropy)
- Verify: TV6 seed with passphrase TREZOR (256-bit entropy)
   - Expected: seed.len() equals `64`
   - Expected: _bytes_hex(seed) equals `_tv6_seed()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("TV6 seed with passphrase TREZOR (256-bit entropy)")
step("Verify: TV6 seed with passphrase TREZOR (256-bit entropy)")
val seed = bip39_mnemonic_to_seed(_tv6_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)  # oracle: 64 — named expected value from the requirement
expect(_bytes_hex(seed)).to_equal(_tv6_seed())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-OS-CRYPTO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e4cbed9014991487bcd3953357d0df5414cf6129d29118288018116bb851a7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e4cbed9014991487bcd3953357d0df5414cf6129d29118288018116bb851a7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e4cbed9014991487bcd3953357d0df5414cf6129d29118288018116bb851a7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/crypto/bip39_kat_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/bip39_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/bip39_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/bip39_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/bip39_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/bip39_kat_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is the official 2048-word BIP-39 English list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/bip39_kat_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV1 00..00 (128-bit) → abandon×11 + about' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/bip39_kat_spec.spl:222:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

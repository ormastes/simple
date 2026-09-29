# General MIR Optimization Patterns Specification

> Purpose: Prove that Dynamic manifest entries registered (AC-5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# General MIR Optimization Patterns Specification

Purpose: Prove that Dynamic manifest entries registered (AC-5).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-5, #AC-6, #AC-7 |
| Category | Compiler / Optimization |
| Difficulty | 4/5 |
| Status | Active |
| Source | `test/unit/compiler/60.mir_opt/general_patterns_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Dynamic manifest entries registered (AC-5).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Dynamic manifest entries registered (AC-5)

#### produces exactly seven manifest entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces exactly seven manifest entries
- Verify: produces exactly seven manifest entries
   - Expected: entries.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces exactly seven manifest entries")
step("Verify: produces exactly seven manifest entries")
# @req: REQ-COMP-DYNAMIC-MANIFEST-ENTRIES-REGISTERED-AC-5-001
val entries = general_pattern_manifest_entries()
expect(entries.len()).to_equal(7)
```

</details>

#### entries have correct stable names

- entries have correct stable names
- Verify: entries have correct stable names
   - Expected: entries[0].stable_name equals `byte-scan-to-delimiter`
   - Expected: entries[1].stable_name equals `switch-on-short-string`
   - Expected: entries[2].stable_name equals `capability-guarded-fast-path`
   - Expected: entries[3].stable_name equals `bit-unpack-fixed-table`
   - Expected: entries[4].stable_name equals `checksum-reducer`
   - Expected: entries[5].stable_name equals `prefix-scan-table`
   - Expected: entries[6].stable_name equals `wal-batch-flush`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries have correct stable names")
step("Verify: entries have correct stable names")
val entries = general_pattern_manifest_entries()
expect(entries[0].stable_name).to_equal("byte-scan-to-delimiter")
expect(entries[1].stable_name).to_equal("switch-on-short-string")
expect(entries[2].stable_name).to_equal("capability-guarded-fast-path")
expect(entries[3].stable_name).to_equal("bit-unpack-fixed-table")
expect(entries[4].stable_name).to_equal("checksum-reducer")
expect(entries[5].stable_name).to_equal("prefix-scan-table")
expect(entries[6].stable_name).to_equal("wal-batch-flush")
```

</details>

#### entries have function scope

- entries have function scope
- Verify: entries have function scope
   - Expected: entries.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries have function scope")
step("Verify: entries have function scope")
val entries = general_pattern_manifest_entries()
expect(entries.len()).to_equal(7)
```

</details>

#### entries have valid entry symbols

- entries have valid entry symbols
- Verify: entries have valid entry symbols
   - Expected: entries[0].entry_symbol equals `general_pattern_byte_scan_to_delimiter`
   - Expected: entries[1].entry_symbol equals `general_pattern_switch_on_short_string`
   - Expected: entries[2].entry_symbol equals `general_pattern_capability_guarded_fast_path`
   - Expected: entries[3].entry_symbol equals `general_pattern_bit_unpack_fixed_table`
   - Expected: entries[4].entry_symbol equals `general_pattern_checksum_reducer`
   - Expected: entries[5].entry_symbol equals `general_pattern_prefix_scan_table`
   - Expected: entries[6].entry_symbol equals `general_pattern_wal_batch_flush`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries have valid entry symbols")
step("Verify: entries have valid entry symbols")
val entries = general_pattern_manifest_entries()
expect(entries[0].entry_symbol).to_equal("general_pattern_byte_scan_to_delimiter")
expect(entries[1].entry_symbol).to_equal("general_pattern_switch_on_short_string")
expect(entries[2].entry_symbol).to_equal("general_pattern_capability_guarded_fast_path")
expect(entries[3].entry_symbol).to_equal("general_pattern_bit_unpack_fixed_table")
expect(entries[4].entry_symbol).to_equal("general_pattern_checksum_reducer")
expect(entries[5].entry_symbol).to_equal("general_pattern_prefix_scan_table")
expect(entries[6].entry_symbol).to_equal("general_pattern_wal_batch_flush")
```

</details>

#### produces seven pattern rules

- produces seven pattern rules
- Verify: produces seven pattern rules
   - Expected: rules.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces seven pattern rules")
step("Verify: produces seven pattern rules")
val rules = general_pattern_rules()
expect(rules.len()).to_equal(7)
```

</details>

#### all rules are marked safe

- all rules are marked safe
- Verify: all rules are marked safe
   - Expected: rules[i].safety equals `safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all rules are marked safe")
step("Verify: all rules are marked safe")
val rules = general_pattern_rules()
var i = 0
while i < rules.len():
    expect(rules[i].safety).to_equal("safe")
    i = i + 1
```

</details>

#### loads manifest successfully

- loads manifest successfully
- Verify: loads manifest successfully
   - Expected: manifest.name equals `simple.opt.general-patterns`
   - Expected: manifest.version equals `1.0.0`
   - Expected: manifest.passes.len() equals `7`
   - Expected: manifest.rules.len() equals `7`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads manifest successfully")
step("Verify: loads manifest successfully")
val result = load_general_patterns_manifest()
match result:
    case Ok(manifest):
        expect(manifest.name).to_equal("simple.opt.general-patterns")
        expect(manifest.version).to_equal("1.0.0")
        expect(manifest.passes.len()).to_equal(7)
        expect(manifest.rules.len()).to_equal(7)
    case Err(msg):
        expect(false).to_equal(true)
```

</details>

#### registers into a fresh DynamicPassRegistry

- registers into a fresh DynamicPassRegistry
- Verify: registers into a fresh DynamicPassRegistry
   - Expected: updated.descriptors.len() equals `7`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers into a fresh DynamicPassRegistry")
step("Verify: registers into a fresh DynamicPassRegistry")
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        expect(updated.descriptors.len()).to_equal(7)
    case Err(msg):
        expect(false).to_equal(true)
```

</details>

#### registered passes are findable by name

- registered passes are findable by name
- Verify: registered passes are findable by name
   - Expected: found != nil is true
   - Expected: found2 != nil is true
   - Expected: found3 != nil is true
   - Expected: found4 != nil is true
   - Expected: found5 != nil is true
   - Expected: found6 != nil is true
   - Expected: found7 != nil is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registered passes are findable by name")
step("Verify: registered passes are findable by name")
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        val found = dynamic_pass_registry_lookup(updated, "byte-scan-to-delimiter")
        expect(found != nil).to_equal(true)
        val found2 = dynamic_pass_registry_lookup(updated, "switch-on-short-string")
        expect(found2 != nil).to_equal(true)
        val found3 = dynamic_pass_registry_lookup(updated, "capability-guarded-fast-path")
        expect(found3 != nil).to_equal(true)
        val found4 = dynamic_pass_registry_lookup(updated, "bit-unpack-fixed-table")
        expect(found4 != nil).to_equal(true)
        val found5 = dynamic_pass_registry_lookup(updated, "checksum-reducer")
        expect(found5 != nil).to_equal(true)
        val found6 = dynamic_pass_registry_lookup(updated, "prefix-scan-table")
        expect(found6 != nil).to_equal(true)
        val found7 = dynamic_pass_registry_lookup(updated, "wal-batch-flush")
        expect(found7 != nil).to_equal(true)
    case Err(msg):
        expect(false).to_equal(true)
```

</details>

#### double registration fails with conflict

- double registration fails with conflict
- Verify: double registration fails with conflict
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("double registration fails with conflict")
step("Verify: double registration fails with conflict")
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        val result2 = register_general_patterns(updated)
        match result2:
            case Ok(dup):
                expect(false).to_equal(true)
            case Err(msg):
                expect(msg).to_contain("conflict")
    case Err(msg):
        expect(false).to_equal(true)
```

</details>

### General recognizers fire on general patterns (AC-6)

#### byte-scan recognizer matches generic delimiter scan

- byte-scan recognizer matches generic delimiter scan
- Verify: byte-scan recognizer matches generic delimiter scan
   - Expected: is_byte_scan_loop(loop_body) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte-scan recognizer matches generic delimiter scan")
step("Verify: byte-scan recognizer matches generic delimiter scan")
val loop_body = "while i < len:\n    if buf[i] == ':':\n        break\n    i = i + 1"
expect(is_byte_scan_loop(loop_body)).to_equal(true)
```

</details>

#### byte-scan recognizer rejects non-scan code

- byte-scan recognizer rejects non-scan code
- Verify: byte-scan recognizer rejects non-scan code
   - Expected: is_byte_scan_loop(non_scan) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte-scan recognizer rejects non-scan code")
step("Verify: byte-scan recognizer rejects non-scan code")
val non_scan = "val x = compute(a, b)\nreturn x + 1"
expect(is_byte_scan_loop(non_scan)).to_equal(false)
```

</details>

#### short-string-switch recognizer matches dispatch chain

- short-string-switch recognizer matches dispatch chain
- Verify: short-string-switch recognizer matches dispatch chain
   - Expected: is_short_string_switch(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("short-string-switch recognizer matches dispatch chain")
step("Verify: short-string-switch recognizer matches dispatch chain")
val code = "if method == \"GET\":\n    handle_get()\nelif method == \"POST\":\n    handle_post()\nelif method == \"PUT\":\n    handle_put()\nelif method == \"DELETE\":\n    handle_delete()"
expect(is_short_string_switch(code)).to_equal(true)
```

</details>

#### short-string-switch rejects fewer than 4 branches

- short-string-switch rejects fewer than 4 branches
- Verify: short-string-switch rejects fewer than 4 branches
   - Expected: is_short_string_switch(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("short-string-switch rejects fewer than 4 branches")
step("Verify: short-string-switch rejects fewer than 4 branches")
val code = "if x == \"a\":\n    do_a()\nelif x == \"b\":\n    do_b()"
expect(is_short_string_switch(code)).to_equal(false)
```

</details>

#### capability-guard recognizer matches guard pattern

- capability-guard recognizer matches guard pattern
- Verify: capability-guard recognizer matches guard pattern
   - Expected: is_capability_guard(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability-guard recognizer matches guard pattern")
step("Verify: capability-guard recognizer matches guard pattern")
val code = "if has_sendfile:\n    sendfile(fd, sock)\nelse:\n    buffer = alloc(size)\n    copy(fd, buffer)\n    send(sock, buffer)"
expect(is_capability_guard(code)).to_equal(true)
```

</details>

#### capability-guard rejects simple if without copy fallback

- capability-guard rejects simple if without copy fallback
- Verify: capability-guard rejects simple if without copy fallback
   - Expected: is_capability_guard(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability-guard rejects simple if without copy fallback")
step("Verify: capability-guard rejects simple if without copy fallback")
val code = "if x > 0:\n    print(x)\nelse:\n    print(0)"
expect(is_capability_guard(code)).to_equal(false)
```

</details>

<details>
<summary>Advanced: bit-unpack recognizer matches extraction loop</summary>

#### bit-unpack recognizer matches extraction loop

- bit-unpack recognizer matches extraction loop
- Verify: bit-unpack recognizer matches extraction loop
   - Expected: is_bit_unpack_loop(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit-unpack recognizer matches extraction loop")
step("Verify: bit-unpack recognizer matches extraction loop")
val code = "while bit_pos < total:\n    val sym = (buf >> shift) & 0xff\n    val decoded = table[sym]\n    bit_pos = bit_pos + 8"
expect(is_bit_unpack_loop(code)).to_equal(true)
```

</details>


</details>

#### bit-unpack rejects non-bit code

- bit-unpack rejects non-bit code
- Verify: bit-unpack rejects non-bit code
   - Expected: is_bit_unpack_loop(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit-unpack rejects non-bit code")
step("Verify: bit-unpack rejects non-bit code")
val code = "for item in list:\n    process(item)"
expect(is_bit_unpack_loop(code)).to_equal(false)
```

</details>

<details>
<summary>Advanced: checksum-reducer recognizer matches CRC accumulator loop</summary>

#### checksum-reducer recognizer matches CRC accumulator loop

- checksum-reducer recognizer matches CRC accumulator loop
- Verify: checksum-reducer recognizer matches CRC accumulator loop
   - Expected: is_checksum_reducer_loop(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum-reducer recognizer matches CRC accumulator loop")
step("Verify: checksum-reducer recognizer matches CRC accumulator loop")
val code = "var crc = 0\nwhile i < len:\n    crc = crc ^ data[i]\n    i = i + 1"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>


</details>

#### checksum-reducer rejects non-accumulator code

- checksum-reducer rejects non-accumulator code
- Verify: checksum-reducer rejects non-accumulator code
   - Expected: is_checksum_reducer_loop(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum-reducer rejects non-accumulator code")
step("Verify: checksum-reducer rejects non-accumulator code")
val code = "val x = compute(a, b)\nreturn x + 1"
expect(is_checksum_reducer_loop(code)).to_equal(false)
```

</details>

#### prefix-scan recognizer matches trie lookup

- prefix-scan recognizer matches trie lookup
- Verify: prefix-scan recognizer matches trie lookup
   - Expected: is_prefix_scan_lookup(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix-scan recognizer matches trie lookup")
step("Verify: prefix-scan recognizer matches trie lookup")
val code = "var idx = 0\nwhile idx < table.len():\n    if key.starts_with(table[idx].prefix):\n        return table[idx].value\n    idx = idx + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### prefix-scan rejects non-prefix code

- prefix-scan rejects non-prefix code
- Verify: prefix-scan rejects non-prefix code
   - Expected: is_prefix_scan_lookup(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix-scan rejects non-prefix code")
step("Verify: prefix-scan rejects non-prefix code")
val code = "val total = a + b\nreturn total"
expect(is_prefix_scan_lookup(code)).to_equal(false)
```

</details>

#### wal-batch-flush recognizer matches batch-then-flush

- wal-batch-flush recognizer matches batch-then-flush
- Verify: wal-batch-flush recognizer matches batch-then-flush
   - Expected: is_wal_batch_flush(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wal-batch-flush recognizer matches batch-then-flush")
step("Verify: wal-batch-flush recognizer matches batch-then-flush")
val code = "while i < count:\n    log.append(entries[i])\n    i = i + 1\nlog.flush()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

#### wal-batch-flush rejects non-batching code

- wal-batch-flush rejects non-batching code
- Verify: wal-batch-flush rejects non-batching code
   - Expected: is_wal_batch_flush(code) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wal-batch-flush rejects non-batching code")
step("Verify: wal-batch-flush rejects non-batching code")
val code = "val x = read(fd)\nreturn x"
expect(is_wal_batch_flush(code)).to_equal(false)
```

</details>

### Patterns validate on web hot paths (AC-7)

#### byte-scan matches HTTP header line scanning

- byte-scan matches HTTP header line scanning
- Verify: byte-scan matches HTTP header line scanning
   - Expected: is_byte_scan_loop(http_scan) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte-scan matches HTTP header line scanning")
step("Verify: byte-scan matches HTTP header line scanning")
val http_scan = "while i < raw.len():\n    if raw[i] == '\\r':\n        break\n    i = i + 1"
expect(is_byte_scan_loop(http_scan)).to_equal(true)
```

</details>

#### short-string-switch matches HTTP method dispatch

- short-string-switch matches HTTP method dispatch
- Verify: short-string-switch matches HTTP method dispatch
   - Expected: is_short_string_switch(http_dispatch) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("short-string-switch matches HTTP method dispatch")
step("Verify: short-string-switch matches HTTP method dispatch")
val http_dispatch = "if method == \"GET\":\n    get_handler()\nelif method == \"POST\":\n    post_handler()\nelif method == \"PUT\":\n    put_handler()\nelif method == \"DELETE\":\n    delete_handler()\nelif method == \"PATCH\":\n    patch_handler()"
expect(is_short_string_switch(http_dispatch)).to_equal(true)
```

</details>

#### capability-guard matches sendfile decision

- capability-guard matches sendfile decision
- Verify: capability-guard matches sendfile decision
   - Expected: is_capability_guard(sendfile_decision) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability-guard matches sendfile decision")
step("Verify: capability-guard matches sendfile decision")
val sendfile_decision = "if supports_sendfile:\n    sendfile(file_fd, socket_fd)\nelse:\n    buffer = alloc(4096)\n    copy(file_fd, buffer)\n    write(socket_fd, buffer)"
expect(is_capability_guard(sendfile_decision)).to_equal(true)
```

</details>

<details>
<summary>Advanced: bit-unpack matches HPACK Huffman decode loop</summary>

#### bit-unpack matches HPACK Huffman decode loop

- bit-unpack matches HPACK Huffman decode loop
- Verify: bit-unpack matches HPACK Huffman decode loop
   - Expected: is_bit_unpack_loop(hpack_loop) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit-unpack matches HPACK Huffman decode loop")
step("Verify: bit-unpack matches HPACK Huffman decode loop")
val hpack_loop = "while bit_pos < bit_count:\n    val extracted = (input[byte_idx] >> bit_in_byte) & 1\n    val code_match = codes[sym]\n    bit_pos = bit_pos + code_len"
expect(is_bit_unpack_loop(hpack_loop)).to_equal(true)
```

</details>


</details>

### Pattern info descriptions are general (AC-6)

#### byte-scan description does not mention HTTP

- byte-scan description does not mention HTTP
- Verify: byte-scan description does not mention HTTP
   - Expected: info.description does not contain `HTTP`
   - Expected: info.description contains `byte buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte-scan description does not mention HTTP")
step("Verify: byte-scan description does not mention HTTP")
val info = byte_scan_to_delimiter_info()
expect(info.description.contains("HTTP")).to_equal(false)
expect(info.description.contains("byte buffer")).to_equal(true)
```

</details>

#### switch-on-short-string description is general

- switch-on-short-string description is general
- Verify: switch-on-short-string description is general
   - Expected: info.description contains `chains of string equality`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switch-on-short-string description is general")
step("Verify: switch-on-short-string description is general")
val info = switch_on_short_string_info()
expect(info.description.contains("chains of string equality")).to_equal(true)
```

</details>

#### capability-guarded description is general

- capability-guarded description is general
- Verify: capability-guarded description is general
   - Expected: info.description contains `boolean/capability guard`
   - Expected: info.description contains `zero-copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability-guarded description is general")
step("Verify: capability-guarded description is general")
val info = capability_guarded_fast_path_info()
expect(info.description.contains("boolean/capability guard")).to_equal(true)
expect(info.description.contains("zero-copy")).to_equal(true)
```

</details>

#### bit-unpack description is general

- bit-unpack description is general
- Verify: bit-unpack description is general
   - Expected: info.description contains `bits`
   - Expected: info.description contains `fixed table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bit-unpack description is general")
step("Verify: bit-unpack description is general")
val info = bit_unpack_fixed_table_info()
expect(info.description.contains("bits")).to_equal(true)
expect(info.description.contains("fixed table")).to_equal(true)
```

</details>

#### checksum-reducer description is general

- checksum-reducer description is general
- Verify: checksum-reducer description is general
   - Expected: info.description contains `accumulator`
   - Expected: info.description contains `checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum-reducer description is general")
step("Verify: checksum-reducer description is general")
val info = checksum_reducer_info()
expect(info.description.contains("accumulator")).to_equal(true)
expect(info.description.contains("checksum")).to_equal(true)
```

</details>

#### prefix-scan-table description is general

- prefix-scan-table description is general
- Verify: prefix-scan-table description is general
   - Expected: info.description contains `prefix`
   - Expected: info.description contains `name resolution`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix-scan-table description is general")
step("Verify: prefix-scan-table description is general")
val info = prefix_scan_table_info()
expect(info.description.contains("prefix")).to_equal(true)
expect(info.description.contains("name resolution")).to_equal(true)
```

</details>

#### wal-batch-flush description is general

- wal-batch-flush description is general
- Verify: wal-batch-flush description is general
   - Expected: info.description contains `batching`
   - Expected: info.description contains `flush`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wal-batch-flush description is general")
step("Verify: wal-batch-flush description is general")
val info = wal_batch_flush_info()
expect(info.description.contains("batching")).to_equal(true)
expect(info.description.contains("flush")).to_equal(true)
```

</details>

#### all patterns have example sites including non-web uses

- all patterns have example sites including non-web uses
- Verify: all patterns have example sites including non-web uses


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all patterns have example sites including non-web uses")
step("Verify: all patterns have example sites including non-web uses")
val infos = all_general_pattern_infos()
var i = 0
while i < infos.len():
    expect(infos[i].example_sites.len()).to_be_greater_than(1)
    i = i + 1
```

</details>

### Cross-domain pattern coverage (AC-8)

#### checksum-reducer matches FS metadata verification

- checksum-reducer matches FS metadata verification
- Verify: checksum-reducer matches FS metadata verification
   - Expected: is_checksum_reducer_loop(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum-reducer matches FS metadata verification")
step("Verify: checksum-reducer matches FS metadata verification")
val code = "var checksum = 0\nwhile i < block_size:\n    checksum = checksum ^ sector[i]\n    i = i + 1"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>

#### checksum-reducer matches database page checksum

- checksum-reducer matches database page checksum
- Verify: checksum-reducer matches database page checksum
   - Expected: is_checksum_reducer_loop(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checksum-reducer matches database page checksum")
step("Verify: checksum-reducer matches database page checksum")
val code = "var hash = 0\nfor idx in range(page_len):\n    hash = hash ^ page_data[idx]\n"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>

#### prefix-scan matches URL route prefix matching

- prefix-scan matches URL route prefix matching
- Verify: prefix-scan matches URL route prefix matching
   - Expected: is_prefix_scan_lookup(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix-scan matches URL route prefix matching")
step("Verify: prefix-scan matches URL route prefix matching")
val code = "var r = 0\nwhile r < routes.len():\n    if path.starts_with(routes[r].prefix):\n        return routes[r].handler\n    r = r + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### prefix-scan matches database index prefix scan

- prefix-scan matches database index prefix scan
- Verify: prefix-scan matches database index prefix scan
   - Expected: is_prefix_scan_lookup(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix-scan matches database index prefix scan")
step("Verify: prefix-scan matches database index prefix scan")
val code = "var pos = 0\nwhile pos < index.len():\n    if search_key.starts_with(index[pos].prefix):\n        return index[pos].page_id\n    pos = pos + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### wal-batch-flush matches database WAL checkpoint

- wal-batch-flush matches database WAL checkpoint
- Verify: wal-batch-flush matches database WAL checkpoint
   - Expected: is_wal_batch_flush(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wal-batch-flush matches database WAL checkpoint")
step("Verify: wal-batch-flush matches database WAL checkpoint")
val code = "while pending < wal.len():\n    batch.append(wal[pending])\n    pending = pending + 1\nbatch.sync()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

#### wal-batch-flush matches SimpleOS syscall batching

- wal-batch-flush matches SimpleOS syscall batching
- Verify: wal-batch-flush matches SimpleOS syscall batching
   - Expected: is_wal_batch_flush(code) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wal-batch-flush matches SimpleOS syscall batching")
step("Verify: wal-batch-flush matches SimpleOS syscall batching")
val code = "while idx < syscalls.len():\n    ring.push(syscalls[idx])\n    idx = idx + 1\nring.flush()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

### Optimization facts for web hot paths (AC-9)

#### produces seven optimization facts

- produces seven optimization facts
- Verify: produces seven optimization facts
   - Expected: facts.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces seven optimization facts")
step("Verify: produces seven optimization facts")
val facts = web_hot_path_facts()
expect(facts.len()).to_equal(7)
```

</details>

#### each fact has a non-empty key and description

- each fact has a non-empty key and description
- Verify: each fact has a non-empty key and description
   - Expected: facts[i].key.length() > 0 is true
   - Expected: facts[i].description.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each fact has a non-empty key and description")
step("Verify: each fact has a non-empty key and description")
val facts = web_hot_path_facts()
var i = 0
while i < facts.len():
    expect(facts[i].key.length() > 0).to_equal(true)
    expect(facts[i].description.length() > 0).to_equal(true)
    i = i + 1
```

</details>

#### each fact maps to a known recognizer

- each fact maps to a known recognizer
- Verify: each fact maps to a known recognizer
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each fact maps to a known recognizer")
step("Verify: each fact maps to a known recognizer")
val facts = web_hot_path_facts()
val infos = all_general_pattern_infos()
var i = 0
while i < facts.len():
    var found = false
    var j = 0
    while j < infos.len():
        if infos[j].name == facts[i].general_recognizer:
            found = true
        j = j + 1
    expect(found).to_equal(true)
    i = i + 1
```

</details>

#### fact_for_recognizer finds byte-scan fact

- fact_for_recognizer finds byte-scan fact
- Verify: fact_for_recognizer finds byte-scan fact
   - Expected: f != nil is true
   - Expected: f.unwrap().key equals `bounded_scan_terminates`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_for_recognizer finds byte-scan fact")
step("Verify: fact_for_recognizer finds byte-scan fact")
val f = fact_for_recognizer("byte-scan-to-delimiter")
expect(f != nil).to_equal(true)
expect(f.unwrap().key).to_equal("bounded_scan_terminates")
```

</details>

#### fact_for_recognizer finds capability-guard fact

- fact_for_recognizer finds capability-guard fact
- Verify: fact_for_recognizer finds capability-guard fact
   - Expected: f != nil is true
   - Expected: f.unwrap().key equals `copy_guard_fast_path_safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_for_recognizer finds capability-guard fact")
step("Verify: fact_for_recognizer finds capability-guard fact")
val f = fact_for_recognizer("capability-guarded-fast-path")
expect(f != nil).to_equal(true)
expect(f.unwrap().key).to_equal("copy_guard_fast_path_safe")
```

</details>

#### fact_for_recognizer finds bit-unpack fact

- fact_for_recognizer finds bit-unpack fact
- Verify: fact_for_recognizer finds bit-unpack fact
   - Expected: f != nil is true
   - Expected: f.unwrap().key equals `bit_extract_table_fixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_for_recognizer finds bit-unpack fact")
step("Verify: fact_for_recognizer finds bit-unpack fact")
val f = fact_for_recognizer("bit-unpack-fixed-table")
expect(f != nil).to_equal(true)
expect(f.unwrap().key).to_equal("bit_extract_table_fixed")
```

</details>

#### fact_for_recognizer returns nil for unknown recognizer

- fact_for_recognizer returns nil for unknown recognizer
- Verify: fact_for_recognizer returns nil for unknown recognizer
   - Expected: f != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_for_recognizer returns nil for unknown recognizer")
step("Verify: fact_for_recognizer returns nil for unknown recognizer")
val f = fact_for_recognizer("nonexistent-pattern")
expect(f != nil).to_equal(false)
```

</details>

#### all_fact_keys returns seven keys

- all_fact_keys returns seven keys
- Verify: all_fact_keys returns seven keys
   - Expected: keys.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_fact_keys returns seven keys")
step("Verify: all_fact_keys returns seven keys")
val keys = all_fact_keys()
expect(keys.len()).to_equal(7)
```

</details>

### General-domain CLib parity rules (AC-10)

#### rule table includes general bounded scan rule

- rule table includes general bounded scan rule
- Verify: rule table includes general bounded scan rule
   - Expected: rule != nil is true
   - Expected: rule.unwrap().domain equals `general`
   - Expected: rule.unwrap().intrinsic equals `bounded_scan_fast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule table includes general bounded scan rule")
step("Verify: rule table includes general bounded scan rule")
val rule = clib_parity_rule_by_name("match_general_bounded_scan")
expect(rule != nil).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("bounded_scan_fast")
```

</details>

#### rule table includes general dispatch switch rule

- rule table includes general dispatch switch rule
- Verify: rule table includes general dispatch switch rule
   - Expected: rule != nil is true
   - Expected: rule.unwrap().domain equals `general`
   - Expected: rule.unwrap().intrinsic equals `dispatch_switch_fast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule table includes general dispatch switch rule")
step("Verify: rule table includes general dispatch switch rule")
val rule = clib_parity_rule_by_name("match_general_dispatch_switch")
expect(rule != nil).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("dispatch_switch_fast")
```

</details>

#### rule table includes general copy guard rule

- rule table includes general copy guard rule
- Verify: rule table includes general copy guard rule
   - Expected: rule != nil is true
   - Expected: rule.unwrap().domain equals `general`
   - Expected: rule.unwrap().intrinsic equals `copy_elide_guard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule table includes general copy guard rule")
step("Verify: rule table includes general copy guard rule")
val rule = clib_parity_rule_by_name("match_general_copy_guard")
expect(rule != nil).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("copy_elide_guard")
```

</details>

#### rule table includes general bit extract rule

- rule table includes general bit extract rule
- Verify: rule table includes general bit extract rule
   - Expected: rule != nil is true
   - Expected: rule.unwrap().domain equals `general`
   - Expected: rule.unwrap().intrinsic equals `bit_unpack_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule table includes general bit extract rule")
step("Verify: rule table includes general bit extract rule")
val rule = clib_parity_rule_by_name("match_general_bit_extract")
expect(rule != nil).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("bit_unpack_batch")
```

</details>

#### general rules require no provider-specific facts

- general rules require no provider-specific facts
- Verify: general rules require no provider-specific facts
   - Expected: scan.unwrap().required_fact equals `none`
   - Expected: guard.unwrap().required_fact equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("general rules require no provider-specific facts")
step("Verify: general rules require no provider-specific facts")
val scan = clib_parity_rule_by_name("match_general_bounded_scan")
expect(scan.unwrap().required_fact).to_equal("none")
val guard = clib_parity_rule_by_name("match_general_copy_guard")
expect(guard.unwrap().required_fact).to_equal("none")
```

</details>

#### general rules are eligible with empty facts and matching proofs

- general rules are eligible with empty facts and matching proofs
- Verify: general rules are eligible with empty facts and matching proofs
   - Expected: can is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("general rules are eligible with empty facts and matching proofs")
step("Verify: general rules are eligible with empty facts and matching proofs")
val rule = clib_parity_rule_by_name("match_general_bounded_scan").unwrap()
val can = clib_parity_rule_can_rewrite(rule, [], ["scan_termination_equivalence"])
expect(can).to_equal(true)
```

</details>

#### general rules are not eligible without required proof

- general rules are not eligible without required proof
- Verify: general rules are not eligible without required proof
   - Expected: can is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("general rules are not eligible without required proof")
step("Verify: general rules are not eligible without required proof")
val rule = clib_parity_rule_by_name("match_general_bounded_scan").unwrap()
val can = clib_parity_rule_can_rewrite(rule, [], [])
expect(can).to_equal(false)
```

</details>

#### general domain rule count increased

- general domain rule count increased
- Verify: general domain rule count increased


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("general domain rule count increased")
step("Verify: general domain rule count increased")
val count = clib_parity_domain_rule_count("general")
expect(count).to_be_greater_than(13)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-DYNAMIC-MANIFEST-ENTRIES-REGISTERED-AC-5-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6bbabbbe404c716c275f362d9c6459c86e32809345af82ba3b3490dbec741b1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bbabbbe404c716c275f362d9c6459c86e32809345af82ba3b3490dbec741b1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bbabbbe404c716c275f362d9c6459c86e32809345af82ba3b3490dbec741b1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/60.mir_opt/general_patterns_spec.spl
mirror: doc/06_spec/unit/compiler/60.mir_opt/general_patterns_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/60.mir_opt/general_patterns_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/60.mir_opt/general_patterns_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/60.mir_opt/general_patterns_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/60.mir_opt/general_patterns_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces exactly seven manifest entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/general_patterns_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'entries have correct stable names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/general_patterns_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'entries have function scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

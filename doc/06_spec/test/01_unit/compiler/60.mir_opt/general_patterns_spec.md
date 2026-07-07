# General MIR Optimization Patterns Specification

> <details>

<!-- sdn-diagram:id=general_patterns_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=general_patterns_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

general_patterns_spec -> std
general_patterns_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=general_patterns_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# General MIR Optimization Patterns Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-5, #AC-6, #AC-7 |
| Category | Compiler / Optimization |
| Difficulty | 4/5 |
| Status | Active |
| Source | `test/01_unit/compiler/60.mir_opt/general_patterns_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Dynamic manifest entries registered (AC-5)

#### produces exactly seven manifest entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = general_pattern_manifest_entries()
expect(entries.len()).to_equal(7)
```

</details>

#### entries have correct stable names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = general_pattern_manifest_entries()
expect(entries.len()).to_equal(7)
```

</details>

#### entries have valid entry symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = general_pattern_rules()
expect(rules.len()).to_equal(7)
```

</details>

#### all rules are marked safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = general_pattern_rules()
var i = 0
while i < rules.len():
    expect(rules[i].safety).to_equal("safe")
    i = i + 1
```

</details>

#### loads manifest successfully

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = load_general_patterns_manifest()
match result:
    case Ok(manifest):
        expect(manifest.name).to_equal("simple.opt.general-patterns")
        expect(manifest.version).to_equal("1.0.0")
        expect(manifest.passes.len()).to_equal(7)
        expect(manifest.rules.len()).to_equal(7)
    case Err(msg):
        fail("load_general_patterns_manifest returned Err: {msg}")
```

</details>

#### registers into a fresh DynamicPassRegistry

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        expect(updated.descriptors.len()).to_equal(7)
    case Err(msg):
        fail("register_general_patterns returned Err: {msg}")
```

</details>

#### registered passes are findable by name

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        val found = dynamic_pass_registry_lookup(updated, "byte-scan-to-delimiter")
        expect(found.?).to_equal(true)
        val found2 = dynamic_pass_registry_lookup(updated, "switch-on-short-string")
        expect(found2.?).to_equal(true)
        val found3 = dynamic_pass_registry_lookup(updated, "capability-guarded-fast-path")
        expect(found3.?).to_equal(true)
        val found4 = dynamic_pass_registry_lookup(updated, "bit-unpack-fixed-table")
        expect(found4.?).to_equal(true)
        val found5 = dynamic_pass_registry_lookup(updated, "checksum-reducer")
        expect(found5.?).to_equal(true)
        val found6 = dynamic_pass_registry_lookup(updated, "prefix-scan-table")
        expect(found6.?).to_equal(true)
        val found7 = dynamic_pass_registry_lookup(updated, "wal-batch-flush")
        expect(found7.?).to_equal(true)
    case Err(msg):
        fail("register_general_patterns returned Err before lookup checks: {msg}")
```

</details>

#### double registration fails with conflict

- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = dynamic_pass_registry_new()
val result = register_general_patterns(registry)
match result:
    case Ok(updated):
        val result2 = register_general_patterns(updated)
        match result2:
            case Ok(dup):
                fail("double registration unexpectedly succeeded")
            case Err(msg):
                expect(msg).to_contain("conflict")
    case Err(msg):
        fail("initial general-pattern registration returned Err: {msg}")
```

</details>

### General recognizers fire on general patterns (AC-6)

#### byte-scan recognizer matches generic delimiter scan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_body = "while i < len:\n    if buf[i] == ':':\n        break\n    i = i + 1"
expect(is_byte_scan_loop(loop_body)).to_equal(true)
```

</details>

#### byte-scan recognizer rejects non-scan code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_scan = "val x = compute(a, b)\nreturn x + 1"
expect(is_byte_scan_loop(non_scan)).to_equal(false)
```

</details>

#### short-string-switch recognizer matches dispatch chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if method == \"GET\":\n    handle_get()\nelif method == \"POST\":\n    handle_post()\nelif method == \"PUT\":\n    handle_put()\nelif method == \"DELETE\":\n    handle_delete()"
expect(is_short_string_switch(code)).to_equal(true)
```

</details>

#### short-string-switch rejects fewer than 4 branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if x == \"a\":\n    do_a()\nelif x == \"b\":\n    do_b()"
expect(is_short_string_switch(code)).to_equal(false)
```

</details>

#### capability-guard recognizer matches guard pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if has_sendfile:\n    sendfile(fd, sock)\nelse:\n    buffer = alloc(size)\n    copy(fd, buffer)\n    send(sock, buffer)"
expect(is_capability_guard(code)).to_equal(true)
```

</details>

#### capability-guard rejects simple if without copy fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "if x > 0:\n    print(x)\nelse:\n    print(0)"
expect(is_capability_guard(code)).to_equal(false)
```

</details>

<details>
<summary>Advanced: bit-unpack recognizer matches extraction loop</summary>

#### bit-unpack recognizer matches extraction loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "while bit_pos < total:\n    val sym = (buf >> shift) & 0xff\n    val decoded = table[sym]\n    bit_pos = bit_pos + 8"
expect(is_bit_unpack_loop(code)).to_equal(true)
```

</details>


</details>

#### bit-unpack rejects non-bit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "for item in list:\n    process(item)"
expect(is_bit_unpack_loop(code)).to_equal(false)
```

</details>

<details>
<summary>Advanced: checksum-reducer recognizer matches CRC accumulator loop</summary>

#### checksum-reducer recognizer matches CRC accumulator loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var crc = 0\nwhile i < len:\n    crc = crc ^ data[i]\n    i = i + 1"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>


</details>

#### checksum-reducer rejects non-accumulator code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val x = compute(a, b)\nreturn x + 1"
expect(is_checksum_reducer_loop(code)).to_equal(false)
```

</details>

#### prefix-scan recognizer matches trie lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var idx = 0\nwhile idx < table.len():\n    if key.starts_with(table[idx].prefix):\n        return table[idx].value\n    idx = idx + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### prefix-scan rejects non-prefix code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val total = a + b\nreturn total"
expect(is_prefix_scan_lookup(code)).to_equal(false)
```

</details>

#### wal-batch-flush recognizer matches batch-then-flush

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "while i < count:\n    log.append(entries[i])\n    i = i + 1\nlog.flush()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

#### wal-batch-flush rejects non-batching code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val x = read(fd)\nreturn x"
expect(is_wal_batch_flush(code)).to_equal(false)
```

</details>

### Patterns validate on web hot paths (AC-7)

#### byte-scan matches HTTP header line scanning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val http_scan = "while i < raw.len():\n    if raw[i] == '\\r':\n        break\n    i = i + 1"
expect(is_byte_scan_loop(http_scan)).to_equal(true)
```

</details>

#### short-string-switch matches HTTP method dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val http_dispatch = "if method == \"GET\":\n    get_handler()\nelif method == \"POST\":\n    post_handler()\nelif method == \"PUT\":\n    put_handler()\nelif method == \"DELETE\":\n    delete_handler()\nelif method == \"PATCH\":\n    patch_handler()"
expect(is_short_string_switch(http_dispatch)).to_equal(true)
```

</details>

#### capability-guard matches sendfile decision

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sendfile_decision = "if supports_sendfile:\n    sendfile(file_fd, socket_fd)\nelse:\n    buffer = alloc(4096)\n    copy(file_fd, buffer)\n    write(socket_fd, buffer)"
expect(is_capability_guard(sendfile_decision)).to_equal(true)
```

</details>

<details>
<summary>Advanced: bit-unpack matches HPACK Huffman decode loop</summary>

#### bit-unpack matches HPACK Huffman decode loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpack_loop = "while bit_pos < bit_count:\n    val extracted = (input[byte_idx] >> bit_in_byte) & 1\n    val code_match = codes[sym]\n    bit_pos = bit_pos + code_len"
expect(is_bit_unpack_loop(hpack_loop)).to_equal(true)
```

</details>


</details>

### Pattern info descriptions are general (AC-6)

#### byte-scan description does not mention HTTP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = byte_scan_to_delimiter_info()
expect(info.description.contains("HTTP")).to_equal(false)
expect(info.description.contains("byte buffer")).to_equal(true)
```

</details>

#### switch-on-short-string description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = switch_on_short_string_info()
expect(info.description.contains("chains of string equality")).to_equal(true)
```

</details>

#### capability-guarded description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = capability_guarded_fast_path_info()
expect(info.description.contains("boolean/capability guard")).to_equal(true)
expect(info.description.contains("zero-copy")).to_equal(true)
```

</details>

#### bit-unpack description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = bit_unpack_fixed_table_info()
expect(info.description.contains("bits")).to_equal(true)
expect(info.description.contains("fixed table")).to_equal(true)
```

</details>

#### checksum-reducer description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = checksum_reducer_info()
expect(info.description.contains("accumulator")).to_equal(true)
expect(info.description.contains("checksum")).to_equal(true)
```

</details>

#### prefix-scan-table description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = prefix_scan_table_info()
expect(info.description.contains("prefix")).to_equal(true)
expect(info.description.contains("name resolution")).to_equal(true)
```

</details>

#### wal-batch-flush description is general

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = wal_batch_flush_info()
expect(info.description.contains("batching")).to_equal(true)
expect(info.description.contains("flush")).to_equal(true)
```

</details>

#### all patterns have example sites including non-web uses

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val infos = all_general_pattern_infos()
var i = 0
while i < infos.len():
    expect(infos[i].example_sites.len()).to_be_greater_than(1)
    i = i + 1
```

</details>

### Cross-domain pattern coverage (AC-8)

#### checksum-reducer matches FS metadata verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var checksum = 0\nwhile i < block_size:\n    checksum = checksum ^ sector[i]\n    i = i + 1"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>

#### checksum-reducer matches database page checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var hash = 0\nfor idx in range(page_len):\n    hash = hash ^ page_data[idx]\n"
expect(is_checksum_reducer_loop(code)).to_equal(true)
```

</details>

#### prefix-scan matches URL route prefix matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var r = 0\nwhile r < routes.len():\n    if path.starts_with(routes[r].prefix):\n        return routes[r].handler\n    r = r + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### prefix-scan matches database index prefix scan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var pos = 0\nwhile pos < index.len():\n    if search_key.starts_with(index[pos].prefix):\n        return index[pos].page_id\n    pos = pos + 1"
expect(is_prefix_scan_lookup(code)).to_equal(true)
```

</details>

#### wal-batch-flush matches database WAL checkpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "while pending < wal.len():\n    batch.append(wal[pending])\n    pending = pending + 1\nbatch.sync()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

#### wal-batch-flush matches SimpleOS syscall batching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "while idx < syscalls.len():\n    ring.push(syscalls[idx])\n    idx = idx + 1\nring.flush()"
expect(is_wal_batch_flush(code)).to_equal(true)
```

</details>

### Optimization facts for web hot paths (AC-9)

#### produces seven optimization facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = web_hot_path_facts()
expect(facts.len()).to_equal(7)
```

</details>

#### each fact has a non-empty key and description

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = web_hot_path_facts()
var i = 0
while i < facts.len():
    expect(facts[i].key.length() > 0).to_equal(true)
    expect(facts[i].description.length() > 0).to_equal(true)
    i = i + 1
```

</details>

#### each fact maps to a known recognizer

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fact_for_recognizer("byte-scan-to-delimiter")
expect(f.?).to_equal(true)
expect(f.unwrap().key).to_equal("bounded_scan_terminates")
```

</details>

#### fact_for_recognizer finds capability-guard fact

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fact_for_recognizer("capability-guarded-fast-path")
expect(f.?).to_equal(true)
expect(f.unwrap().key).to_equal("copy_guard_fast_path_safe")
```

</details>

#### fact_for_recognizer finds bit-unpack fact

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fact_for_recognizer("bit-unpack-fixed-table")
expect(f.?).to_equal(true)
expect(f.unwrap().key).to_equal("bit_extract_table_fixed")
```

</details>

#### fact_for_recognizer returns nil for unknown recognizer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fact_for_recognizer("nonexistent-pattern")
expect(f.?).to_equal(false)
```

</details>

#### all_fact_keys returns seven keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keys = all_fact_keys()
expect(keys.len()).to_equal(7)
```

</details>

### General-domain CLib parity rules (AC-10)

#### rule table includes general bounded scan rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_bounded_scan")
expect(rule.?).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("bounded_scan_fast")
```

</details>

#### rule table includes general dispatch switch rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_dispatch_switch")
expect(rule.?).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("dispatch_switch_fast")
```

</details>

#### rule table includes general copy guard rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_copy_guard")
expect(rule.?).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("copy_elide_guard")
```

</details>

#### rule table includes general bit extract rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_bit_extract")
expect(rule.?).to_equal(true)
expect(rule.unwrap().domain).to_equal("general")
expect(rule.unwrap().intrinsic).to_equal("bit_unpack_batch")
```

</details>

#### general rules require no provider-specific facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scan = clib_parity_rule_by_name("match_general_bounded_scan")
expect(scan.unwrap().required_fact).to_equal("none")
val guard = clib_parity_rule_by_name("match_general_copy_guard")
expect(guard.unwrap().required_fact).to_equal("none")
```

</details>

#### general rules are eligible with empty facts and matching proofs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_bounded_scan").unwrap()
val can = clib_parity_rule_can_rewrite(rule, [], ["scan_termination_equivalence"])
expect(can).to_equal(true)
```

</details>

#### general rules are not eligible without required proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = clib_parity_rule_by_name("match_general_bounded_scan").unwrap()
val can = clib_parity_rule_can_rewrite(rule, [], [])
expect(can).to_equal(false)
```

</details>

#### general domain rule count increased

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

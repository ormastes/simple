# File Io Specification

> 1. write config

<!-- sdn-diagram:id=file_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Io Specification

## Scenarios

### SDN File I/O System Tests

#### file loading

#### loads and parses SDN file

1. write config
2. Ok
3. expect path text
   - Expected: json contains `8080`
4. Err
5. fail
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
write_config(TEMP_CONFIG)
match SdnDocument.from_file(TEMP_CONFIG):
    Ok(doc):
        expect_path_text(doc, "app.name", "MyService")
        val json = doc.to_json()
        expect(json.contains("8080")).to_equal(true)
    Err(e):
        fail("Load error: " + e.to_string())
file_delete(TEMP_CONFIG)
```

</details>

#### handles missing file

1. Ok
2. fail
3. Err
   - Expected: e.to_string().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match SdnDocument.from_file("/tmp/simple_missing_sdn_file.sdn"):
    Ok(_):
        fail("Should have failed for missing file")
    Err(e):
        expect(e.to_string().len() > 0).to_equal(true)
```

</details>

#### file writing

#### writes document to file

1. Ok
2. Ok
   - Expected: content contains `Alice`
   - Expected: content contains `30`
3. Err
4. fail
5. Err
6. fail
7. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match SdnDocument.parse("name: Alice\nage: 30"):
    Ok(doc):
        match doc.write_file(TEMP_CONFIG):
            Ok(_):
                val content = file_read(TEMP_CONFIG)
                expect(content.contains("Alice")).to_equal(true)
                expect(content.contains("30")).to_equal(true)
            Err(e):
                fail("Write error: " + e.to_string())
    Err(e):
        fail("Parse error: " + e.to_string())
file_delete(TEMP_CONFIG)
```

</details>

#### handles write errors

1. Ok
2. Ok
3. fail
4. Err
   - Expected: e.to_string().len() > 0 is true
5. Err
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match SdnDocument.parse("key: value"):
    Ok(doc):
        match doc.write_file("/nonexistent_directory/simple_file.sdn"):
            Ok(_):
                fail("Should have failed for invalid path")
            Err(e):
                expect(e.to_string().len() > 0).to_equal(true)
    Err(e):
        fail("Parse error: " + e.to_string())
```

</details>

#### modification and persistence

#### modifies and persists changes

1. write config
2. Ok
3. "name": SdnValue text
4. "version": SdnValue text
   - Expected: doc.is_modified() is true
5. Ok
6. Ok
7. expect path text
8. Err
9. fail
10. Err
11. fail
12. Err
13. fail
14. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
write_config(TEMP_CONFIG)
match SdnDocument.from_file(TEMP_CONFIG):
    Ok(mut doc):
        doc.set("app", SdnValue.Dict({
            "name": SdnValue.text("MyService"),
            "version": SdnValue.text("2.0.0")
        }))
        expect(doc.is_modified()).to_equal(true)
        match doc.write_file(TEMP_CONFIG):
            Ok(_):
                match SdnDocument.from_file(TEMP_CONFIG):
                    Ok(reloaded):
                        expect_path_text(reloaded, "app.version", "2.0.0")
                    Err(e):
                        fail("Reload error: " + e.to_string())
            Err(e):
                fail("Write error: " + e.to_string())
    Err(e):
        fail("Load error: " + e.to_string())
file_delete(TEMP_CONFIG)
```

</details>

#### persists scalar updates

1. file write
2. Ok
3. doc set
4. Ok
5. Ok
   - Expected: reloaded.get("a").is_some() is true
6. expect path i64
   - Expected: reloaded.get("c").is_some() is true
7. Err
8. fail
9. Err
10. fail
11. Err
12. fail
13. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file_write(TEMP_CONFIG, "a: 1\nb: 2\nc: 3")
match SdnDocument.from_file(TEMP_CONFIG):
    Ok(mut doc):
        doc.set("b", SdnValue.i32(20))
        match doc.write_file(TEMP_CONFIG):
            Ok(_):
                match SdnDocument.from_file(TEMP_CONFIG):
                    Ok(reloaded):
                        expect(reloaded.get("a").is_some()).to_equal(true)
                        expect_path_i64(reloaded, "b", 20)
                        expect(reloaded.get("c").is_some()).to_equal(true)
                    Err(e):
                        fail("Reload error: " + e.to_string())
            Err(e):
                fail("Write error: " + e.to_string())
    Err(e):
        fail("Load error: " + e.to_string())
file_delete(TEMP_CONFIG)
```

</details>

#### concurrent file operations

#### handles multiple documents from same file

1. write config
2. Ok
3. Ok
   - Expected: doc1.get("app.name") equals `doc2.get("app.name")`
4. Err
5. fail
6. Err
7. fail
8. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
write_config(TEMP_CONFIG)
match SdnDocument.from_file(TEMP_CONFIG):
    Ok(doc1):
        match SdnDocument.from_file(TEMP_CONFIG):
            Ok(doc2):
                expect(doc1.get("app.name")).to_equal(doc2.get("app.name"))
            Err(e):
                fail("Load error for doc2: " + e.to_string())
    Err(e):
        fail("Load error for doc1: " + e.to_string())
file_delete(TEMP_CONFIG)
```

</details>

#### handles large file operations

1. file write
2. Ok
   - Expected: doc.get("key_0").is_some() is true
   - Expected: doc.get("key_50").is_some() is true
   - Expected: doc.get("key_99").is_some() is true
3. Err
4. fail
5. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = ""
for i in 0..100:
    content = content + "key_{i}: value_{i}\n"
file_write(TEMP_LARGE, content)
match SdnDocument.from_file(TEMP_LARGE):
    Ok(doc):
        expect(doc.get("key_0").is_some()).to_equal(true)
        expect(doc.get("key_50").is_some()).to_equal(true)
        expect(doc.get("key_99").is_some()).to_equal(true)
    Err(e):
        fail("Load error: " + e.to_string())
file_delete(TEMP_LARGE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/file_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN File I/O System Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

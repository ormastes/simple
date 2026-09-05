# Feature-document app index specification

> Source-reviewed, manually unverified contract for exact aggregate app-index
> bytes, input ordering, nested behavior counts, status fallback, output path,
> and basename rules.

## Filename extraction

```simple
expect(extract_app_index_filename("test/app/alpha_spec.spl")).to_equal("alpha")
expect(extract_app_index_filename("nested/beta.spl")).to_equal("beta")
expect(extract_app_index_filename("plain")).to_equal("plain")
expect(extract_app_index_filename("nested/")).to_equal("")
```

## Exact nonempty index

Two ordered inputs require `First` before `Second`, status `ready` then `N/A`,
and nested context totals of 2 and 3 behaviors. The paired executable spec
asserts the complete Markdown string, including headers, separator, both rows,
blank lines, final newline, and `{output_dir}/INDEX.md` return value.

```simple
fn _app_info(path: text, title: text, status: text, first_count: i64, second_count: i64) -> FeatureFileInfo:
    var first_its: [ItBlock] = []
    var index = 0
    while index < first_count:
        first_its.push(ItBlock(name: "first {index}", expects: []))
        index = index + 1
    var second_its: [ItBlock] = []
    index = 0
    while index < second_count:
        second_its.push(ItBlock(name: "second {index}", expects: []))
        index = index + 1
    val describe = DescribeBlock(
        name: "describe", doc: "",
        contexts: [
            ContextBlock(name: "first", doc: "", its: first_its),
            ContextBlock(name: "second", doc: "", its: second_its)
        ])
    FeatureFileInfo(
        file_path: path, title: title,
        metadata: FeatureFileMeta(feature_ids: "", category: "", status: status),
        doc_blocks: [], describes: [describe], test_type: "app")

val output_dir = "/tmp/simple_feature_doc_app_index_spec"
val output_path = "{output_dir}/INDEX.md"
val infos = [
    _app_info("tools/first_spec.spl", "First", "ready", 1, 1),
    _app_info("tools/second_spec.spl", "Second", "", 1, 2)
]
val generated = generate_app_index(infos, output_dir)
val markdown = rt_file_read_text(generated)
val expected = "# App Feature Documentation Index\n\n" +
    "CLI and tool system tests with manual-style documentation.\n\n" +
    "**Total commands/tools:** 2\n\n---\n\n" +
    "| Command/Tool | Status | Details |\n" +
    "|-------------|--------|---------|\n" +
    "| [First](first.md) | ready | 2 behaviors |\n" +
    "| [Second](second.md) | N/A | 3 behaviors |\n\n"
expect(generated).to_equal(output_path)
expect(markdown).to_equal(expected)
```

`_app_info` is the paired spec's fixture constructor; it creates one describe
with two contexts containing the requested behavior counts.

## Exact empty index

The paired executable spec requires the fixed heading, zero summary, table
header/separator, no rows, and exact final blank line.

```simple
val output_dir = "/tmp/simple_feature_doc_app_index_empty_spec"
val output_path = "{output_dir}/INDEX.md"
val generated = generate_app_index([], output_dir)
val markdown = rt_file_read_text(generated)
val expected = "# App Feature Documentation Index\n\n" +
    "CLI and tool system tests with manual-style documentation.\n\n" +
    "**Total commands/tools:** 0\n\n---\n\n" +
    "| Command/Tool | Status | Details |\n" +
    "|-------------|--------|---------|\n\n"
expect(generated).to_equal(output_path)
expect(markdown).to_equal(expected)
```

Static source review separately pins append-only fragments plus one `join("")`
and a final-slash slice without whole-path splitting.

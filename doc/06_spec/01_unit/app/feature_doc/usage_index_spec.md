# Feature-document usage index specification

> Source-reviewed and manually unverified contract for stable category/feature
> order, exact summary rows, and allocation-bounded index construction.

## Filename extraction

The paired executable specs require `_spec.spl`, `.spl`, and extensionless
paths to retain the historical stems without splitting the whole path.

```simple
expect(extract_index_filename("test/feature/alpha_spec.spl")).to_equal("alpha")
expect(extract_index_filename("beta.spl")).to_equal("beta")
expect(extract_index_filename("plain")).to_equal("plain")
```

## Stable grouped rendering

Four inputs span `Zeta`, `Alpha`, `Zeta`, and an empty category in that order.
The empty category is rendered as `Uncategorized`. The rendered index
must keep first-category order (`Zeta` before `Alpha`), preserve `First` before
`Third` inside `Zeta`, render exact category counts, apply `N/A`/`-` defaults,
and count nested test cases accurately.

```simple
fn _usage_info(path: text, title: text, category: text, status: text, feature_ids: text, test_count: i64) -> FeatureFileInfo:
    var its: [ItBlock] = []
    var index = 0
    while index < test_count:
        its.push(ItBlock(name: "case {index}", expects: []))
        index = index + 1
    val context = ContextBlock(name: "context", doc: "", its: its)
    val describe = DescribeBlock(name: "describe", doc: "", contexts: [context])
    FeatureFileInfo(
        file_path: path, title: title,
        metadata: FeatureFileMeta(feature_ids: feature_ids, category: category, status: status),
        doc_blocks: [], describes: [describe], test_type: "usage")

val output_dir = "/tmp/simple_feature_doc_usage_index_spec"
val output_path = "{output_dir}/INDEX.md"
val table_header = "| Feature | Status | Feature IDs | Details |\n" +
    "|---------|--------|-------------|---------|\n"
val infos = [
    _usage_info("z/first_spec.spl", "First", "Zeta", "ready", "F-1", 2),
    _usage_info("a/second_spec.spl", "Second", "Alpha", "", "", 1),
    _usage_info("z/third_spec.spl", "Third", "Zeta", "draft", "F-3", 3),
    _usage_info("other_spec.spl", "Other", "", "", "", 0)
]
val generated = generate_usage_index(infos, output_dir)
val markdown = rt_file_read_text(generated)
val expected = "# Usage Feature Documentation Index\n\n" +
    "Language feature tests with Cucumber-style documentation.\n\n" +
    "**Total features:** 4\n\n---\n\n" +
    "## Zeta (2 features)\n\n" + table_header +
    "| [First](first.md) | ready | F-1 | 1 describes, 2 tests |\n" +
    "| [Third](third.md) | draft | F-3 | 1 describes, 3 tests |\n\n" +
    "## Alpha (1 features)\n\n" + table_header +
    "| [Second](second.md) | N/A | - | 1 describes, 1 tests |\n\n" +
    "## Uncategorized (1 features)\n\n" + table_header +
    "| [Other](other.md) | N/A | - | 1 describes, 0 tests |\n\n"
expect(generated).to_equal(output_path)
expect(markdown).to_equal(expected)
```

The executable spec spells `table_header` inline as the exact two Markdown
table lines; it is abbreviated above only for readability.

## Empty input

```simple
val output_dir = "/tmp/simple_feature_doc_usage_index_empty_spec"
val output_path = "{output_dir}/INDEX.md"
val generated = generate_usage_index([], output_dir)
val markdown = rt_file_read_text(generated)
val expected = "# Usage Feature Documentation Index\n\n" +
    "Language feature tests with Cucumber-style documentation.\n\n" +
    "**Total features:** 0\n\n---\n\n"
expect(generated).to_equal(output_path)
expect(markdown).to_equal(expected)
```

Static source review separately establishes that Markdown is joined once and
that nested category arrays are mutated through indexed buckets rather than
copied out of dictionary values.

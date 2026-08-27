# Documentation Coverage Single-Scan Specification

Normal terminal, JSON, and Markdown reporting scans every distinct exact
requested or breakdown root string once. A request-local root-index cache preserves duplicate-root
multiplicity in the requested aggregate while reusing `src/lib` facts for both
the historical `std/` and `lib/` rows.

The Pure Simple scanner preserves the former grep definitions: public functions
begin with column-zero `pub fn `; documented functions have an immediately
preceding column-zero `#` line; docstring count is the number of distinct `"""`
lines in the union of every public function's two-line context.

```simple
val source = ("# documented\n" +
    "pub fn first():\n" +
    "\"\"\" first doc line \"\"\"\n" +
    "\"\"\" second doc line \"\"\"\n" +
    "pub fn second():\n" +
    "pub fn adjacent():\n" +
    "    pub fn indented_not_public():\n")
val counts = dc_counts_for_source(source)
expect(counts.total).to_equal(3)
expect(counts.documented).to_equal(1)
expect(counts.with_docstring).to_equal(2)
```

```simple
expect(dc_get_path([]).roots).to_equal(
    ["src/lib", "src/core", "src/lib", "src/app"])
expect(dc_path_roots("src/*")).to_equal(["src/*"])
expect(dc_path_roots("a root with spaces")).to_equal(["a root with spaces"])
expect(dc_get_path(["src/lib src/core src/lib src/app"]).roots).to_equal(
    ["src/lib src/core src/lib src/app"])
```

The built-in default is the only multi-root spelling. A user-supplied path is
one literal root, including spaces; glob, quoting, and shell-word expansion are
intentionally unsupported in normal reports. This removes the former implicit
shell-language and command-injection surface.

The executable fixture also bounds each renderer separately. It requires the
distinct-root loop to push one `dc_scan_root(root)` result, requires requested
aggregation through `root_counts[root_index[root]]`, and requires exactly one
`dc_report_facts(request.roots)` call in each renderer. Each bounded renderer rejects
direct scans, all three legacy count adapters, and process execution.
It also pins root real-path resolution and the recursive resolved-child equality
guard that prevents following directory-entry symlinks or cycles.

The mirrored fixture bounds the cache and renderer bodies, requires one scan
call site after distinct-root indexing and one fact request in each normal
renderer, and excludes process/count adapters from those renderers. `--missing`
remains a separate compatibility path. No manual execution, timing, subprocess,
byte-read, or RSS measurement was performed under the user override.

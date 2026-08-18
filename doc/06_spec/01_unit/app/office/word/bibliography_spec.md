# bibliography_spec

> Word Citations & Bibliography spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bibliography_spec

Word Citations & Bibliography spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word/bibliography_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Word Citations & Bibliography spec.

Ground truth (hand-computed):
- Sources: Smith2020(author "Smith, John", title "Systems", year "2020",
  publisher "ACME"); Adams2019(author "Adams, Beth", title "Design",
  year "2019", publisher "Wiley").
- in_text_citation(Smith2020) == "(Smith, 2020)" (last name = text before
  first comma in author); unknown tag "Nope" == "(??)".
- bibliography_entries_apa sorts ascending by author last name: "Adams" <
  "Smith", so Adams2019's entry comes first:
  ["Adams, Beth (2019). Design. Wiley.", "Smith, John (2020). Systems. ACME."]
- bibliography_render_html wraps the sorted APA entries in
  <ol class="bibliography"> with one <li> per entry, and escapes "<" in
  titles to "&lt;".
- source_count == 2.

## Scenarios

### in_text_citation: parenthetical citation by tag

#### renders (LastName, year) for a known tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
expect(in_text_citation(bib, "Smith2020")).to_equal("(Smith, 2020)")
```

</details>

#### renders the other known source's citation too

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
expect(in_text_citation(bib, "Adams2019")).to_equal("(Adams, 2019)")
```

</details>

#### renders (??) for an unknown tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
expect(in_text_citation(bib, "Nope")).to_equal("(??)")
```

</details>

### bibliography_entries_apa: sorted APA-ish reference lines

#### sorts entries ascending by author last name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
val entries = bibliography_entries_apa(bib)
expect(entries.len()).to_equal(2)
expect(entries[0]).to_equal("Adams, Beth (2019). Design. Wiley.")
expect(entries[1]).to_equal("Smith, John (2020). Systems. ACME.")
```

</details>

### bibliography_render_html: HTML ordered list

#### contains the <ol> wrapper and two <li> items

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
val html = bibliography_render_html(bib)
expect(html).to_contain("<ol")
expect(html).to_contain("<li>Adams, Beth (2019). Design. Wiley.</li>")
expect(html).to_contain("<li>Smith, John (2020). Systems. ACME.</li>")
```

</details>

#### contains both titles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
val html = bibliography_render_html(bib)
expect(html).to_contain("Systems")
expect(html).to_contain("Design")
```

</details>

#### escapes < in a title to &lt;

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsafe_source = source_new("X2021", "Xu, Amy", "A <script> Tag", "2021", "Foo")
var bib = bibliography_new()
bib = bibliography_add(bib, unsafe_source)
val html = bibliography_render_html(bib)
expect(html).to_contain("A &lt;script&gt; Tag")
```

</details>

### source_count: number of sources in the bibliography

#### counts both added sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
expect(source_count(bib)).to_equal(2)
```

</details>

#### counts zero for an empty bibliography

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = bibliography_new()
expect(source_count(bib)).to_equal(0)
```

</details>

### deliberate-fail probe (must be fixed to green before landing)

#### confirms Adams sorts before Smith in APA entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bib = _sample_bib()
val entries = bibliography_entries_apa(bib)
# ground truth: "Adams" < "Smith" lexicographically, so Adams'
# entry must be first.
expect(entries[0]).to_contain("Adams")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

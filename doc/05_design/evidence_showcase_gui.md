<!-- codex-design -->
# GUI/Rendered Markdown Design: Evidence Showcase

## Purpose

Define the GitHub and generated-HTML presentation without adding a standalone
showcase application.

## Root page

```text
┌──────────────────────────────────────────────────────────────┐
│ Simple Evidence Showcase                 revision · generated │
│ Receipt-derived truth; statuses are not manually editable.   │
├──────────────────────────────────────────────────────────────┤
│ Review in 30 seconds: choose → read boundary → open proof     │
├──────────────────────────────────────────────────────────────┤
│ live-pass 4 | historical 3 | contract 7 | blocked 5 | ...    │
├──────────────────────────────────────────────────────────────┤
│ Operating systems and hardware                               │
│ Capability | Status | Claim | Target | Proof | Resume         │
│ ...                                                          │
├──────────────────────────────────────────────────────────────┤
│ Web and DB · UI/IDE · LLM · GPU · Protocol · Recent          │
└──────────────────────────────────────────────────────────────┘
```

No remote badge service is used. Optional icons supplement literal status text.

## Still evidence

```text
[descriptive image]
SimpleOS WM after maximize; current x86_64 QEMU frame.
Baseline · diff · receipt · dimensions/checksum
```

PNG/lossless WebP is the pixel oracle. AVIF presentation must include a
PNG/WebP fallback link. SVG is used only for vector-native evidence.

## Motion evidence

Rendered Markdown shows:

1. baseline and final keyframes;
2. ordered event table;
3. transcript link;
4. animated WebP in optional details when compatible; and
5. WebM as a review link.

WebM is not assumed to play in GitHub Markdown and no media autoplays.

## HTML evidence

```text
HTTP 200 · text/html

Selector / attribute assertions
selector | expected | actual | status

Visible text
...

HTML source (folded, escaped)
```html
...
```

[optional still]
```

Captured HTML is never inserted into the page DOM.

## Protocol evidence

```text
Raw bytes: frame.hex.txt

offset | bits | mask | endian | field | actual | expected | status | importance
0      | 7..4 | f0   | big    | ver   | 4      | 4        | PASS   | CRITICAL
```

Field names link to numbered raw-byte lines. Bold/status text accompanies any
visual highlight.

## Manual folding

Visible:

- evidence-at-a-glance;
- primary operator steps;
- structured checks;
- compact still/keyframe evidence.

Folded:

- edge/error/matrix scenarios;
- raw logs and full transcripts;
- reproduction details; and
- executable SSpec.

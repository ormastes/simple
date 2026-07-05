---
id: interp_chained_replace_2026-07-05
status: OPEN
severity: medium
discovered: 2026-07-05
discovered_by: Manual testing in tools/pixel_compare/render_simple_html.spl development
related: tools/pixel_compare/render_simple_html.spl
related: src/lib/common/text/string.spl
---

# Interpreter fails on chained string method calls

## Summary

The interpreter rejects chained calls to string methods: `s.replace(a,b).replace(c,d)` errors with:
```
semantic: method 'replace' not found ... in nested call context
```

Workaround: split into two statements:
```simple
val s2 = s.replace(a, b)
val s3 = s2.replace(c, d)
```

## Evidence

From `tools/pixel_compare/render_simple_html.spl` (lines 37-39), the workaround is currently applied:

```simple
# BUG workaround: chained .replace() not supported in interpreter
val html = text_html.replace("</button>", "}").replace("</div>", "]").replace("<button>", "{").replace("<div>", "[")
# Rewritten as:
val html = text_html.replace("</button>", "}")
val html = html.replace("</div>", "]")
val html = html.replace("<button>", "{")
val html = html.replace("<div>", "[")
```

## Impact

Grammar workaround normalization required by CLAUDE.md. The chained form is a valid expression and should compile; forcing developers to split into multiple statements reduces readability.

## Scope

Interpreter-specific (parsing/semantic analysis of nested method calls in expression context).

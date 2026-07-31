# Linear DOM querySelectorAll Specification

> Executable source:
> `test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl`

This manual proves that the Simple Web DOM `querySelectorAll` owner uses one
iterative preorder traversal and preserves document order. It is source and
semantic evidence only; it does not claim production timing or RSS evidence.

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

### Uses one iterative preorder traversal

1. **Inspect the querySelectorAll traversal owner.**
2. Require one `BeDomNode` stack rooted at the query root.
3. Require stack-pop traversal.
4. Reject recursive child calls and per-child result arrays.

### Preserves exact order for 512 siblings

1. **Build 512 matching siblings in document order.**
2. **Query every matching sibling once.**
3. Require exactly 512 matches.
4. Require every returned `id` to equal its document index from `0` through
   `511`.

### Preserves preorder across a deep chain and siblings

1. **Build a 64-level chain with a preceding sibling at each level.**
2. **Query the mixed tree in preorder.**
3. Require exactly 127 matches.
4. Require `deep-N`, `side-N` order at each level, followed by `deep-63`.

<details>
<summary>Executable SSpec</summary>

```simple
use std.spec.*
use std.io_runtime.{rt_file_read_text}
use std.gc_async_mut.gpu.browser_engine.dom.{BeDomNode}
use std.gc_async_mut.gpu.browser_engine.script.dom_api.{
    document_create_element, document_query_selector_all,
    node_append_child, node_get_attribute, node_set_attribute
}

fn _query_node(node_id: text) -> BeDomNode:
    var node = document_create_element("p")
    node = node_set_attribute(node, "id", node_id)
    node

describe "DOM querySelectorAll linear traversal":
    it "uses one iterative preorder traversal":
        step("Inspect the querySelectorAll traversal owner")
        val source = rt_file_read_text(
            "src/lib/gc_async_mut/gpu/browser_engine/script/dom_api.spl"
        ) ?? ""
        expect(source).to_contain("var stack: [BeDomNode] = [root]")
        expect(source).to_contain("val node = stack.pop()")
        expect(source.contains(
            "document_query_selector_all(root.children[i], sel)"
        )).to_equal(false)
        expect(source.contains(
            "val child_matches = document_query_selector_all"
        )).to_equal(false)

    it "preserves exact order for 512 siblings":
        step("Build 512 matching siblings in document order")
        var root = document_create_element("div")
        var i = 0
        while i < 512:
            root = node_append_child(root, _query_node(i.to_text()))
            i = i + 1
        step("Query every matching sibling once")
        val matches = document_query_selector_all(root, "p")
        expect(matches.len()).to_equal(512)
        i = 0
        while i < matches.len():
            expect(node_get_attribute(matches[i], "id") ?? "").to_equal(
                i.to_text()
            )
            i = i + 1

    it "preserves preorder across a deep chain and siblings":
        step("Build a 64-level chain with a preceding sibling at each level")
        var chain = _query_node("deep-63")
        var depth = 62
        while depth >= 0:
            var parent = _query_node("deep-" + depth.to_text())
            parent = node_append_child(
                parent, _query_node("side-" + depth.to_text())
            )
            parent = node_append_child(parent, chain)
            chain = parent
            depth = depth - 1
        step("Query the mixed tree in preorder")
        val matches = document_query_selector_all(chain, "p")
        expect(matches.len()).to_equal(127)
        depth = 0
        var match_i = 0
        while depth < 63:
            expect(node_get_attribute(
                matches[match_i], "id"
            ) ?? "").to_equal("deep-" + depth.to_text())
            expect(node_get_attribute(
                matches[match_i + 1], "id"
            ) ?? "").to_equal("side-" + depth.to_text())
            depth = depth + 1
            match_i = match_i + 2
        expect(node_get_attribute(
            matches[126], "id"
        ) ?? "").to_equal("deep-63")
```

</details>

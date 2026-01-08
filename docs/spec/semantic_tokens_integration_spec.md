# Multiple tokens across lines

*Source: `./vulkan-backend/simple/std_lib/test/unit/lsp/semantic_tokens_integration_spec.spl`*

---

if parser == none:
                return

            let tree = parser!.parse(code).unwrap()
            let result = st.handle_semantic_tokens_full(tree, code)

            expect(result).to_be_ok()

            let data = result.unwrap()["data"]

            # Multiple tokens across lines
            expect(data.len()).to_be_greater_than(0)

        it("parses class declaration"):
            code = """
            class Point:
                x: i32
                y: i32

                fn new(x: i32, y: i32): Point =
                    Point(x: x, y: y)

if parser == none:
                return

            let tree = parser!.parse(code).unwrap()
            let result = st.handle_semantic_tokens_full(tree, code)

            expect(result).to_be_ok()

            let data = result.unwrap()["data"]

            # Should have many tokens
            expect(data.len()).to_be_greater_than(40)

        it("tokenizes import statements"):
            code = """
            import std.io
            import std.collections as coll
            from std.math import sqrt, pow

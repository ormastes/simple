# LLVM-Direct Minimal C Source Specification

The minimal fallback C generator preserves first-seen non-main function order,
emits one stub and one call per unique name, and always emits exactly one C
`main`. A Simple `main` declaration is intentionally excluded from the helper
list because the generated C shell owns that symbol.

## Exact ordered output

```simple
val source = "fn beta():\nfn main():\nfn alpha():\nfn beta():\n"
val expected = ("#include <stdint.h>\n" +
    "static int beta(void) {\n  return 0;\n}\n" +
    "static int alpha(void) {\n  return 0;\n}\n" +
    "int main(void) {\n" +
    "  (void)beta();\n" +
    "  (void)alpha();\n" +
    "  return 0;\n}\n")
expect(llvm_direct_minimal_c_source(source)).to_equal(expected)
```

## Empty input

```simple
expect(llvm_direct_minimal_c_source("")).to_equal(
    "#include <stdint.h>\nint main(void) {\n  return 0;\n}\n")
```

## Main-presence parity

```simple
val with_main = "fn beta():\nfn main():\nfn alpha():\nfn beta():\n"
val without_main = "fn beta():\nfn alpha():\nfn beta():\n"
expect(llvm_direct_minimal_c_source(without_main)).to_equal(
    llvm_direct_minimal_c_source(with_main))
```

## Structural construction contract

```simple
val implementation = file_read("src/app/compile/llvm_direct.spl")
val start = implementation.index_of(
    "pub fn llvm_direct_minimal_c_source(source: text) -> text:")
val finish = implementation.index_of(
    "pub fn llvm_direct_minimal_c_source_from_simple", start)
val body = implementation.slice(start, finish)
expect(body).to_contain("var seen: {text: bool} = {}")
expect(body).to_contain("seen[name] = true")
expect(body).to_contain("fragments.push(\"static int ")
expect(body).to_contain("fragments.push(\"  (void)")
expect(body.split("fragments.join(\"\")").len()).to_equal(2)
expect(body).not.to_contain("functions.contains(name)")
expect(body).not.to_contain("c = c +")
```

## File adapter ownership

```simple
val implementation = file_read("src/app/compile/llvm_direct.spl")
val start = implementation.index_of(
    "pub fn llvm_direct_minimal_c_source_from_simple")
val finish = implementation.index_of(
    "fn llvm_direct_generated_c_is_textual", start)
val body = implementation.slice(start, finish)
expect(body).to_contain(
    "llvm_direct_minimal_c_source(read_file_text(source_file))")
expect(body.split("read_file_text(source_file)").len()).to_equal(2)
expect(body.split("llvm_direct_minimal_c_source(").len()).to_equal(2)
```

The canonical fixture pins dictionary-backed uniqueness, complete owner-local
fragments, exactly one final join, no linear membership scan, and no growing
immutable C prefix. No manual execution or measurement was performed under the
user override.

# compatibility_spec

*Source: `./vulkan-backend/simple/std_lib/test/unit/sdn/compatibility_spec.spl`*

---

let (matches, diff) = compare_with_rust(input)
            expect matches, "Output differs from Rust:\n${diff}"

        it "matches Rust for data file":
            let input = """
users |id, name, email|
    1, Alice, alice@example.com
    2, Bob, bob@example.com
    3, Carol, carol@example.com

Compare Simple SDN implementation with Rust implementation

    Returns: (matches: Bool, diff: String)

Run Rust SDN CLI to convert SDN to JSON

    Returns JSON output from Rust implementation

Find Rust sdn binary in common locations

    Checks:
    - ./target/debug/sdn
    - ./target/release/sdn
    - PATH (sdn)

Normalize JSON for comparison

    - Parse and re-serialize to canonical form
    - Sort object keys
    - Consistent whitespace

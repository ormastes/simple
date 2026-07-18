<!-- codex-research -->
# External Comparison For Simple Language Article

Date: 2026-06-07

Subject: comparison points for `doc/07_guide/language/simple_language.md`.

## Main Thesis

The article's strongest external positioning is not "Simple invented all these checks." It is "Simple packages known high-assurance techniques into the default workflow for LLM-scale generated code."

That comparison is credible because every major article theme has external precedent:

- Avoiding mocks in high-fidelity tests: Google Testing Blog has long warned against overusing mocks and recommends higher-fidelity dependencies where practical.
- Duplication gates: SonarQube duplication metrics and PMD CPD treat duplication as measurable quality data.
- Architecture constraints: ArchUnit makes architecture rules executable instead of prose-only.
- No-null and option types: Kotlin, Rust, and NullAway show industrial approaches to making absent values explicit.
- Exhaustive matching: Rust's match checking is the clearest mainstream analogy for forcing cases into code.
- Units/newtypes: F# units of measure and Rust newtypes show that domain-specific primitive wrappers prevent same-representation bugs.
- Formal verification: Lean, Dafny, and TLA+ are better comparisons than ordinary static analysis, but at different layers.
- Executable documentation: Python doctest and Rust rustdoc doctests are direct analogues for Simple SDoctest.
- UI test protocol: WebDriver, Playwright, and Testing Library establish the value of driving UI through an observable protocol.

## Useful External References

- Rust option/enums: https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html
- Rust pattern syntax: https://doc.rust-lang.org/book/ch19-03-pattern-syntax.html
- Rust exhaustiveness internals: https://rustc-dev-guide.rust-lang.org/pat-exhaustive-checking.html
- Python doctest: https://docs.python.org/3/library/doctest.html
- Rust doctests: https://doc.rust-lang.org/rustdoc/documentation-tests.html
- ArchUnit user guide: https://www.archunit.org/userguide/html/000_Index.html
- Kotlin null safety: https://kotlinlang.org/docs/null-safety.html
- NullAway: https://www.uber.com/blog/research/nullaway-practical-type-based-null-safety-for-java/
- F# units of measure: https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure
- Rust newtype example: https://doc.rust-lang.org/rust-by-example/generics/new_types.html
- Lean reference: https://lean-lang.org/doc/reference/latest/
- Dafny reference: https://dafny.org/dafny/DafnyRef/DafnyRef
- TLA+ model checking paper: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/Model-Checking-TLA-Specifications.pdf
- W3C WebDriver: https://www.w3.org/TR/webdriver1/
- Playwright assertions: https://playwright.dev/docs/test-assertions
- Testing Library principles: https://testing-library.com/docs/guiding-principles/

## Comparison Notes

### LLM-Generated Code

The external literature is strongest for coding-assistant productivity and local code quality. It is weaker for multi-year maintenance of millions of generated lines. The article should keep the first-person framing and avoid implying a mature research consensus about very large LLM-generated systems.

Best wording: LLMs move the bottleneck from writing code to constraining, verifying, and debugging code.

### Mock Policy

Google's testing guidance supports the article's position that system tests should avoid mocks when fidelity matters. Simple's contribution is making that policy tool-enforced at the SPipe system-test level, with HAL-only/custom exceptions.

### Duplication

SonarQube and CPD show duplication is already an accepted quality signal. Simple's article should emphasize that LLM-scale generation changes the economics: duplication must be a routine gate, not a reviewer observation.

### Architecture Rules

ArchUnit is the closest external analogy. Simple's MDSOC and predicate pointcuts should be framed as architecture-as-code for a language/toolchain, not merely as documentation.

### No Null, Exhaustive Matches, Units, And Newtypes

Rust, Kotlin, NullAway, F# units, and Rust newtypes support the article's argument that whole bug classes can be moved from runtime/review into type or lint systems.

The Simple-specific nuance is important: current evidence supports optional/nil handling and deny-able match-exhaustiveness linting, not a universal always-error high-robustness mode.

### Formal Verification

Lean, Dafny, and TLA+ are useful comparisons but should not be collapsed. Lean is a theorem-proving foundation, Dafny verifies programs against specs, and TLA+ explores system/protocol models. Simple should present Lean integration as a selective supported subset with deterministic artifact management.

### Executable Documentation

Python doctest and Rust rustdoc doctests are direct precedent. Simple's SDoctest claim is strongest when tied to Markdown/source examples plus generated SPipe docs.

### UI Protocol

WebDriver and Playwright establish protocol-driven UI automation. Simple's distinctive claim is unifying repo UI access for web/TUI-web/MCP-style agent workflows, with native GUI still incomplete.

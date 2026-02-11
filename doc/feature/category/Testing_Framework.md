# Testing Framework

| ID | Feature | Description | Pure | Hybrid | LLVM | Status | Spec |
|----|---------|-------------|------|--------|------|--------|------|
| <a id="feature-180"></a>180 | Describe Blocks | BDD describe blocks for grouping related test examples. Creates example groups with descriptions that organize tests hierarchically. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-181"></a>181 | Context Blocks | BDD context blocks for creating nested example groups. Provides conditional grouping with when/with semantics for test organization. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-182"></a>182 | It Examples | BDD it blocks for defining individual test examples. Each it block represents a single test case with description and assertion block. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-183"></a>183 | Before Each Hooks | BDD before_each hooks for running setup code before each test example. Ensures consistent test state and reduces duplication. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-184"></a>184 | After Each Hooks | BDD after_each hooks for running cleanup code after each test example. Ensures resources are released and state is cleaned up. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-187"></a>187 | Expect Matchers | BDD expect/to assertion DSL with composable matchers. Provides readable assertions with clear failure messages. | done | done | done | ✅ done | [spec](../../doc/spec/testing/testing_bdd_framework.md) |
| <a id="feature-192"></a>192 | Doctest | Documentation testing framework that extracts and runs code examples from docstrings. Ensures documentation stays in sync with code. | done | done | done | ✅ done | [spec](../../doc/spec/testing/sdoctest.md) |

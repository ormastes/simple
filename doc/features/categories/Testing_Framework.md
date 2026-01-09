# Testing Framework

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| 180 | Describe Blocks | BDD describe blocks for grouping related test examples. Creates example groups with descriptions that organize tests hierarchically. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 181 | Context Blocks | BDD context blocks for creating nested example groups. Provides conditional grouping with when/with semantics for test organization. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 182 | It Examples | BDD it blocks for defining individual test examples. Each it block represents a single test case with description and assertion block. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 183 | Before Each Hooks | BDD before_each hooks for running setup code before each test example. Ensures consistent test state and reduces duplication. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 184 | After Each Hooks | BDD after_each hooks for running cleanup code after each test example. Ensures resources are released and state is cleaned up. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 187 | Expect Matchers | BDD expect/to assertion DSL with composable matchers. Provides readable assertions with clear failure messages. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| 192 | Doctest | Documentation testing framework that extracts and runs code examples from docstrings. Ensures documentation stays in sync with code. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |

# context_blocks_spec

*Source: `simple/std_lib/test/features/testing_framework/context_blocks_spec.spl`*

---

Context Blocks - Feature #181

Overview:
    BDD context blocks for creating nested example groups. Provides conditional
    grouping with when/with semantics for test organization. Alias for nested
    describe blocks that supports context composition.

Syntax:
    describe "User":
        context "when logged in":
            it "shows dashboard":
                expect(user.dashboard).to be_visible

        context "when admin":
            it "shows admin panel":
                expect(user.admin_panel).to be_visible

Implementation:
    - context creates nested groups inside describe
    - Supports deep nesting for hierarchical organization
    - when prefix for conditional contexts
    - with prefix for fixture contexts
    - Inherits parent scope values
    - Allows value overrides in child contexts

Notes:
    - Alias for nested describe
    - Supports context composition and reusable context definitions
    - Maintains hierarchical structure (Parent > Child)

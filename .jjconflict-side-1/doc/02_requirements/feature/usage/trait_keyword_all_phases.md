# trait keyword all phases
*Source:* `test/feature/usage/trait_keyword_all_phases_spec.spl`

## Feature: Trait Keyword: Phase 1 - Trait detection

### Scenario: basic detection

| # | Example | Status |
|---|---------|--------|
| 1 | trait declaration is recognized | pass |
| 2 | trait name is extracted correctly | pass |
| 3 | trait without methods has empty method list | pass |
| 4 | source with no traits returns empty list | pass |

**Example:** trait declaration is recognized
    Given var src = "trait Display:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(1)
    Then  expect(traits[0].name).to_equal("Display")

**Example:** trait name is extracted correctly
    Given var src = "trait Container:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].name).to_equal("Container")

**Example:** trait without methods has empty method list
    Given var src = "trait Marker:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(1)
    Then  expect(traits[0].methods.len()).to_equal(0)

**Example:** source with no traits returns empty list
    Given var src = "class Foo:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(0)

### Scenario: multiple traits

| # | Example | Status |
|---|---------|--------|
| 1 | finds two traits in source | pass |
| 2 | traits mixed with non-trait declarations are detected | pass |
| 3 | trait with lowercase start is ignored | pass |

**Example:** finds two traits in source
    Given var src = "trait Readable:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(2)
    Then  expect(traits[0].name).to_equal("Readable")
    Then  expect(traits[1].name).to_equal("Writable")

**Example:** traits mixed with non-trait declarations are detected
    Given var src = "class Helper:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(1)
    Then  expect(traits[0].name).to_equal("Sizeable")

**Example:** trait with lowercase start is ignored
    Given var src = "trait myTrait:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits.len()).to_equal(0)

### Scenario: find_trait

| # | Example | Status |
|---|---------|--------|
| 1 | find_trait returns matching trait | pass |
| 2 | find_trait returns empty trait for unknown name | pass |

**Example:** find_trait returns matching trait
    Given var src = "trait Logger:" + NL
    Given val traits = scan_traits(src)
    Given val found = find_trait("Logger", traits)
    Then  expect(found.name).to_equal("Logger")
    Then  expect(found.methods.len()).to_equal(1)

**Example:** find_trait returns empty trait for unknown name
    Given var src = "trait Display:" + NL
    Given val traits = scan_traits(src)
    Given val found = find_trait("Unknown", traits)
    Then  expect(found.name).to_equal("Unknown")
    Then  expect(found.methods.len()).to_equal(0)

## Feature: Trait Keyword: Phase 2 - Method signature extraction

### Scenario: fn methods

| # | Example | Status |
|---|---------|--------|
| 1 | fn method is detected with is_me=false | pass |
| 2 | fn method with return type extracts name correctly | pass |

**Example:** fn method is detected with is_me=false
    Given var src = "trait Inspect:" + NL
    Given val traits = scan_traits(src)
    Given val t = traits[0]
    Then  expect(t.methods[0].name).to_equal("inspect")
    Then  expect(t.methods[0].is_me).to_equal(false)

**Example:** fn method with return type extracts name correctly
    Given var src = "trait Measurable:" + NL
    Given val traits = scan_traits(src)
    Given val t = traits[0]
    Then  expect(t.methods.len()).to_equal(2)
    Then  expect(t.methods[0].name).to_equal("length")
    Then  expect(t.methods[1].name).to_equal("weight")

### Scenario: me methods

| # | Example | Status |
|---|---------|--------|
| 1 | me method is detected with is_me=true | pass |
| 2 | mixed fn and me methods in same trait | pass |

**Example:** me method is detected with is_me=true
    Given var src = "trait Mutable:" + NL
    Given val traits = scan_traits(src)
    Given val t = traits[0]
    Then  expect(t.methods[0].name).to_equal("update")
    Then  expect(t.methods[0].is_me).to_equal(true)

**Example:** mixed fn and me methods in same trait
    Given var src = "trait Repository:" + NL
    Given val traits = scan_traits(src)
    Given val t = traits[0]
    Then  expect(t.methods.len()).to_equal(3)
    Then  expect(t.methods[0].is_me).to_equal(false)
    Then  expect(t.methods[1].is_me).to_equal(true)
    Then  expect(t.methods[2].is_me).to_equal(true)

### Scenario: parameter extraction

| # | Example | Status |
|---|---------|--------|
| 1 | no-arg method has empty param_names | pass |
| 2 | single-param method extracts name | pass |
| 3 | multi-param method extracts all param names | pass |

**Example:** no-arg method has empty param_names
    Given var src = "trait Closeable:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods[0].param_names.len()).to_equal(0)

**Example:** single-param method extracts name
    Given var src = "trait Processor:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods[0].param_names.len()).to_equal(1)
    Then  expect(traits[0].methods[0].param_names[0]).to_equal("item")

**Example:** multi-param method extracts all param names
    Given var src = "trait Transformer:" + NL
    Given val traits = scan_traits(src)
    Given val method = traits[0].methods[0]
    Then  expect(method.param_names.len()).to_equal(3)
    Then  expect(method.param_names[0]).to_equal("input")
    Then  expect(method.param_names[1]).to_equal("count")
    Then  expect(method.param_names[2]).to_equal("flag")

### Scenario: comments and type lines skipped

| # | Example | Status |
|---|---------|--------|
| 1 | comment lines in trait body are skipped | pass |
| 2 | type declaration lines in trait body are skipped | pass |

**Example:** comment lines in trait body are skipped
    Given var src = "trait Iter:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods.len()).to_equal(1)
    Then  expect(traits[0].methods[0].name).to_equal("next")

**Example:** type declaration lines in trait body are skipped
    Given var src = "trait Collection:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods.len()).to_equal(1)
    Then  expect(traits[0].methods[0].name).to_equal("get_item")

## Feature: Trait Keyword: Phase 3 - Default method detection

### Scenario: abstract vs default methods

| # | Example | Status |
|---|---------|--------|
| 1 | method without body has has_default=false | pass |
| 2 | method with multi-line body has has_default=true | pass |
| 3 | method with inline body has has_default=true | pass |

**Example:** method without body has has_default=false
    Given var src = "trait Eq:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods[0].has_default).to_equal(false)

**Example:** method with multi-line body has has_default=true
    Given var src = "trait Eq:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods[0].has_default).to_equal(false)
    Then  expect(traits[0].methods[1].has_default).to_equal(true)

**Example:** method with inline body has has_default=true
    Given var src = "trait StringProvider:" + NL
    Given val traits = scan_traits(src)
    Then  expect(traits[0].methods[0].has_default).to_equal(true)

### Scenario: trait alias forwarding skips default methods

| # | Example | Status |
|---|---------|--------|
| 1 | alias TraitName=field only generates for abstract methods | pass |
| 2 | all-abstract trait generates forwarding for every method | pass |

**Example:** alias TraitName=field only generates for abstract methods
    Given var src = "trait Eq:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn eq(other):")
    Then  expect(out).to_contain("self.inner.eq(other)")
    Given val has_ne = out.contains("self.inner.ne(")
    Then  expect(has_ne).to_equal(false)

**Example:** all-abstract trait generates forwarding for every method
    Given var src = "trait Printable:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn print_text():")
    Then  expect(out).to_contain("self.content.print_text()")
    Then  expect(out).to_contain("fn print_count():")
    Then  expect(out).to_contain("self.content.print_count()")

## Feature: Trait Keyword: Phase 4 - Forwarding

### Scenario: Phase 2: alias fn and alias me

| # | Example | Status |
|---|---------|--------|
| 1 | alias fn generates immutable forwarding method | pass |
| 2 | alias fn with args generates forwarding with parameters | pass |
| 3 | alias me generates mutable forwarding method | pass |

**Example:** alias fn generates immutable forwarding method
    Given var src = "class Wrapper:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn len():")
    Then  expect(out).to_contain("self.inner.len()")

**Example:** alias fn with args generates forwarding with parameters
    Given var src = "class Wrapper:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn get(key, default_val):")
    Then  expect(out).to_contain("self.inner.get(key, default_val)")

**Example:** alias me generates mutable forwarding method
    Given var src = "class Wrapper:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("me push(item):")
    Then  expect(out).to_contain("self.inner.push(item)")

### Scenario: Phase 3: alias TraitName = field

| # | Example | Status |
|---|---------|--------|
| 1 | alias Trait generates fn forwarding for fn methods | pass |
| 2 | alias Trait generates me forwarding for me methods | pass |
| 3 | unknown trait generates no forwarding code | pass |

**Example:** alias Trait generates fn forwarding for fn methods
    Given var src = "trait Sizeable:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn size():")
    Then  expect(out).to_contain("self.items.size()")
    Then  expect(out).to_contain("fn is_empty():")
    Then  expect(out).to_contain("self.items.is_empty()")

**Example:** alias Trait generates me forwarding for me methods
    Given var src = "trait Writable:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("me write(data):")
    Then  expect(out).to_contain("self.buf.write(data)")
    Then  expect(out).to_contain("me clear():")
    Then  expect(out).to_contain("self.buf.clear()")

**Example:** unknown trait generates no forwarding code
    Given var src = "class Wrapper:" + NL
    Given val out = desugar_forwarding(src)
    Given val has_self_inner = out.contains("self.inner.")
    Then  expect(has_self_inner).to_equal(false)

### Scenario: Phase 4: blanket alias field

| # | Example | Status |
|---|---------|--------|
| 1 | alias field_name forwards all methods from field type | pass |

**Example:** alias field_name forwards all methods from field type
    Given var src = "class Storage:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn size():")
    Then  expect(out).to_contain("self.store.size()")
    Then  expect(out).to_contain("me clear():")
    Then  expect(out).to_contain("self.store.clear()")

## Feature: Trait Keyword: Phase 5 - End-to-end usage

### Scenario: complete trait workflow

| # | Example | Status |
|---|---------|--------|
| 1 | define a trait, scan it, use find_trait to retrieve | pass |
| 2 | complete define-implement-forward workflow | pass |
| 3 | multiple traits in source: each generates correct forwarding | pass |
| 4 | trait with default methods: only abstract methods are forwarded | pass |
| 5 | trait scanner and forwarding agree on method count | pass |

**Example:** define a trait, scan it, use find_trait to retrieve
    Given var src = "trait EventHandler:" + NL
    Given val traits = scan_traits(src)
    Given val handler = find_trait("EventHandler", traits)
    Then  expect(handler.name).to_equal("EventHandler")
    Then  expect(handler.methods.len()).to_equal(2)
    Then  expect(handler.methods[0].name).to_equal("on_event")
    Then  expect(handler.methods[0].is_me).to_equal(true)
    Then  expect(handler.methods[1].name).to_equal("handler_name")
    Then  expect(handler.methods[1].is_me).to_equal(false)

**Example:** complete define-implement-forward workflow
    Given var src = "trait Formatter:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn format(value):")
    Then  expect(out).to_contain("self.inner.format(value)")
    Then  expect(out).to_contain("fn name():")
    Then  expect(out).to_contain("self.inner.name()")

**Example:** multiple traits in source: each generates correct forwarding
    Given var src = "trait Readable:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn read():")
    Then  expect(out).to_contain("self.reader.read()")
    Then  expect(out).to_contain("me close():")
    Then  expect(out).to_contain("self.handle.close()")

**Example:** trait with default methods: only abstract methods are forwarded
    Given var src = "trait Comparable:" + NL
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("fn compare_to(other):")
    Then  expect(out).to_contain("self.inner.compare_to(other)")
    Given val has_less = out.contains("self.inner.less_than(")
    Given val has_greater = out.contains("self.inner.greater_than(")
    Then  expect(has_less).to_equal(false)
    Then  expect(has_greater).to_equal(false)

**Example:** trait scanner and forwarding agree on method count
    Given var src = "trait Pipeline:" + NL
    Given val traits = scan_traits(src)
    Given val t = find_trait("Pipeline", traits)
    Then  expect(t.methods.len()).to_equal(3)
    Given val out = desugar_forwarding(src)
    Then  expect(out).to_contain("me run(input):")
    Then  expect(out).to_contain("self.impl.run(input)")
    Then  expect(out).to_contain("fn status():")
    Then  expect(out).to_contain("self.impl.status()")
    Then  expect(out).to_contain("fn name():")
    Then  expect(out).to_contain("self.impl.name()")



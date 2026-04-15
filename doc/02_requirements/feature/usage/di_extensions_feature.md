# di extensions feature
*Source:* `test/feature/usage/di_extensions_feature_spec.spl`

## Feature: DI Extensions Feature: Phase 1 - Basic plugin registration

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can register a plugin by name | pass |
| 2 | can retrieve a registered plugin | pass |
| 3 | unregistered plugin returns nil via resolve_or | pass |
| 4 | unregistered plugin returns default via resolve_or | pass |
| 5 | has returns false for unregistered plugin | pass |
| 6 | has returns true after registration | pass |
| 7 | can register integer plugin value | pass |
| 8 | can register boolean plugin value | pass |

**Example:** can register a plugin by name
    Given val ext = make_ext()
    Then  expect(ext.has("Profiler")).to_equal(true)

**Example:** can retrieve a registered plugin
    Given val ext = make_ext()
    Given val result = ext.resolve("Formatter")
    Then  expect(result).to_equal("fmt-plugin")

**Example:** unregistered plugin returns nil via resolve_or
    Given val ext = make_ext()
    Given val result = ext.resolve_or("MissingPlugin", nil)
    Then  expect(result).to_be_nil()

**Example:** unregistered plugin returns default via resolve_or
    Given val ext = make_ext()
    Given val result = ext.resolve_or("MissingPlugin", "default-value")
    Then  expect(result).to_equal("default-value")

**Example:** has returns false for unregistered plugin
    Given val ext = make_ext()
    Then  expect(ext.has("NotHere")).to_equal(false)

**Example:** has returns true after registration
    Given val ext = make_ext()
    Then  expect(ext.has("MyPlugin")).to_equal(true)

**Example:** can register integer plugin value
    Given val ext = make_ext()
    Given val result = ext.resolve("MaxWorkers")
    Then  expect(result).to_equal(8)

**Example:** can register boolean plugin value
    Given val ext = make_ext()
    Given val result = ext.resolve("DebugMode")
    Then  expect(result).to_equal(true)

## Feature: DI Extensions Feature: Phase 2 - Multiple plugins

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can register multiple independent plugins | pass |
| 2 | plugins do not interfere with each other | pass |
| 3 | can overwrite an existing plugin registration | pass |
| 4 | resolves three plugins independently | pass |
| 5 | factory and instance bindings coexist | pass |
| 6 | resolves two plugins after separate registration | pass |

**Example:** can register multiple independent plugins
    Given val ext = make_ext()
    Then  expect(ext.has("PluginA")).to_equal(true)
    Then  expect(ext.has("PluginB")).to_equal(true)

**Example:** plugins do not interfere with each other
    Given val ext = make_ext()
    Given val other = ext.resolve_or("PluginY", nil)
    Then  expect(other).to_be_nil()
    Given val x = ext.resolve("PluginX")
    Then  expect(x).to_equal("x-value")

**Example:** can overwrite an existing plugin registration
    Given val ext = make_ext()
    Given val result = ext.resolve("Plugin")
    Then  expect(result).to_equal("v2")

**Example:** resolves three plugins independently
    Given val ext = make_ext()
    Then  expect(ext.resolve("A")).to_equal("alpha")
    Then  expect(ext.resolve("B")).to_equal("beta")
    Then  expect(ext.resolve("C")).to_equal("gamma")

**Example:** factory and instance bindings coexist
    Given val ext = make_ext()
    Then  expect(ext.resolve("LazyPlugin")).to_equal("lazy-value")
    Then  expect(ext.resolve("EagerPlugin")).to_equal("eager-value")

**Example:** resolves two plugins after separate registration
    Given val ext = make_ext()
    Given val a = ext.resolve("PluginA")
    Given val b = ext.resolve("PluginB")
    Then  expect(a).to_equal("value-a")
    Then  expect(b).to_equal("value-b")

## Feature: DI Extensions Feature: Phase 3 - Separation from core services

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | extensions container starts empty | pass |
| 2 | extensions container is independent of typed backend port | pass |
| 3 | core services not accessible via extensions | pass |
| 4 | factory-bound extension resolves lazily | pass |
| 5 | profile is preserved on extensions container | pass |

**Example:** extensions container starts empty
    Given val ext = make_ext()
    Then  expect(ext.has("Backend")).to_equal(false)
    Then  expect(ext.has("Logger")).to_equal(false)
    Then  expect(ext.has("AnyPlugin")).to_equal(false)

**Example:** extensions container is independent of typed backend port
    Given val ext = make_ext()
    Given val backend_in_ext = ext.resolve_or("Backend", nil)
    Then  expect(backend_in_ext).to_be_nil()

**Example:** core services not accessible via extensions
    Given val ext = make_ext()
    Given val logger = ext.resolve_or("Logger", nil)
    Given val parser = ext.resolve_or("Parser", nil)
    Given val lexer = ext.resolve_or("Lexer", nil)
    Then  expect(logger).to_be_nil()
    Then  expect(parser).to_be_nil()
    Then  expect(lexer).to_be_nil()

**Example:** factory-bound extension resolves lazily
    Given val ext = make_ext()
    Then  expect(ext.has("LazyPlugin")).to_equal(true)
    Given val result = ext.resolve("LazyPlugin")
    Then  expect(result).to_equal("lazy-created")

**Example:** profile is preserved on extensions container
    Given val ext = DiContainer(bindings: {}, singletons: {}, profile: "prod", all_bindings: [], locked: false)
    Then  expect(ext.profile).to_equal("prod")

## Feature: DI Extensions Feature: Phase 4 - Integration with CompileContext

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | extensions container starts with empty bindings | pass |
| 2 | register_extension adds to extensions (via bind_instance) | pass |
| 3 | get_extension retrieves registered value (via resolve_or) | pass |
| 4 | get_extension returns nil for unregistered (resolve_or nil default) | pass |
| 5 | extensions uses profile from options | pass |
| 6 | extensions starts unlocked | pass |

**Example:** extensions container starts with empty bindings
    Given val extensions = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(extensions.has("AnyPlugin")).to_equal(false)

**Example:** register_extension adds to extensions (via bind_instance)
    Given val extensions = make_ext()
    Then  expect(extensions.has("MyPlugin")).to_equal(true)

**Example:** get_extension retrieves registered value (via resolve_or)
    Given val extensions = make_ext()
    Given val result = extensions.resolve_or("MyPlugin", nil)
    Then  expect(result).to_equal("plugin-value")

**Example:** get_extension returns nil for unregistered (resolve_or nil default)
    Given val extensions = make_ext()
    Given val result = extensions.resolve_or("UnregisteredPlugin", nil)
    Then  expect(result).to_be_nil()

**Example:** extensions uses profile from options
    Given val extensions = DiContainer(bindings: {}, singletons: {}, profile: "test", all_bindings: [], locked: false)
    Then  expect(extensions.profile).to_equal("test")

**Example:** extensions starts unlocked
    Given val extensions = make_ext()
    Then  expect(extensions.is_locked()).to_equal(false)

## Feature: DI Extensions Feature: Phase 5 - Plugin lifecycle

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | plugin registration before lock succeeds | pass |
| 2 | plugin retrieval after lock works | pass |
| 3 | plugin registration after lock fails or is ignored | pass |
| 4 | unlock allows plugin registration again | pass |
| 5 | full plugin lifecycle: register, lock, resolve, unlock, re-register | pass |
| 6 | locked container uses resolve_or for missing plugins | pass |

**Example:** plugin registration before lock succeeds
    Given val ext = make_ext()
    Then  expect(ext.has("LifecyclePlugin")).to_equal(true)

**Example:** plugin retrieval after lock works
    Given val ext = make_ext()
    Given val result = ext.resolve("LifecyclePlugin")
    Then  expect(result).to_equal("before-lock")

**Example:** plugin registration after lock fails or is ignored
    Given val ext = make_ext()
    Then  expect(ext.has("PostLockPlugin")).to_equal(false)

**Example:** unlock allows plugin registration again
    Given val ext = make_ext()
    Then  expect(ext.has("TempPlugin")).to_equal(false)
    Then  expect(ext.has("TempPlugin")).to_equal(true)

**Example:** full plugin lifecycle: register, lock, resolve, unlock, re-register
    Given val ext = make_ext()
    Then  expect(ext.has("CorePlugin")).to_equal(true)
    Given val result = ext.resolve("CorePlugin")
    Then  expect(result).to_equal("core-v1")
    Then  expect(ext.has("NewPlugin")).to_equal(true)

**Example:** locked container uses resolve_or for missing plugins
    Given val ext = make_ext()
    Given val result = ext.resolve_or("MissingPlugin", "default-plugin")
    Then  expect(result).to_equal("default-plugin")



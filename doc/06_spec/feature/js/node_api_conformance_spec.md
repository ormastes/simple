# Node Api Conformance Specification

## Scenarios

### Node.js path module

### path.dirname

#### gets directory name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "/usr/local/bin/node")]))).to_equal("/usr/local/bin")
```

</details>

#### root path

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "/file")]))).to_equal("/")
```

</details>

#### no slash

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_dirname([JsValue.String(v: "file.js")]))).to_equal(".")
```

</details>

### path.basename

#### gets base name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_basename([JsValue.String(v: "/usr/local/bin/node")]))).to_equal("node")
```

</details>

#### strips extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_basename([JsValue.String(v: "/path/file.js"), JsValue.String(v: ".js")]))).to_equal("file")
```

</details>

### path.extname

#### gets extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "file.js")]))).to_equal(".js")
```

</details>

#### no extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "file")]))).to_equal("")
```

</details>

#### multiple dots

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_extname([JsValue.String(v: "archive.tar.gz")]))).to_equal(".gz")
```

</details>

### path.isAbsolute

#### absolute

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_isAbsolute([JsValue.String(v: "/usr/bin")]))).to_equal("true")
```

</details>

#### relative

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_isAbsolute([JsValue.String(v: "src/main.js")]))).to_equal("false")
```

</details>

### path.join

#### joins paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: "bin")]))).to_equal("/usr/local/bin")
```

</details>

#### normalizes joined paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/usr/"), JsValue.String(v: "./local"), JsValue.String(v: "../bin")]))).to_equal("/usr/bin")
```

</details>

#### preserves trailing separator like path.posix.join

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_join([JsValue.String(v: "/foo/"), JsValue.String(v: "bar/")]))).to_equal("/foo/bar/")
```

</details>

### path.resolve

#### resolves relative paths from deterministic root

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_resolve([JsValue.String(v: "tmp"), JsValue.String(v: "simple.js")]))).to_equal("/tmp/simple.js")
```

</details>

#### stops at the rightmost absolute path

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_resolve([JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: "../bin")]))).to_equal("/usr/bin")
```

</details>

#### normalizes empty resolve to deterministic root

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_resolve([]))).to_equal("/")
```

</details>

### path.normalize

#### removes dot and dotdot segments

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo/../bar/./baz")]))).to_equal("bar/baz")
```

</details>

#### preserves root for absolute paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "/foo/../bar")]))).to_equal("/bar")
```

</details>

#### preserves trailing separator like path.posix.normalize

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo//bar//")]))).to_equal("foo/bar/")
```

</details>

#### preserves trailing separator for normalized relative dot result

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(path_normalize([JsValue.String(v: "foo/..//")]))).to_equal("./")
```

</details>

### Node.js process module

### process identity

#### returns a stable Node-like platform

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_platform([]))).to_equal("linux")
```

</details>

#### returns a stable Node-like architecture

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_arch([]))).to_equal("x64")
```

</details>

#### returns a version-shaped string

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_version([]))).to_start_with("v")
```

</details>

### process versions and release

#### returns deterministic process.versions.node

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_node([]))).to_equal("0.0.0-simple")
```

</details>

#### returns deterministic process.versions.v8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_v8([]))).to_equal("simple-js")
```

</details>

#### keeps libuv version typed unavailable until scheduler parity exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_versions_uv([]))).to_equal("unavailable")
```

</details>

#### returns a Node-compatible release name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_release_name([]))).to_equal("node")
```

</details>

#### does not fake release source URLs

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_release_sourceUrl([]))).to_equal("undefined")
```

</details>

#### reports non-LTS for the deterministic Simple compatibility profile

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_release_lts([]))).to_equal("false")
```

</details>

### process working directory and argv

#### uses deterministic cwd when host cwd is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_cwd([]))).to_equal("/")
```

</details>

#### returns a deterministic argv shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = process_argv([])
expect(argv.len()).to_equal(2)
expect(argv[0]).to_equal("simple")
expect(argv[1]).to_equal("")
```

</details>

### process env

#### does not expose ambient host environment

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_env_get([JsValue.String(v: "PATH")]))).to_equal("undefined")
```

</details>

#### keeps missing env keys typed as unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_env_get([JsValue.String(v: "")]))).to_equal("undefined")
```

</details>

### process.nextTick

#### is typed unavailable without runtime scheduler support

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_kind(process_nextTick([]))).to_equal("undefined")
```

</details>

### process.exit

#### returns zero for embedded no-arg exit intent

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_exit([]))).to_equal("0")
```

</details>

#### returns the requested embedded exit code

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(process_exit([JsValue.Number(v: 7.0)]))).to_equal("7")
```

</details>

### Node.js os module

### deterministic os identity

#### returns stable os.platform

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_platform([]))).to_equal("linux")
```

</details>

#### returns stable os.arch

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_arch([]))).to_equal("x64")
```

</details>

#### returns stable os.type

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_type([]))).to_equal("Linux")
```

</details>

#### returns stable os.release

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_release([]))).to_equal("0.0.0-simple")
```

</details>

#### keeps homedir deterministic without leaking host users

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_homedir([]))).to_equal("/")
```

</details>

#### keeps tmpdir deterministic without leaking host paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_tmpdir([]))).to_equal("/tmp")
```

</details>

#### reports deterministic little-endian byte order

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_endianness([]))).to_equal("LE")
```

</details>

#### uses POSIX EOL for the deterministic compatibility profile

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(os_eol([]))).to_equal("\n")
```

</details>

### Node.js Buffer module

### Buffer.byteLength

#### counts utf8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "hello"), JsValue.String(v: "utf8")]))).to_equal("5")
```

</details>

#### counts hex decoded bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex")]))).to_equal("5")
```

</details>

#### counts base64 decoded bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_byteLength([JsValue.String(v: "aGVsbG8="), JsValue.String(v: "base64")]))).to_equal("5")
```

</details>

### Buffer.from(...).toString(...)

#### encodes utf8 input as hex

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "hello"), JsValue.String(v: "utf8"), JsValue.String(v: "hex")]))).to_equal("68656c6c6f")
```

</details>

#### decodes hex input as utf8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

#### decodes multibyte hex input as utf8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "e282ac"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")]))).to_equal("€")
```

</details>

#### replaces invalid utf8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "c328"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")])).char_code_at(0)).to_equal(65533)
```

</details>

#### round trips base64 input to utf8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "aGVsbG8="), JsValue.String(v: "base64"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

#### encodes utf8 input as base64

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_from_toString([JsValue.String(v: "hello"), JsValue.String(v: "utf8"), JsValue.String(v: "base64")]))).to_equal("aGVsbG8=")
```

</details>

### Buffer.concat

#### concatenates byte buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(buffer_concat_toString([JsValue.String(v: "6865"), JsValue.String(v: "hex"), JsValue.String(v: "6c6c6f"), JsValue.String(v: "hex"), JsValue.String(v: "utf8")]))).to_equal("hello")
```

</details>

### NodeBuffer value semantics

#### compares exact byte contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = NodeBuffer.from_text("68656c6c6f", "hex")
val right = NodeBuffer.from_text("hello", "utf8")
expect(left.equals(right)).to_equal(true)
expect(left.length()).to_equal(5)
```

</details>

### Node.js crypto module

### createHash digest

#### computes deterministic sha256 hex digests

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(crypto_createHash_digest([JsValue.String(v: "sha256"), JsValue.String(v: "hello"), JsValue.String(v: "hex")]))).to_equal("2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824")
```

</details>

#### accepts Node-style sha-256 aliases

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(crypto_createHash_digest([JsValue.String(v: "sha-256"), JsValue.String(v: "hello"), JsValue.String(v: "hex")]))).to_equal("2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824")
```

</details>

#### computes deterministic sha1 hex digests

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(crypto_createHash_digest([JsValue.String(v: "sha1"), JsValue.String(v: "hello"), JsValue.String(v: "hex")]))).to_equal("aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d")
```

</details>

#### denies unsupported algorithms

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(crypto_createHash_digest([JsValue.String(v: "md5"), JsValue.String(v: "hello"), JsValue.String(v: "hex")]))).to_equal("denied")
```

</details>

#### reports randomBytes unavailable without secure entropy

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str(crypto_randomBytes_status([JsValue.Number(v: 16.0)]))).to_equal("denied:no-secure-entropy")
```

</details>

### Node.js runtime shape

### String primitives

#### checks prefixes and suffixes through runtime text primitives

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("'simple-runtime'.startsWith('simple')")).to_equal("true")
expect(_eval_str("'simple-runtime'.startsWith('runtime')")).to_equal("false")
expect(_eval_str("'simple-runtime'.endsWith('runtime')")).to_equal("true")
expect(_eval_str("'simple-runtime'.endsWith('simple')")).to_equal("false")
```

</details>

### JSON.parse host path

#### parses JSON objects through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,\"name\":\"simple\"}').ok")).to_equal("true")
```

</details>

#### parses JSON object string properties through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,\"name\":\"simple\"}').name")).to_equal("simple")
```

</details>

#### parses JSON arrays through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('[1,2,3]').length")).to_equal("3")
```

</details>

#### parses JSON array indexes through the runtime allocator

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('[1,2,3]')[1]")).to_equal("2")
```

</details>

#### rejects malformed JSON before JS allocation

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("JSON.parse('{\"ok\":true,}')")).to_equal("error")
```

</details>

### require builtins

#### resolves node:path through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('node:path').join('/usr', 'local', '..', 'bin')")).to_equal("/usr/bin")
```

</details>

#### resolves path alias through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('path').basename('/tmp/simple.js')")).to_equal("simple.js")
```

</details>

#### exposes the POSIX path namespace through require

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('node:path').posix.normalize('foo//bar//')")).to_equal("foo/bar/")
expect(_eval_str("require('path').posix.join('/foo/', 'bar/')")).to_equal("/foo/bar/")
expect(_eval_str("require('node:path').posix.resolve('/usr', 'local', '..', 'bin')")).to_equal("/usr/bin")
```

</details>

#### resolves path and node:path through deterministic root

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('path').resolve('tmp', 'simple.js')")).to_equal("/tmp/simple.js")
expect(_eval_str("require('node:path').resolve('/usr', 'local', '..', 'bin')")).to_equal("/usr/bin")
```

</details>

#### caches builtin modules across repeated require calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var p = require('path'); p.cached = 'yes'; require('node:path').cached")).to_equal("yes")
expect(_eval_str("var b = require('buffer'); b.cached = 'yes'; require('node:buffer').cached")).to_equal("yes")
```

</details>

#### keeps builtin require cache stable on a hot repeated module

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var p = require('path'); p.hot = 0; var q = require('node:path'); q.hot = p.hot + 1; var r = require('path'); r.hot = q.hot + 1; var s = require('node:path'); s.hot = r.hot + 1; require('path').hot")).to_equal("3")
```

</details>

#### denies ungranted CommonJS modules without host filesystem access

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('missing-package').error")).to_equal("module-denied")
expect(_eval_str("require('missing-package').specifier")).to_equal("missing-package")
```

</details>

#### resolves explicitly granted CommonJS text exports without host filesystem access

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_text_export("widget", "name", "panel", "require('widget').name")).to_equal("panel")
expect(_eval_str_with_module_text_export("widget", "name", "panel", "require('missing-package').error")).to_equal("module-denied")
```

</details>

#### caches explicitly granted CommonJS module exports across repeated require calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_text_export("widget", "name", "panel", "var m = require('widget'); m.cached = 'yes'; require('widget').cached")).to_equal("yes")
```

</details>

#### executes explicitly granted CommonJS source exports without host filesystem access

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_source("widget", "exports.name = 'panel'; exports.kind = 'source'", "require('widget').name")).to_equal("panel")
expect(_eval_str_with_module_source("widget", "exports.name = 'panel'; exports.kind = 'source'", "require('widget').kind")).to_equal("source")
```

</details>

#### caches source-executed CommonJS exports across repeated require calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_source("widget", "exports.name = 'panel'", "var m = require('widget'); m.cached = 'yes'; require('widget').cached")).to_equal("yes")
```

</details>

#### honors source-executed CommonJS module.exports replacement

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_source("widget", "module.exports = { name: 'panel', kind: 'replacement' }", "require('widget').name")).to_equal("panel")
expect(_eval_str_with_module_source("widget", "module.exports = { name: 'panel', kind: 'replacement' }", "require('widget').kind")).to_equal("replacement")
```

</details>

#### caches source-executed CommonJS module.exports replacement objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_source("widget", "module.exports = { name: 'panel' }", "var m = require('widget'); m.cached = 'yes'; require('widget').cached")).to_equal("yes")
```

</details>

#### executes explicitly granted slash-bearing CommonJS source specifiers

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_module_source("./widget.js", "exports.name = 'panel'", "require('./widget.js').name")).to_equal("panel")
expect(_eval_str_with_module_source("./widget.js", "exports.dir = __dirname", "require('./widget.js').dir")).to_equal(".")
```

</details>

#### resolves granted CommonJS packages from in-memory node_modules index files

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/node_modules/widget/index.js", "exports.name = 'panel'", "require('widget').name")).to_equal("panel")
expect(_eval_str_with_file("/node_modules/widget/index.js", "exports.filename = __filename", "require('widget').filename")).to_equal("/node_modules/widget/index.js")
```

</details>

#### resolves granted CommonJS packages through package main fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_two_files("/node_modules/widget/package.json", "{\"main\":\"main.js\"}", "/node_modules/widget/main.js", "module.exports = { name: 'panel' }", "require('widget').name")).to_equal("panel")
```

</details>

#### caches granted filesystem-backed CommonJS package exports

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/node_modules/widget/index.js", "exports.name = 'panel'", "var m = require('widget'); m.cached = 'yes'; require('widget').cached")).to_equal("yes")
```

</details>

#### resolves fs sync APIs as fail-closed file API

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('fs').readFileSync")).to_equal("function")
expect(_eval_str("typeof require('node:fs').readFileSync")).to_equal("function")
expect(_eval_str("typeof require('fs').readdirSync")).to_equal("function")
expect(_eval_str("typeof require('node:fs').mkdirSync")).to_equal("function")
```

</details>

#### denies fs sync APIs without file grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('fs').readFileSync('/etc/passwd', 'utf8').status")).to_equal("denied")
expect(_eval_str("require('node:fs').writeFileSync('/tmp/simple.txt', 'data').error")).to_equal("file-denied")
expect(_eval_str("require('fs').existsSync('/tmp/simple.txt').operation")).to_equal("existsSync")
expect(_eval_str("require('fs').statSync('/tmp/simple.txt').path")).to_equal("/tmp/simple.txt")
expect(_eval_str("require('fs').readdirSync('/tmp').status")).to_equal("denied")
expect(_eval_str("require('node:fs').mkdirSync('/tmp/simple').reason")).to_equal("file-grant-denied")
```

</details>

#### denies fs promises APIs without file grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('fs').promises.readFile('/tmp/simple.txt', 'utf8').status")).to_equal("denied")
expect(_eval_str("require('node:fs').promises.writeFile('/tmp/simple.txt', 'data').error")).to_equal("file-denied")
```

</details>

#### allows fs sync APIs only for explicitly granted file paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/work/main.spl", "print('ok')", "require('fs').readFileSync('/home/user/work/main.spl', 'utf8').status")).to_equal("allowed")
expect(_eval_str_with_file("/home/user/work/main.spl", "print('ok')", "require('fs').readFileSync('/home/user/work/main.spl', 'utf8').data")).to_equal("print('ok')")
expect(_eval_str_with_file("/home/user/work/main.spl", "print('ok')", "require('fs').readFileSync('/home/user/workspace/main.spl', 'utf8').reason")).to_equal("file-grant-denied")
expect(_eval_str_with_file("/home/user/work/main.spl", "print('ok')", "require('fs').readFileSync('relative.txt', 'utf8').reason")).to_equal("invalid-path")
```

</details>

#### allows fs write APIs only for explicitly granted file paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/work/main.spl", "", "require('node:fs').writeFileSync('/home/user/work/main.spl', 'new-data').status")).to_equal("allowed")
expect(_eval_str_with_file("/home/user/work/main.spl", "", "require('node:fs').writeFileSync('/home/user/workspace/main.spl', 'new-data').reason")).to_equal("file-grant-denied")
expect(_eval_str_with_file("/home/user/work/main.spl", "", "require('fs').promises.writeFile('/home/user/work/main.spl', 'new-data').status")).to_equal("allowed")
```

</details>

#### applies explicit file grant prefixes in fs compatibility dispatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/native", "", "require('fs').readFileSync('/home/user/native/main.spl', 'utf8').status")).to_equal("allowed")
expect(_eval_str_with_file("/home/user/native", "", "require('fs').readFileSync('/home/user/native2/main.spl', 'utf8').reason")).to_equal("file-grant-denied")
```

</details>

#### shares explicit file grants with parsed native fs module dispatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/native/main.spl", "native-data", "var fs = require('fs'); fs.readFileSync('/home/user/native/main.spl', 'utf8').data")).to_equal("native-data")
expect(_eval_str_with_file("/home/user/native/main.spl", "", "var fs = require('node:fs'); fs.writeFileSync('/home/user/native/main.spl', 'changed'); fs.readFileSync('/home/user/native/main.spl', 'utf8').data")).to_equal("changed")
expect(_eval_str_with_file("/home/user/native/main.spl", "", "var fs = require('fs'); fs.readFileSync('/home/user/native2/main.spl', 'utf8').reason")).to_equal("file-grant-denied")
```

</details>

#### allows fs directory metadata only under explicit file grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs').status")).to_equal("allowed")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs'); var entries = fs.readdirSync('/home/user/work'); entries.firstEntry")).to_equal("logs")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('node:fs'); fs.mkdirSync('/home/user/work/logs'); var entries = fs.readdirSync('/home/user/work'); entries.entryCount")).to_equal("1")
```

</details>

#### returns directory entries as real readdirSync arrays

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs'); var entries = fs.readdirSync('/home/user/work'); entries[0]")).to_equal("logs")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs'); var entries = fs.readdirSync('/home/user/work'); entries.join(',')")).to_equal("logs")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('node:fs'); fs.mkdirSync('/home/user/work/logs'); var entries = fs.readdirSync('/home/user/work'); entries.length")).to_equal("1")
```

</details>

#### creates nested granted directories with recursive mkdirSync

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs/archive', { recursive: true }).recursive")).to_equal("true")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/work/logs/archive', { recursive: true }); fs.readdirSync('/home/user/work').join(',')")).to_equal("logs")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('node:fs'); fs.mkdirSync('/home/user/work/logs/archive', { recursive: true }); fs.readdirSync('/home/user/work/logs')[0]")).to_equal("archive")
expect(_eval_str_with_file("/home/user/work", "", "var fs = require('fs'); fs.mkdirSync('/home/user/workspace/logs', { recursive: true }).reason")).to_equal("file-grant-denied")
```

</details>

#### resolves os and node:os through deterministic require

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('os').platform()")).to_equal("linux")
expect(_eval_str("require('node:os').arch()")).to_equal("x64")
expect(_eval_str("require('os').type()")).to_equal("Linux")
expect(_eval_str("require('node:os').type()")).to_equal("Linux")
expect(_eval_str("require('os').release()")).to_equal("0.0.0-simple")
expect(_eval_str("require('node:os').release()")).to_equal("0.0.0-simple")
expect(_eval_str("require('os').homedir()")).to_equal("/")
expect(_eval_str("require('node:os').homedir()")).to_equal("/")
expect(_eval_str("require('node:os').tmpdir()")).to_equal("/tmp")
expect(_eval_str("require('os').endianness()")).to_equal("LE")
expect(_eval_str("require('node:os').endianness()")).to_equal("LE")
expect(_eval_str("require('os').EOL")).to_equal("\n")
expect(_eval_str("require('node:os').EOL")).to_equal("\n")
```

</details>

#### resolves crypto and node:crypto deterministic hashing

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('crypto').createHash('sha256').update('hello').digest('hex')")).to_equal("2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824")
expect(_eval_str("require('node:crypto').createHash('sha1').update('hello').digest('hex')")).to_equal("aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d")
```

</details>

#### denies unsupported crypto algorithms

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('crypto').createHash('md5').update('hello').digest('hex')")).to_equal("denied")
```

</details>

#### fails closed for crypto.randomBytes until secure entropy is wired

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('crypto').randomBytes(16).status")).to_equal("denied")
expect(_eval_str("require('node:crypto').randomBytes(16).error")).to_equal("no-secure-entropy")
expect(_eval_str("require('crypto').randomBytes(16).byteLength")).to_equal("16")
```

</details>

#### resolves events and node:events EventEmitter constructors

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('events').EventEmitter")).to_equal("function")
expect(_eval_str("typeof require('node:events').EventEmitter")).to_equal("function")
```

</details>

#### tracks EventEmitter listener counts

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); e.on('ready', () => 1); e.listenerCount('ready')")).to_equal("1")
```

</details>

#### reports whether EventEmitter emit found listeners

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); e.emit('missing')")).to_equal("false")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); e.once('ready', () => 1); e.emit('ready')")).to_equal("true")
```

</details>

#### invokes bounded EventEmitter callbacks with emitted arguments

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = 'no'; e.on('ready', (a, b) => { seen = a + ':' + b; }); e.emit('ready', 'ok', 7); seen")).to_equal("ok:7")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = 'no'; e.once('ready', (value) => { seen = value; }); e.emit('ready', 'once'); e.emit('ready', 'twice'); seen + ':' + e.listenerCount('ready')")).to_equal("once:0")
```

</details>

#### removes bounded EventEmitter callbacks by listener identity

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); typeof e.removeListener + ':' + typeof e.off")).to_equal("function:function")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = 'no'; var cb = (value) => { seen = value; }; e.on('ready', cb); var returned = e.removeListener('ready', cb) === e; e.emit('ready', 'late') + ':' + e.listenerCount('ready') + ':' + seen + ':' + returned")).to_equal("false:0:no:true")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = 'no'; var cb = (value) => { seen = value; }; e.on('ready', cb); e.off('ready', cb); e.emit('ready', 'late') + ':' + seen")).to_equal("false:no")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var cb = () => 1; var other = () => 2; e.on('ready', cb); e.removeListener('ready', other); e.listenerCount('ready') + ':' + e.emit('ready')")).to_equal("1:true")
```

</details>

#### emits multiple bounded EventEmitter callbacks in registration order

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = ''; e.on('ready', (v) => { seen = seen + 'a' + v; }); e.on('ready', (v) => { seen = seen + 'b' + v; }); e.emit('ready', 7); seen + ':' + e.listenerCount('ready')")).to_equal("a7b7:2")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = ''; e.once('ready', () => { seen = seen + 'once'; }); e.on('ready', () => { seen = seen + ':on'; }); e.emit('ready'); e.emit('ready'); seen + ':' + e.listenerCount('ready')")).to_equal("once:on:on:1")
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); var seen = ''; var a = () => { seen = seen + 'a'; }; var b = () => { seen = seen + 'b'; }; e.on('ready', a); e.on('ready', b); e.removeListener('ready', a); e.emit('ready'); seen + ':' + e.listenerCount('ready')")).to_equal("b:1")
```

</details>

#### removes EventEmitter listeners by event name

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var EventEmitter = require('events').EventEmitter; var e = new EventEmitter(); e.on('ready', () => 1); e.removeAllListeners('ready'); e.listenerCount('ready')")).to_equal("0")
```

</details>

#### resolves child_process spawn as fail-closed process API

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('child_process').spawn")).to_equal("function")
expect(_eval_str("typeof require('node:child_process').spawn")).to_equal("function")
```

</details>

#### denies child_process spawn without process grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('child_process').spawn('node', ['--version']).status")).to_equal("denied")
expect(_eval_str("require('node:child_process').spawn('node', ['--version']).error")).to_equal("process-denied")
expect(_eval_str("require('child_process').spawn('node', ['--version']).command")).to_equal("node")
```

</details>

#### allows child_process spawn only for explicitly granted commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_process("node", "require('child_process').spawn('node', ['--version']).status")).to_equal("allowed")
expect(_eval_str_with_process("node", "require('node:child_process').spawn('node', ['--version']).pid")).to_equal("1")
expect(_eval_str_with_process("python", "require('child_process').spawn('node', ['--version']).reason")).to_equal("process-grant-denied")
expect(_eval_str_with_process("node", "require('child_process').spawn('node --version').reason")).to_equal("invalid-command")
expect(_eval_str_with_process("git", "require('child_process').spawn('git', ['status']).status")).to_equal("allowed")
expect(_eval_str_with_process("node", "require('child_process').spawn('git', ['status']).reason")).to_equal("process-grant-denied")
```

</details>

#### reports bounded child_process spawn metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_process("node", "var child = require('child_process').spawn('node', ['--version']); child.exitCode + ':' + child.signal + ':' + child.stdout + ':' + child.stderr + ':' + child.argvLength")).to_equal("0::::1")
expect(_eval_str("var child = require('node:child_process').spawn('node', ['--version']); child.exitCode + ':' + child.signal + ':' + child.stdout + ':' + child.stderr + ':' + child.pid")).to_equal("-1::::-1")
expect(_eval_str_with_process("node", "require('child_process').spawn('node --version').exitCode")).to_equal("-1")
```

</details>

#### resolves net and http request APIs as fail-closed network APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('net').Socket")).to_equal("function")
expect(_eval_str("typeof require('node:net').Socket")).to_equal("function")
expect(_eval_str("typeof require('http').request")).to_equal("function")
expect(_eval_str("typeof require('node:https').request")).to_equal("function")
```

</details>

#### denies net and http APIs without network grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('net').createConnection({host:'example.com',port:80}).status")).to_equal("denied")
expect(_eval_str("require('node:net').createConnection(80, 'example.com').error")).to_equal("network-denied")
expect(_eval_str("require('http').request('http://example.com').status")).to_equal("denied")
expect(_eval_str("require('node:https').request('https://example.com').scheme")).to_equal("https")
```

</details>

#### allows net APIs only for explicitly granted endpoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("tcp://example.com:80", "require('net').createConnection({host:'example.com',port:80}).status")).to_equal("allowed")
expect(_eval_str_with_network("tcp://example.com:80", "require('node:net').createConnection(80, 'example.com').status")).to_equal("allowed")
expect(_eval_str_with_network("tcp://api.example.com:443", "require('net').createConnection({host:'example.com',port:80}).reason")).to_equal("network-grant-denied")
```

</details>

#### allows http APIs only for explicitly granted endpoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://example.com:80", "require('http').request('http://example.com').status")).to_equal("allowed")
expect(_eval_str_with_network("https://example.com:443", "require('node:https').request('https://example.com').status")).to_equal("allowed")
expect(_eval_str_with_network("https://example.com:443", "require('http').request('http://example.com').reason")).to_equal("network-grant-denied")
```

</details>

#### covers bounded network request aliases

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("tcp://example.com:80", "require('net').connect(80, 'example.com').status")).to_equal("allowed")
expect(_eval_str_with_network("http://example.com:80", "require('http').get('http://example.com').operation")).to_equal("http.request")
expect(_eval_str_with_network("https://example.com:443", "require('node:https').get('https://example.com').status")).to_equal("allowed")
```

</details>

#### parses bounded http request endpoints from URL strings

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request('http://api.example.com:8080/v1').status")).to_equal("allowed")
expect(_eval_str_with_network("https://api.example.com:444", "require('node:https').request('https://api.example.com:444/v1').target")).to_equal("https://api.example.com:444")
expect(_eval_str_with_network("http://api.example.com:8081", "require('http').request('http://api.example.com:8080/v1').reason")).to_equal("network-grant-denied")
```

</details>

#### parses bounded http request endpoints from option objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request({hostname:'api.example.com', port:8080}).status")).to_equal("allowed")
expect(_eval_str_with_network("https://secure.example.com:443", "require('node:https').request({host:'secure.example.com'}).target")).to_equal("https://secure.example.com:443")
expect(_eval_str_with_network("https://secure.example.com:444", "require('node:https').request({host:'secure.example.com'}).reason")).to_equal("network-grant-denied")
```

</details>

#### reports bounded http request metadata from URL strings

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request('http://api.example.com:8080/v1/items?limit=2').method")).to_equal("GET")
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request('http://api.example.com:8080/v1/items?limit=2').path")).to_equal("/v1/items?limit=2")
```

</details>

#### reports bounded http request metadata from option objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request({hostname:'api.example.com', port:8080, method:'POST', path:'/submit'}).method")).to_equal("POST")
expect(_eval_str_with_network("http://api.example.com:8080", "require('http').request({hostname:'api.example.com', port:8080, method:'POST', path:'/submit'}).path")).to_equal("/submit")
```

</details>

#### loads bounded http request headers from option objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var headers = {Accept:'json', Authorization:'token'}; var opts = {hostname:'api.example.com', port:8080}; opts.headers = headers; require('http').request(opts).getHeader('accept')")).to_equal("json")
expect(_eval_str_with_network("http://api.example.com:8080", "var headers = {Accept:'json', Authorization:'token'}; var opts = {hostname:'api.example.com', port:8080}; opts.headers = headers; require('http').request(opts).getHeaderNames()")).to_equal("accept,authorization")
expect(_eval_str_with_network("http://api.example.com:8080", "var headers = {Accept:'json', Authorization:'token'}; var opts = {hostname:'api.example.com', port:8080}; opts.headers = headers; var req = require('http').request(opts); req.flushHeaders(); req.flushedHeaderCount")).to_equal("2")
```

</details>

#### exposes bounded http request lifecycle methods

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').write")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').end")).to_equal("function")
expect(_eval_str_with_network("https://api.example.com:443", "typeof require('node:https').request('https://api.example.com').abort")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').on")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').once")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').listenerCount")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').setHeader")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').removeHeader")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').getHeaderNames")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').getHeaders")).to_equal("function")
expect(_eval_str_with_network("http://api.example.com:8080", "typeof require('http').request('http://api.example.com:8080').flushHeaders")).to_equal("function")
```

</details>

#### tracks bounded http request body writes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.write('abc').bytes")).to_equal("3")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.write('ab'); req.write('cde'); req.bodyBytes")).to_equal("5")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.write('ab'); req.write('cde'); req.bodyChunks")).to_equal("2")
```

</details>

#### rejects bounded http request writes after terminal state

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.writeRejected + ':' + req.writeRejectReason")).to_equal("false:")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); var r = req.write('late'); r.status + ':' + r.error + ':' + req.writeRejected + ':' + req.writeRejectReason")).to_equal("denied:request-ended:true:request-ended")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.abort(); var r = req.write('late'); r.status + ':' + r.error + ':' + req.writeRejected + ':' + req.writeRejectReason")).to_equal("denied:request-aborted:true:request-aborted")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.write('ok'); req.end(); req.write('late'); req.bodyBytes + ':' + req.bodyChunks")).to_equal("2:1")
```

</details>

#### tracks bounded http request headers

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Authorization', 'Bearer token'); req.getHeader('authorization')")).to_equal("Bearer token")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.headerCount")).to_equal("1")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('accept', 'text'); req.getHeader('ACCEPT')")).to_equal("text")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('accept', 'text'); req.headerCount")).to_equal("1")
```

</details>

#### removes bounded http request headers

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.hasHeader('ACCEPT')")).to_equal("true")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.hasHeader('missing')")).to_equal("false")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.removeHeader('accept'); req.hasHeader('Accept')")).to_equal("false")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.removeHeader('accept'); req.headerCount")).to_equal("0")
```

</details>

#### reports bounded http request header names

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('Authorization', 'token'); req.getHeaderNames()")).to_equal("accept,authorization")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('accept', 'text'); req.getHeaderNames()")).to_equal("accept")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.removeHeader('accept'); req.getHeaderNames()")).to_equal("")
```

</details>

#### reports bounded http request header objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.getHeaders().accept")).to_equal("json")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('accept', 'text'); req.getHeaders().accept")).to_equal("text")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.removeHeader('accept'); req.getHeaders().accept")).to_equal("undefined")
```

</details>

#### flushes bounded http request headers

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.flushHeaders(); req.headersFlushed")).to_equal("true")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.setHeader('Accept', 'json'); req.setHeader('Authorization', 'token'); req.flushHeaders(); req.flushedHeaderCount")).to_equal("2")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.flushHeaders(); req.requestEnded")).to_equal("false")
```

</details>

#### tracks bounded http request end and abort state

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); req.requestEnded")).to_equal("true")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.abort(); req.aborted")).to_equal("true")
```

</details>

#### tracks bounded http request lifecycle flags

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.writableEnded + ':' + req.writableFinished + ':' + req.destroyed + ':' + req.closed")).to_equal("false:false:false:false")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); req.writableEnded + ':' + req.writableFinished + ':' + req.destroyed + ':' + req.closed")).to_equal("true:true:false:true")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.abort(); req.writableEnded + ':' + req.writableFinished + ':' + req.destroyed + ':' + req.closed")).to_equal("false:false:true:true")
```

</details>

#### emits bounded http request finish events on end

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('finish', () => { seen = 'yes'; }); req.end(); seen + ':' + req.finishEmitted + ':' + req.finishListenerCount")).to_equal("yes:true:1")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 0; var req = require('http').request('http://api.example.com:8080'); req.once('finish', () => { seen = seen + 1; }); req.end(); req.end(); seen + ':' + req.listenerCount('finish')")).to_equal("1:0")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); req.finishEmitted + ':' + req.finishListenerCount")).to_equal("false:0")
```

</details>

#### emits bounded http request abort events

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('abort', () => { seen = 'yes'; }); req.abort(); seen + ':' + req.abortEmitted + ':' + req.abortListenerCount")).to_equal("yes:true:1")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 0; var req = require('http').request('http://api.example.com:8080'); req.once('abort', () => { seen = seen + 1; }); req.abort(); req.abort(); seen + ':' + req.listenerCount('abort')")).to_equal("1:0")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.abort(); req.abortEmitted + ':' + req.abortListenerCount")).to_equal("false:0")
```

</details>

#### emits bounded http request close events

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('close', () => { seen = 'end'; }); req.end(); seen + ':' + req.closeEmitted + ':' + req.closeListenerCount")).to_equal("end:true:1")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('close', () => { seen = 'abort'; }); req.abort(); seen + ':' + req.closeEmitted + ':' + req.closeListenerCount")).to_equal("abort:true:1")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 0; var req = require('http').request('http://api.example.com:8080'); req.once('close', () => { seen = seen + 1; }); req.end(); req.end(); seen + ':' + req.listenerCount('close')")).to_equal("1:0")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); req.closeEmitted + ':' + req.closeListenerCount")).to_equal("false:0")
```

</details>

#### delivers bounded http response callbacks on request end

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080', (res) => { seen = res.statusCode; }); req.end(); seen")).to_equal("200")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080/v1', (res) => { seen = res.path; }); req.end(); seen")).to_equal("/v1")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080', (res) => {}); req.end(); req.responseDelivered")).to_equal("true")
```

</details>

#### emits bounded http request response events on request end

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('response', (res) => { seen = res.statusCode + ':' + res.path; }); req.end(); seen + ':' + req.responseEmitted + ':' + req.responseListenerCount")).to_equal("200:/:true:1")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 0; var req = require('http').request('http://api.example.com:8080/v1'); req.once('response', (res) => { seen = seen + res.statusCode; }); req.end(); req.end(); seen + ':' + req.listenerCount('response')")).to_equal("200:0")
expect(_eval_str_with_network("http://api.example.com:8080", "var req = require('http').request('http://api.example.com:8080'); req.end(); req.responseEmitted + ':' + req.responseListenerCount")).to_equal("false:0")
```

</details>

#### delivers bounded http response data and end events

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080', (res) => { res.on('data', (chunk) => { seen = chunk; }); }); req.end(); seen")).to_equal("bounded-response")
expect(_eval_str_with_network("http://api.example.com:8080", "var ended = 'no'; var req = require('http').request('http://api.example.com:8080', (res) => { res.on('end', () => { ended = 'yes'; }); }); req.end(); ended")).to_equal("yes")
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; res.once('end', () => {}); }); req.end(); saved.listenerCount('end')")).to_equal("0")
```

</details>

#### tracks bounded http response lifecycle state

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; }); req.end(); saved.complete + ':' + saved.readableEnded + ':' + saved.endDelivered")).to_equal("true:true:false")
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; res.on('data', () => {}); res.on('end', () => {}); }); req.end(); saved.dataListenerCount + ':' + saved.endListenerCount + ':' + saved.dataDelivered + ':' + saved.endDelivered")).to_equal("1:1:true:true")
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080'); req.on('response', (res) => { saved = res; res.on('end', () => {}); }); req.end(); saved.complete + ':' + saved.readableEnded + ':' + saved.endListenerCount")).to_equal("true:true:1")
```

</details>

#### reports bounded http response headers

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; }); req.end(); saved.httpVersion + ':' + saved.headerCount + ':' + saved.headerNames")).to_equal("1.1:3:content-type,content-length,x-simple-runtime")
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; }); req.end(); saved.headers['content-type'] + ':' + saved.headers['content-length']")).to_equal("text/plain:16")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('response', (res) => { seen = res.headers['x-simple-runtime']; }); req.end(); seen")).to_equal("bounded")
```

</details>

#### reports bounded http response raw header ordering

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("http://api.example.com:8080", "var saved = null; var req = require('http').request('http://api.example.com:8080', (res) => { saved = res; }); req.end(); saved.httpVersionMajor + ':' + saved.httpVersionMinor + ':' + saved.rawHeaders")).to_equal("1:1:Content-Type,text/plain,Content-Length,16,X-Simple-Runtime,bounded")
expect(_eval_str_with_network("http://api.example.com:8080", "var seen = 'no'; var req = require('http').request('http://api.example.com:8080'); req.on('response', (res) => { seen = res.httpVersionMajor + '.' + res.httpVersionMinor + ':' + res.rawHeaders; }); req.end(); seen")).to_equal("1.1:Content-Type,text/plain,Content-Length,16,X-Simple-Runtime,bounded")
expect(_eval_str_with_network("https://api.example.com:443", "var saved = null; var req = require('node:https').request('https://api.example.com', (res) => { saved = res; }); req.end(); saved.statusMessage + ':' + saved.rawHeaders")).to_equal("OK:Content-Type,text/plain,Content-Length,16,X-Simple-Runtime,bounded")
```

</details>

#### resolves Express-like http server creation as fail-closed network API

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('http').createServer")).to_equal("function")
expect(_eval_str("typeof require('node:http').createServer")).to_equal("function")
```

</details>

#### denies Express-like http server listen without network grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('http').createServer((req,res)=>{}).status")).to_equal("denied")
expect(_eval_str("require('http').createServer((req,res)=>{}).listen(0).error")).to_equal("network-denied")
expect(_eval_str("require('node:http').createServer((req,res)=>{}).listen(3000).operation")).to_equal("http.Server.listen")
expect(_eval_str("require('http').createServer((req,res)=>{}).close().status")).to_equal("denied")
```

</details>

#### allows http server listen only for explicitly granted listen endpoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_network("listen://0.0.0.0:3000", "require('http').createServer((req,res)=>{}).listen(3000).status")).to_equal("allowed")
expect(_eval_str_with_network("listen://0.0.0.0:3000", "require('node:http').createServer((req,res)=>{}).listen(3000).port")).to_equal("3000")
expect(_eval_str_with_network("listen://0.0.0.0:3000", "require('http').createServer((req,res)=>{}).listen(0).reason")).to_equal("network-grant-denied")
```

</details>

#### resolves stream APIs as bounded deterministic objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('stream').Readable.from")).to_equal("function")
expect(_eval_str("typeof require('node:stream').Writable")).to_equal("function")
```

</details>

#### reads from bounded stream Readable.from inputs

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); r.readableLength")).to_equal("2")
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); r.read()")).to_equal("a")
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); r.read(); r.read()")).to_equal("b")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.on('end', () => { seen = seen + 1; }); r.read(); r.read(); seen + ':' + r.readableEnded + ':' + r.readable")).to_equal("1:true:false")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a','b']); r.on('end', () => { seen = seen + 1; }); r.read(); seen + ':' + r.readableLength + ':' + r.endEmitted")).to_equal("0:1:false")
```

</details>

#### tracks bounded readable pause and resume flow state

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var r = require('stream').Readable.from(['a']); typeof r.pause + ':' + typeof r.resume + ':' + typeof r.isPaused")).to_equal("function:function:function")
expect(_eval_str("var r = require('stream').Readable.from(['a']); r.pause(); r.isPaused() + ':' + r.readableFlowing")).to_equal("true:false")
expect(_eval_str("var r = require('stream').Readable.from(['a']); r.pause(); r.resume(); r.isPaused() + ':' + r.readableFlowing")).to_equal("false:true")
```

</details>

#### emits bounded readable availability events

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a','b']); r.on('readable', () => { seen = r.readableLength; }); seen + ':' + r.readableNotified + ':' + r.readableAvailableEmitted")).to_equal("2:true:true")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.once('readable', () => { seen = seen + 1; }); seen + ':' + r.listenerCount('readable') + ':' + r.readableNotified")).to_equal("1:0:true")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.read(); r.read(); r.on('readable', () => { seen = seen + 1; }); seen + ':' + r.readableEnded + ':' + r.readable")).to_equal("0:true:false")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.pause(); r.on('readable', () => { seen = r.readableLength; }); seen + ':' + r.isPaused() + ':' + r.readableNotified")).to_equal("1:true:true")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.destroy(); r.on('readable', () => { seen = seen + 1; }); seen + ':' + r.destroyed + ':' + r.readableLength")).to_equal("0:true:0")
```

</details>

#### tracks bounded stream Writable writes and end state

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var w = require('stream').Writable(); w.write('abc').status")).to_equal("ok")
expect(_eval_str("var w = require('stream').Writable(); w.write('abc').bytes")).to_equal("3")
expect(_eval_str("var w = require('stream').Writable(); w.end(); w.writableEnded")).to_equal("true")
```

</details>

#### reports bounded writable backpressure after end

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var w = require('stream').Writable(); w.end(); w.write('late').status")).to_equal("backpressure")
expect(_eval_str("var w = require('stream').Writable(); w.end(); w.write('late').error")).to_equal("write-after-end")
expect(_eval_str("var w = require('stream').Writable(); w.end(); w.write('late'); w.backpressure")).to_equal("true")
expect(_eval_str("var w = require('stream').Writable(); w.write('ok'); w.end(); w.write('late'); w.chunksWritten")).to_equal("1")
```

</details>

#### tracks bounded writable high-water backpressure

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var opts = {}; opts.highWaterMark = 4; var w = require('stream').Writable(opts); w.writableHighWaterMark")).to_equal("4")
expect(_eval_str("var opts = {}; opts.highWaterMark = 4; var w = require('stream').Writable(opts); w.write('abc').status + ':' + w.writableLength + ':' + w.backpressure")).to_equal("ok:3:false")
expect(_eval_str("var opts = {}; opts.highWaterMark = 3; var w = require('stream').Writable(opts); w.write('ab'); var result = w.write('c'); result.status + ':' + result.ok + ':' + result.writableLength + ':' + w.backpressure + ':' + w.bytesWritten")).to_equal("backpressure:false:3:true:3")
```

</details>

#### emits bounded writable drain when end clears backpressure

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var opts = {}; opts.highWaterMark = 3; var seen = 'no'; var w = require('stream').Writable(opts); w.on('drain', () => { seen = w.writableLength + ':' + w.backpressure; }); w.write('abc'); w.end(); seen + ':' + w.drainEmitted + ':' + w.drainListenerCount")).to_equal("0:false:true:1")
expect(_eval_str("var opts = {}; opts.highWaterMark = 2; var seen = 0; var w = require('stream').Writable(opts); w.once('drain', () => { seen = seen + 1; }); w.write('ab'); w.end(); w.end(); seen + ':' + w.listenerCount('drain')")).to_equal("1:0")
expect(_eval_str("var opts = {}; opts.highWaterMark = 9; var seen = 'no'; var w = require('stream').Writable(opts); w.on('drain', () => { seen = 'yes'; }); w.write('ab'); w.end(); seen + ':' + w.drainEmitted + ':' + w.backpressure")).to_equal("no:false:false")
```

</details>

#### pipes bounded readable chunks into writable destinations

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pipe(w); w.lastChunk")).to_equal("abc")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pipe(w); w.bytesWritten")).to_equal("3")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['ab','cde']); var w = s.Writable(); r.pipe(w); w.bytesWritten")).to_equal("5")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['ab','cde']); var w = s.Writable(); r.pipe(w); w.lastChunk")).to_equal("cde")
```

</details>

#### emits bounded readable end after pipe drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var seen = 0; var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.on('end', () => { seen = seen + 1; }); r.pipe(w); seen + ':' + r.endEmitted + ':' + r.readableLength")).to_equal("1:true:0")
expect(_eval_str("var seen = 0; var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.once('end', () => { seen = seen + 1; }); r.pipe(w); r.pipe(w); seen + ':' + r.listenerCount('end') + ':' + r.endEmitted")).to_equal("1:0:true")
expect(_eval_str("var seen = 0; var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.on('end', () => { seen = seen + 1; }); r.pipe(w); r.resume(); seen + ':' + r.endEmitted + ':' + w.bytesWritten")).to_equal("1:true:3")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pipe(w); r.readableEnded + ':' + r.readable")).to_equal("true:false")
```

</details>

#### defers bounded pipe drains while readable is paused

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.pipe(w); r.readableLength + ':' + w.bytesWritten + ':' + r.pipePaused")).to_equal("1:0:true")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.resume(); r.pipe(w); r.readableLength + ':' + w.bytesWritten + ':' + r.pipePaused")).to_equal("0:3:false")
```

</details>

#### resumes bounded pending pipe drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.pipe(w); r.resume(); r.readableLength + ':' + w.bytesWritten + ':' + r.pipePaused + ':' + r.pipeResumed")).to_equal("0:3:false:true")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['ab','cde']); var w = s.Writable(); r.pause(); r.pipe(w); r.resume(); w.lastChunk + ':' + w.bytesWritten")).to_equal("cde:5")
```

</details>

#### unpipes bounded pending readable destinations

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var r = require('stream').Readable.from(['a']); typeof r.unpipe")).to_equal("function")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.pipe(w); r.unpipe(); r.resume(); r.readableLength + ':' + w.bytesWritten + ':' + r.pipeUnpiped + ':' + r.pipeResumed")).to_equal("1:0:true:false")
```

</details>

#### destroys bounded readable streams

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var r = require('stream').Readable.from(['a']); typeof r.destroy")).to_equal("function")
expect(_eval_str("var r = require('stream').Readable.from(['a']); r.destroy(); r.destroyed + ':' + r.closed + ':' + r.readable + ':' + r.readableLength")).to_equal("true:true:false:0")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.on('close', () => { seen = seen + 1; }); r.destroy(); r.destroy(); seen + ':' + r.closeEmitted + ':' + r.listenerCount('close')")).to_equal("1:true:1")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.once('close', () => { seen = seen + 1; }); r.destroy(); r.destroy(); seen + ':' + r.listenerCount('close')")).to_equal("1:0")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pause(); r.pipe(w); r.destroy(); r.resume(); w.bytesWritten + ':' + r.pipePaused + ':' + r.destroyed")).to_equal("0:false:true")
```

</details>

#### delivers bounded readable data listeners

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.on('data', (c) => { seen = seen + c; }); seen + ':' + r.readableLength + ':' + r.readableFlowing")).to_equal("ab:0:true")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.once('data', (c) => { seen = seen + c; }); seen + ':' + r.readableLength + ':' + r.listenerCount('data')")).to_equal("a:1:0")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.pause(); r.on('data', (c) => { seen = seen + c; }); seen + ':' + r.readableLength + ':' + r.readableFlowing")).to_equal(":2:false")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.pause(); r.on('data', (c) => { seen = seen + c; }); r.resume(); seen + ':' + r.readableLength + ':' + r.readableFlowing")).to_equal("ab:0:true")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a']); r.destroy(); r.on('data', (c) => { seen = seen + c; }); seen + ':' + r.readableLength + ':' + r.destroyed")).to_equal(":0:true")
```

</details>

#### emits bounded readable end after data drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.on('end', () => { seen = seen + ':end'; }); r.on('data', (c) => { seen = seen + c; }); seen + ':' + r.endEmitted")).to_equal("ab:end:true")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.once('end', () => { seen = seen + 1; }); r.on('data', (c) => {}); r.resume(); seen + ':' + r.listenerCount('end') + ':' + r.endEmitted")).to_equal("1:0:true")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a','b']); r.once('data', (c) => { seen = seen + c; }); seen + ':' + r.readableLength + ':' + r.endEmitted")).to_equal("a:1:false")
expect(_eval_str("var seen = ''; var r = require('stream').Readable.from(['a']); r.pause(); r.on('end', () => { seen = seen + ':end'; }); r.on('data', (c) => { seen = seen + c; }); r.resume(); seen + ':' + r.endEmitted")).to_equal("a:end:true")
expect(_eval_str("var r = require('stream').Readable.from(['a']); r.on('data', (c) => {}); r.readableEnded + ':' + r.readable")).to_equal("true:false")
```

</details>

#### propagates bounded pipe backpressure to writable destinations

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var opts = {}; opts.highWaterMark = 4; var s = require('stream'); var r = s.Readable.from(['ab','cde']); var w = s.Writable(opts); r.pipe(w); w.writableLength + ':' + w.backpressure")).to_equal("5:true")
expect(_eval_str("var opts = {}; opts.highWaterMark = 4; var s = require('stream'); var r = s.Readable.from(['ab','cd','ef']); var w = s.Writable(opts); r.pipe(w); w.bytesWritten + ':' + r.readableLength + ':' + r.pipeBackpressured + ':' + r.pipePaused + ':' + r.endEmitted")).to_equal("4:1:true:true:false")
expect(_eval_str("var opts = {}; opts.highWaterMark = 4; var s = require('stream'); var r = s.Readable.from(['ab','cd','ef']); var w = s.Writable(opts); r.pipe(w); w.writableLength = 0; w.backpressure = false; r.resume(); w.bytesWritten + ':' + w.lastChunk + ':' + r.readableLength + ':' + r.pipeBackpressured + ':' + r.endEmitted")).to_equal("6:ef:0:false:true")
```

</details>

#### returns the writable destination from bounded stream pipe

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pipe(w).lastChunk")).to_equal("abc")
expect(_eval_str("var s = require('stream'); var r = s.Readable.from(['abc']); var w = s.Writable(); r.pipe(w); r.readableLength")).to_equal("0")
```

</details>

#### iterates bounded readable chunks through explicit async iterator subset

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('stream').Readable.from(['a']).streamAsyncIterator")).to_equal("function")
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); var it = r.streamAsyncIterator(); it.next().value")).to_equal("a")
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); var it = r.streamAsyncIterator(); it.next(); it.next().value")).to_equal("b")
expect(_eval_str("var r = require('stream').Readable.from(['a']); var it = r.streamAsyncIterator(); it.next(); it.next().done")).to_equal("true")
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); var it = r.streamAsyncIterator(); it.next(); r.readableLength")).to_equal("1")
```

</details>

#### emits bounded readable end after async iterator exhaustion

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.on('end', () => { seen = seen + 1; }); var it = r.streamAsyncIterator(); it.next(); it.next(); seen + ':' + r.endEmitted + ':' + r.readableLength")).to_equal("1:true:0")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.once('end', () => { seen = seen + 1; }); var it = r.streamAsyncIterator(); it.next(); it.next(); it.next(); seen + ':' + r.listenerCount('end') + ':' + r.endEmitted")).to_equal("1:0:true")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a','b']); r.on('end', () => { seen = seen + 1; }); var it = r.streamAsyncIterator(); it.next(); seen + ':' + r.endEmitted + ':' + r.readableLength")).to_equal("0:false:1")
expect(_eval_str("var r = require('stream').Readable.from(['a']); var it = r.streamAsyncIterator(); it.next(); it.next(); r.readableEnded + ':' + r.readable")).to_equal("true:false")
```

</details>

#### exposes bounded Symbol asyncIterator key

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Symbol.asyncIterator")).to_equal("Symbol.asyncIterator")
```

</details>

#### exposes bounded readable Symbol asyncIterator method

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('stream').Readable.from(['a'])[Symbol.asyncIterator]")).to_equal("function")
```

</details>

#### iterates bounded readable chunks through Symbol asyncIterator

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var r = require('stream').Readable.from(['a','b']); var it = r[Symbol.asyncIterator](); it.next().value")).to_equal("a")
expect(_eval_str("var seen = 0; var r = require('stream').Readable.from(['a']); r.on('end', () => { seen = seen + 1; }); var it = r[Symbol.asyncIterator](); it.next(); it.next(); seen + ':' + r.endEmitted")).to_equal("1:true")
```

</details>

#### tracks bounded writable finish event listeners

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var w = require('stream').Writable(); w.on('finish', () => 1); w.listenerCount('finish')")).to_equal("1")
expect(_eval_str("var w = require('stream').Writable(); w.on('finish', () => 1); w.end(); w.finishEmitted")).to_equal("true")
expect(_eval_str("var w = require('stream').Writable(); w.on('finish', () => 1); w.end(); w.finishListenerCount")).to_equal("1")
```

</details>

#### clears bounded once finish listeners after end

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var w = require('stream').Writable(); w.once('finish', () => 1); w.end(); w.listenerCount('finish')")).to_equal("0")
```

</details>

#### invokes bounded writable finish callbacks on end

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var finished = 'no'; var w = require('stream').Writable(); w.on('finish', () => { finished = 'yes'; }); w.end(); finished")).to_equal("yes")
expect(_eval_str("var finished = 'no'; var w = require('stream').Writable(); w.once('finish', () => { finished = 'once'; }); w.end(); finished")).to_equal("once")
```

</details>

#### caches stream module state across repeated require calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = require('stream'); s.cached = 'yes'; require('node:stream').cached")).to_equal("yes")
```

</details>

#### resolves timers APIs through the runtime scheduler

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('timers').setTimeout")).to_equal("function")
expect(_eval_str("typeof require('node:timers').clearTimeout")).to_equal("function")
expect(_eval_str("typeof require('timers').setImmediate")).to_equal("function")
expect(_eval_str("typeof require('node:timers').clearImmediate")).to_equal("function")
expect(_eval_str("typeof setImmediate")).to_equal("function")
expect(_eval_str("typeof clearImmediate")).to_equal("function")
```

</details>

#### schedules timers module setTimeout callbacks through runtime drain

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; require('timers').setTimeout(() => { timerValue = 11; }, 0); timerValue", "timerValue", 0)).to_equal("0:1:11")
```

</details>

#### cancels timers module callbacks through clearTimeout

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; var id = require('timers').setTimeout(() => { timerValue = 11; }, 0); require('node:timers').clearTimeout(id); timerValue", "timerValue", 0)).to_equal("0:0:0")
```

</details>

#### marks bounded timer object handles closed through clear calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); require('node:timers').clearTimeout(h); h.closed")).to_equal("true")
expect(_eval_str("var h = require('timers').setInterval(() => {}, 5); require('node:timers').clearInterval(h); h.closed")).to_equal("true")
expect(_eval_str("var h = require('timers').setImmediate(() => {}); require('node:timers').clearImmediate(h); h.closed")).to_equal("true")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); require('node:timers').clearTimeout(h); h.active")).to_equal("false")
```

</details>

#### schedules bounded setImmediate callbacks through runtime drain

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; require('timers').setImmediate(() => { timerValue = 13; }); timerValue", "timerValue", 0)).to_equal("0:1:13")
```

</details>

#### cancels bounded setImmediate callbacks through clearImmediate

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; var id = require('timers').setImmediate(() => { timerValue = 13; }); require('node:timers').clearImmediate(id); timerValue", "timerValue", 0)).to_equal("0:0:0")
```

</details>

#### schedules global bounded setImmediate callbacks through runtime drain

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; setImmediate(() => { timerValue = 17; }); timerValue", "timerValue", 0)).to_equal("0:1:17")
```

</details>

#### cancels global bounded setImmediate callbacks through clearImmediate

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; var id = setImmediate(() => { timerValue = 17; }); clearImmediate(id); timerValue", "timerValue", 0)).to_equal("0:0:0")
```

</details>

#### returns bounded Node timer handle objects

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); typeof h")).to_equal("object")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); typeof h.ref")).to_equal("function")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); typeof h.refresh")).to_equal("function")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.active + ':' + h.closed")).to_equal("true:false")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.fired + ':' + h.fireCount")).to_equal("false:0")
expect(_eval_str("var h = require('timers').setInterval(() => {}, 5); h.repeat")).to_equal("true")
```

</details>

#### tracks bounded Node timer handle ref state

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.hasRef()")).to_equal("true")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.unref(); h.hasRef()")).to_equal("false")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.unref(); h.ref(); h.hasRef()")).to_equal("true")
```

</details>

#### closes bounded Node timer handles

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); typeof h.close")).to_equal("function")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.close() === h")).to_equal("true")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.close(); h.closed")).to_equal("true")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.close(); h.active")).to_equal("false")
```

</details>

#### cancels timers through bounded handle close

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var timerValue = 0; var h = require('timers').setTimeout(() => { timerValue = 11; }, 0); h.close(); timerValue", "timerValue", 0)).to_equal("0:0:0")
```

</details>

#### tracks bounded timer handle fire state during drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var h = require('timers').setTimeout(() => {}, 0); h.active + ':' + h.fired + ':' + h.fireCount", "h.active + ':' + h.fired + ':' + h.fireCount", 0)).to_equal("true:false:0:1:false:true:1")
expect(_eval_before_after_two_timer_drains("var h = require('timers').setInterval(() => {}, 1); h.fireCount", "h.active + ':' + h.fired + ':' + h.fireCount", 1, 2)).to_equal("0:1:true:true:1:1:true:true:2")
```

</details>

#### refreshes bounded Node timer handles

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.refresh(); h.refreshed")).to_equal("true")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.refresh(); h.refreshedAt")).to_equal("0")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.refresh(); h.active + ':' + h.closed")).to_equal("true:false")
expect(_eval_str("var h = require('timers').setTimeout(() => {}, 5); h.close(); h.refresh(); h.refreshed")).to_equal("false")
```

</details>

#### reschedules timers module setInterval callbacks across drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_two_timer_drains("var timerValue = 0; require('timers').setInterval(() => { timerValue = timerValue + 1; }, 1); timerValue", "timerValue", 1, 2)).to_equal("0:1:1:1:2")
```

</details>

#### cancels timers module intervals from their callback

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_two_timer_drains("var timerValue = 0; var id = require('timers').setInterval(() => { timerValue = timerValue + 1; require('node:timers').clearInterval(id); }, 1); timerValue", "timerValue", 1, 2)).to_equal("0:1:1:0:1")
```

</details>

#### caches timers module state across repeated require calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var t = require('timers'); t.cached = 'yes'; require('node:timers').cached")).to_equal("yes")
```

</details>

#### resolves readline createInterface as fail-closed terminal API

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof require('readline').createInterface")).to_equal("function")
expect(_eval_str("typeof require('node:readline').createInterface")).to_equal("function")
```

</details>

#### denies readline interaction without terminal grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('readline').createInterface({}).status")).to_equal("denied")
expect(_eval_str("require('node:readline').createInterface({}).error")).to_equal("terminal-denied")
expect(_eval_str("require('readline').createInterface({}).question('name?').operation")).to_equal("readline.question")
expect(_eval_str("require('readline').createInterface({}).close().status")).to_equal("denied")
```

</details>

#### allows bounded readline interaction with terminal grants

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_terminal("Ada", "require('readline').createInterface({}).status")).to_equal("allowed")
expect(_eval_str_with_terminal("Ada", "require('node:readline').createInterface({}).terminal")).to_equal("true")
expect(_eval_str_with_terminal("Ada", "var rl = require('readline').createInterface({}); var seen = ''; var result = rl.question('name?', (answer) => { seen = answer; }); result.status + ':' + result.prompt + ':' + result.answer + ':' + seen")).to_equal("allowed:name?:Ada:Ada")
expect(_eval_str_with_terminal("Ada", "var rl = require('node:readline').createInterface({}); var result = rl.close(); result.status + ':' + result.closed + ':' + rl.closed")).to_equal("allowed:true:true")
```

</details>

### Buffer global and module shape

#### exposes Buffer through require('buffer')

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.from('68656c6c6f', 'hex').toString('utf8')")).to_equal("hello")
```

</details>

#### decodes multibyte Buffer UTF-8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('e282ac', 'hex').toString('utf8')")).to_equal("€")
```

</details>

#### replaces invalid Buffer UTF-8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('c328', 'hex').toString('utf8').charCodeAt(0)")).to_equal("65533")
```

</details>

#### builds buffers from numeric byte arrays

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.from([104,101,108,108,111]).toString('utf8')")).to_equal("hello")
```

</details>

#### builds buffers from Uint8Array bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from(new Uint8Array([226,130,172])).toString('utf8')")).to_equal("€")
```

</details>

#### builds zero-filled buffers from ArrayBuffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from(new ArrayBuffer(2)).toString('hex')")).to_equal("0000")
```

</details>

#### normalizes numeric array bytes like Node buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255,256,-1]).toString('hex')")).to_equal("0061ff00ff")
```

</details>

#### compares lower buffers before higher buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.compare(Buffer.from('61', 'hex'), Buffer.from('62', 'hex'))")).to_equal("-1")
```

</details>

#### compares higher buffers after lower buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.compare(require('buffer').Buffer.from('62', 'hex'), require('buffer').Buffer.from('61', 'hex'))")).to_equal("1")
```

</details>

#### compares identical buffers equally

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.compare(Buffer.from('6162', 'hex'), Buffer.from('6162', 'hex'))")).to_equal("0")
```

</details>

#### checks equal buffer contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('6162', 'hex').equals(Buffer.from('6162', 'hex'))")).to_equal("true")
```

</details>

#### checks unequal buffer contents

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('6162', 'hex').equals(Buffer.from('6163', 'hex'))")).to_equal("false")
```

</details>

#### slices buffer byte ranges

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').slice(1, 4).toString('utf8')")).to_equal("ell")
```

</details>

#### slices with negative and clamped indexes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').slice(-2, 99).toString('hex')")).to_equal("6c6f")
```

</details>

#### subarrays buffer byte ranges

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').subarray(1, 4).toString('utf8')")).to_equal("ell")
```

</details>

#### subarrays with negative start

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from('68656c6c6f', 'hex').subarray(-2).toString('hex')")).to_equal("6c6f")
```

</details>

#### reads unsigned bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255]).readUInt8(1)")).to_equal("97")
```

</details>

#### bounds out-of-range unsigned byte reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,255]).readUInt8(99)")).to_equal("0")
```

</details>

#### reads little-endian unsigned 16-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52,18,86,120]).readUInt16LE(0)")).to_equal("4660")
```

</details>

#### reads big-endian unsigned 16-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52,18,86,120]).readUInt16BE(2)")).to_equal("22136")
```

</details>

#### bounds out-of-range unsigned 16-bit reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([52]).readUInt16LE(0)")).to_equal("0")
```

</details>

#### reads WASM magic as little-endian u32

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32LE(0)")).to_equal("1836278016")
```

</details>

#### reads WASM version as little-endian u32

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32LE(4)")).to_equal("1")
```

</details>

#### reads big-endian unsigned 32-bit values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([0,97,115,109,1,0,0,0]).readUInt32BE(0)")).to_equal("6388590")
```

</details>

#### bounds out-of-range unsigned 32-bit big-endian reads

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.from([1,2,3]).readUInt32BE(0)")).to_equal("0")
```

</details>

#### writes unsigned bytes and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt8(255, 1)")).to_equal("2")
```

</details>

#### writes little-endian unsigned 16-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt16LE(4660, 0)")).to_equal("2")
```

</details>

#### writes big-endian unsigned 16-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(2).writeUInt16BE(4660, 0)")).to_equal("2")
```

</details>

#### writes little-endian unsigned 32-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(4).writeUInt32LE(1836278016, 0)")).to_equal("4")
```

</details>

#### writes big-endian unsigned 32-bit values and returns the next offset

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(4).writeUInt32BE(6388590, 0)")).to_equal("4")
```

</details>

#### exposes Buffer.concat through require('buffer')

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.concat([require('buffer').Buffer.from('6865', 'hex'), require('buffer').Buffer.from('6c6c6f', 'hex')]).toString('utf8')")).to_equal("hello")
```

</details>

#### allocates zero-filled buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.alloc(3).toString('hex')")).to_equal("000000")
```

</details>

#### allocates filled buffers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.alloc(4, 97).toString('utf8')")).to_equal("aaaa")
```

</details>

#### identifies bounded Buffer instances

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('buffer').Buffer.isBuffer(require('buffer').Buffer.from('68656c6c6f', 'hex'))")).to_equal("true")
```

</details>

#### rejects non-buffer values for Buffer.isBuffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("Buffer.isBuffer('hello')")).to_equal("false")
```

</details>

#### exposes Buffer through globalThis

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("globalThis.Buffer.byteLength('hello', 'utf8')")).to_equal("5")
```

</details>

### process global shape

#### exposes deterministic process cwd

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.cwd()")).to_equal("/")
```

</details>

#### denies ambient process env values

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("typeof process.env.PATH")).to_equal("undefined")
```

</details>

#### exposes only explicitly granted credential env values

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str_with_credential("openai-api-key", "test-token", "process.env.OPENAI_API_KEY")).to_equal("test-token")
expect(_eval_str_with_credential("openai-api-key", "test-token", "require('process').env.OPENAI_API_KEY")).to_equal("test-token")
expect(_eval_str_with_credential("openai-api-key", "test-token", "typeof process.env.PATH")).to_equal("undefined")
expect(_eval_str_with_credential("openai-api-key", "test-token", "typeof process.env.ANTHROPIC_API_KEY")).to_equal("undefined")
```

</details>

#### exposes deterministic process versions

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.versions.node")).to_equal("0.0.0-simple")
```

</details>

#### exposes deterministic process argv length

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.argv.length")).to_equal("2")
```

</details>

#### exposes deterministic process argv executable

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.argv[0]")).to_equal("simple")
```

</details>

#### exposes deterministic require process argv

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('process').argv.length")).to_equal("2")
```

</details>

#### exposes embedded process exit intent

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("process.exit(7)")).to_equal("7")
```

</details>

#### exposes embedded require process exit intent

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("require('process').exit(7)")).to_equal("7")
```

</details>

#### schedules process.nextTick callbacks through the runtime drain

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var tickValue = 0; process.nextTick(() => { tickValue = 7; }); tickValue", "tickValue", 0)).to_equal("0:1:7")
```

</details>

#### schedules require process.nextTick callbacks through the runtime drain

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var tickValue = 0; require('process').nextTick(() => { tickValue = 9; }); tickValue", "tickValue", 0)).to_equal("0:1:9")
```

</details>

#### drains process.nextTick before already queued timers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var order = ''; require('timers').setTimeout(() => { order = order + 'timer'; }, 0); process.nextTick(() => { order = order + 'tick'; }); order", "order", 0)).to_equal(":2:ticktimer")
```

</details>

#### drains nested process.nextTick callbacks before timers

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_before_after_timer_drain("var order = ''; require('timers').setTimeout(() => { order = order + 'timer'; }, 0); process.nextTick(() => { order = order + 'tick'; process.nextTick(() => { order = order + 'nested'; }); }); order", "order", 0)).to_equal(":3:ticknestedtimer")
```

</details>

### TextEncoder and TextDecoder globals

#### encodes text to Uint8Array-compatible bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextEncoder().encode('hello').length")).to_equal("5")
expect(_eval_str("new TextEncoder().encode('hello')[1]")).to_equal("101")
```

</details>

#### encodes text into caller-provided Uint8Array storage

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var dst = new Uint8Array(5); var r = new TextEncoder().encodeInto('hello', dst); r.read + ':' + r.written + ':' + dst[0] + ':' + dst[4]")).to_equal("5:5:104:111")
```

</details>

#### reports partial encodeInto writes when destination storage is short

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var dst = new Uint8Array(3); var r = new TextEncoder().encodeInto('hello', dst); r.read + ':' + r.written + ':' + dst[0] + ':' + dst[2]")).to_equal("3:3:104:108")
```

</details>

#### decodes Uint8Array-compatible bytes as UTF-8

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextDecoder().decode(new Uint8Array([104,101,108,108,111]))")).to_equal("hello")
```

</details>

#### encodes multibyte UTF-8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var b = new TextEncoder().encode('\\u20ac'); b[0]")).to_equal("226")
expect(_eval_str("var b = new TextEncoder().encode('\\u20ac'); b[1]")).to_equal("130")
expect(_eval_str("var b = new TextEncoder().encode('\\u20ac'); b[2]")).to_equal("172")
```

</details>

#### decodes multibyte UTF-8 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = new TextDecoder().decode(new Uint8Array([226,130,172])); s.charCodeAt(0)")).to_equal("8364")
```

</details>

#### replaces invalid UTF-8 continuation bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = new TextDecoder().decode(new Uint8Array([195,40])); s.charCodeAt(0)")).to_equal("65533")
expect(_eval_str("var s = new TextDecoder().decode(new Uint8Array([195,40])); s.charAt(1)")).to_equal("(")
```

</details>

#### replaces truncated UTF-8 sequences

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("var s = new TextDecoder().decode(new Uint8Array([226,130])); s.charCodeAt(0)")).to_equal("65533")
```

</details>

#### reports deterministic UTF-8 labels

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_str("new TextEncoder().encoding")).to_equal("utf-8")
expect(_eval_str("new TextDecoder('utf8').encoding")).to_equal("utf-8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/js/node_api_conformance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Node.js path module
- path.dirname
- path.basename
- path.extname
- path.isAbsolute
- path.join
- path.resolve
- path.normalize
- Node.js process module
- process identity
- process versions and release
- process working directory and argv
- process env
- process.nextTick
- process.exit
- Node.js os module
- deterministic os identity
- Node.js Buffer module
- Buffer.byteLength
- Buffer.from(...).toString(...)
- Buffer.concat
- NodeBuffer value semantics
- Node.js crypto module
- createHash digest
- Node.js runtime shape
- String primitives
- JSON.parse host path
- require builtins
- Buffer global and module shape
- process global shape
- TextEncoder and TextDecoder globals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 245 |
| Active scenarios | 245 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


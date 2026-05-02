# JavaScript/TypeScript Helper Methods — Comprehensive Inventory

## 1. String Methods

### String.prototype (instance methods)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `at(index)` | Returns character at given index, supports negative indexing | Access |
| 2 | `charAt(index)` | Returns character at specified index (no negative support) | Access |
| 3 | `charCodeAt(index)` | Returns UTF-16 code unit (0-65535) at index | Encoding |
| 4 | `codePointAt(index)` | Returns Unicode code point at index (handles surrogate pairs) | Encoding |
| 5 | `concat(...strings)` | Concatenates one or more strings, returns new string | Combine |
| 6 | `endsWith(search, length?)` | Checks if string ends with given substring | Search |
| 7 | `includes(search, position?)` | Checks if string contains given substring | Search |
| 8 | `indexOf(search, position?)` | Returns first index of substring, or -1 | Search |
| 9 | `isWellFormed()` | Checks if string contains no lone surrogates (ES2024) | Validation |
| 10 | `lastIndexOf(search, position?)` | Returns last index of substring, or -1 | Search |
| 11 | `localeCompare(other, locales?, options?)` | Compares strings in locale-sensitive manner, returns -1/0/1 | Comparison |
| 12 | `match(regexp)` | Matches string against regex, returns matches array or null | Pattern |
| 13 | `matchAll(regexp)` | Returns iterator of all regex matches (regex must have /g flag) | Pattern |
| 14 | `normalize(form?)` | Returns Unicode normalization form (NFC, NFD, NFKC, NFKD) | Encoding |
| 15 | `padEnd(targetLength, padString?)` | Pads end of string to target length with given string | Formatting |
| 16 | `padStart(targetLength, padString?)` | Pads start of string to target length with given string | Formatting |
| 17 | `repeat(count)` | Returns string repeated count times | Transform |
| 18 | `replace(pattern, replacement)` | Replaces first match of pattern with replacement | Transform |
| 19 | `replaceAll(pattern, replacement)` | Replaces all matches of pattern with replacement | Transform |
| 20 | `search(regexp)` | Returns index of first regex match, or -1 | Pattern |
| 21 | `slice(start, end?)` | Extracts section of string, supports negative indices | Extract |
| 22 | `split(separator, limit?)` | Splits string by separator into array | Transform |
| 23 | `startsWith(search, position?)` | Checks if string starts with given substring | Search |
| 24 | `substring(start, end?)` | Extracts characters between two indices (no negatives) | Extract |
| 25 | `toLocaleLowerCase(locales?)` | Converts to lowercase using locale-specific mappings | Case |
| 26 | `toLocaleUpperCase(locales?)` | Converts to uppercase using locale-specific mappings | Case |
| 27 | `toLowerCase()` | Converts all characters to lowercase | Case |
| 28 | `toUpperCase()` | Converts all characters to uppercase | Case |
| 29 | `toWellFormed()` | Returns copy with lone surrogates replaced by U+FFFD (ES2024) | Encoding |
| 30 | `trim()` | Removes whitespace from both ends | Whitespace |
| 31 | `trimEnd()` | Removes whitespace from end (alias: trimRight) | Whitespace |
| 32 | `trimStart()` | Removes whitespace from start (alias: trimLeft) | Whitespace |
| 33 | `toString()` | Returns the string value | Conversion |
| 34 | `valueOf()` | Returns primitive value of String object | Conversion |
| 35 | `[Symbol.iterator]()` | Returns iterator over characters (supports for...of) | Iteration |

### String static methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `String.raw(strings, ...subs)` | Tag function for template literals, returns raw string (no escape processing) | Template |
| 2 | `String.fromCharCode(...codes)` | Creates string from UTF-16 code units | Encoding |
| 3 | `String.fromCodePoint(...codePoints)` | Creates string from Unicode code points (handles supplementary) | Encoding |

### Template literal features

| # | Feature | Description | Category |
|---|---------|-------------|----------|
| 1 | Template literals | Backtick strings with `${expr}` interpolation | Syntax |
| 2 | Tagged templates | `tag\`...\`` — custom processing via tag function | Syntax |
| 3 | Raw strings | `String.raw\`...\`` — no escape sequence processing | Syntax |
| 4 | Nested templates | Template literals inside `${}` expressions | Syntax |
| 5 | Multi-line | Template literals preserve newlines | Syntax |

### Additional text utilities

| # | API | Description | Category |
|---|-----|-------------|----------|
| 1 | `Intl.Collator` | Locale-sensitive string comparison with configurable sensitivity/ordering | Unicode |
| 2 | `Intl.Segmenter` | Proper Unicode segmentation (grapheme, word, sentence boundaries) | Unicode |
| 3 | `TextEncoder` | Encodes string to Uint8Array (UTF-8) | Encoding |
| 4 | `TextDecoder` | Decodes Uint8Array to string (supports many encodings) | Encoding |
| 5 | `encodeURI(uri)` | Encodes URI, preserving special URI characters (:/?#@!$&) | URI |
| 6 | `encodeURIComponent(str)` | Encodes URI component, escapes all special characters | URI |
| 7 | `decodeURI(encoded)` | Decodes a URI encoded by encodeURI | URI |
| 8 | `decodeURIComponent(encoded)` | Decodes a URI component encoded by encodeURIComponent | URI |
| 9 | `btoa(string)` | Encodes binary string to base64 ASCII string | Base64 |
| 10 | `atob(encoded)` | Decodes base64 ASCII string to binary string | Base64 |
| 11 | `JSON.stringify(value, replacer?, space?)` | Serializes value to JSON string | Serialization |
| 12 | `JSON.parse(text, reviver?)` | Parses JSON string to JavaScript value | Serialization |

---

## 2. File/Path (Node.js)

### fs module — Callback-based async

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `readFile(path, options?, cb)` | Reads entire file contents asynchronously | Read |
| 2 | `writeFile(path, data, options?, cb)` | Writes data to file, replacing if exists | Write |
| 3 | `appendFile(path, data, options?, cb)` | Appends data to end of file | Write |
| 4 | `readdir(path, options?, cb)` | Reads directory contents as array of filenames | Directory |
| 5 | `stat(path, options?, cb)` | Returns file metadata (size, dates, type) via Stats object | Metadata |
| 6 | `lstat(path, options?, cb)` | Like stat but does not follow symlinks | Metadata |
| 7 | `access(path, mode?, cb)` | Tests file accessibility (existence, read, write, execute) | Metadata |
| 8 | `exists(path, cb)` | Tests if path exists (DEPRECATED — use access) | Metadata |
| 9 | `mkdir(path, options?, cb)` | Creates directory (supports recursive via options) | Directory |
| 10 | `rmdir(path, options?, cb)` | Removes directory (DEPRECATED for recursive — use rm) | Directory |
| 11 | `rm(path, options?, cb)` | Removes files and directories (supports recursive, force) | Delete |
| 12 | `rename(oldPath, newPath, cb)` | Renames/moves file or directory | Modify |
| 13 | `copyFile(src, dest, mode?, cb)` | Copies file from src to dest | Copy |
| 14 | `cp(src, dest, options?, cb)` | Copies files/directories recursively (ES2022+) | Copy |
| 15 | `link(existingPath, newPath, cb)` | Creates hard link | Link |
| 16 | `symlink(target, path, type?, cb)` | Creates symbolic link | Link |
| 17 | `readlink(path, options?, cb)` | Reads value of symbolic link | Link |
| 18 | `unlink(path, cb)` | Deletes file or symbolic link | Delete |
| 19 | `chmod(path, mode, cb)` | Changes file permissions | Permission |
| 20 | `chown(path, uid, gid, cb)` | Changes file ownership | Permission |
| 21 | `truncate(path, len?, cb)` | Truncates file to specified length | Modify |
| 22 | `watch(filename, options?, listener?)` | Watches for file/directory changes (returns FSWatcher) | Watch |
| 23 | `watchFile(filename, options?, listener)` | Watches for file changes via polling (stat-based) | Watch |
| 24 | `unwatchFile(filename, listener?)` | Stops watching file previously watched with watchFile | Watch |
| 25 | `createReadStream(path, options?)` | Creates readable stream from file | Stream |
| 26 | `createWriteStream(path, options?)` | Creates writable stream to file | Stream |
| 27 | `open(path, flags, mode?, cb)` | Opens file, returns file descriptor | Low-level |
| 28 | `close(fd, cb)` | Closes file descriptor | Low-level |
| 29 | `read(fd, buffer, offset, length, position, cb)` | Reads data from file descriptor into buffer | Low-level |
| 30 | `write(fd, buffer, offset, length, position, cb)` | Writes buffer data to file descriptor | Low-level |
| 31 | `realpath(path, options?, cb)` | Resolves canonical absolute pathname (resolves symlinks, `.`, `..`) | Path |
| 32 | `mkdtemp(prefix, options?, cb)` | Creates unique temporary directory with given prefix | Directory |
| 33 | `glob(pattern, options?, cb)` | Matches files using glob pattern (Node 22+) | Search |

### fs module — Sync versions

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `readFileSync(path, options?)` | Synchronously reads entire file contents | Read |
| 2 | `writeFileSync(path, data, options?)` | Synchronously writes data to file | Write |
| 3 | `appendFileSync(path, data, options?)` | Synchronously appends data to file | Write |
| 4 | `readdirSync(path, options?)` | Synchronously reads directory contents | Directory |
| 5 | `statSync(path, options?)` | Synchronously returns file Stats | Metadata |
| 6 | `lstatSync(path, options?)` | Synchronously returns symlink Stats | Metadata |
| 7 | `accessSync(path, mode?)` | Synchronously tests file accessibility (throws on fail) | Metadata |
| 8 | `existsSync(path)` | Synchronously tests if path exists (returns boolean) | Metadata |
| 9 | `mkdirSync(path, options?)` | Synchronously creates directory | Directory |
| 10 | `rmdirSync(path, options?)` | Synchronously removes directory | Directory |
| 11 | `rmSync(path, options?)` | Synchronously removes files/directories | Delete |
| 12 | `renameSync(oldPath, newPath)` | Synchronously renames/moves file | Modify |
| 13 | `copyFileSync(src, dest, mode?)` | Synchronously copies file | Copy |
| 14 | `cpSync(src, dest, options?)` | Synchronously copies files/directories recursively | Copy |
| 15 | `linkSync(existingPath, newPath)` | Synchronously creates hard link | Link |
| 16 | `symlinkSync(target, path, type?)` | Synchronously creates symbolic link | Link |
| 17 | `readlinkSync(path, options?)` | Synchronously reads symbolic link target | Link |
| 18 | `unlinkSync(path)` | Synchronously deletes file | Delete |
| 19 | `chmodSync(path, mode)` | Synchronously changes file permissions | Permission |
| 20 | `chownSync(path, uid, gid)` | Synchronously changes file ownership | Permission |
| 21 | `truncateSync(path, len?)` | Synchronously truncates file | Modify |
| 22 | `openSync(path, flags, mode?)` | Synchronously opens file, returns fd | Low-level |
| 23 | `closeSync(fd)` | Synchronously closes file descriptor | Low-level |
| 24 | `readSync(fd, buffer, offset, length, position)` | Synchronously reads from file descriptor | Low-level |
| 25 | `writeSync(fd, buffer, offset, length, position)` | Synchronously writes to file descriptor | Low-level |
| 26 | `realpathSync(path, options?)` | Synchronously resolves canonical path | Path |
| 27 | `mkdtempSync(prefix, options?)` | Synchronously creates unique temp directory | Directory |
| 28 | `globSync(pattern, options?)` | Synchronously matches files by glob (Node 22+) | Search |

### fs.promises (promise-based async)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `readFile(path, options?)` | Reads file, returns Promise<Buffer/string> | Read |
| 2 | `writeFile(path, data, options?)` | Writes file, returns Promise<void> | Write |
| 3 | `appendFile(path, data, options?)` | Appends to file, returns Promise<void> | Write |
| 4 | `readdir(path, options?)` | Reads directory, returns Promise<string[]> | Directory |
| 5 | `stat(path, options?)` | Returns Promise<Stats> | Metadata |
| 6 | `lstat(path, options?)` | Returns Promise<Stats> without following symlinks | Metadata |
| 7 | `access(path, mode?)` | Tests accessibility, returns Promise<void> | Metadata |
| 8 | `mkdir(path, options?)` | Creates directory, returns Promise | Directory |
| 9 | `rmdir(path, options?)` | Removes directory, returns Promise | Directory |
| 10 | `rm(path, options?)` | Removes file/directory, returns Promise | Delete |
| 11 | `rename(oldPath, newPath)` | Renames, returns Promise | Modify |
| 12 | `copyFile(src, dest, mode?)` | Copies file, returns Promise | Copy |
| 13 | `cp(src, dest, options?)` | Copies recursively, returns Promise | Copy |
| 14 | `link(existingPath, newPath)` | Creates hard link, returns Promise | Link |
| 15 | `symlink(target, path, type?)` | Creates symlink, returns Promise | Link |
| 16 | `readlink(path, options?)` | Reads symlink target, returns Promise | Link |
| 17 | `unlink(path)` | Deletes file, returns Promise | Delete |
| 18 | `chmod(path, mode)` | Changes permissions, returns Promise | Permission |
| 19 | `chown(path, uid, gid)` | Changes ownership, returns Promise | Permission |
| 20 | `truncate(path, len?)` | Truncates file, returns Promise | Modify |
| 21 | `open(path, flags, mode?)` | Opens file, returns Promise<FileHandle> | Low-level |
| 22 | `realpath(path, options?)` | Resolves path, returns Promise | Path |
| 23 | `mkdtemp(prefix, options?)` | Creates temp dir, returns Promise<string> | Directory |
| 24 | `glob(pattern, options?)` | Glob match, returns AsyncIterable (Node 22+) | Search |
| 25 | `watch(filename, options?)` | Returns async iterable of file changes | Watch |

### path module

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `basename(path, ext?)` | Returns last portion of path (filename), optionally removing extension | Parse |
| 2 | `dirname(path)` | Returns directory name of path | Parse |
| 3 | `extname(path)` | Returns file extension (including dot: `.js`) | Parse |
| 4 | `format(pathObject)` | Creates path string from `{dir, root, base, name, ext}` object | Build |
| 5 | `isAbsolute(path)` | Returns true if path is absolute | Query |
| 6 | `join(...paths)` | Joins path segments with platform separator, normalizes result | Build |
| 7 | `normalize(path)` | Resolves `.` and `..` segments, normalizes separators | Normalize |
| 8 | `parse(path)` | Parses path into `{root, dir, base, ext, name}` object | Parse |
| 9 | `relative(from, to)` | Returns relative path from `from` to `to` | Compute |
| 10 | `resolve(...paths)` | Resolves sequence of paths to absolute path | Build |
| 11 | `sep` | Platform-specific path separator (`/` or `\\`) | Constant |
| 12 | `delimiter` | Platform-specific PATH delimiter (`:` or `;`) | Constant |
| 13 | `toNamespacedPath(path)` | On Windows, converts to extended-length path (`\\?\`); noop on POSIX | Platform |
| 14 | `path.posix` | Provides POSIX-specific path methods regardless of platform | Namespace |
| 15 | `path.win32` | Provides Windows-specific path methods regardless of platform | Namespace |

### stream module

| # | Class/Function | Description | Category |
|---|----------------|-------------|----------|
| 1 | `Readable` | Base class for readable streams (data source) | Class |
| 2 | `Writable` | Base class for writable streams (data sink) | Class |
| 3 | `Transform` | Duplex stream that transforms data passing through | Class |
| 4 | `Duplex` | Stream that is both readable and writable | Class |
| 5 | `PassThrough` | Transform stream that passes data through unchanged | Class |
| 6 | `pipeline(...streams, cb)` | Pipes streams together with error handling and cleanup | Utility |
| 7 | `finished(stream, options?, cb)` | Notifies when stream is no longer readable/writable or has errored | Utility |
| 8 | `Readable.from(iterable, options?)` | Creates Readable from iterable or async iterable | Factory |
| 9 | `Readable.toWeb(readable)` | Converts Node Readable to Web ReadableStream | Interop |
| 10 | `Writable.toWeb(writable)` | Converts Node Writable to Web WritableStream | Interop |

---

## 3. Collection Methods

### Array.prototype (instance methods)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `at(index)` | Returns element at index, supports negative indexing | Access |
| 2 | `concat(...items)` | Merges arrays/values, returns new array | Combine |
| 3 | `copyWithin(target, start, end?)` | Copies sequence of elements within array (mutates) | Mutate |
| 4 | `entries()` | Returns iterator of [index, value] pairs | Iteration |
| 5 | `every(callback, thisArg?)` | Tests if all elements pass predicate | Search |
| 6 | `fill(value, start?, end?)` | Fills array range with static value (mutates) | Mutate |
| 7 | `filter(callback, thisArg?)` | Returns new array with elements passing predicate | Transform |
| 8 | `find(callback, thisArg?)` | Returns first element passing predicate, or undefined | Search |
| 9 | `findIndex(callback, thisArg?)` | Returns index of first element passing predicate, or -1 | Search |
| 10 | `findLast(callback, thisArg?)` | Returns last element passing predicate (ES2023) | Search |
| 11 | `findLastIndex(callback, thisArg?)` | Returns index of last element passing predicate (ES2023) | Search |
| 12 | `flat(depth?)` | Flattens nested arrays to specified depth (default 1) | Transform |
| 13 | `flatMap(callback, thisArg?)` | Maps then flattens one level (more efficient than map+flat) | Transform |
| 14 | `forEach(callback, thisArg?)` | Executes callback for each element (no return value) | Iteration |
| 15 | `includes(value, fromIndex?)` | Checks if array contains value (uses SameValueZero) | Search |
| 16 | `indexOf(value, fromIndex?)` | Returns first index of value, or -1 | Search |
| 17 | `join(separator?)` | Joins all elements into string with separator (default `,`) | Convert |
| 18 | `keys()` | Returns iterator of array indices | Iteration |
| 19 | `lastIndexOf(value, fromIndex?)` | Returns last index of value, or -1 | Search |
| 20 | `map(callback, thisArg?)` | Returns new array with results of calling callback on each element | Transform |
| 21 | `pop()` | Removes and returns last element (mutates) | Mutate |
| 22 | `push(...items)` | Adds elements to end, returns new length (mutates) | Mutate |
| 23 | `reduce(callback, initialValue?)` | Reduces array to single value left-to-right | Aggregate |
| 24 | `reduceRight(callback, initialValue?)` | Reduces array to single value right-to-left | Aggregate |
| 25 | `reverse()` | Reverses array in place (mutates) | Mutate |
| 26 | `shift()` | Removes and returns first element (mutates) | Mutate |
| 27 | `slice(start?, end?)` | Returns shallow copy of portion, supports negatives | Extract |
| 28 | `some(callback, thisArg?)` | Tests if at least one element passes predicate | Search |
| 29 | `sort(compareFn?)` | Sorts array in place (mutates); default is string-order | Mutate |
| 30 | `splice(start, deleteCount?, ...items)` | Adds/removes elements at position (mutates) | Mutate |
| 31 | `toLocaleString(locales?, options?)` | Returns locale-aware string representation | Convert |
| 32 | `toReversed()` | Returns new reversed array without mutating (ES2023) | Transform |
| 33 | `toSorted(compareFn?)` | Returns new sorted array without mutating (ES2023) | Transform |
| 34 | `toSpliced(start, deleteCount?, ...items)` | Returns new array with splice applied, no mutation (ES2023) | Transform |
| 35 | `toString()` | Returns comma-separated string of elements | Convert |
| 36 | `unshift(...items)` | Adds elements to beginning, returns new length (mutates) | Mutate |
| 37 | `values()` | Returns iterator of array values | Iteration |
| 38 | `with(index, value)` | Returns new array with element at index replaced (ES2023) | Transform |
| 39 | `[Symbol.iterator]()` | Returns default iterator (same as values()) | Iteration |

### Array static methods

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `Array.from(iterable, mapFn?, thisArg?)` | Creates array from iterable or array-like object | Factory |
| 2 | `Array.fromAsync(iterable, mapFn?, thisArg?)` | Creates array from async iterable (ES2024) | Factory |
| 3 | `Array.isArray(value)` | Returns true if value is an Array | Query |
| 4 | `Array.of(...items)` | Creates array from arguments (unlike `Array(n)` which creates sparse) | Factory |

### Object.groupBy / Map.groupBy (ES2024)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `Object.groupBy(iterable, keyFn)` | Groups elements into object by key function result | Group |
| 2 | `Map.groupBy(iterable, keyFn)` | Groups elements into Map by key function result | Group |

### Map

| # | Method/Property | Description | Category |
|---|-----------------|-------------|----------|
| 1 | `set(key, value)` | Adds or updates entry, returns the Map | Mutate |
| 2 | `get(key)` | Returns value for key, or undefined | Access |
| 3 | `has(key)` | Returns true if key exists | Query |
| 4 | `delete(key)` | Removes entry by key, returns true if existed | Mutate |
| 5 | `clear()` | Removes all entries | Mutate |
| 6 | `forEach(callback, thisArg?)` | Executes callback for each entry | Iteration |
| 7 | `entries()` | Returns iterator of [key, value] pairs | Iteration |
| 8 | `keys()` | Returns iterator of keys | Iteration |
| 9 | `values()` | Returns iterator of values | Iteration |
| 10 | `size` | Returns number of entries (property, not method) | Query |
| 11 | `[Symbol.iterator]()` | Returns default iterator (same as entries()) | Iteration |

### Set

| # | Method/Property | Description | Category |
|---|-----------------|-------------|----------|
| 1 | `add(value)` | Adds value to set, returns the Set | Mutate |
| 2 | `has(value)` | Returns true if value exists in set | Query |
| 3 | `delete(value)` | Removes value, returns true if existed | Mutate |
| 4 | `clear()` | Removes all values | Mutate |
| 5 | `forEach(callback, thisArg?)` | Executes callback for each value | Iteration |
| 6 | `entries()` | Returns iterator of [value, value] pairs (for Map compat) | Iteration |
| 7 | `keys()` | Returns iterator of values (alias of values()) | Iteration |
| 8 | `values()` | Returns iterator of values | Iteration |
| 9 | `size` | Returns number of values (property) | Query |
| 10 | `[Symbol.iterator]()` | Returns default iterator (same as values()) | Iteration |
| 11 | `difference(other)` | Returns new Set with elements not in other (ES2025) | Set-op |
| 12 | `intersection(other)` | Returns new Set with elements in both (ES2025) | Set-op |
| 13 | `symmetricDifference(other)` | Returns new Set with elements in either but not both (ES2025) | Set-op |
| 14 | `union(other)` | Returns new Set with all elements from both (ES2025) | Set-op |
| 15 | `isSubsetOf(other)` | Returns true if all elements are in other (ES2025) | Set-op |
| 16 | `isSupersetOf(other)` | Returns true if contains all elements of other (ES2025) | Set-op |
| 17 | `isDisjointFrom(other)` | Returns true if no elements in common (ES2025) | Set-op |

### WeakMap

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `set(key, value)` | Adds entry with object/symbol key, returns WeakMap | Mutate |
| 2 | `get(key)` | Returns value for key, or undefined | Access |
| 3 | `has(key)` | Returns true if key exists | Query |
| 4 | `delete(key)` | Removes entry, returns true if existed | Mutate |

### WeakSet

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `add(value)` | Adds object/symbol value, returns WeakSet | Mutate |
| 2 | `has(value)` | Returns true if value exists | Query |
| 3 | `delete(value)` | Removes value, returns true if existed | Mutate |

### Object (as collection utility)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `Object.keys(obj)` | Returns array of own enumerable string property names | Enumerate |
| 2 | `Object.values(obj)` | Returns array of own enumerable property values | Enumerate |
| 3 | `Object.entries(obj)` | Returns array of own enumerable [key, value] pairs | Enumerate |
| 4 | `Object.assign(target, ...sources)` | Copies own enumerable properties from sources to target | Merge |
| 5 | `Object.fromEntries(iterable)` | Creates object from iterable of [key, value] pairs | Factory |
| 6 | `Object.hasOwn(obj, prop)` | Returns true if object has own property (ES2022, replaces hasOwnProperty) | Query |
| 7 | `Object.freeze(obj)` | Prevents modifications to object (shallow) | Immutability |
| 8 | `Object.seal(obj)` | Prevents adding/removing properties, allows value changes | Immutability |
| 9 | `Object.isFrozen(obj)` | Returns true if object is frozen | Query |
| 10 | `Object.isSealed(obj)` | Returns true if object is sealed | Query |
| 11 | `Object.is(value1, value2)` | Compares values using SameValue algorithm (NaN === NaN is true) | Comparison |
| 12 | `Object.create(proto, propertiesObject?)` | Creates object with specified prototype | Factory |
| 13 | `Object.defineProperty(obj, prop, descriptor)` | Defines/modifies property with descriptor | Define |
| 14 | `Object.defineProperties(obj, props)` | Defines/modifies multiple properties | Define |
| 15 | `Object.getOwnPropertyDescriptor(obj, prop)` | Returns property descriptor for own property | Inspect |
| 16 | `Object.getOwnPropertyDescriptors(obj)` | Returns all own property descriptors | Inspect |
| 17 | `Object.getOwnPropertyNames(obj)` | Returns all own property names (including non-enumerable) | Enumerate |
| 18 | `Object.getOwnPropertySymbols(obj)` | Returns all own Symbol properties | Enumerate |
| 19 | `Object.getPrototypeOf(obj)` | Returns prototype of object | Prototype |
| 20 | `Object.setPrototypeOf(obj, proto)` | Sets prototype of object (slow, avoid in hot paths) | Prototype |
| 21 | `Object.groupBy(iterable, keyFn)` | Groups iterable elements by key function (ES2024) | Group |

### Iterator helpers (ES2025)

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `Iterator.prototype.map(fn)` | Returns iterator that applies fn to each element | Transform |
| 2 | `Iterator.prototype.filter(fn)` | Returns iterator of elements passing predicate | Filter |
| 3 | `Iterator.prototype.take(limit)` | Returns iterator of first N elements | Limit |
| 4 | `Iterator.prototype.drop(limit)` | Returns iterator skipping first N elements | Limit |
| 5 | `Iterator.prototype.flatMap(fn)` | Maps then flattens one level, returns iterator | Transform |
| 6 | `Iterator.prototype.reduce(fn, initial?)` | Reduces iterator to single value | Aggregate |
| 7 | `Iterator.prototype.toArray()` | Collects iterator into array | Convert |
| 8 | `Iterator.prototype.forEach(fn)` | Executes fn for each element | Iteration |
| 9 | `Iterator.prototype.some(fn)` | Returns true if any element passes predicate | Search |
| 10 | `Iterator.prototype.every(fn)` | Returns true if all elements pass predicate | Search |
| 11 | `Iterator.prototype.find(fn)` | Returns first element passing predicate | Search |
| 12 | `Iterator.from(iterableOrIterator)` | Wraps iterable/iterator as proper Iterator object | Factory |

### TypedArray shared methods

All TypedArrays (`Int8Array`, `Uint8Array`, `Uint8ClampedArray`, `Int16Array`, `Uint16Array`, `Int32Array`, `Uint32Array`, `Float32Array`, `Float64Array`, `BigInt64Array`, `BigUint64Array`) share these methods:

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `at(index)` | Returns element at index, supports negatives | Access |
| 2 | `copyWithin(target, start, end?)` | Copies sequence within array | Mutate |
| 3 | `entries()` | Returns iterator of [index, value] pairs | Iteration |
| 4 | `every(callback, thisArg?)` | Tests if all elements pass predicate | Search |
| 5 | `fill(value, start?, end?)` | Fills range with value | Mutate |
| 6 | `filter(callback, thisArg?)` | Returns new TypedArray with passing elements | Transform |
| 7 | `find(callback, thisArg?)` | Returns first passing element | Search |
| 8 | `findIndex(callback, thisArg?)` | Returns index of first passing element | Search |
| 9 | `findLast(callback, thisArg?)` | Returns last passing element (ES2023) | Search |
| 10 | `findLastIndex(callback, thisArg?)` | Returns index of last passing element (ES2023) | Search |
| 11 | `forEach(callback, thisArg?)` | Executes callback per element | Iteration |
| 12 | `includes(value, fromIndex?)` | Checks if value exists | Search |
| 13 | `indexOf(value, fromIndex?)` | Returns first index of value | Search |
| 14 | `join(separator?)` | Joins elements as string | Convert |
| 15 | `keys()` | Returns iterator of indices | Iteration |
| 16 | `lastIndexOf(value, fromIndex?)` | Returns last index of value | Search |
| 17 | `map(callback, thisArg?)` | Returns new TypedArray with mapped values | Transform |
| 18 | `reduce(callback, initialValue?)` | Reduces left-to-right | Aggregate |
| 19 | `reduceRight(callback, initialValue?)` | Reduces right-to-left | Aggregate |
| 20 | `reverse()` | Reverses in place | Mutate |
| 21 | `set(array, offset?)` | Copies values from array/TypedArray into this | Mutate |
| 22 | `slice(start?, end?)` | Returns new TypedArray with portion | Extract |
| 23 | `some(callback, thisArg?)` | Tests if any element passes predicate | Search |
| 24 | `sort(compareFn?)` | Sorts in place (numeric by default, unlike Array) | Mutate |
| 25 | `subarray(begin?, end?)` | Returns new TypedArray sharing same buffer (no copy) | View |
| 26 | `toLocaleString(locales?, options?)` | Returns locale-aware string | Convert |
| 27 | `toString()` | Returns comma-separated string | Convert |
| 28 | `values()` | Returns iterator of values | Iteration |
| 29 | `toReversed()` | Returns new reversed TypedArray (ES2023) | Transform |
| 30 | `toSorted(compareFn?)` | Returns new sorted TypedArray (ES2023) | Transform |
| 31 | `with(index, value)` | Returns new TypedArray with element replaced (ES2023) | Transform |
| 32 | `[Symbol.iterator]()` | Default iterator (same as values()) | Iteration |

TypedArray static methods:

| # | Method | Description | Category |
|---|--------|-------------|----------|
| 1 | `TypedArray.from(source, mapFn?, thisArg?)` | Creates TypedArray from iterable/array-like | Factory |
| 2 | `TypedArray.of(...items)` | Creates TypedArray from arguments | Factory |
| 3 | `TypedArray.BYTES_PER_ELEMENT` | Number of bytes per element (constant per type) | Constant |

### Utility functions

| # | Function | Description | Category |
|---|----------|-------------|----------|
| 1 | `structuredClone(value, options?)` | Deep clones value (handles circular refs, typed arrays, etc.) | Clone |
| 2 | `Promise.all(iterable)` | Resolves when all promises resolve, rejects on first reject | Async |
| 3 | `Promise.allSettled(iterable)` | Resolves when all promises settle (fulfilled or rejected) | Async |
| 4 | `Promise.any(iterable)` | Resolves with first fulfilled promise, rejects if all reject | Async |
| 5 | `Promise.race(iterable)` | Resolves/rejects with first settled promise | Async |
| 6 | `Promise.resolve(value)` | Returns Promise resolved with value | Async |
| 7 | `Promise.reject(reason)` | Returns Promise rejected with reason | Async |
| 8 | `Promise.withResolvers()` | Returns {promise, resolve, reject} (ES2024) | Async |

---

## Summary Statistics

| Section | Count |
|---------|-------|
| String.prototype methods | 35 |
| String static methods | 3 |
| Template literal features | 5 |
| Text utilities (Intl, encoding, URI, etc.) | 12 |
| **String total** | **55** |
| fs callback methods | 33 |
| fs sync methods | 28 |
| fs.promises methods | 25 |
| path module | 15 |
| stream module | 10 |
| **File/Path total** | **111** |
| Array.prototype methods | 39 |
| Array static methods | 4 |
| Map methods | 11 |
| Set methods | 17 |
| WeakMap methods | 4 |
| WeakSet methods | 3 |
| Object utility methods | 21 |
| Iterator helpers | 12 |
| TypedArray shared methods | 32 |
| TypedArray static methods | 3 |
| Utility functions (clone, Promise) | 8 |
| groupBy (Object/Map) | 2 |
| **Collection total** | **156** |
| **Grand total** | **322** |

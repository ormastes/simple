# Stdlib Helper Methods — Gap Analysis & Implementation Plan

**Date:** 2026-03-26
**Scope:** Text, File/IO, Collection helper methods
**Compared against:** Python, Ruby, Go, TypeScript/JavaScript
**Status:** Phase 1 Requirements

---

## Executive Summary

Cross-referenced Simple's existing stdlib (~850+ methods) against Python (404), Ruby (769), Go (430), and TypeScript (322) method inventories. Simple already has excellent coverage in most areas. This plan identifies **83 missing methods** worth implementing, organized into 6 priority tiers.

**Coverage by category:**
| Category | Simple Has | Cross-Lang Union | Coverage | Missing |
|----------|-----------|-----------------|----------|---------|
| Text/String | ~200 | ~250 | ~80% | ~25 |
| Collections | ~350 | ~400 | ~87% | ~33 |
| File/IO | ~300 | ~325 | ~92% | ~25 |

---

## TIER 1: High-Value Missing Methods (Essential)

Methods present in 3+ languages that Simple lacks. Highest developer productivity impact.

### 1.1 Text/String Methods

| # | Method | Signature | Description | In Languages | Priority |
|---|--------|-----------|-------------|-------------|----------|
| T1 | `to_kebab_case()` | `() -> text` | Convert to kebab-case ("hello-world") | Py(lib), Ruby(lib), JS(lib) | P1 |
| T2 | `to_pascal_case()` | `() -> text` | Convert to PascalCase ("HelloWorld") | Py(lib), Ruby(lib), JS(lib) | P1 |
| T3 | `to_screaming_snake()` | `() -> text` | Convert to SCREAMING_SNAKE ("HELLO_WORLD") | Py(lib), Ruby(lib), Go(lib) | P1 |
| T4 | `chars_map(fn)` | `(fn(text)->text) -> text` | Apply function to each character, rebuild | Go(strings.Map), Ruby(tr concept) | P1 |
| T5 | `tr(from, to)` | `(text, text) -> text` | Character transliteration (a->b, c->d) | Ruby(tr), Python(maketrans/translate) | P1 |
| T6 | `encode(encoding)` | `(text) -> [u8]` | Encode string to bytes with charset | Python, Ruby, Go, JS | P2 |
| T7 | `decode(bytes, encoding)` | `([u8], text) -> text` | Decode bytes to string with charset | Python, Ruby, Go, JS | P2 |
| T8 | `normalize(form)` | `(text) -> text` | Unicode normalization (NFC/NFD/NFKC/NFKD) | Python, Ruby, Go, JS | P2 |
| T9 | `is_title()` | `() -> bool` | Check if string is title-cased | Python(istitle), Ruby | P2 |
| T10 | `expandtabs(tabsize?)` | `(i64?) -> text` | Replace tabs with spaces | Python(expandtabs) | P3 |
| T11 | `scan(pattern)` | `(text) -> [text]` | Find all pattern matches (alias regex_find_all) | Ruby(scan), Go(FindAll) | P2 |
| T12 | `gsub(pattern, fn)` | `(text, fn(text)->text) -> text` | Replace with callback function | Ruby(gsub+block), JS(replace+fn), Go(ReplaceAllStringFunc) | P1 |
| T13 | `ljust(width, char?)` | `(i64, text?) -> text` | Left-justify (alias pad_right) | Python(ljust), Ruby(ljust) | P3-alias |
| T14 | `rjust(width, char?)` | `(i64, text?) -> text` | Right-justify (alias pad_left) | Python(rjust), Ruby(rjust) | P3-alias |
| T15 | `casefold()` | `() -> text` | Aggressive case folding for caseless matching | Python(casefold) | P3 |
| T16 | `each_char(fn)` | `(fn(text))` | Iterate over characters with callback | Ruby(each_char), Go(range) | P2 |
| T17 | `each_line(fn)` | `(fn(text))` | Iterate over lines with callback | Ruby(each_line) | P2 |
| T18 | `match_all(pattern)` | `(text) -> Iterator` | Iterator over all regex matches | JS(matchAll), Ruby(scan) | P2 |
| T19 | `replace_n(old, new, n)` | `(text, text, i64) -> text` | Replace first N occurrences | Go(Replace with count), Python | P2 |
| T20 | `split_n(sep, n)` | `(text, i64) -> [text]` | Split with limit | Go(SplitN), Ruby(split+limit), JS(split+limit) | P1 |
| T21 | `hex_to_int()` | `() -> i64?` | Parse hex string to integer | Ruby(hex), Python(int(s,16)) | P2 |
| T22 | `oct_to_int()` | `() -> i64?` | Parse octal string to integer | Ruby(oct), Python(int(s,8)) | P3 |
| T23 | `to_int_radix(base)` | `(i64) -> i64?` | Parse string as number in given base | Python(int(s,base)), Go(ParseInt) | P2 |
| T24 | `multiply(n)` | `(i64) -> text` | Alias for repeat (Ruby's * operator) | Ruby(*), Python(*) | P3-alias |
| T25 | `insert(idx, s)` | `(i64, text) -> text` | Insert string at index | Ruby(insert) | P2 |

### 1.2 Collection Methods

| # | Method | Target | Signature | Description | In Languages | Priority |
|---|--------|--------|-----------|-------------|-------------|----------|
| C1 | `sort_by_key(fn)` | Array | `(fn(T)->K) -> [T]` | Sort by extracted key | Ruby(sort_by), Python(key=) | P1 |
| C2 | `min_by(fn)` | Array | `(fn(T,T)->i64) -> T?` | Min by comparator | Ruby, Python, Go, JS | P1 |
| C3 | `max_by(fn)` | Array | `(fn(T,T)->i64) -> T?` | Max by comparator | Ruby, Python, Go, JS | P1 |
| C4 | `min_by_key(fn)` | Array | `(fn(T)->K) -> T?` | Min by key function | Ruby(min_by), Python(min+key) | P1 |
| C5 | `max_by_key(fn)` | Array | `(fn(T)->K) -> T?` | Max by key function | Ruby(max_by), Python(max+key) | P1 |
| C6 | `minmax()` | Array | `() -> (T?, T?)` | Both min and max in one pass | Ruby(minmax) | P2 |
| C7 | `sample(n?)` | Array | `(i64?) -> T or [T]` | Random sample | Ruby(sample), Python(random.choice) | P2 |
| C8 | `shuffle()` | Array | `() -> [T]` | Random shuffle | Ruby(shuffle), Python(random.shuffle) | P2 |
| C9 | `combination(n)` | Array | `(i64) -> [[T]]` | N-element combinations | Ruby(combination), Python(itertools) | P2 |
| C10 | `permutation(n?)` | Array | `(i64?) -> [[T]]` | N-element permutations | Ruby(permutation), Python(itertools) | P2 |
| C11 | `each(fn)` | Array | `(fn(T))` | Iterate with callback (alias for_each) | Ruby(each), JS(forEach) | P1 |
| C12 | `each_with_index(fn)` | Array | `(fn(T, i64))` | Iterate with index callback | Ruby(each_with_index), JS(forEach) | P1 |
| C13 | `flat_map(fn)` | Array(method) | `(fn(T)->[U]) -> [U]` | Map then flatten (as built-in method) | Ruby, Python, JS, Go | P1 |
| C14 | `compact_map(fn)` | Array | `(fn(T)->U?) -> [U]` | Map then remove nils | Swift(compactMap), Ruby(filter_map) | P2 |
| C15 | `fill(value)` | Array | `(T) -> [T]` | Fill array with value | JS(fill), Ruby(fill) | P2 |
| C16 | `fill_range(value, start, end)` | Array | `(T, i64, i64) -> [T]` | Fill range with value | JS(fill), Ruby(fill) | P3 |
| C17 | `insert_at(idx, item)` | Array | `(i64, T) -> [T]` | Insert at index | Ruby(insert), Python(insert), JS(splice) | P1 |
| C18 | `remove_at(idx)` | Array | `(i64) -> [T]` | Remove at index | Python(pop(i)), Ruby(delete_at), JS(splice) | P1 |
| C19 | `values_at(indices)` | Array | `([i64]) -> [T]` | Get multiple elements by indices | Ruby(values_at) | P2 |
| C20 | `bsearch(target)` | Array | `(T) -> i64?` | Binary search (sorted array) | Ruby(bsearch), Go(slices.BinarySearch) | P2 |
| C21 | `unshift(item)` | Array | `(T) -> [T]` | Prepend element (alias) | Ruby(unshift), JS(unshift) | P2-alias |
| C22 | `shift()` | Array | `() -> T?` | Remove first element | Ruby(shift), JS(shift) | P2 |
| C23 | `pop()` | Array | `() -> T?` | Remove last element | Ruby(pop), Python(pop), JS(pop) | P1 |
| C24 | `sum_by(fn)` | Array | `(fn(T)->i64) -> i64` | Sum by extracted value | Ruby(sum+block), Python(sum+gen) | P2 |
| C25 | `tally()` | Array | `() -> Map<T, i64>` | Count element frequencies | Ruby(tally) | P2 |
| C26 | `each_slice(n, fn)` | Array | `(i64, fn([T]))` | Process in chunks with callback | Ruby(each_slice) | P2 |
| C27 | `each_cons(n, fn)` | Array | `(i64, fn([T]))` | Sliding window with callback | Ruby(each_cons) | P2 |
| C28 | `reject(fn)` | Array | `(fn(T)->bool) -> [T]` | Inverse filter (keep non-matching) | Ruby(reject) | P1 |
| C29 | `detect(fn)` | Array | `(fn(T)->bool) -> T?` | Alias for find | Ruby(detect) | P3-alias |
| C30 | `collect(fn)` | Array | `(fn(T)->U) -> [U]` | Alias for map | Ruby(collect) | P3-alias |
| C31 | `select(fn)` | Array | `(fn(T)->bool) -> [T]` | Alias for filter | Ruby(select) | P3-alias |
| C32 | `inject(init, fn)` | Array | `(U, fn(U,T)->U) -> U` | Alias for reduce | Ruby(inject) | P3-alias |
| C33 | `none(fn)` | Array | `(fn(T)->bool) -> bool` | No elements match predicate | Ruby(none?), JS(none equiv), Python | P1 |

### 1.3 File/IO Methods

| # | Method | Target | Signature | Description | In Languages | Priority |
|---|--------|--------|-----------|-------------|-------------|----------|
| F1 | `File.touch(path)` | File | `(text) -> bool` | Create empty or update mtime | Ruby(FileUtils.touch), Python(Path.touch) | P1 |
| F2 | `File.move(src, dst)` | File | `(text, text) -> bool` | Move/rename (cross-device) | Ruby(FileUtils.mv), Python(shutil.move) | P1 |
| F3 | `File.compare(a, b)` | File | `(text, text) -> bool` | Compare two files for equality | Ruby(FileUtils.compare_file), Python(filecmp) | P2 |
| F4 | `File.readlines(path)` | File | `(text) -> [text]` | Read all lines as array | Python(readlines), Ruby(readlines), Go(bufio) | P1 |
| F5 | `File.write_lines(path, lines)` | File | `(text, [text]) -> bool` | Write array of lines | Python(writelines) | P2 |
| F6 | `File.temp(prefix?, suffix?)` | File | `(text?, text?) -> (text, FileHandle)` | Create temp file, return path+handle | Python(tempfile), Go(os.CreateTemp) | P2 |
| F7 | `Dir.temp(prefix?)` | Dir | `(text?) -> text` | Create temp directory | Python(tempfile.mkdtemp), Go(os.MkdirTemp) | P2 |
| F8 | `Dir.copy(src, dst)` | Dir | `(text, text) -> bool` | Recursive directory copy | Python(shutil.copytree), Ruby(FileUtils.cp_r) | P2 |
| F9 | `Dir.move(src, dst)` | Dir | `(text, text) -> bool` | Move directory | Python(shutil.move), Ruby(FileUtils.mv) | P2 |
| F10 | `Dir.size(path)` | Dir | `(text) -> i64` | Total size of directory tree | Python(custom), Ruby(custom) | P3 |
| F11 | `Path.realpath()` | Path | `() -> Path` | Resolve all symlinks | Python(Path.resolve), Ruby(Pathname.realpath), Go(filepath.EvalSymlinks) | P2 |
| F12 | `Path.expand_user()` | Path | `() -> Path` | Expand ~ to home directory | Python(expanduser), Go(os.UserHomeDir+) | P3 |
| F13 | `Path.match(pattern)` | Path | `(text) -> bool` | Match path against glob pattern | Python(Path.match), Go(filepath.Match) | P2 |
| F14 | `Path.with_name(name)` | Path | `(text) -> Path` | Replace filename component | Python(Path.with_name) | P2 |
| F15 | `which(name)` | Standalone | `(text) -> text?` | Find executable in PATH | Python(shutil.which), Ruby(which) | P1 |
| F16 | `File.is_readable(path)` | File | `(text) -> bool` | Check read permission | Python(os.access), Ruby(File.readable?) | P2 |
| F17 | `File.is_writable(path)` | File | `(text) -> bool` | Check write permission | Python(os.access), Ruby(File.writable?) | P2 |
| F18 | `File.is_executable(path)` | File | `(text) -> bool` | Check execute permission | Python(os.access), Ruby(File.executable?) | P2 |
| F19 | `File.is_symlink(path)` | File | `(text) -> bool` | Check if symlink | Python, Ruby, Go, JS | P2 |
| F20 | `File.symlink(target, link)` | File | `(text, text) -> bool` | Create symbolic link | Python, Ruby, Go, JS | P2 |
| F21 | `File.readlink(path)` | File | `(text) -> text?` | Read symlink target | Python, Ruby, Go, JS | P2 |
| F22 | `File.modified_time(path)` | File | `(text) -> i64` | Get modification timestamp | All languages | P1 |
| F23 | `File.created_time(path)` | File | `(text) -> i64` | Get creation timestamp | All languages | P2 |
| F24 | `File.chmod(path, mode)` | File | `(text, i64) -> bool` | Change file permissions | Python, Ruby, Go, JS | P2 |
| F25 | `Dir.glob(pattern)` | Dir | `(text) -> [text]` | Glob pattern matching from dir | Python(glob), Ruby(Dir.glob), Go(filepath.Glob) | P1 |

---

## TIER 2: Aliases for Multi-Language Compatibility

These are simple aliases to match naming conventions from other languages. Trivial to implement.

| # | Alias | Maps To | From Language |
|---|-------|---------|---------------|
| A1 | `ljust(w, c?)` | `pad_right(w, c?)` | Python, Ruby |
| A2 | `rjust(w, c?)` | `pad_left(w, c?)` | Python, Ruby |
| A3 | `detect(fn)` | `find(fn)` | Ruby |
| A4 | `collect(fn)` | `map(fn)` | Ruby |
| A5 | `select(fn)` | `filter(fn)` | Ruby |
| A6 | `inject(init, fn)` | `reduce(init, fn)` | Ruby |
| A7 | `multiply(n)` | `repeat(n)` | Ruby |
| A8 | `each(fn)` | `for_each(fn)` | Ruby, JS |
| A9 | `each_with_index(fn)` | `enumerate().each(fn)` | Ruby |
| A10 | `unshift(item)` | `prepend(item)` | Ruby, JS |
| A11 | `size()` | `len()` | Ruby |
| A12 | `length()` | `len()` | Ruby, JS |
| A13 | `count()` (no args) | `len()` | Ruby, Python |
| A14 | `include?(item)` | `contains(item)` | Ruby |
| A15 | `member?(item)` | `contains(item)` | Ruby |
| A16 | `empty?()` | `is_empty()` | Ruby |
| A17 | `strip()` | `trim()` | Python (already exists) |
| A18 | `lstrip()` | `trim_start()` | Python |
| A19 | `rstrip()` | `trim_end()` | Python |
| A20 | `downcase()` | `to_lower()` | Ruby |
| A21 | `upcase()` | `to_upper()` | Ruby |
| A22 | `chop()` | `drop_last(1)` | Ruby |
| A23 | `chomp()` | `chomp()` | Ruby (already exists) |
| A24 | `freeze()` | no-op (val is immutable) | Ruby |
| A25 | `forEach(fn)` | `each(fn)` | JS |

**Implementation note:** Most aliases already exist in Simple's runtime (e.g., `strip` -> `trim`, `upper` -> `to_upper`). Only add if not already present.

---

## TIER 3: Cross-Cutting Utilities

Higher-level utilities that combine multiple operations.

| # | Utility | Category | Description | Priority |
|---|---------|----------|-------------|----------|
| U1 | `Enum` module | Collection | Ruby-style Enumerable mixin with shared iteration methods | P3 |
| U2 | `DefaultMap<K,V>` | Collection | Map with default value factory (Python defaultdict) | P2 |
| U3 | `Counter<T>` | Collection | Frequency counter class (Python Counter) | P2 |
| U4 | `OrderedMap<K,V>` | Collection | Insertion-ordered map (Python 3.7+ dict) | P3 |
| U5 | `LazyIterator<T>` | Collection | Lazy evaluation iterator (Ruby Enumerator::Lazy) | P3 |
| U6 | `TextScanner` | Text | Token-by-token text scanning (Go Scanner, Ruby StringScanner) | P3 |
| U7 | `Glob.recursive(pattern)` | File | Recursive glob (Python Path.rglob, Ruby Dir.glob("**/...")) | P2 |
| U8 | `FileIterator` | File | Lazy line-by-line file reading | P2 |
| U9 | `text.template(vars)` | Text | Simple string templating beyond {key} | P3 |
| U10 | `Comparable` trait | Collection | Spaceship operator for custom sorting | P3 |

---

## Implementation Plan

### Phase A: Core Methods (P1) — 28 items

**Target:** Built-in methods and most-requested standalone functions.

#### A1: Text P1 Methods (6 items)
- `to_kebab_case()`, `to_pascal_case()`, `to_screaming_snake()` — case conversions
- `chars_map(fn)`, `tr(from, to)` — character transformation
- `gsub(pattern, fn)` — replace with callback
- `split_n(sep, n)` — split with limit

**Location:** `src/lib/common/text_advanced.spl` (case conversions), runtime built-in (methods)
**Difficulty:** 2-3 | **Estimated methods:** 7

#### A2: Collection P1 Methods (12 items)
- `sort_by_key(fn)`, `min_by(fn)`, `max_by(fn)`, `min_by_key(fn)`, `max_by_key(fn)` — sorting/extrema
- `each(fn)`, `each_with_index(fn)`, `flat_map(fn)` — iteration as built-in methods
- `insert_at(idx, item)`, `remove_at(idx)`, `pop()`, `shift()` — array mutation
- `reject(fn)`, `none(fn)` — filtering

**Location:** Runtime built-in methods (interpreter_method), `src/lib/nogc_sync_mut/array.spl`
**Difficulty:** 2-3 | **Estimated methods:** 14

#### A3: File P1 Methods (5 items)
- `File.touch(path)` — create/update mtime
- `File.move(src, dst)` — cross-device move
- `File.readlines(path)` — read lines array
- `File.modified_time(path)` — mod time (standardize existing)
- `which(name)` — find executable in PATH
- `Dir.glob(pattern)` — glob matching

**Location:** `src/lib/nogc_sync_mut/fs.spl`, `src/lib/nogc_sync_mut/io/file_ops.spl`
**Difficulty:** 2 | **Estimated methods:** 6

### Phase B: Productivity Methods (P2) — 38 items

#### B1: Text P2 Methods (10 items)
- `encode(encoding)`, `decode(bytes, encoding)` — charset encoding
- `normalize(form)` — Unicode normalization
- `is_title()` — title case check
- `scan(pattern)` — alias for regex_find_all on text
- `each_char(fn)`, `each_line(fn)` — iteration callbacks
- `match_all(pattern)` — iterator over regex matches
- `replace_n(old, new, n)` — limited replacement
- `hex_to_int()`, `to_int_radix(base)` — radix parsing
- `insert(idx, s)` — string insertion

**Location:** Runtime built-in, `src/lib/common/text_advanced.spl`
**Difficulty:** 3 | **Estimated methods:** 12

#### B2: Collection P2 Methods (16 items)
- `minmax()` — min+max in one pass
- `sample(n?)`, `shuffle()` — random operations
- `combination(n)`, `permutation(n?)` — combinatorics
- `compact_map(fn)` — map+filter nil
- `fill(value)` — fill array
- `values_at(indices)` — multi-index access
- `bsearch(target)` — binary search
- `shift()`, `unshift(item)` — front operations
- `sum_by(fn)` — sum with extractor
- `tally()` — frequency map
- `each_slice(n, fn)`, `each_cons(n, fn)` — chunk/window iteration
- `DefaultMap<K,V>`, `Counter<T>` — utility classes

**Location:** `src/lib/nogc_sync_mut/array.spl`, `src/lib/common/pure/collections.spl`, new files
**Difficulty:** 3-4 | **Estimated methods:** 18

#### B3: File P2 Methods (12 items)
- `File.compare(a, b)` — file comparison
- `File.write_lines(path, lines)` — write line array
- `File.temp(prefix?, suffix?)` — temp file creation
- `Dir.temp(prefix?)` — temp dir creation
- `Dir.copy(src, dst)`, `Dir.move(src, dst)` — directory operations
- `Path.realpath()`, `Path.match(pattern)`, `Path.with_name(name)` — path ops
- `File.is_readable/writable/executable(path)` — permission checks
- `File.is_symlink/symlink/readlink` — symlink operations
- `Glob.recursive(pattern)`, `FileIterator` — lazy file iteration

**Location:** `src/lib/nogc_sync_mut/fs.spl`, `src/lib/nogc_sync_mut/io/file_ops.spl`
**Difficulty:** 2-3 | **Estimated methods:** 14

### Phase C: Aliases & Compatibility (P3) — 25 aliases + 8 methods

#### C1: Aliases (25 items)
Add Python/Ruby/JS naming aliases to existing built-in methods. Most are one-line delegations.

**Location:** Runtime built-in (already has alias infrastructure)
**Difficulty:** 1 | **Estimated work:** Trivial

#### C2: Remaining P3 Methods (8 items)
- `expandtabs(tabsize?)`, `casefold()`, `oct_to_int()` — text niche
- `fill_range(value, start, end)` — array fill with range
- `Dir.size(path)`, `Path.expand_user()` — file niche
- `OrderedMap<K,V>`, `LazyIterator<T>`, `TextScanner`, `Comparable` trait — utility classes

**Location:** Various
**Difficulty:** 2-4 | **Estimated methods:** 10

---

## Already Implemented (Confirmed Coverage)

Methods that other languages have which Simple **already implements** (no action needed):

### Text (already covered)
| Method | Simple Equivalent | Notes |
|--------|-------------------|-------|
| `len/length/size` | `.len()`, `.length` | Built-in |
| `contains/includes` | `.contains()`, `.has` | Built-in |
| `startsWith/start_with?` | `.starts_with()` | Built-in |
| `endsWith/end_with?` | `.ends_with()` | Built-in |
| `indexOf/index` | `.index_of()`, `.find` | Built-in |
| `lastIndexOf/rindex` | `.last_index_of()`, `.rfind` | Built-in |
| `toUpperCase/upcase` | `.to_upper()` + aliases | Built-in |
| `toLowerCase/downcase` | `.to_lower()` + aliases | Built-in |
| `trim/strip` | `.trim()`, `.strip` | Built-in |
| `trimStart/lstrip` | `.trim_start()`, `.trim_left` | Built-in |
| `trimEnd/rstrip` | `.trim_end()`, `.trim_right` | Built-in |
| `replace/gsub` | `.replace()` (all occurrences) | Built-in |
| `split` | `.split()` | Built-in |
| `join` | `.join()` | Built-in |
| `repeat/*` | `.repeat()` | Built-in |
| `reverse` | `.reverse()` | Built-in |
| `capitalize` | `.capitalize()` | Built-in |
| `swapcase` | `.swapcase()` | Built-in |
| `title/titlecase` | `.title()` | Built-in |
| `padStart/ljust` | `.pad_left()` | Built-in |
| `padEnd/rjust` | `.pad_right()` | Built-in |
| `center` | `.center()` | Built-in |
| `zfill` | `.zfill()` | Built-in |
| `chars/each_char` | `.chars()` | Built-in |
| `bytes/each_byte` | `.bytes()` | Built-in |
| `lines/split_lines` | `.split_lines()`, `.lines` | Built-in |
| `count` | `.count()` | Built-in |
| `charAt/at/[]` | `.char_at()`, `.at` | Built-in |
| `charCodeAt/ord` | `.char_code_at()`, `.ord` | Built-in |
| `substring/slice` | `.substring()`, `.slice` | Built-in |
| `isEmpty/empty?` | `.is_empty()` | Built-in |
| `isDigit/isNumeric` | `.is_numeric()`, `.is_digit()` | Built-in |
| `isAlpha/isalpha` | `.is_alpha()` | Built-in |
| `isAlphanumeric` | `.is_alphanumeric()` | Built-in |
| `isWhitespace/isspace` | `.is_whitespace()` | Built-in |
| `removeprefix` | `.removeprefix()` | Built-in |
| `removesuffix` | `.removesuffix()` | Built-in |
| `partition` | `.partition()` | Built-in |
| `rpartition` | `.rpartition()` | Built-in |
| `chomp` | `.chomp()` | Built-in |
| `squeeze` | `.squeeze()` | Built-in |
| `parse_int/to_i` | `.parse_int()`, `.to_int()` | Built-in |
| `parse_float/to_f` | `.parse_float()`, `.to_float()` | Built-in |
| `to_snake_case` | `to_snake_case()` | Library |
| `to_camel_case` | `to_camel_case()` | Library |
| `to_title_case` | `to_title_case()` | Library |
| `word_count` | `word_count()` | Library |
| `word_wrap` | `word_wrap()` | Library |
| `levenshtein` | `levenshtein_distance()` | Library |
| `regex match/find/replace/split` | `regex_*` functions | Library |
| `base64 encode` | `encode_base64()` | Library |
| `uri encode/decode` | `uri_encode/decode()` | Library |
| `StringBuilder` | `StringBuilder` class | Library |

### Collections (already covered)
| Method | Simple Equivalent | Notes |
|--------|-------------------|-------|
| `push/append/<<` | `.push()` | Built-in |
| `map/collect` | `.map()` | Built-in |
| `filter/select` | `.filter()` | Built-in |
| `reduce/inject/fold` | `.reduce()` | Built-in |
| `sort` | `.sort()` | Built-in |
| `reverse` | `.reverse()` | Built-in |
| `first/last` | `.first()`, `.last()` | Built-in |
| `contains/include?` | `.contains()` | Built-in |
| `index_of/index` | `.index_of()` | Built-in |
| `flatten` | `.flatten()` | Built-in |
| `unique/uniq` | `.unique()` | Built-in |
| `zip` | `.zip()` | Built-in |
| `enumerate` | `.enumerate()` | Built-in |
| `take/drop` | `.take()`, `.drop()` | Built-in |
| `join` | `.join()` | Built-in |
| `any/all` | `array_any()`, `array_all()` | Library |
| `sum/min/max` | `array_sum/min/max()` | Library |
| `sort_by` | `array_sort_by()` | Library |
| `chunk/each_slice` | `array_chunk()` | Library |
| `flat_map` | `array_flat_map()` | Library |
| `take_while/drop_while` | `array_take_while/drop_while()` | Library |
| `group_by` | `array_group_by()` | Library |
| `partition` | `array_partition()` | Library |
| `compact` | `array_compact()` | Library |
| `windows` | `array_windows()` | Library |
| `interleave/intersperse` | `array_interleave/intersperse()` | Library |
| `rotate` | `array_rotate_left/right()` | Library |
| `dedup` | `array_dedup()` | Library |
| `is_sorted` | `array_is_sorted()` | Library |
| `frequencies/tally` | `array_frequencies()` | Library |
| `transpose` | `array_transpose()` | Library |
| `cartesian_product` | `array_cartesian_product()` | Library |
| `intersect/difference/union` | `array_intersect/difference/union()` | Library |
| `Map.new/insert/get/remove/keys/values` | `Map<K,V>` class | Library |
| `Set.new/insert/has/union/intersect/diff` | `Set<T>` class | Library |
| `Queue/Stack/Deque/PriorityQueue` | Queue module | Library |
| `LinkedList` | LinkedList module | Library |
| `Iterator combinators` | Iterator module (50+ functions) | Library |

### File/IO (already covered)
| Method | Simple Equivalent | Notes |
|--------|-------------------|-------|
| `File.read/write/append` | `File.read/write/append()` | Library |
| `File.exists/delete/copy/rename` | All present | Library |
| `Path.join/parent/extension/stem` | `Path` class | Library |
| `Dir.create/delete/read/exists` | `Dir` class | Library |
| `Walk/Glob` | `Walk`, `Glob` classes | Library |
| `BufferedReader/Writer` | Present | Library |
| `BinaryReader/Writer` | Present | Library |
| `TCP/UDP` | Present | Library |
| `Stdin/Stdout/Stderr` | Present | Library |
| `Process execution` | `shell()`, `process_run()` | Library |
| `Environment variables` | `env_get/set()` | Library |
| `File locking/mmap` | Present | Library |
| `Async file IO` | Present | Library |
| `File hash (SHA256)` | `file_hash_sha256()` | Library |
| `Atomic writes` | `file_atomic_write()` | Library |

---

## Implementation Order (Recommended)

```
Week 1: Phase A1 (Text P1)     — 7 methods  — case conversions, char transforms
Week 2: Phase A2 (Collection P1) — 14 methods — sort_by_key, min/max_by, array mutation
Week 3: Phase A3 (File P1)     — 6 methods  — touch, move, readlines, which
Week 4: Phase B1 (Text P2)     — 12 methods — encoding, normalization, radix parsing
Week 5: Phase B2 (Collection P2) — 18 methods — combinatorics, random, bsearch
Week 6: Phase B3 (File P2)     — 14 methods — permissions, symlinks, temp files
Week 7: Phase C (Aliases+P3)   — 33 items   — compatibility aliases, niche methods
```

**Total: 83 new methods + 25 aliases = 108 additions**

---

## Research Sources

- `doc/research/python_helper_methods_inventory.md` — Python 404 methods
- `doc/research/ruby_methods_inventory.md` — Ruby 769 methods
- `doc/research/go_helper_functions_inventory.md` — Go 430 methods
- `doc/research/js_ts_method_inventory.md` — TypeScript 322 methods

---

## Acceptance Criteria

1. All P1 methods implemented with tests
2. All P1 methods have sdoctest examples
3. Built-in methods accessible via dot-call syntax on native types
4. Library methods importable via `use std.X`
5. No breaking changes to existing method signatures
6. 80%+ branch coverage on new code
7. Documentation coverage for all public functions

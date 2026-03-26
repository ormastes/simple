# Stdlib Helper Methods — Gap Analysis & Implementation Plan

**Date:** 2026-03-26
**Scope:** Text, File/IO, Collection helper methods
**Compared against:** Python, Ruby, Go, TypeScript/JavaScript
**Status:** Phase 1 Requirements

---

## Executive Summary

Cross-referenced Simple's existing stdlib (~850+ methods) against Python (404), Ruby (769), Go (430), and TypeScript (322) method inventories. This plan targets **100% coverage** — every useful method from all 4 languages. Total: **159 new methods + 25 aliases = 184 additions**.

**Coverage target:**
| Category | Simple Has | Cross-Lang Union | Current | After Plan | To Add |
|----------|-----------|-----------------|---------|-----------|--------|
| Text/String | ~200 | ~245 | ~82% | 100% | 45 |
| Collections | ~350 | ~426 | ~82% | 100% | 76 |
| File/IO | ~300 | ~338 | ~89% | 100% | 38 |

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
| T26 | `contains_any(chars)` | `(text) -> bool` | Contains any char from set | Go(ContainsAny) | P1 |
| T27 | `index_of_any(chars)` | `(text) -> i64?` | Index of any char from set | Go(IndexAny) | P2 |
| T28 | `index_of_func(fn)` | `(fn(text)->bool) -> i64?` | Index of first char matching fn | Go(IndexFunc) | P2 |
| T29 | `last_index_of_func(fn)` | `(fn(text)->bool) -> i64?` | Last index of char matching fn | Go(LastIndexFunc) | P2 |
| T30 | `fields_func(fn)` | `(fn(text)->bool) -> [text]` | Split by custom char predicate | Go(FieldsFunc) | P2 |
| T31 | `delete_chars(chars)` | `(text) -> text` | Delete all chars in set | Ruby(delete) | P2 |
| T32 | `succ()` | `() -> text` | Next string in sequence ("a"->"b","az"->"ba") | Ruby(succ/next) | P3 |
| T33 | `scrub(replacement?)` | `(text?) -> text` | Replace invalid UTF-8 bytes | Ruby(scrub), Go(ToValidUTF8) | P2 |
| T34 | `dump()` | `() -> text` | Escape all non-printable characters | Ruby(dump) | P3 |
| T35 | `grapheme_clusters()` | `() -> [text]` | Split into Unicode grapheme clusters | Ruby(grapheme_clusters), JS(Intl.Segmenter) | P2 |
| T36 | `is_printable()` | `() -> bool` | All chars are printable (as method) | Python(isprintable) | P2 |
| T37 | `is_ascii()` | `() -> bool` | All chars are ASCII (as method) | Python(isascii), Ruby(ascii_only?) | P2 |
| T38 | `is_upper()` | `() -> bool` | Entire string is uppercase | Python(isupper), Ruby | P2 |
| T39 | `is_lower()` | `() -> bool` | Entire string is lowercase | Python(islower), Ruby | P2 |
| T40 | `cut(sep)` | `(text) -> (text, text, bool)` | Cut at separator -> (before, after, found) | Go(strings.Cut) | P1 |
| T41 | `multi_replace(pairs)` | `([(text,text)]) -> text` | Replace multiple pairs at once | Go(strings.Replacer) | P2 |
| T42 | `quote()` | `() -> text` | Escape string for safe repr (add quotes+escapes) | Go(strconv.Quote), Ruby(inspect) | P2 |
| T43 | `unquote()` | `() -> text` | Unescape quoted string | Go(strconv.Unquote) | P3 |
| T44 | `split_after(sep)` | `(text) -> [text]` | Split but keep separator at end of each part | Go(SplitAfter) | P3 |
| T45 | `format(args)` | `([text]) -> text` | Positional placeholder formatting ({0}, {1}) | Python(str.format), Go(fmt.Sprintf) | P2 |

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
| C34 | `find_last(fn)` | Array | `(fn(T)->bool) -> T?` | Find last matching element | JS(findLast), Ruby(reverse.find) | P1 |
| C35 | `find_last_index(fn)` | Array | `(fn(T)->bool) -> i64?` | Index of last matching element | JS(findLastIndex) | P1 |
| C36 | `at(idx)` | Array | `(i64) -> T?` | Element at index (supports negative) | JS(at), Python(a[-1]) | P1 |
| C37 | `clone()` | Array | `() -> [T]` | Shallow copy of array | Go(slices.Clone), Ruby(clone) | P1 |
| C38 | `compare(other)` | Array | `([T]) -> i64` | Lexicographic comparison (-1/0/1) | Go(slices.Compare) | P2 |
| C39 | `dedup_by(fn)` | Array | `(fn(T,T)->bool) -> [T]` | Dedup with custom equality | Go(slices.CompactFunc) | P2 |
| C40 | `replace_range(start,end,items)` | Array | `(i64,i64,[T]) -> [T]` | Replace range of elements | Go(slices.Replace), JS(splice) | P2 |
| C41 | `sort_stable()` | Array | `() -> [T]` | Stable sort (preserves equal order) | Go(sort.Stable), Python(default) | P2 |
| C42 | `sort_stable_by(fn)` | Array | `(fn(T,T)->i64) -> [T]` | Stable sort with comparator | Go(sort.StableFunc) | P2 |
| C43 | `one(fn)` | Array | `(fn(T)->bool) -> bool` | Exactly one element matches | Ruby(one?) | P2 |
| C44 | `top_n(n)` | Array | `(i64) -> [T]` | N largest elements | Ruby(max(n)), Python(heapq.nlargest) | P2 |
| C45 | `bottom_n(n)` | Array | `(i64) -> [T]` | N smallest elements | Ruby(min(n)), Python(heapq.nsmallest) | P2 |
| C46 | `slice_when(fn)` | Array | `(fn(T,T)->bool) -> [[T]]` | Split when pred true between consecutive | Ruby(slice_when) | P2 |
| C47 | `chunk_while(fn)` | Array | `(fn(T,T)->bool) -> [[T]]` | Chunk while pred true between consecutive | Ruby(chunk_while) | P2 |
| C48 | `dig(keys)` | Array | `([i64]) -> T?` | Nested array access by index chain | Ruby(dig) | P2 |
| C49 | `assoc(key)` | Array | `(T) -> [T]?` | Find sub-array by first element | Ruby(assoc) | P3 |
| C50 | `rassoc(value)` | Array | `(T) -> [T]?` | Find sub-array by second element | Ruby(rassoc) | P3 |
| C51 | `repeated_combination(n)` | Array | `(i64) -> [[T]]` | Combinations with repetition | Ruby(repeated_combination) | P3 |
| C52 | `repeated_permutation(n)` | Array | `(i64) -> [[T]]` | Permutations with repetition | Ruby(repeated_permutation) | P3 |
| C53 | `each_with_object(init,fn)` | Array | `(U, fn(T,U)) -> U` | Iterate accumulating into object | Ruby(each_with_object) | P2 |
| C54 | `zip_longest(other, default)` | Array | `([U], T) -> [(T,U)]` | Zip with fill for unequal lengths | Python(zip_longest) | P2 |
| C55 | `pairwise()` | Array | `() -> [(T,T)]` | Consecutive pairs | Python(itertools.pairwise) | P2 |
| C56 | `compress(selectors)` | Array | `([bool]) -> [T]` | Filter by boolean selector array | Python(itertools.compress) | P2 |
| C57 | `reduce_right(init, fn)` | Array | `(U, fn(U,T)->U) -> U` | Right fold on arrays | JS(reduceRight) | P2 |
| C58 | `copy_within(target,start,end)` | Array | `(i64,i64,i64) -> [T]` | Copy elements within array | JS(copyWithin) | P3 |
| C59 | `product()` | Array | `() -> i64` | Multiply all numeric elements | Ruby(inject(:*)), Python(math.prod) | P2 |
| C60 | `map_dig(keys)` | Map | `([K]) -> V?` | Nested map access by key chain | Ruby(Hash#dig) | P2 |
| C61 | `map_fetch(key)` | Map | `(K) -> Result<V,E>` | Get with error on missing key | Ruby(Hash#fetch) | P2 |
| C62 | `map_fetch_or(key, default)` | Map | `(K, V) -> V` | Get with default, error-safe | Ruby(Hash#fetch) | P2 |
| C63 | `map_min_by(fn)` | Map | `(fn(K,V)->C) -> (K,V)?` | Entry with min by function | Ruby(min_by) | P2 |
| C64 | `map_max_by(fn)` | Map | `(fn(K,V)->C) -> (K,V)?` | Entry with max by function | Ruby(max_by) | P2 |
| C65 | `map_sort_by(fn)` | Map | `(fn(K,V)->C) -> [(K,V)]` | Sort entries by function | Ruby(sort_by) | P2 |
| C66 | `map_flat_map(fn)` | Map | `(fn(K,V)->[(K2,V2)]) -> Map` | Flat map on entries | Ruby(flat_map) | P3 |
| C67 | `map_each_with_object(init,fn)` | Map | `(U, fn(K,V,U)) -> U` | Iterate accumulating object | Ruby(each_with_object) | P3 |
| C68 | `map_clone()` | Map | `() -> Map<K,V>` | Shallow copy | Go(maps.Clone), Ruby(clone) | P2 |
| C69 | `map_reject(fn)` | Map | `(fn(K,V)->bool) -> Map` | Inverse filter on map | Ruby(reject) | P2 |
| C70 | `set_classify(fn)` | Set | `(fn(T)->K) -> Map<K,Set<T>>` | Group set by function | Ruby(Set#classify) | P3 |
| C71 | `set_divide(fn)` | Set | `(fn(T,T)->bool) -> Set<Set<T>>` | Partition into equivalence classes | Ruby(Set#divide) | P3 |
| C72 | `partial(fn, args)` | Functional | `(fn, ...) -> fn` | Partial function application | Python(functools.partial) | P2 |
| C73 | `memoize(fn)` | Functional | `(fn) -> fn` | Memoization/caching wrapper | Python(lru_cache) | P2 |
| C74 | `identity(x)` | Functional | `(T) -> T` | Identity function | Haskell(id), lodash | P2 |
| C75 | `constantly(value)` | Functional | `(T) -> fn()->T` | Function that always returns value | Clojure(constantly) | P3 |
| C76 | `Heap<T>` | Data Structure | Min/max heap with push/pop/peek | Go(container/heap), Python(heapq) | P2 |

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
| F26 | `File.ftype(path)` | File | `(text) -> text` | File type as string ("file","directory","link") | Ruby(File.ftype) | P3 |
| F27 | `File.is_zero(path)` | File | `(text) -> bool` | Check if file is empty (0 bytes) | Ruby(File.zero?) | P2 |
| F28 | `File.link(target, link)` | File | `(text, text) -> bool` | Create hard link | Python(os.link), Ruby(File.link), Go(os.Link) | P2 |
| F29 | `File.identical(a, b)` | File | `(text, text) -> bool` | Check if same inode (not content) | Ruby(File.identical?), Go(os.SameFile) | P3 |
| F30 | `File.truncate(path, size)` | File | `(text, i64) -> bool` | Truncate file to size | Python, Ruby, Go, JS | P2 |
| F31 | `File.foreach(path, fn)` | File | `(text, fn(text))` | Iterate lines with callback | Ruby(File.foreach), Python(for line in f) | P1 |
| F32 | `File.write_lines(path, lines)` | File | `(text, [text]) -> bool` | Write array of lines | Python(writelines) | P2 |
| F33 | `Dir.children(path)` | Dir | `(text) -> [text]` | List entries (no . and ..) | Ruby(Dir.children), Python(iterdir) | P2 |
| F34 | `Dir.each_child(path, fn)` | Dir | `(text, fn(text))` | Iterate children with callback | Ruby(Dir.each_child) | P2 |
| F35 | `Dir.rglob(pattern)` | Dir | `(text) -> [text]` | Recursive glob pattern matching | Python(Path.rglob), Ruby(Dir.glob("**/...")) | P1 |
| F36 | `disk_usage(path)` | Standalone | `(text) -> (i64, i64, i64)` | Disk usage (total, used, free) | Python(shutil.disk_usage) | P3 |
| F37 | `Path.suffixes()` | Path | `() -> [text]` | All extensions (.tar.gz -> [".tar", ".gz"]) | Python(Path.suffixes) | P3 |
| F38 | `Path.as_uri()` | Path | `() -> text` | Convert to file:// URI | Python(Path.as_uri), Go(url.Parse) | P3 |

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
| U11 | `Heap<T>` | Collection | Min/max heap with push/pop/peek/heapify | Go(container/heap), Python(heapq) | P2 |
| U12 | `ChainMap<K,V>` | Collection | Layered map search (Python collections.ChainMap) | P3 |
| U13 | `partial(fn, args)` | Functional | Partial function application | Python(functools.partial) | P2 |
| U14 | `memoize(fn)` | Functional | Memoization/caching wrapper | Python(functools.lru_cache) | P2 |
| U15 | `identity(x)` / `constantly(v)` | Functional | Identity and constant functions | Standard FP | P2 |

---

## Implementation Plan (100% Coverage)

### Phase A: Core Methods (P1) — 42 items

**Target:** Built-in methods and most-requested standalone functions.

#### A1: Text P1 Methods (9 items)
- `to_kebab_case()`, `to_pascal_case()`, `to_screaming_snake()` — case conversions
- `chars_map(fn)`, `tr(from, to)` — character transformation
- `gsub(pattern, fn)` — replace with callback
- `split_n(sep, n)` — split with limit
- `contains_any(chars)` — contains any char from set
- `cut(sep)` — cut at separator -> (before, after, found)

**Location:** `src/lib/common/text_advanced.spl` (case conversions), runtime built-in (methods)
**Difficulty:** 2-3

#### A2: Collection P1 Methods (18 items)
- `sort_by_key(fn)`, `min_by(fn)`, `max_by(fn)`, `min_by_key(fn)`, `max_by_key(fn)` — sorting/extrema
- `each(fn)`, `each_with_index(fn)`, `flat_map(fn)` — iteration as built-in methods
- `insert_at(idx, item)`, `remove_at(idx)`, `pop()`, `shift()` — array mutation
- `reject(fn)`, `none(fn)` — filtering
- `find_last(fn)`, `find_last_index(fn)` — reverse search
- `at(idx)` with negative index, `clone()` — access/copy

**Location:** Runtime built-in methods (interpreter_method), `src/lib/nogc_sync_mut/array.spl`
**Difficulty:** 2-3

#### A3: File P1 Methods (8 items)
- `File.touch(path)` — create/update mtime
- `File.move(src, dst)` — cross-device move
- `File.readlines(path)` — read lines array
- `File.foreach(path, fn)` — iterate lines with callback
- `File.modified_time(path)` — mod time (standardize existing)
- `which(name)` — find executable in PATH
- `Dir.glob(pattern)` — glob matching
- `Dir.rglob(pattern)` — recursive glob

**Location:** `src/lib/nogc_sync_mut/fs.spl`, `src/lib/nogc_sync_mut/io/file_ops.spl`
**Difficulty:** 2

### Phase B: Productivity Methods (P2) — 90 items

#### B1: Text P2 Methods (22 items)
- `encode(encoding)`, `decode(bytes, encoding)` — charset encoding
- `normalize(form)` — Unicode normalization
- `is_title()`, `is_upper()`, `is_lower()`, `is_printable()`, `is_ascii()` — string predicates
- `scan(pattern)`, `match_all(pattern)` — pattern matching
- `each_char(fn)`, `each_line(fn)` — iteration callbacks
- `replace_n(old, new, n)` — limited replacement
- `hex_to_int()`, `to_int_radix(base)` — radix parsing
- `insert(idx, s)` — string insertion
- `index_of_any(chars)`, `index_of_func(fn)`, `last_index_of_func(fn)` — advanced search
- `fields_func(fn)`, `delete_chars(chars)` — char-level operations
- `scrub(replacement?)`, `grapheme_clusters()` — Unicode safety
- `multi_replace(pairs)`, `quote()`, `format(args)` — formatting

**Location:** Runtime built-in, `src/lib/common/text_advanced.spl`
**Difficulty:** 2-3

#### B2: Collection P2 Methods (46 items)
**Array methods (28):**
- `minmax()`, `compare(other)` — comparison
- `sample(n?)`, `shuffle()` — random operations
- `combination(n)`, `permutation(n?)` — combinatorics
- `compact_map(fn)`, `dedup_by(fn)` — transformation
- `fill(value)`, `replace_range(start,end,items)` — mutation
- `values_at(indices)`, `bsearch(target)` — access
- `shift()`, `unshift(item)` — front operations
- `sum_by(fn)`, `product()`, `reduce_right(init,fn)` — aggregation
- `tally()` — frequency map
- `each_slice(n, fn)`, `each_cons(n, fn)`, `each_with_object(init,fn)` — iteration
- `sort_stable()`, `sort_stable_by(fn)` — stable sorting
- `one(fn)`, `top_n(n)`, `bottom_n(n)` — predicates/selection
- `slice_when(fn)`, `chunk_while(fn)`, `pairwise()` — partitioning
- `zip_longest(other, default)`, `compress(selectors)` — combining
- `dig(keys)` — nested access

**Map methods (10):**
- `map_dig(keys)`, `map_fetch(key)`, `map_fetch_or(key,default)` — access
- `map_min_by(fn)`, `map_max_by(fn)`, `map_sort_by(fn)` — ordering
- `map_clone()`, `map_reject(fn)` — copy/filter
- `map_flat_map(fn)`, `map_each_with_object(init,fn)` — transformation

**Utility classes (5):**
- `DefaultMap<K,V>` — map with default factory
- `Counter<T>` — frequency counter
- `Heap<T>` — min/max heap
- `partial(fn, args)`, `memoize(fn)` — functional utilities
- `identity(x)`, `constantly(value)` — function combinators

**Location:** `src/lib/nogc_sync_mut/array.spl`, `src/lib/common/pure/collections.spl`, new files
**Difficulty:** 2-4

#### B3: File P2 Methods (22 items)
- `File.compare(a, b)` — content comparison
- `File.write_lines(path, lines)` — write line array
- `File.temp(prefix?, suffix?)` — temp file creation
- `File.is_zero(path)` — check empty file
- `File.link(target, link)` — hard link
- `File.truncate(path, size)` — truncate to size
- `Dir.temp(prefix?)` — temp dir creation
- `Dir.copy(src, dst)`, `Dir.move(src, dst)` — directory operations
- `Dir.children(path)`, `Dir.each_child(path, fn)` — listing
- `Path.realpath()`, `Path.match(pattern)`, `Path.with_name(name)` — path ops
- `File.is_readable/writable/executable(path)` — permission checks (3)
- `File.is_symlink/symlink/readlink` — symlink operations (3)
- `File.chmod(path, mode)`, `File.created_time(path)` — metadata
- `Glob.recursive(pattern)`, `FileIterator` — lazy file iteration

**Location:** `src/lib/nogc_sync_mut/fs.spl`, `src/lib/nogc_sync_mut/io/file_ops.spl`
**Difficulty:** 2-3

### Phase C: Aliases & Full Completion (P3) — 25 aliases + 27 methods

#### C1: Aliases (25 items)
Add Python/Ruby/JS naming aliases to existing built-in methods. Most are one-line delegations.

**Location:** Runtime built-in (already has alias infrastructure)
**Difficulty:** 1

#### C2: Remaining Text P3 (7 items)
- `expandtabs(tabsize?)`, `casefold()` — text niche
- `oct_to_int()`, `succ()` — parsing/sequence
- `dump()`, `unquote()` — escaping
- `split_after(sep)` — split variant

#### C3: Remaining Collection P3 (12 items)
- `fill_range(value, start, end)`, `copy_within(target,start,end)` — array mutation
- `assoc(key)`, `rassoc(value)` — pair lookup
- `repeated_combination(n)`, `repeated_permutation(n)` — combinatorics
- `map_flat_map(fn)`, `map_each_with_object(init,fn)` — map iteration
- `set_classify(fn)`, `set_divide(fn)` — set partitioning
- `constantly(value)` — functional
- `OrderedMap<K,V>`, `LazyIterator<T>`, `ChainMap<K,V>` — utility classes
- `TextScanner`, `Comparable` trait

#### C4: Remaining File P3 (8 items)
- `Dir.size(path)`, `Path.expand_user()` — directory/path
- `File.ftype(path)`, `File.identical(a,b)` — metadata
- `disk_usage(path)` — disk stats
- `Path.suffixes()`, `Path.as_uri()` — path utilities

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

## Implementation Order (100% Coverage)

```
Week 1:  Phase A1 (Text P1)       —  9 methods — case conversions, char transforms, cut, split_n
Week 2:  Phase A2 (Collection P1) — 18 methods — sort_by_key, min/max_by, array mutation, find_last
Week 3:  Phase A3 (File P1)       —  8 methods — touch, move, readlines, foreach, which, glob
Week 4:  Phase B1 (Text P2)       — 22 methods — encoding, normalization, predicates, Unicode
Week 5:  Phase B2a (Array P2)     — 28 methods — combinatorics, random, bsearch, stable sort
Week 6:  Phase B2b (Map+Util P2)  — 18 methods — map methods, DefaultMap, Counter, Heap, FP utils
Week 7:  Phase B3 (File P2)       — 22 methods — permissions, symlinks, temp files, dir ops
Week 8:  Phase C1 (Aliases)       — 25 aliases — Python/Ruby/JS naming compatibility
Week 9:  Phase C2 (Text P3)       —  7 methods — expandtabs, casefold, succ, dump
Week 10: Phase C3 (Collection P3) — 12 methods — repeated_comb/perm, set classify, OrderedMap
Week 11: Phase C4 (File P3)       —  8 methods — ftype, disk_usage, suffixes, as_uri
```

**Total: 159 new methods + 25 aliases = 184 additions → 100% coverage**

---

## Research Sources

- `doc/research/python_helper_methods_inventory.md` — Python 404 methods
- `doc/research/ruby_methods_inventory.md` — Ruby 769 methods
- `doc/research/go_helper_functions_inventory.md` — Go 430 methods
- `doc/research/js_ts_method_inventory.md` — TypeScript 322 methods

---

## Acceptance Criteria (100% Target)

1. **ALL** methods (P1+P2+P3) implemented — no exceptions
2. ALL methods have sdoctest examples
3. Built-in methods accessible via dot-call syntax on native types
4. Library methods importable via `use std.X`
5. No breaking changes to existing method signatures
6. 80%+ branch coverage on new code
7. Documentation coverage for all public functions
8. Every method from Python, Ruby, Go, TypeScript has a Simple equivalent
9. Cross-language compatibility aliases enable familiar naming from any background
10. All utility classes (DefaultMap, Counter, Heap, OrderedMap, ChainMap) fully operational

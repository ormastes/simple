# Go Helper Functions - Comprehensive Inventory

## 1. String/Text Functions

### 1.1 strings package

| # | Function | Description |
|---|----------|-------------|
| 1 | `strings.Contains(s, substr string) bool` | Reports whether substr is within s |
| 2 | `strings.ContainsAny(s, chars string) bool` | Reports whether any Unicode code points in chars are within s |
| 3 | `strings.ContainsRune(s string, r rune) bool` | Reports whether the Unicode code point r is within s |
| 4 | `strings.Count(s, substr string) int` | Counts the number of non-overlapping instances of substr in s |
| 5 | `strings.Cut(s, sep string) (before, after string, found bool)` | Slices s around the first instance of sep |
| 6 | `strings.CutPrefix(s, prefix string) (after string, found bool)` | Returns s without the provided leading prefix string |
| 7 | `strings.CutSuffix(s, suffix string) (before string, found bool)` | Returns s without the provided trailing suffix string |
| 8 | `strings.EqualFold(s, t string) bool` | Reports whether s and t are equal under Unicode case-folding (case-insensitive) |
| 9 | `strings.Fields(s string) []string` | Splits s around each instance of one or more consecutive white space characters |
| 10 | `strings.FieldsFunc(s string, f func(rune) bool) []string` | Splits s at each run of code points satisfying f |
| 11 | `strings.HasPrefix(s, prefix string) bool` | Tests whether s begins with prefix |
| 12 | `strings.HasSuffix(s, suffix string) bool` | Tests whether s ends with suffix |
| 13 | `strings.Index(s, substr string) int` | Returns the index of the first instance of substr in s, or -1 |
| 14 | `strings.IndexAny(s, chars string) int` | Returns the index of the first instance of any Unicode code point from chars in s |
| 15 | `strings.IndexByte(s string, c byte) int` | Returns the index of the first instance of c in s, or -1 |
| 16 | `strings.IndexFunc(s string, f func(rune) bool) int` | Returns the index of the first Unicode code point satisfying f |
| 17 | `strings.IndexRune(s string, r rune) int` | Returns the index of the first instance of the Unicode code point r |
| 18 | `strings.Join(elems []string, sep string) string` | Concatenates elements of a string slice with separator |
| 19 | `strings.LastIndex(s, substr string) int` | Returns the index of the last instance of substr in s |
| 20 | `strings.LastIndexAny(s, chars string) int` | Returns the index of the last instance of any Unicode code point from chars |
| 21 | `strings.LastIndexByte(s string, c byte) int` | Returns the index of the last instance of c in s |
| 22 | `strings.LastIndexFunc(s string, f func(rune) bool) int` | Returns the index of the last Unicode code point satisfying f |
| 23 | `strings.Map(mapping func(rune) rune, s string) string` | Returns a copy of s with all characters modified by mapping function |
| 24 | `strings.NewReader(s string) *Reader` | Returns a new Reader reading from s |
| 25 | `strings.NewReplacer(oldnew ...string) *Replacer` | Returns a new Replacer from a list of old/new string pairs |
| 26 | `strings.Repeat(s string, count int) string` | Returns a new string consisting of count copies of s |
| 27 | `strings.Replace(s, old, new string, n int) string` | Returns a copy of s with the first n non-overlapping instances of old replaced by new |
| 28 | `strings.ReplaceAll(s, old, new string) string` | Returns a copy of s with all non-overlapping instances of old replaced by new |
| 29 | `strings.Split(s, sep string) []string` | Slices s into all substrings separated by sep |
| 30 | `strings.SplitAfter(s, sep string) []string` | Slices s into all substrings after each instance of sep (keeps sep) |
| 31 | `strings.SplitAfterN(s, sep string, n int) []string` | Slices s into substrings after each instance of sep, up to n substrings |
| 32 | `strings.SplitN(s, sep string, n int) []string` | Slices s into substrings separated by sep, up to n substrings |
| 33 | `strings.Title(s string) string` | (Deprecated) Returns a copy with all Unicode letters that begin words mapped to title case |
| 34 | `strings.ToLower(s string) string` | Returns s with all Unicode letters mapped to lower case |
| 35 | `strings.ToLowerSpecial(c unicode.SpecialCase, s string) string` | Returns s with all Unicode letters mapped to lower case using specified case mapping |
| 36 | `strings.ToTitle(s string) string` | Returns s with all Unicode letters mapped to title case |
| 37 | `strings.ToTitleSpecial(c unicode.SpecialCase, s string) string` | Returns s with all Unicode letters mapped to title case using specified case mapping |
| 38 | `strings.ToUpper(s string) string` | Returns s with all Unicode letters mapped to upper case |
| 39 | `strings.ToUpperSpecial(c unicode.SpecialCase, s string) string` | Returns s with all Unicode letters mapped to upper case using specified case mapping |
| 40 | `strings.ToValidUTF8(s, replacement string) string` | Returns a copy of s with each run of invalid UTF-8 byte sequences replaced by replacement |
| 41 | `strings.Trim(s, cutset string) string` | Returns s with all leading and trailing Unicode code points in cutset removed |
| 42 | `strings.TrimFunc(s string, f func(rune) bool) string` | Returns s with all leading and trailing Unicode code points satisfying f removed |
| 43 | `strings.TrimLeft(s, cutset string) string` | Returns s with all leading Unicode code points in cutset removed |
| 44 | `strings.TrimLeftFunc(s string, f func(rune) bool) string` | Returns s with all leading Unicode code points satisfying f removed |
| 45 | `strings.TrimPrefix(s, prefix string) string` | Returns s without the provided leading prefix (unchanged if no prefix) |
| 46 | `strings.TrimRight(s, cutset string) string` | Returns s with all trailing Unicode code points in cutset removed |
| 47 | `strings.TrimRightFunc(s string, f func(rune) bool) string` | Returns s with all trailing Unicode code points satisfying f removed |
| 48 | `strings.TrimSpace(s string) string` | Returns s with all leading and trailing white space removed |
| 49 | `strings.TrimSuffix(s, suffix string) string` | Returns s without the provided trailing suffix (unchanged if no suffix) |

### 1.2 strings.Builder methods

| # | Method | Description |
|---|--------|-------------|
| 1 | `Builder.Grow(n int)` | Grows the builder's capacity by n bytes (pre-allocate) |
| 2 | `Builder.Len() int` | Returns the number of accumulated bytes |
| 3 | `Builder.Cap() int` | Returns the capacity of the builder's underlying byte slice |
| 4 | `Builder.Reset()` | Resets the builder to be empty |
| 5 | `Builder.String() string` | Returns the accumulated string |
| 6 | `Builder.Write(p []byte) (int, error)` | Appends the contents of p to the buffer |
| 7 | `Builder.WriteByte(c byte) error` | Appends the byte c to the buffer |
| 8 | `Builder.WriteRune(r rune) (int, error)` | Appends the UTF-8 encoding of Unicode code point r |
| 9 | `Builder.WriteString(s string) (int, error)` | Appends the contents of s to the buffer |

### 1.3 strings.Reader methods

| # | Method | Description |
|---|--------|-------------|
| 1 | `Reader.Len() int` | Returns the number of unread bytes of the string |
| 2 | `Reader.Read(b []byte) (n int, err error)` | Reads up to len(b) bytes into b |
| 3 | `Reader.ReadAt(b []byte, off int64) (n int, err error)` | Reads len(b) bytes from the string starting at byte offset off |
| 4 | `Reader.ReadByte() (byte, error)` | Reads and returns the next byte |
| 5 | `Reader.ReadRune() (ch rune, size int, err error)` | Reads and returns the next UTF-8-encoded Unicode code point |
| 6 | `Reader.Reset(s string)` | Resets the Reader to be reading from s |
| 7 | `Reader.Seek(offset int64, whence int) (int64, error)` | Sets the read position relative to whence |
| 8 | `Reader.Size() int64` | Returns the original length of the underlying string |
| 9 | `Reader.UnreadByte() error` | Unreads the last byte read |
| 10 | `Reader.UnreadRune() error` | Unreads the last rune read |
| 11 | `Reader.WriteTo(w io.Writer) (n int64, err error)` | Writes remaining data to w (implements io.WriterTo) |

### 1.4 strings.Replacer methods

| # | Method | Description |
|---|--------|-------------|
| 1 | `Replacer.Replace(s string) string` | Returns a copy of s with all replacements performed |
| 2 | `Replacer.WriteString(w io.Writer, s string) (n int, err error)` | Writes s to w with all replacements performed |

### 1.5 strconv package

| # | Function | Description |
|---|----------|-------------|
| 1 | `strconv.Atoi(s string) (int, error)` | Converts a string to an int (shorthand for ParseInt(s, 10, 0)) |
| 2 | `strconv.Itoa(i int) string` | Converts an int to its decimal string representation |
| 3 | `strconv.FormatBool(b bool) string` | Returns "true" or "false" according to the value of b |
| 4 | `strconv.FormatFloat(f float64, fmt byte, prec, bitSize int) string` | Converts a float64 to a string with given format and precision |
| 5 | `strconv.FormatInt(i int64, base int) string` | Returns the string representation of i in the given base |
| 6 | `strconv.FormatUint(i uint64, base int) string` | Returns the string representation of i in the given base |
| 7 | `strconv.ParseBool(str string) (bool, error)` | Returns the boolean value represented by the string |
| 8 | `strconv.ParseFloat(s string, bitSize int) (float64, error)` | Converts the string s to a floating-point number |
| 9 | `strconv.ParseInt(s string, base int, bitSize int) (int64, error)` | Interprets a string s in the given base and bit size and returns int64 |
| 10 | `strconv.ParseUint(s string, base int, bitSize int) (uint64, error)` | Like ParseInt but for unsigned numbers |
| 11 | `strconv.Quote(s string) string` | Returns a double-quoted Go string literal representing s |
| 12 | `strconv.QuoteRune(r rune) string` | Returns a single-quoted Go character literal representing the rune |
| 13 | `strconv.QuoteToASCII(s string) string` | Returns a double-quoted Go string literal, with non-ASCII escaped |
| 14 | `strconv.Unquote(s string) (string, error)` | Interprets s as a single-quoted, double-quoted, or backquoted Go string literal |
| 15 | `strconv.AppendBool(dst []byte, b bool) []byte` | Appends "true" or "false" to dst and returns the extended buffer |
| 16 | `strconv.AppendFloat(dst []byte, f float64, fmt byte, prec, bitSize int) []byte` | Appends the string form of the floating-point number to dst |
| 17 | `strconv.AppendInt(dst []byte, i int64, base int) []byte` | Appends the string form of the integer i to dst |
| 18 | `strconv.AppendUint(dst []byte, i uint64, base int) []byte` | Appends the string form of the unsigned integer i to dst |
| 19 | `strconv.CanBackquote(s string) bool` | Reports whether the string s can be represented unchanged as a single-line backquoted string |
| 20 | `strconv.IsGraphic(r rune) bool` | Reports whether the rune is defined as a Graphic by Unicode |
| 21 | `strconv.IsPrint(r rune) bool` | Reports whether the rune is defined as printable by Go |

### 1.6 fmt package (string-related)

| # | Function | Description |
|---|----------|-------------|
| 1 | `fmt.Sprintf(format string, a ...any) string` | Formats according to a format specifier and returns the resulting string |
| 2 | `fmt.Fprintf(w io.Writer, format string, a ...any) (int, error)` | Formats according to a format specifier and writes to w |
| 3 | `fmt.Sprint(a ...any) string` | Formats using default formats and returns the resulting string |
| 4 | `fmt.Sscan(str string, a ...any) (int, error)` | Scans the argument string, storing successive space-separated values into arguments |
| 5 | `fmt.Sscanf(str string, format string, a ...any) (int, error)` | Scans the argument string according to a format specifier, storing values into arguments |

### 1.7 unicode package

| # | Function | Description |
|---|----------|-------------|
| 1 | `unicode.IsLetter(r rune) bool` | Reports whether the rune is a letter (category L) |
| 2 | `unicode.IsDigit(r rune) bool` | Reports whether the rune is a decimal digit |
| 3 | `unicode.IsUpper(r rune) bool` | Reports whether the rune is an upper case letter |
| 4 | `unicode.IsLower(r rune) bool` | Reports whether the rune is a lower case letter |
| 5 | `unicode.IsSpace(r rune) bool` | Reports whether the rune is a space character as defined by Unicode |
| 6 | `unicode.IsPunct(r rune) bool` | Reports whether the rune is a Unicode punctuation character |
| 7 | `unicode.IsControl(r rune) bool` | Reports whether the rune is a control character |
| 8 | `unicode.IsGraphic(r rune) bool` | Reports whether the rune is defined as a Graphic by Unicode |
| 9 | `unicode.IsPrint(r rune) bool` | Reports whether the rune is defined as printable by Go |
| 10 | `unicode.IsSymbol(r rune) bool` | Reports whether the rune is a symbolic character |
| 11 | `unicode.IsNumber(r rune) bool` | Reports whether the rune is a number (category N) |
| 12 | `unicode.IsTitle(r rune) bool` | Reports whether the rune is a title case letter |
| 13 | `unicode.ToUpper(r rune) rune` | Maps the rune to upper case |
| 14 | `unicode.ToLower(r rune) rune` | Maps the rune to lower case |
| 15 | `unicode.ToTitle(r rune) rune` | Maps the rune to title case |
| 16 | `unicode.In(r rune, ranges ...*RangeTable) bool` | Reports whether the rune is a member of one of the ranges |
| 17 | `unicode.Is(rangeTab *RangeTable, r rune) bool` | Reports whether the rune is in the specified table of ranges |

### 1.8 regexp package

| # | Function/Method | Description |
|---|-----------------|-------------|
| 1 | `regexp.Compile(expr string) (*Regexp, error)` | Parses a regular expression and returns a Regexp object |
| 2 | `regexp.MustCompile(str string) *Regexp` | Like Compile but panics if the expression cannot be parsed |
| 3 | `regexp.Match(pattern string, b []byte) (bool, error)` | Reports whether the byte slice contains any match of the pattern |
| 4 | `regexp.MatchString(pattern string, s string) (bool, error)` | Reports whether the string contains any match of the pattern |
| 5 | `Regexp.Find(b []byte) []byte` | Returns a byte slice holding the leftmost match in b |
| 6 | `Regexp.FindAll(b []byte, n int) [][]byte` | Returns a slice of all successive matches, up to n (-1 for all) |
| 7 | `Regexp.FindString(s string) string` | Returns a string holding the leftmost match in s |
| 8 | `Regexp.FindAllString(s string, n int) []string` | Returns a slice of all successive string matches |
| 9 | `Regexp.FindStringIndex(s string) []int` | Returns a two-element slice of integers [start, end] for the leftmost match |
| 10 | `Regexp.FindAllStringIndex(s string, n int) [][]int` | Returns a slice of all successive index pairs for matches |
| 11 | `Regexp.FindSubmatch(b []byte) [][]byte` | Returns a slice of byte slices holding the match and submatches |
| 12 | `Regexp.FindAllSubmatch(b []byte, n int) [][][]byte` | Returns a slice of all successive submatch results |
| 13 | `Regexp.ReplaceAll(src, repl []byte) []byte` | Returns a copy of src with all matches replaced by repl |
| 14 | `Regexp.ReplaceAllString(src, repl string) string` | Returns a copy of src with all matches replaced by repl string |
| 15 | `Regexp.ReplaceAllFunc(src []byte, repl func([]byte) []byte) []byte` | Returns a copy with all matches replaced by the return value of repl function |
| 16 | `Regexp.ReplaceAllStringFunc(src string, repl func(string) string) string` | Returns a copy with all matches replaced by the return value of repl function |
| 17 | `Regexp.Split(s string, n int) []string` | Slices s into substrings separated by the expression matches |
| 18 | `Regexp.SubexpNames() []string` | Returns the names of the parenthesized subexpressions |
| 19 | `Regexp.NumSubexp() int` | Returns the number of parenthesized subexpressions |

### 1.9 bytes package (mirrors strings for []byte)

| # | Function | Description |
|---|----------|-------------|
| 1 | `bytes.Contains(b, subslice []byte) bool` | Reports whether subslice is within b |
| 2 | `bytes.ContainsAny(b []byte, chars string) bool` | Reports whether any of the UTF-8-encoded code points in chars are within b |
| 3 | `bytes.ContainsRune(b []byte, r rune) bool` | Reports whether the rune is contained in the UTF-8-encoded byte slice |
| 4 | `bytes.Count(s, sep []byte) int` | Counts the number of non-overlapping instances of sep in s |
| 5 | `bytes.Cut(s, sep []byte) (before, after []byte, found bool)` | Slices s around the first instance of sep |
| 6 | `bytes.CutPrefix(s, prefix []byte) (after []byte, found bool)` | Returns s without the provided leading prefix |
| 7 | `bytes.CutSuffix(s, suffix []byte) (before []byte, found bool)` | Returns s without the provided trailing suffix |
| 8 | `bytes.Equal(a, b []byte) bool` | Reports whether a and b are the same length and contain the same bytes |
| 9 | `bytes.EqualFold(s, t []byte) bool` | Reports whether s and t are equal under Unicode case-folding |
| 10 | `bytes.Fields(s []byte) [][]byte` | Splits s around each instance of one or more consecutive white space characters |
| 11 | `bytes.FieldsFunc(s []byte, f func(rune) bool) [][]byte` | Splits s at each run of code points satisfying f |
| 12 | `bytes.HasPrefix(s, prefix []byte) bool` | Tests whether s begins with prefix |
| 13 | `bytes.HasSuffix(s, suffix []byte) bool` | Tests whether s ends with suffix |
| 14 | `bytes.Index(s, sep []byte) int` | Returns the index of the first instance of sep in s |
| 15 | `bytes.IndexAny(s []byte, chars string) int` | Returns the index of the first instance of any Unicode code point from chars |
| 16 | `bytes.IndexByte(b []byte, c byte) int` | Returns the index of the first instance of c in b |
| 17 | `bytes.IndexFunc(s []byte, f func(rune) bool) int` | Returns the index of the first Unicode code point satisfying f |
| 18 | `bytes.IndexRune(s []byte, r rune) int` | Returns the index of the first instance of the rune |
| 19 | `bytes.Join(s [][]byte, sep []byte) []byte` | Concatenates byte slices with separator |
| 20 | `bytes.LastIndex(s, sep []byte) int` | Returns the index of the last instance of sep in s |
| 21 | `bytes.LastIndexAny(s []byte, chars string) int` | Returns the index of the last instance of any Unicode code point from chars |
| 22 | `bytes.LastIndexByte(s []byte, c byte) int` | Returns the index of the last instance of c in s |
| 23 | `bytes.LastIndexFunc(s []byte, f func(rune) bool) int` | Returns the index of the last Unicode code point satisfying f |
| 24 | `bytes.Map(mapping func(rune) rune, s []byte) []byte` | Returns a copy with all characters modified by the mapping function |
| 25 | `bytes.Repeat(b []byte, count int) []byte` | Returns a new byte slice consisting of count copies of b |
| 26 | `bytes.Replace(s, old, new []byte, n int) []byte` | Returns a copy with the first n instances of old replaced by new |
| 27 | `bytes.ReplaceAll(s, old, new []byte) []byte` | Returns a copy with all instances of old replaced by new |
| 28 | `bytes.Split(s, sep []byte) [][]byte` | Slices s into substrings separated by sep |
| 29 | `bytes.SplitAfter(s, sep []byte) [][]byte` | Slices s into substrings after each instance of sep |
| 30 | `bytes.SplitAfterN(s, sep []byte, n int) [][]byte` | Slices s into substrings after each instance of sep, up to n |
| 31 | `bytes.SplitN(s, sep []byte, n int) [][]byte` | Slices s into substrings separated by sep, up to n |
| 32 | `bytes.Title(s []byte) []byte` | (Deprecated) Returns a copy with all Unicode letters that begin words mapped to title case |
| 33 | `bytes.ToLower(s []byte) []byte` | Returns a copy with all Unicode letters mapped to lower case |
| 34 | `bytes.ToUpper(s []byte) []byte` | Returns a copy with all Unicode letters mapped to upper case |
| 35 | `bytes.ToTitle(s []byte) []byte` | Returns a copy with all Unicode letters mapped to title case |
| 36 | `bytes.Trim(s []byte, cutset string) []byte` | Returns a subslice with all leading and trailing cutset code points removed |
| 37 | `bytes.TrimFunc(s []byte, f func(rune) bool) []byte` | Returns a subslice with all leading and trailing code points satisfying f removed |
| 38 | `bytes.TrimLeft(s []byte, cutset string) []byte` | Returns a subslice with all leading cutset code points removed |
| 39 | `bytes.TrimLeftFunc(s []byte, f func(rune) bool) []byte` | Returns a subslice with all leading code points satisfying f removed |
| 40 | `bytes.TrimPrefix(s, prefix []byte) []byte` | Returns s without the provided leading prefix |
| 41 | `bytes.TrimRight(s []byte, cutset string) []byte` | Returns a subslice with all trailing cutset code points removed |
| 42 | `bytes.TrimRightFunc(s []byte, f func(rune) bool) []byte` | Returns a subslice with all trailing code points satisfying f removed |
| 43 | `bytes.TrimSpace(s []byte) []byte` | Returns a subslice with all leading and trailing white space removed |
| 44 | `bytes.TrimSuffix(s, suffix []byte) []byte` | Returns s without the provided trailing suffix |
| 45 | `bytes.Compare(a, b []byte) int` | Returns an integer comparing two byte slices lexicographically |
| 46 | `bytes.NewBuffer(buf []byte) *Buffer` | Creates and initializes a new Buffer using buf as its initial contents |
| 47 | `bytes.NewBufferString(s string) *Buffer` | Creates and initializes a new Buffer using string s as its initial contents |
| 48 | `bytes.NewReader(b []byte) *Reader` | Returns a new Reader reading from b |

---

## 2. File/IO Functions

### 2.1 os package

| # | Function | Description |
|---|----------|-------------|
| 1 | `os.Create(name string) (*File, error)` | Creates or truncates the named file for writing (mode 0666) |
| 2 | `os.Open(name string) (*File, error)` | Opens the named file for reading |
| 3 | `os.OpenFile(name string, flag int, perm FileMode) (*File, error)` | Opens a file with specified flag (O_RDONLY, O_WRONLY, O_CREATE, etc.) and permissions |
| 4 | `os.Remove(name string) error` | Removes the named file or empty directory |
| 5 | `os.RemoveAll(path string) error` | Removes path and any children it contains |
| 6 | `os.Rename(oldpath, newpath string) error` | Renames (moves) oldpath to newpath |
| 7 | `os.Stat(name string) (FileInfo, error)` | Returns a FileInfo describing the named file |
| 8 | `os.Lstat(name string) (FileInfo, error)` | Like Stat but does not follow symbolic links |
| 9 | `os.Mkdir(name string, perm FileMode) error` | Creates a new directory with the specified permissions |
| 10 | `os.MkdirAll(path string, perm FileMode) error` | Creates a directory along with any necessary parents |
| 11 | `os.ReadDir(name string) ([]DirEntry, error)` | Reads the named directory, returning all its directory entries sorted by name |
| 12 | `os.ReadFile(name string) ([]byte, error)` | Reads the entire named file and returns the contents |
| 13 | `os.WriteFile(name string, data []byte, perm FileMode) error` | Writes data to the named file, creating it if necessary |
| 14 | `os.TempDir() string` | Returns the default directory for temporary files |
| 15 | `os.CreateTemp(dir, pattern string) (*File, error)` | Creates a new temporary file in dir with a name matching pattern |
| 16 | `os.MkdirTemp(dir, pattern string) (string, error)` | Creates a new temporary directory in dir with a name matching pattern |
| 17 | `os.UserHomeDir() (string, error)` | Returns the current user's home directory |
| 18 | `os.UserCacheDir() (string, error)` | Returns the default root directory for user-specific cached data |
| 19 | `os.Getwd() (string, error)` | Returns a rooted path name corresponding to the current directory |
| 20 | `os.Chdir(dir string) error` | Changes the current working directory to the named directory |
| 21 | `os.Chmod(name string, mode FileMode) error` | Changes the mode of the named file |
| 22 | `os.Chown(name string, uid, gid int) error` | Changes the numeric uid and gid of the named file |
| 23 | `os.Chtimes(name string, atime, mtime time.Time) error` | Changes the access and modification times of the named file |
| 24 | `os.Link(oldname, newname string) error` | Creates newname as a hard link to oldname |
| 25 | `os.Symlink(oldname, newname string) error` | Creates newname as a symbolic link to oldname |
| 26 | `os.Readlink(name string) (string, error)` | Returns the destination of the named symbolic link |
| 27 | `os.SameFile(fi1, fi2 FileInfo) bool` | Reports whether fi1 and fi2 describe the same file |
| 28 | `os.IsExist(err error) bool` | Reports whether the error is known to report that a file or directory already exists |
| 29 | `os.IsNotExist(err error) bool` | Reports whether the error is known to report that a file or directory does not exist |
| 30 | `os.IsPermission(err error) bool` | Reports whether the error is known to report a permission denied error |
| 31 | `os.Hostname() (string, error)` | Returns the host name reported by the kernel |
| 32 | `os.Environ() []string` | Returns a copy of strings representing the environment ("key=value") |
| 33 | `os.Getenv(key string) string` | Retrieves the value of the environment variable named by key |
| 34 | `os.Setenv(key, value string) error` | Sets the value of the environment variable named by key |
| 35 | `os.Unsetenv(key string) error` | Unsets a single environment variable |
| 36 | `os.LookupEnv(key string) (string, bool)` | Retrieves the value and presence of an environment variable |
| 37 | `os.Executable() (string, error)` | Returns the path name of the executable that started the current process |
| 38 | `os.Exit(code int)` | Causes the current program to exit with the given status code |
| 39 | `os.Getpid() int` | Returns the process id of the caller |
| 40 | `os.Getppid() int` | Returns the process id of the caller's parent |

### 2.2 os.File methods

| # | Method | Description |
|---|--------|-------------|
| 1 | `File.Read(b []byte) (n int, err error)` | Reads up to len(b) bytes from the File |
| 2 | `File.ReadAt(b []byte, off int64) (n int, err error)` | Reads len(b) bytes from the File starting at byte offset off |
| 3 | `File.ReadFrom(r io.Reader) (n int64, err error)` | Reads from r until EOF and appends it to the file |
| 4 | `File.Write(b []byte) (n int, err error)` | Writes len(b) bytes to the File |
| 5 | `File.WriteAt(b []byte, off int64) (n int, err error)` | Writes len(b) bytes to the File starting at byte offset off |
| 6 | `File.WriteString(s string) (n int, err error)` | Writes the contents of string s to the file |
| 7 | `File.Seek(offset int64, whence int) (int64, error)` | Sets the offset for the next Read or Write on file |
| 8 | `File.Close() error` | Closes the File, rendering it unusable for I/O |
| 9 | `File.Name() string` | Returns the name of the file as presented to Open |
| 10 | `File.Stat() (FileInfo, error)` | Returns the FileInfo structure describing the file |
| 11 | `File.Sync() error` | Commits the current contents of the file to stable storage (fsync) |
| 12 | `File.Truncate(size int64) error` | Changes the size of the file |
| 13 | `File.Fd() uintptr` | Returns the integer Unix file descriptor referencing the open file |
| 14 | `File.Chmod(mode FileMode) error` | Changes the mode of the file |
| 15 | `File.Chown(uid, gid int) error` | Changes the numeric uid and gid of the named file |
| 16 | `File.ReadDir(n int) ([]DirEntry, error)` | Reads the contents of the directory, returning up to n DirEntry values |
| 17 | `File.Readdirnames(n int) ([]string, error)` | Reads the names of files in the directory, up to n names |
| 18 | `File.SetDeadline(t time.Time) error` | Sets the read and write deadlines for the File |
| 19 | `File.SetReadDeadline(t time.Time) error` | Sets the deadline for future Read calls and any currently-blocked Read |
| 20 | `File.SetWriteDeadline(t time.Time) error` | Sets the deadline for future Write calls and any currently-blocked Write |

### 2.3 io package

| # | Function | Description |
|---|----------|-------------|
| 1 | `io.Copy(dst Writer, src Reader) (int64, error)` | Copies from src to dst until EOF or an error |
| 2 | `io.CopyBuffer(dst Writer, src Reader, buf []byte) (int64, error)` | Like Copy but uses the provided buffer for staging |
| 3 | `io.CopyN(dst Writer, src Reader, n int64) (int64, error)` | Copies n bytes from src to dst |
| 4 | `io.ReadAll(r Reader) ([]byte, error)` | Reads from r until EOF and returns the data read |
| 5 | `io.ReadAtLeast(r Reader, buf []byte, min int) (int, error)` | Reads from r into buf until it has read at least min bytes |
| 6 | `io.ReadFull(r Reader, buf []byte) (int, error)` | Reads exactly len(buf) bytes from r into buf |
| 7 | `io.WriteString(w Writer, s string) (int, error)` | Writes the contents of string s to w |
| 8 | `io.Pipe() (*PipeReader, *PipeWriter)` | Creates a synchronous in-memory pipe |
| 9 | `io.LimitReader(r Reader, n int64) Reader` | Returns a Reader that reads from r but stops with EOF after n bytes |
| 10 | `io.NewSectionReader(r ReaderAt, off, n int64) *SectionReader` | Returns a SectionReader that reads from r starting at offset off for n bytes |
| 11 | `io.TeeReader(r Reader, w Writer) Reader` | Returns a Reader that writes to w what it reads from r |
| 12 | `io.MultiReader(readers ...Reader) Reader` | Returns a Reader that is the logical concatenation of the provided readers |
| 13 | `io.MultiWriter(writers ...Writer) Writer` | Creates a Writer that duplicates its writes to all the provided writers |
| 14 | `io.NopCloser(r Reader) ReadCloser` | Returns a ReadCloser with a no-op Close method wrapping the provided Reader |

### 2.4 io/fs package

| # | Function | Description |
|---|----------|-------------|
| 1 | `fs.Glob(fsys FS, pattern string) ([]string, error)` | Returns the names of all files matching pattern in the file system |
| 2 | `fs.WalkDir(fsys FS, root string, fn WalkDirFunc) error` | Walks the file tree rooted at root, calling fn for each file or directory |
| 3 | `fs.ReadFile(fsys FS, name string) ([]byte, error)` | Reads the named file from the file system and returns its contents |
| 4 | `fs.ReadDir(fsys FS, name string) ([]DirEntry, error)` | Reads the named directory and returns a list of directory entries |
| 5 | `fs.Stat(fsys FS, name string) (FileInfo, error)` | Returns a FileInfo describing the named file from the file system |
| 6 | `fs.Sub(fsys FS, dir string) (FS, error)` | Returns an FS corresponding to the subtree rooted at dir |
| 7 | `fs.ValidPath(name string) bool` | Reports whether the given path name is valid for use in a call to Open |

### 2.5 path/filepath package

| # | Function | Description |
|---|----------|-------------|
| 1 | `filepath.Abs(path string) (string, error)` | Returns an absolute representation of path |
| 2 | `filepath.Base(path string) string` | Returns the last element of path |
| 3 | `filepath.Clean(path string) string` | Returns the shortest path name equivalent to path by purely lexical processing |
| 4 | `filepath.Dir(path string) string` | Returns all but the last element of path (the directory) |
| 5 | `filepath.EvalSymlinks(path string) (string, error)` | Returns the path name after evaluation of any symbolic links |
| 6 | `filepath.Ext(path string) string` | Returns the file name extension used by path |
| 7 | `filepath.FromSlash(path string) string` | Returns the result of replacing each slash in path with the OS separator |
| 8 | `filepath.Glob(pattern string) ([]string, error)` | Returns the names of all files matching pattern |
| 9 | `filepath.IsAbs(path string) bool` | Reports whether the path is absolute |
| 10 | `filepath.IsLocal(path string) bool` | Reports whether path is local (does not escape the current directory) |
| 11 | `filepath.Join(elem ...string) string` | Joins any number of path elements into a single path, separated by the OS separator |
| 12 | `filepath.Match(pattern, name string) (bool, error)` | Reports whether name matches the shell file name pattern |
| 13 | `filepath.Rel(basepath, targpath string) (string, error)` | Returns a relative path that is lexically equivalent to targpath when joined to basepath |
| 14 | `filepath.Split(path string) (dir, file string)` | Splits path immediately following the final separator into directory and file components |
| 15 | `filepath.SplitList(path string) []string` | Splits a list of paths joined by the OS-specific ListSeparator |
| 16 | `filepath.ToSlash(path string) string` | Returns the result of replacing each OS separator in path with a slash |
| 17 | `filepath.VolumeName(path string) string` | Returns the leading volume name (Windows drive letter or UNC path prefix) |
| 18 | `filepath.Walk(root string, fn WalkFunc) error` | Walks the file tree rooted at root, calling fn for each file or directory (legacy) |
| 19 | `filepath.WalkDir(root string, fn fs.WalkDirFunc) error` | Like Walk but more efficient; uses fs.DirEntry instead of calling Lstat |

### 2.6 bufio package

| # | Function/Method | Description |
|---|-----------------|-------------|
| 1 | `bufio.NewReader(rd io.Reader) *Reader` | Returns a new Reader whose buffer has the default size (4096) |
| 2 | `bufio.NewReaderSize(rd io.Reader, size int) *Reader` | Returns a new Reader with at least the specified buffer size |
| 3 | `bufio.NewWriter(w io.Writer) *Writer` | Returns a new Writer whose buffer has the default size (4096) |
| 4 | `bufio.NewWriterSize(w io.Writer, size int) *Writer` | Returns a new Writer with at least the specified buffer size |
| 5 | `bufio.NewScanner(r io.Reader) *Scanner` | Returns a new Scanner to read from r |
| 6 | `Reader.ReadLine() (line []byte, isPrefix bool, err error)` | Reads a single line, not including the end-of-line bytes |
| 7 | `Reader.ReadString(delim byte) (string, error)` | Reads until the first occurrence of delim, returning the data read including the delimiter |
| 8 | `Reader.ReadBytes(delim byte) ([]byte, error)` | Reads until the first occurrence of delim, returning a byte slice including the delimiter |
| 9 | `Reader.ReadByte() (byte, error)` | Reads and returns a single byte |
| 10 | `Reader.UnreadByte() error` | Unreads the last byte read |
| 11 | `Reader.ReadRune() (r rune, size int, err error)` | Reads a single UTF-8 encoded Unicode character |
| 12 | `Reader.UnreadRune() error` | Unreads the last rune read |
| 13 | `Reader.Peek(n int) ([]byte, error)` | Returns the next n bytes without advancing the reader |
| 14 | `Reader.Buffered() int` | Returns the number of bytes that can be read from the current buffer |
| 15 | `Reader.Reset(r io.Reader)` | Discards any buffered data and resets the reader to read from r |
| 16 | `Writer.Write(p []byte) (int, error)` | Writes the contents of p into the buffer |
| 17 | `Writer.WriteString(s string) (int, error)` | Writes a string into the buffer |
| 18 | `Writer.WriteByte(c byte) error` | Writes a single byte |
| 19 | `Writer.WriteRune(r rune) (int, error)` | Writes a single Unicode code point |
| 20 | `Writer.Flush() error` | Writes any buffered data to the underlying io.Writer |
| 21 | `Writer.Available() int` | Returns how many bytes are unused in the buffer |
| 22 | `Writer.Buffered() int` | Returns the number of bytes that have been written into the current buffer |
| 23 | `Writer.Reset(w io.Writer)` | Discards any unflushed buffered data and resets the writer to write to w |
| 24 | `Scanner.Scan() bool` | Advances the Scanner to the next token (returns false at EOF or error) |
| 25 | `Scanner.Text() string` | Returns the most recent token generated by a call to Scan as a string |
| 26 | `Scanner.Bytes() []byte` | Returns the most recent token generated by a call to Scan as a byte slice |
| 27 | `Scanner.Err() error` | Returns the first non-EOF error encountered by the Scanner |
| 28 | `Scanner.Split(split SplitFunc)` | Sets the split function for the Scanner (default: ScanLines) |
| 29 | `Scanner.Buffer(buf []byte, max int)` | Sets the initial buffer and maximum size for scanning |

---

## 3. Collection Functions

### 3.1 Built-in functions (slices, maps, channels)

| # | Function | Description |
|---|----------|-------------|
| 1 | `append(slice []T, elems ...T) []T` | Appends elements to the end of a slice and returns the updated slice |
| 2 | `copy(dst, src []T) int` | Copies elements from a source slice into a destination slice, returns count copied |
| 3 | `len(v T) int` | Returns the length of a string, array, slice, map, or channel |
| 4 | `cap(v T) int` | Returns the capacity of an array, slice, or channel |
| 5 | `make(t T, size ...int) T` | Allocates and initializes a slice, map, or channel |
| 6 | `delete(m map[K]V, key K)` | Deletes the element with the specified key from a map |
| 7 | `clear(t T)` | Clears a map or zeroes a slice (Go 1.21+) |
| 8 | `min(x T, y ...T) T` | Returns the smallest value among its arguments (Go 1.21+) |
| 9 | `max(x T, y ...T) T` | Returns the largest value among its arguments (Go 1.21+) |
| 10 | `new(T) *T` | Allocates memory for a value of type T and returns a pointer to it |
| 11 | `close(ch chan<- T)` | Closes a channel |

### 3.2 slices package (Go 1.21+)

| # | Function | Description |
|---|----------|-------------|
| 1 | `slices.BinarySearch(x []E, target E) (int, bool)` | Searches for target in a sorted slice, returns index and found flag |
| 2 | `slices.BinarySearchFunc(x []E, target T, cmp func(E, T) int) (int, bool)` | Like BinarySearch but uses a custom comparison function |
| 3 | `slices.Clip(s []E) []E` | Removes unused capacity from the slice (sets cap to len) |
| 4 | `slices.Clone(s []E) []E` | Returns a copy of the slice |
| 5 | `slices.Compact(s []E) []E` | Replaces consecutive runs of equal elements with a single copy (in-place) |
| 6 | `slices.CompactFunc(s []E, eq func(E, E) bool) []E` | Like Compact but uses an equality function |
| 7 | `slices.Compare(s1, s2 []E) int` | Compares elements of two slices using operators < and > |
| 8 | `slices.CompareFunc(s1 []E1, s2 []E2, cmp func(E1, E2) int) int` | Like Compare but uses a custom comparison function |
| 9 | `slices.Concat(slices ...[]E) []E` | Returns a new slice concatenating the passed in slices |
| 10 | `slices.Contains(s []E, v E) bool` | Reports whether v is present in s |
| 11 | `slices.ContainsFunc(s []E, f func(E) bool) bool` | Reports whether at least one element satisfies f |
| 12 | `slices.Delete(s []E, i, j int) []E` | Removes the elements s[i:j] from s, returning the modified slice |
| 13 | `slices.DeleteFunc(s []E, del func(E) bool) []E` | Removes any elements for which del returns true |
| 14 | `slices.Equal(s1, s2 []E) bool` | Reports whether two slices are equal (same length and all elements equal) |
| 15 | `slices.EqualFunc(s1 []E1, s2 []E2, eq func(E1, E2) bool) bool` | Reports whether two slices are equal using a custom equality function |
| 16 | `slices.Grow(s []E, n int) []E` | Increases the slice's capacity by at least n elements |
| 17 | `slices.Index(s []E, v E) int` | Returns the index of the first occurrence of v in s, or -1 |
| 18 | `slices.IndexFunc(s []E, f func(E) bool) int` | Returns the index of the first element satisfying f, or -1 |
| 19 | `slices.Insert(s []E, i int, v ...E) []E` | Inserts the values v... into s at index i |
| 20 | `slices.IsSorted(x []E) bool` | Reports whether x is sorted in ascending order |
| 21 | `slices.IsSortedFunc(x []E, cmp func(a, b E) int) bool` | Reports whether x is sorted according to the provided comparison function |
| 22 | `slices.Max(x []E) E` | Returns the maximal value in x (panics if empty) |
| 23 | `slices.MaxFunc(x []E, cmp func(a, b E) int) E` | Returns the maximal value using a custom comparison function |
| 24 | `slices.Min(x []E) E` | Returns the minimal value in x (panics if empty) |
| 25 | `slices.MinFunc(x []E, cmp func(a, b E) int) E` | Returns the minimal value using a custom comparison function |
| 26 | `slices.Replace(s []E, i, j int, v ...E) []E` | Replaces the elements s[i:j] with v... |
| 27 | `slices.Reverse(s []E)` | Reverses the elements of the slice in place |
| 28 | `slices.Sort(x []E)` | Sorts a slice of any ordered type in ascending order |
| 29 | `slices.SortFunc(x []E, cmp func(a, b E) int)` | Sorts x using the provided comparison function |
| 30 | `slices.SortStableFunc(x []E, cmp func(a, b E) int)` | Sorts x using the provided comparison function, keeping equal elements in original order |

### 3.3 maps package (Go 1.21+)

| # | Function | Description |
|---|----------|-------------|
| 1 | `maps.Clone(m map[K]V) map[K]V` | Returns a copy of the map (shallow clone) |
| 2 | `maps.Copy(dst, src map[K]V)` | Copies all key/value pairs from src to dst |
| 3 | `maps.DeleteFunc(m map[K]V, del func(K, V) bool)` | Deletes any key/value pairs for which del returns true |
| 4 | `maps.Equal(m1, m2 map[K]V) bool` | Reports whether two maps contain the same key/value pairs |
| 5 | `maps.EqualFunc(m1 map[K]V1, m2 map[K]V2, eq func(V1, V2) bool) bool` | Like Equal but uses a custom equality function for values |
| 6 | `maps.Keys(m map[K]V) []K` | Returns the keys of the map in an indeterminate order |
| 7 | `maps.Values(m map[K]V) []V` | Returns the values of the map in an indeterminate order |
| 8 | `maps.Collect(seq iter.Seq2[K, V]) map[K]V` | Collects key-value pairs from an iterator into a new map |

### 3.4 sort package

| # | Function | Description |
|---|----------|-------------|
| 1 | `sort.Sort(data Interface)` | Sorts data in ascending order as determined by the Less method |
| 2 | `sort.Stable(data Interface)` | Sorts data while keeping the original order of equal elements |
| 3 | `sort.Slice(x any, less func(i, j int) bool)` | Sorts a slice given a less function (not stable) |
| 4 | `sort.SliceStable(x any, less func(i, j int) bool)` | Sorts a slice given a less function (stable) |
| 5 | `sort.SliceIsSorted(x any, less func(i, j int) bool) bool` | Reports whether the slice x is sorted according to the less function |
| 6 | `sort.Search(n int, f func(int) bool) int` | Binary search: returns smallest index i in [0, n) at which f(i) is true |
| 7 | `sort.SearchInts(a []int, x int) int` | Searches for x in a sorted slice of ints and returns the index |
| 8 | `sort.SearchFloat64s(a []float64, x float64) int` | Searches for x in a sorted slice of float64s and returns the index |
| 9 | `sort.SearchStrings(a []string, x string) int` | Searches for x in a sorted slice of strings and returns the index |
| 10 | `sort.Ints(x []int)` | Sorts a slice of ints in increasing order |
| 11 | `sort.Float64s(x []float64)` | Sorts a slice of float64s in increasing order |
| 12 | `sort.Strings(x []string)` | Sorts a slice of strings in increasing order |
| 13 | `sort.Reverse(data Interface) Interface` | Returns the reverse of data's sort order (wraps Interface) |

### 3.5 container/list (doubly linked list)

| # | Method | Description |
|---|--------|-------------|
| 1 | `List.PushBack(v any) *Element` | Inserts a new element with value v at the back of the list |
| 2 | `List.PushFront(v any) *Element` | Inserts a new element with value v at the front of the list |
| 3 | `List.InsertBefore(v any, mark *Element) *Element` | Inserts a new element with value v immediately before mark |
| 4 | `List.InsertAfter(v any, mark *Element) *Element` | Inserts a new element with value v immediately after mark |
| 5 | `List.MoveToFront(e *Element)` | Moves element e to the front of the list |
| 6 | `List.MoveToBack(e *Element)` | Moves element e to the back of the list |
| 7 | `List.MoveBefore(e, mark *Element)` | Moves element e to its new position before mark |
| 8 | `List.MoveAfter(e, mark *Element)` | Moves element e to its new position after mark |
| 9 | `List.Remove(e *Element) any` | Removes e from the list and returns e's value |
| 10 | `List.Front() *Element` | Returns the first element of the list or nil if the list is empty |
| 11 | `List.Back() *Element` | Returns the last element of the list or nil if the list is empty |
| 12 | `List.Len() int` | Returns the number of elements in the list |
| 13 | `List.Init() *List` | Initializes or clears the list |
| 14 | `list.New() *List` | Returns an initialized list |
| 15 | `Element.Next() *Element` | Returns the next list element or nil |
| 16 | `Element.Prev() *Element` | Returns the previous list element or nil |

### 3.6 container/heap

| # | Function | Description |
|---|----------|-------------|
| 1 | `heap.Init(h Interface)` | Establishes the heap invariants on a collection implementing heap.Interface |
| 2 | `heap.Push(h Interface, x any)` | Pushes the element x onto the heap and re-establishes heap ordering |
| 3 | `heap.Pop(h Interface) any` | Removes and returns the minimum element (according to Less) from the heap |
| 4 | `heap.Remove(h Interface, i int) any` | Removes and returns the element at index i from the heap |
| 5 | `heap.Fix(h Interface, i int)` | Re-establishes the heap ordering after the element at index i has changed its value |

### 3.7 container/ring (circular list)

| # | Method | Description |
|---|--------|-------------|
| 1 | `Ring.Do(f func(any))` | Calls function f on each element of the ring, in forward order |
| 2 | `Ring.Len() int` | Computes the number of elements in ring r (executes in O(n) time) |
| 3 | `Ring.Link(s *Ring) *Ring` | Connects ring r with ring s such that r.Next() becomes s |
| 4 | `Ring.Move(n int) *Ring` | Moves n elements backward (n < 0) or forward (n > 0) in the ring |
| 5 | `Ring.Next() *Ring` | Returns the next ring element |
| 6 | `Ring.Prev() *Ring` | Returns the previous ring element |
| 7 | `Ring.Unlink(n int) *Ring` | Removes n elements from the ring starting from r.Next() |
| 8 | `ring.New(n int) *Ring` | Creates a ring of n elements (value of the new ring is nil) |

### 3.8 sync.Map (concurrent map)

| # | Method | Description |
|---|--------|-------------|
| 1 | `Map.Load(key any) (value any, ok bool)` | Returns the value stored for a key, or nil if no value is present |
| 2 | `Map.Store(key, value any)` | Sets the value for a key |
| 3 | `Map.Delete(key any)` | Deletes the value for a key |
| 4 | `Map.LoadOrStore(key, value any) (actual any, loaded bool)` | Returns the existing value if present; otherwise stores and returns the given value |
| 5 | `Map.LoadAndDelete(key any) (value any, loaded bool)` | Deletes the value for a key, returning the previous value if any |
| 6 | `Map.Range(f func(key, value any) bool)` | Calls f sequentially for each key/value pair; stops if f returns false |
| 7 | `Map.CompareAndSwap(key, old, new any) bool` | Swaps the old and new values for a key if the value stored equals old |
| 8 | `Map.CompareAndDelete(key, old any) bool` | Deletes the entry for key if its value is equal to old |
| 9 | `Map.Swap(key, value any) (previous any, loaded bool)` | Swaps the value for a key and returns the previous value if any |

---

## Summary Statistics

| Category | Count |
|----------|-------|
| strings package | 49 |
| strings.Builder | 9 |
| strings.Reader | 11 |
| strings.Replacer | 2 |
| strconv package | 21 |
| fmt (string-related) | 5 |
| unicode package | 17 |
| regexp package | 19 |
| bytes package | 48 |
| os package | 40 |
| os.File methods | 20 |
| io package | 14 |
| io/fs package | 7 |
| path/filepath package | 19 |
| bufio package | 29 |
| Built-in functions | 11 |
| slices package | 30 |
| maps package | 8 |
| sort package | 13 |
| container/list | 16 |
| container/heap | 5 |
| container/ring | 8 |
| sync.Map | 9 |
| **TOTAL** | **430** |

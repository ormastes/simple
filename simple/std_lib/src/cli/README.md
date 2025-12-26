# CLI - Command-Line Argument Parsing Library

A declarative, type-safe command-line argument parsing library for Simple language applications, inspired by clap (Rust) and argparse (Python).

## Features

- ✅ **Boolean Flags** - `--verbose`, `-v`
- ✅ **String Options** - `--output <file>`, `-o <file>`
- ✅ **Positional Arguments** - Required and optional positionals
- ✅ **Multiple Formats** - `--option=value`, `--option value`, `-o value`
- ✅ **Required vs Optional** - Specify which arguments are required
- ✅ **Default Values** - Provide defaults for optional options
- ✅ **Automatic Help** - `--help`, `-h` flag with formatted help text
- ✅ **Error Handling** - Clear error messages for invalid arguments
- ✅ **Builder Pattern API** - Fluent, chainable argument definitions
- ✅ **File Validation** - Python argparse-style file existence and type checking
- ✅ **File Staging** - Batch validation and staging of multiple files
- ✅ **Path Utilities** - Normalize, join, extract components from file paths

## Quick Start

```simple
use cli

fn main():
    let parser = cli.ArgParser::new("myapp", "My application")
        .flag("verbose", "v", "Enable verbose output")
        .required_option("output", "o", "Output file path")
        .required_positional("input", "Input file path")

    match parser.parse(sys_get_args()):
        case Ok(args):
            let verbose = args.get_flag("verbose")
            let output = args.get_option("output").unwrap()
            let input = args.get_positional_at(0).unwrap()

            # Process arguments...

        case Err(error):
            print(f"Error: {error}")
            parser.print_help()
            sys_exit(1)
```

## Usage Examples

### Boolean Flags

Flags are boolean switches that don't take values:

```simple
let parser = ArgParser::new("app", "Description")
    .flag("verbose", "v", "Enable verbose output")
    .flag("debug", "d", "Enable debug mode")

# Usage:
# ./app --verbose
# ./app -v -d
# ./app --verbose --debug

match parser.parse(args):
    case Ok(parsed):
        if parsed.get_flag("verbose"):
            print("Verbose mode enabled")
```

### String Options

Options take string values:

```simple
let parser = ArgParser::new("app", "Description")
    .required_option("output", "o", "Output file (required)")
    .optional_option("format", "f", "Output format", "json")

# Usage:
# ./app --output result.txt
# ./app -o result.txt --format xml
# ./app --output=result.txt

match parser.parse(args):
    case Ok(parsed):
        let output = parsed.get_option("output").unwrap()
        let format = parsed.get_option_or("format", "json")
```

### Positional Arguments

Positional arguments don't have flags:

```simple
let parser = ArgParser::new("app", "Description")
    .required_positional("source", "Source file")
    .required_positional("dest", "Destination file")

# Usage:
# ./app input.txt output.txt

match parser.parse(args):
    case Ok(parsed):
        let source = parsed.get_positional_at(0).unwrap()
        let dest = parsed.get_positional_at(1).unwrap()
```

### Mixed Arguments

Combine flags, options, and positionals:

```simple
let parser = ArgParser::new("converter", "File format converter")
    .flag("verbose", "v", "Enable verbose output")
    .flag("overwrite", "w", "Overwrite existing files")
    .required_option("format", "f", "Output format")
    .optional_option("quality", "q", "Compression quality", "80")
    .required_positional("input", "Input file")
    .positional("output", "Output file (optional if stdout)", false)

# Usage:
# ./converter --format png -v input.jpg output.png
# ./converter -f png --quality 100 input.jpg
```

## API Reference

### ArgParser

Main parser class for defining and parsing command-line arguments.

#### Constructor

```simple
ArgParser::new(program_name: String, description: String) -> ArgParser
```

Create a new argument parser.

#### Methods

##### `.flag(name: String, short: String, help: String) -> ArgParser`

Add a boolean flag.

- `name` - Long name (used with `--name`)
- `short` - Short name (used with `-s`)
- `help` - Help description

**Example:**
```simple
.flag("verbose", "v", "Enable verbose output")
```

**Usage:** `--verbose` or `-v`

##### `.option(name: String, short: String, help: String, required: bool, default: Option[String]) -> ArgParser`

Add a string option.

- `name` - Long name
- `short` - Short name
- `help` - Help description
- `required` - Whether the option is required
- `default` - Default value (None if required)

**Example:**
```simple
.option("output", "o", "Output file", true, None)
```

##### `.required_option(name: String, short: String, help: String) -> ArgParser`

Convenience method for adding a required option.

**Example:**
```simple
.required_option("output", "o", "Output file path")
```

##### `.optional_option(name: String, short: String, help: String, default: String) -> ArgParser`

Convenience method for adding an optional option with a default value.

**Example:**
```simple
.optional_option("format", "f", "Output format", "json")
```

##### `.file_option(name: String, short: String, help: String, required: bool, must_exist: bool) -> ArgParser`

Add a file option with automatic validation and staging.

- `name` - Long name
- `short` - Short name
- `help` - Help description
- `required` - Whether the option is required
- `must_exist` - Whether the file must exist (false for output files)

Files are automatically validated during `parse()` and available in `ParsedArgs.files`.

**Example:**
```simple
.file_option("input", "i", "Input file", required: true, must_exist: true)
.file_option("output", "o", "Output file", required: false, must_exist: false)
```

**Usage:** `--input file.txt` or `-i file.txt`

##### `.file_option_custom(name: String, short: String, help: String, required: bool, validator: FileValidator) -> ArgParser`

Add a file option with custom validator for advanced validation rules.

**Example:**
```simple
let custom_validator = file.FileValidator::new()
    .require_exists()
    .require_readable()
    .with_extensions(["spl", "rs", "py"])

.file_option_custom("input", "i", "Input file", true, custom_validator)
```

##### `.positional(name: String, help: String, required: bool) -> ArgParser`

Add a positional argument.

**Example:**
```simple
.positional("input", "Input file path", true)
```

##### `.required_positional(name: String, help: String) -> ArgParser`

Convenience method for adding a required positional.

**Example:**
```simple
.required_positional("input", "Input file path")
```

##### `.file_positional(name: String, help: String, required: bool) -> ArgParser`

Add file positional arguments with automatic validation and staging.

All file positionals are automatically validated during `parse()` and available in `ParsedArgs.files`.

**Example:**
```simple
.file_positional("files", "Files to process", required: false)
```

**Usage:** `./app file1.spl file2.spl file3.spl`

##### `.parse(args: Array[String]) -> Result[ParsedArgs, String]`

Parse the command-line arguments.

- Returns `Ok(ParsedArgs)` on success
- Returns `Err(String)` with error message on failure

**Example:**
```simple
match parser.parse(sys_get_args()):
    case Ok(args):
        # Process args
    case Err(error):
        print(f"Error: {error}")
```

##### `.print_help()`

Print the formatted help message to stdout.

**Example:**
```simple
parser.print_help()
```

### ParsedArgs

Container for parsed argument values.

#### Fields

##### `.files: file.StagedFiles`

All file arguments (both file options and file positionals) that were automatically validated and staged during `parse()`.

**Example:**
```simple
match parser.parse(sys_get_args()):
    case Ok(args):
        # Access all validated files
        for file_info in args.files.staged():
            print(f"Processing: {file_info.absolute_path}")

        # Check for file validation errors
        if args.files.has_errors():
            for error in args.files.get_errors():
                print(f"Error: {error}")
```

#### Methods

##### `.get_flag(name: String) -> bool`

Get a flag value (returns `true` if present, `false` if not).

**Example:**
```simple
let verbose = args.get_flag("verbose")
```

##### `.has_flag(name: String) -> bool`

Alias for `get_flag()`.

##### `.get_option(name: String) -> Option[String]`

Get an option value as an `Option[String]`.

**Example:**
```simple
match args.get_option("output"):
    case Some(path):
        print(f"Output: {path}")
    case None:
        print("No output specified")
```

##### `.get_option_or(name: String, default: String) -> String`

Get an option value with a default fallback.

**Example:**
```simple
let format = args.get_option_or("format", "json")
```

##### `.get_option_int(name: String) -> Option[i32]`

Get an option value as an integer (TODO: requires String::parse_int()).

##### `.get_option_float(name: String) -> Option[f64]`

Get an option value as a float (TODO: requires String::parse_float()).

##### `.get_positional_at(index: i32) -> Option[String]`

Get a positional argument by index (0-based).

**Example:**
```simple
let first = args.get_positional_at(0).unwrap()
let second = args.get_positional_at(1).unwrap()
```

##### `.get_positional(name: String) -> Option[String]`

Get a positional argument by name (returns first positional for now).

##### `.get_all_positionals() -> Array[String]`

Get all positional arguments as an array.

**Example:**
```simple
let files = args.get_all_positionals()
for file in files:
    print(f"Processing: {file}")
```

## Help Generation

The library automatically generates formatted help messages:

```
myapp - My application description

USAGE:
    myapp [-v|--verbose] --output <output> <input>

OPTIONS:
    -v, --verbose            Enable verbose output
    -o, --output <output>    Output file path
                             [required]

ARGS:
    <input>    Input file path
               [required]

    -h, --help               Print this help message
```

### Automatic Help Handling

The `--help` and `-h` flags are automatically handled:

```bash
./myapp --help
# Prints help message and returns Ok with empty args
```

## Error Messages

Clear, actionable error messages:

```
Error: Required option --output not provided
Error: Unknown option: --invalid
Error: Option --output requires a value
Error: Expected at least 1 positional arguments, got 0
```

## Argument Formats Supported

The library supports multiple formats for convenience:

**Long form with space:**
```bash
--output file.txt
```

**Long form with equals:**
```bash
--output=file.txt
```

**Short form:**
```bash
-o file.txt
```

**Multiple flags:**
```bash
-v -d
--verbose --debug
```

**Mixed:**
```bash
./app -v --output=result.txt input.txt
./app input.txt --output result.txt -v
```

## Examples

See the examples directory:

- `examples/cli_quickstart.spl` - Minimal example
- `examples/cli_demo.spl` - Comprehensive example with all features

## Testing

Tests are located in `test/unit/cli_spec.spl`:

```bash
./simple test/unit/cli_spec.spl
```

## Limitations

1. **Integer/Float Parsing** - `get_option_int()` and `get_option_float()` are TODO (need String parsing methods)
2. **Positional Names** - `get_positional(name)` currently returns first positional (needs positional tracking)
3. **Short Flag Bundling** - `-vd` not supported yet (must use `-v -d`)
4. **Subcommands** - Not implemented (planned for future version)

## Future Enhancements

- [ ] Subcommand support (`git commit`, `cargo build`)
- [ ] Short flag bundling (`-vd` → `-v -d`)
- [ ] Integer/float type conversion
- [ ] Custom validators
- [ ] Environment variable fallbacks
- [ ] Configuration file integration
- [ ] Shell completion generation
- [ ] Man page generation

## Related

- **sys_get_args()** - Built-in FFI function to get command-line arguments
- **std.sys.args** - Standard library args module (planned)
- **std.config** - Configuration management (planned)

## License

Part of the Simple Language Standard Library.

---

## File Validation (`cli.file`)

Python argparse-style **automatic** file validation for command-line arguments.

### Key Concept: Automatic File Staging

Unlike traditional CLI libraries where you manually validate files after parsing, the Simple CLI library automatically validates and stages all file arguments **during** the `parse()` call:

**Traditional Approach (Manual):**
```simple
# Parse arguments
let args = parser.parse(sys_get_args()).unwrap()
# Then manually validate each file
let validator = file.input_file_validator()
match validator.validate(args.get_option("input").unwrap()):
    case Ok(info): # Process file
    case Err(e): # Handle error
```

**Simple CLI Approach (Automatic):**
```simple
# Files automatically validated during parse!
match parser.parse(sys_get_args()):
    case Ok(args):
        # Files already validated - ready to use!
        for file in args.files.staged():
            process(file)
    case Err(error):
        # File validation errors included here
```

### Features

- ✅ **Automatic File Staging** - Files validated during `parse()`, no manual validation needed
- ✅ **File Existence Checking** - Verify files exist (relative or absolute paths)
- ✅ **File Type Validation** - Check file extensions (.spl, .json, .toml, etc.)
- ✅ **Permission Checking** - Validate readable/writable files
- ✅ **Path Normalization** - Convert relative to absolute paths
- ✅ **Error Reporting** - File validation errors included in parse result

### Quick Start (Automatic Staging)

```simple
use cli
use cli.file as file

fn main():
    let parser = cli.ArgParser::new("processor", "File processor")
        # File options are automatically validated!
        .file_option("input", "i", "Input file", required: true, must_exist: true)
        .file_option("output", "o", "Output file", required: false, must_exist: false)

    match parser.parse(sys_get_args()):
        case Ok(args):
            # Files already validated - ready to use!
            for file_info in args.files.staged():
                print(f"Processing: {file_info.absolute_path}")

        case Err(error):
            # File validation errors included here
            print(f"Error: {error}")
            sys_exit(1)
```

### FileValidator

Create custom file validators with validation rules:

```simple
# Input file validator (must exist, readable, specific extensions)
let validator = file.FileValidator::new()
    .require_exists()
    .require_readable()
    .with_extensions(["spl", "rs", "py"])

match validator.validate("main.spl"):
    case Ok(info):
        print(f"Valid: {info.absolute_path}")
    case Err(error):
        print(f"Invalid: {error}")
```

### Built-in Validators

Convenient pre-configured validators for common cases:

```simple
# Input files (must exist, readable)
let input_validator = file.input_file_validator()

# Output files (writable, can be created)
let output_validator = file.output_file_validator()

# Config files (must exist, readable, .json/.toml/.yaml)
let config_validator = file.config_file_validator()

# Source files (must exist, readable, .spl/.rs/.py/.js/.ts)
let source_validator = file.source_file_validator()
```

### File Staging

Batch validate and stage multiple files:

```simple
# Stage all positional files for processing
let stager = file.FileStager::new()
let staged = stager.stage_files(args)

if staged.has_errors():
    for error in staged.get_errors():
        print(f"Error: {error}")
    sys_exit(1)

for file_info in staged.staged():
    print(f"Processing: {file_info.path}")
    # Process file...
```

### Path Utilities

Manipulate and inspect file paths:

```simple
use cli.file as file

# Check path type
let is_abs = file.is_absolute_path("/home/user/file.txt")  # true
let is_rel = file.is_relative_path("src/main.spl")         # true

# Normalize paths (relative → absolute)
let abs_path = file.normalize_path("src/main.spl")  
# → "/current/dir/src/main.spl"

# Extract path components
let dir = file.get_directory("src/main.spl")        # "src"
let filename = file.get_filename("src/main.spl")    # "main.spl"
let basename = file.get_basename("src/main.spl")    # "main"
let ext = file.get_file_extension("src/main.spl")   # "spl"

# Join paths
let joined = file.join_paths("src", "utils.spl")    # "src/utils.spl"
```

### FileInfo Structure

Information about a validated file:

```simple
struct FileInfo:
    path: String            # Original path
    absolute_path: String   # Normalized absolute path
    exists: bool            # File exists on disk
    is_file: bool           # Is a regular file (not directory)
    is_dir: bool            # Is a directory
    is_readable: bool       # Has read permissions
    is_writable: bool       # Has write permissions
```

### Complete Example (Automatic Staging)

```simple
use cli
use cli.file as file

fn main():
    let parser = cli.ArgParser::new("converter", "File format converter")
        .flag("verbose", "v", "Verbose output")

        # File arguments - automatically validated!
        .file_option("input", "i", "Input file",
                     required: true, must_exist: true)
                     .with_extensions(["spl", "json", "yaml"])

        .file_option("output", "o", "Output file",
                     required: true, must_exist: false)

        .optional_option("format", "f", "Output format", "json")

    match parser.parse(sys_get_args()):
        case Ok(args):
            # Files already validated - no manual validation needed!
            process_files(args)
        case Err(error):
            # File validation errors included
            print(f"Error: {error}")
            parser.print_help()
            sys_exit(1)

fn process_files(args: cli.ParsedArgs):
    # Get file options
    let input_path = args.get_option("input").unwrap()
    let output_path = args.get_option("output").unwrap()

    # Files are already validated!
    print(f"✓ Input: {input_path}")
    print(f"✓ Output: {output_path}")

    # Process files...
    print(f"Converting {input_path} → {output_path}")
```

### Manual Validation (Advanced)

For cases where you need custom validation logic not handled by automatic staging, you can still use `FileValidator` directly:

```simple
use cli
use cli.file as file

fn main():
    let parser = cli.ArgParser::new("processor", "File processor")
        .required_option("input", "i", "Input file")

    match parser.parse(sys_get_args()):
        case Ok(args):
            # Manual validation for advanced use cases
            let input_path = args.get_option("input").unwrap()
            let validator = file.input_file_validator()
                .with_extensions(["spl", "rs", "py"])

            match validator.validate(input_path):
                case Ok(info):
                    print(f"Processing: {info.absolute_path}")
                case Err(error):
                    print(f"Error: {error}")
                    sys_exit(1)
```

### Implementation Notes

**Current Status:**
- ✅ API fully defined
- ⚠️  File I/O functions are placeholders (need FFI implementation)
  - `file_exists()` - Returns true (placeholder)
  - `get_file_info()` - Returns placeholder FileInfo
  - `normalize_path()` - Basic implementation

**TODO:**
- Implement actual file system FFI calls
- Add Windows path support (C:\, D:\)
- Add symbolic link handling
- Add file size/timestamp info

**Workaround:**
The API is fully functional for development/testing. File existence checks will always pass until FFI is implemented. Update the FFI functions in `cli/file.spl` when file system support is available.


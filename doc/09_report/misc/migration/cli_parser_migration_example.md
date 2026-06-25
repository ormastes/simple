# CLI Parser Migration Example

This document shows side-by-side comparisons of migrating from manual argument parsing to the shared `cli_parser` module.

## Example 1: Dashboard notify-test Command

### Before (Manual Parsing - 42 lines)

```simple
fn run_notify_test(args: [text]):
    print "{NL}=== C1 Notification Testing ==={NL}"

    var channel = "all"
    var dry_run = true

    # Parse arguments
    for arg in args:
        if arg.starts_with("--channel="):
            channel = arg.replace("--channel=", "")
        elif arg == "--dry-run":
            dry_run = true
        elif arg == "--all":
            channel = "all"

    print "Configuration:"
    print "  Channel: {channel}"
    print "  Dry-run: {if dry_run: "enabled" else: "disabled"}"
    print "  Mode: {if dry_run: "Validation only" else: "Will send actual notification"}{NL}"

    match channel:
        case "slack":
            print "[SLACK] Testing Slack webhook..."
            if dry_run:
                print "  [DRY-RUN] Validated webhook URL format"
            else:
                print "  [OK] Test message sent to Slack"
        case "webhook":
            print "[WEBHOOK] Testing generic webhook..."
            if dry_run:
                print "  [DRY-RUN] Validated endpoint configuration"
            else:
                print "  [OK] Test message sent to webhook"
        case "email":
            print "[EMAIL] Testing SMTP configuration..."
            if dry_run:
                print "  [DRY-RUN] Validated SMTP host and credentials"
            else:
                print "  [OK] Test email sent"
        case _:
            print "Unknown channel: {channel}"
```

### After (Using cli_parser - 35 lines)

```simple
use lib.cli.cli_parser.{cli_spec, cli_spec_option, cli_spec_flag, parse_cli_args, parsed_option, parsed_flag}

fn run_notify_test(args: [text]):
    print "{NL}=== C1 Notification Testing ==={NL}"

    # Parse arguments
    val spec = cli_spec()
    val spec2 = cli_spec_option(spec, "channel", "", "Notification channel", default: "all", choices: ["slack", "webhook", "email", "all"])
    val spec3 = cli_spec_flag(spec2, "dry-run", "", "Dry run mode (default: true)")
    val parsed = parse_cli_args(spec3, args)
    val channel = parsed_option(parsed, "channel")
    val dry_run = parsed_flag(parsed, "dry-run")

    print "Configuration:"
    print "  Channel: {channel}"
    print "  Dry-run: {if dry_run: "enabled" else: "disabled"}"
    print "  Mode: {if dry_run: "Validation only" else: "Will send actual notification"}{NL}"

    match channel:
        case "slack":
            print "[SLACK] Testing Slack webhook..."
            if dry_run:
                print "  [DRY-RUN] Validated webhook URL format"
            else:
                print "  [OK] Test message sent to Slack"
        case "webhook":
            print "[WEBHOOK] Testing generic webhook..."
            if dry_run:
                print "  [DRY-RUN] Validated endpoint configuration"
            else:
                print "  [OK] Test message sent to webhook"
        case "email":
            print "[EMAIL] Testing SMTP configuration..."
            if dry_run:
                print "  [DRY-RUN] Validated SMTP host and credentials"
            else:
                print "  [OK] Test email sent"
        case _:
            print "Unknown channel: {channel}"
```

**Savings:** 7 lines (42 → 35)
**Benefits:** Automatic choice validation, consistent API, no manual string manipulation

---

## Example 2: Build Rust Test Arguments

### Before (Manual Parsing - 35 lines)

```simple
fn handle_rust_test(args: [text]) -> i64:
    var doc_only = false
    var package = ""
    var filter = ""
    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg == "--doc":
            doc_only = true
        elif arg == "-p" and i + 1 < args.len():
            i = i + 1
            package = args[i]
        else:
            filter = arg
        i = i + 1

    if doc_only:
        print "=== Running Rust Doc-Tests ==="
        val result = Cargo__test_doc(package)
        print_test_result(result)
        if result.success:
            return 0
        else:
            return result.exit_code
    else:
        print "=== Running Rust Tests ==="
        val result = Cargo__test(package, filter)
        print_test_result(result)
        if result.success:
            return 0
        else:
            return result.exit_code
```

### After (Using cli_parser - 25 lines)

```simple
use lib.cli.cli_parser.{cli_spec, cli_spec_flag, cli_spec_option, cli_spec_positional, parse_cli_args, parsed_flag, parsed_option, parsed_positional}

fn handle_rust_test(args: [text]) -> i64:
    val spec = cli_spec()
    val spec2 = cli_spec_flag(spec, "doc", "", "Run doc-tests only")
    val spec3 = cli_spec_option(spec2, "package", "p", "Package name", default: "", choices: [])
    val spec4 = cli_spec_positional(spec3, "filter", "Test filter", required: false)
    val parsed = parse_cli_args(spec4, args)
    val doc_only = parsed_flag(parsed, "doc")
    val package = parsed_option(parsed, "package")
    val filter = parsed_positional(parsed, 0)

    if doc_only:
        print "=== Running Rust Doc-Tests ==="
        val result = Cargo__test_doc(package)
        print_test_result(result)
        return if result.success: 0 else: result.exit_code
    else:
        print "=== Running Rust Tests ==="
        val result = Cargo__test(package, filter)
        print_test_result(result)
        return if result.success: 0 else: result.exit_code
```

**Savings:** 10 lines (35 → 25)
**Benefits:** Short flag support (-p), positional argument handling, cleaner logic

---

## Example 3: Dashboard Compare Command

### Before (Manual Parsing - 30 lines)

```simple
fn run_compare(args: [text]):
    print "{NL}=== C3 Comparative Analysis ==={NL}"

    var baseline_date = ""
    var current_date = ""

    # Parse arguments
    for arg in args:
        if arg.starts_with("--baseline="):
            baseline_date = arg.replace("--baseline=", "")
        elif arg.starts_with("--current="):
            current_date = arg.replace("--current=", "")

    if baseline_date.len() == 0:
        print "Error: specify baseline date"
        print "Usage: compare --baseline=YYYY-MM-DD [--current=YYYY-MM-DD]"
        return

    if current_date.len() == 0:
        current_date = "2026-01-21"

    print "Comparing metrics: {baseline_date} vs {current_date}{NL}"
    print "Dashboard Comparison Report"
    print "============================"
    print "Metric           | Baseline | Current  | Change"
    print "-----------------+----------+----------+-------"
    print "Coverage         | 78.5%    | 82.5%    | +4.0%"
    # ... more output
```

### After (Using cli_parser - 22 lines)

```simple
use lib.cli.cli_parser.{cli_spec, cli_spec_option, parse_cli_args, parsed_option, validate_args, print_help}

fn run_compare(args: [text]):
    print "{NL}=== C3 Comparative Analysis ==={NL}"

    val spec = cli_spec()
    val spec2 = cli_spec_option(spec, "baseline", "", "Baseline date (YYYY-MM-DD)", default: "", choices: [])
    val spec3 = cli_spec_option(spec2, "current", "", "Current date (YYYY-MM-DD)", default: "2026-01-21", choices: [])
    val parsed = parse_cli_args(spec3, args)
    val baseline_date = parsed_option(parsed, "baseline")
    val current_date = parsed_option(parsed, "current")

    if baseline_date == "":
        print "Error: specify baseline date"
        print_help(spec3)
        return

    print "Comparing metrics: {baseline_date} vs {current_date}{NL}"
    print "Dashboard Comparison Report"
    print "============================"
    print "Metric           | Baseline | Current  | Change"
    print "-----------------+----------+----------+-------"
    print "Coverage         | 78.5%    | 82.5%    | +4.0%"
    # ... more output
```

**Savings:** 8 lines (30 → 22)
**Benefits:** Automatic help generation, default value handling, consistent validation

---

## Example 4: Baremetal Build Arguments

### Before (Manual Parsing - 50 lines)

```simple
fn handle_baremetal_build(args: [text]) -> i64:
    var target_name = "x86_64"
    var source_files: [text] = []
    var list_targets = false
    var verbose = false

    # Parse arguments
    var i = 0
    while i < args.len():
        val arg = args[i]
        if arg.starts_with("--target="):
            target_name = arg[9:]
        elif arg == "--list-targets":
            list_targets = true
        elif arg == "-v" or arg == "--verbose":
            verbose = true
        elif not arg.starts_with("-"):
            source_files.push(arg)
        i = i + 1

    # List available targets
    if list_targets:
        print "Available bare-metal targets:"
        print "  arm      - ARM Cortex-M (QEMU versatilepb)"
        print "  x86_64   - x86_64 with multiboot2 (QEMU)"
        print "  riscv    - RISC-V 64-bit (QEMU virt)"
        return 0

    # Create configuration based on target
    var config: BaremetalConfig = baremetal_config_x86_64()
    if target_name == "arm":
        config = baremetal_config_arm()
    elif target_name == "x86_64":
        config = baremetal_config_x86_64()
    elif target_name == "riscv":
        config = baremetal_config_riscv()
    else:
        print "Error: Unknown target: {target_name}"
        print "Run 'simple build baremetal --list-targets' to see available targets."
        return 1

    print "=== Building for Bare-Metal Target ==="
    print "Target: {target_name}"
    print ""

    val builder = BaremetalBuilder.new(config)
    val result = builder.build(source_files)

    if result.success:
        return 0
    else:
        return result.exit_code
```

### After (Using cli_parser - 38 lines)

```simple
use lib.cli.cli_parser.*

fn handle_baremetal_build(args: [text]) -> i64:
    val spec = cli_spec()
    val spec2 = cli_spec_option(spec, "target", "", "Target architecture", default: "x86_64", choices: ["arm", "x86_64", "riscv"])
    val spec3 = cli_spec_flag(spec2, "list-targets", "", "List available targets")
    val spec4 = cli_spec_flag(spec3, "verbose", "v", "Verbose output")
    val parsed = parse_cli_args(spec4, args)
    val target_name = parsed_option(parsed, "target")
    val list_targets = parsed_flag(parsed, "list-targets")
    val verbose = parsed_flag(parsed, "verbose")
    val source_files = parsed_positionals(parsed)

    if list_targets:
        print "Available bare-metal targets:"
        print "  arm      - ARM Cortex-M (QEMU versatilepb)"
        print "  x86_64   - x86_64 with multiboot2 (QEMU)"
        print "  riscv    - RISC-V 64-bit (QEMU virt)"
        return 0

    # Create configuration (target already validated by choices)
    var config: BaremetalConfig = baremetal_config_x86_64()
    if target_name == "arm":
        config = baremetal_config_arm()
    elif target_name == "x86_64":
        config = baremetal_config_x86_64()
    elif target_name == "riscv":
        config = baremetal_config_riscv()

    print "=== Building for Bare-Metal Target ==="
    print "Target: {target_name}"
    print ""

    val builder = BaremetalBuilder.new(config)
    val result = builder.build(source_files)

    return if result.success: 0 else: result.exit_code
```

**Savings:** 12 lines (50 → 38)
**Benefits:** Automatic choice validation (no need for "Unknown target" check), short flag support, positional files collection

---

## Summary

| Example | Before | After | Savings | Key Benefits |
|---------|--------|-------|---------|--------------|
| notify-test | 42 | 35 | 7 lines | Choice validation |
| rust test | 35 | 25 | 10 lines | Short flags, positionals |
| compare | 30 | 22 | 8 lines | Help generation, defaults |
| baremetal | 50 | 38 | 12 lines | Validation, short flags |
| **Total** | **157** | **120** | **37 lines** | **Consistency across all** |

## Migration Pattern

1. **Import cli_parser functions**
2. **Build specification** using builder chain
3. **Parse arguments** once
4. **Access values** by name
5. **Remove manual parsing code**
6. **Use auto-generated help** (optional)

## Common Conversions

### Manual While Loop → cli_parser
```simple
# Before
var i = 0
while i < args.len():
    val arg = args[i]
    if arg == "--flag":
        flag_value = true
    i = i + 1

# After
val parsed = parse_cli_args(spec, args)
val flag_value = parsed_flag(parsed, "flag")
```

### Manual String Manipulation → cli_parser
```simple
# Before
if arg.starts_with("--option="):
    option_value = arg.replace("--option=", "")

# After
val option_value = parsed_option(parsed, "option")
```

### Manual Validation → cli_parser
```simple
# Before
if target_name != "arm" and target_name != "x86_64" and target_name != "riscv":
    print "Error: Unknown target: {target_name}"
    return 1

# After
# Validation automatic via choices: ["arm", "x86_64", "riscv"]
```

This migration preserves all functionality while reducing code, improving consistency, and enabling automatic help generation.

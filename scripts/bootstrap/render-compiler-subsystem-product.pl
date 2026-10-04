#!/usr/bin/env perl
# Render one namespaced native product from canonical parser source intervals.
# The input span ledger is produced by the admitted Stage 2 compiled generator.
use strict;
use warnings;
use bytes;
use Digest::SHA qw(sha256_hex);
use File::Basename qw(dirname basename);
use File::Find qw(find);
use File::Path qw(make_path);

@ARGV == 7 or die "usage: $0 SOURCE_ROOT INVENTORY SPANS MAIN_VERDICTS GENERATED_ROOT SUBSYSTEM BACKEND\n";
my ($source_root, $inventory_path, $spans_path, $main_verdicts_path, $generated_root, $subsystem, $backend) = @ARGV;
$subsystem =~ /\A(?:compiler|interpreter|loader)\z/ or die "invalid subsystem\n";
$backend =~ /\A(?:llvm|cranelift)\z/ or die "invalid backend\n";
-d $source_root && !-l $source_root or die "invalid physical source root\n";
-d $generated_root && !-l $generated_root or die "generated root must be an isolated source directory\n";
!-e "$generated_root/product" && !-e "$generated_root/generated-manifest.tsv"
    or die "generated product already exists\n";

sub bytes_of {
    my ($path) = @_;
    open my $fh, '<:raw', $path or die "cannot read $path: $!\n";
    local $/;
    my $bytes = <$fh>;
    close $fh or die "cannot close $path: $!\n";
    return $bytes;
}

sub safe_relative {
    my ($path) = @_;
    return $path =~ m{\A(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\z}
        && $path !~ m{(?:\A|/)\.\.(?:/|\z)}
        && $path !~ m{(?:\A|/)\.(?:/|\z)};
}

sub literal {
    my ($value) = @_;
    $value =~ /["\\\r\n\t]/ and die "unrepresentable generated Simple literal\n";
    return '"' . $value . '"';
}

sub put {
    my ($relative, $bytes) = @_;
    safe_relative($relative) or die "unsafe generated path: $relative\n";
    my $path = "$generated_root/$relative";
    make_path(dirname($path));
    open my $fh, '>:raw', $path or die "cannot write $path: $!\n";
    print {$fh} $bytes or die "cannot write $path: $!\n";
    close $fh or die "cannot close $path: $!\n";
}

my $inventory_bytes = bytes_of($inventory_path);
my @inventory_lines = split /\n/, $inventory_bytes;
shift(@inventory_lines) eq "subsystem\tlevel\tpath\tsha256"
    or die "invalid inventory header\n";
my @owners;
my %source_sha;
my $subset_bytes = "subsystem\tlevel\tpath\tsha256\n";
for my $line (@inventory_lines) {
    next if $line eq '';
    my @f = split /\t/, $line, -1;
    @f == 4 && safe_relative($f[2]) && $f[2] =~ m{\Atest/}
        && $f[3] =~ /\A[0-9a-f]{64}\z/ or die "invalid inventory row\n";
    next unless $f[0] eq $subsystem;
    !exists $source_sha{$f[2]} or die "duplicate inventory owner: $f[2]\n";
    push @owners, $f[2];
    $source_sha{$f[2]} = $f[3];
    $subset_bytes .= "$line\n";
}
@owners or die "empty subsystem inventory\n";
my $whole_sha = sha256_hex($inventory_bytes);
my $subset_sha = sha256_hex($subset_bytes);

my $spans_bytes = bytes_of($spans_path);
my @span_lines = split /\n/, $spans_bytes;
shift(@span_lines) eq "simple-subsystem-source-spans-v1\t$subsystem\t$whole_sha"
    or die "span ledger authority mismatch\n";
my $trailer = pop @span_lines;
$trailer eq 'complete' . "\t" . scalar(@owners) or die "incomplete span ledger\n";
my %decls;
my %decl_count;
my @span_owner_order;
for my $line (@span_lines) {
    next if $line eq '';
    my @f = split /\t/, $line, -1;
    if ($f[0] eq 'owner') {
        @f == 4 && exists($source_sha{$f[1]}) && $f[2] eq $source_sha{$f[1]}
            && $f[3] =~ /\A[0-9]+\z/ or die "invalid span owner\n";
        !exists $decl_count{$f[1]} or die "duplicate span owner\n";
        $decl_count{$f[1]} = int($f[3]);
        push @span_owner_order, $f[1];
    } elsif ($f[0] eq 'decl') {
        @f == 7 && exists($decl_count{$f[1]})
            && $f[2] =~ /\A[0-9]+\z/ && $f[3] =~ /\A[0-9]+\z/
            && $f[5] =~ /\A[0-9]+\z/ && $f[6] =~ /\A[0-9]+\z/
            or die "invalid span declaration\n";
        push @{$decls{$f[1]}}, [int($f[2]), int($f[3]), $f[4], int($f[5]), int($f[6])];
    } else {
        die "unknown span row\n";
    }
}
join("\n", @span_owner_order) eq join("\n", @owners)
    or die "span owners differ from inventory order\n";

my %main_verdict;
if ($main_verdicts_path ne '-') {
    my $adapter_bytes = bytes_of($main_verdicts_path);
    my @adapter_lines = split /\n/, $adapter_bytes;
    shift(@adapter_lines) eq "owner-main-verdict-v1\t$whole_sha\t" . sha256_hex($spans_bytes)
        or die "main verdict authority mismatch\n";
    my $adapter_trailer = pop @adapter_lines;
    $adapter_trailer =~ /\Acomplete\t[0-9]+\z/ or die "incomplete main verdict manifest\n";
    for my $line (@adapter_lines) {
        next if $line eq '';
        my @f = split /\t/, $line, -1;
        @f >= 7 && $f[0] eq 'owner' && exists($source_sha{$f[1]})
            && $f[2] eq $source_sha{$f[1]} && $f[3] =~ /\A[0-9]+\z/
            or die "invalid main verdict row\n";
        !exists $main_verdict{$f[1]} or die "duplicate main verdict owner\n";
        $main_verdict{$f[1]} = \@f;
    }
}

my @imports;
my @calls;
my @generated_files;
for my $owner (@owners) {
    my $source = bytes_of("$source_root/$owner");
    sha256_hex($source) eq $source_sha{$owner} or die "source changed: $owner\n";
    my $ds = $decls{$owner} // [];
    @$ds == $decl_count{$owner} or die "declaration count changed: $owner\n";
    my $hash = substr(sha256_hex($owner), 0, 20);
    my $pkg = "owner_$hash";
    my $register = "register_$hash";
    my $relative = "product/$pkg/register.spl";
    my (@top, @body);
    my $previous = 0;
    my $main_ordinal = -1;
    my $needs_fixtures = 0;
    for my $d (@$ds) {
        my ($ordinal, $tag, $name, $start, $end) = @$d;
        $ordinal == @top + @body or die "nonsequential declaration: $owner\n";
        $start >= $previous && $end > $start && $end <= length($source)
            or die "overlapping or invalid source interval: $owner\n";
        my $gap = substr($source, $previous, $start - $previous);
        # Comments and whitespace are nonexecuting; a decorator outside the
        # parser span must be handled by the parser instead of silently lost.
        $gap =~ s/^[ \t]*(?:\#[^\n]*)?\n//mg;
        $gap =~ /\S/ and die "unowned source between declarations: $owner\n";
        my $authored = substr($source, $start, $end - $start);
        if ($tag == 6 && $authored =~ /\b(?:use|import)\s+\./) {
            $authored =~ /\b(?:use|import)\s+\.fixtures\b/
                or die "unsupported relative import route: $owner\n";
            $needs_fixtures = 1;
        }
        if ($name =~ /\A_(?:expr|if|for|while|ct|ct_blk)_/) {
            push @body, $authored;
        } else {
            push @top, $authored;
        }
        $main_ordinal = $ordinal if $tag == 1 && $name eq 'main';
        $previous = $end;
    }
    my $tail = substr($source, $previous);
    $tail =~ s/^[ \t]*(?:\#[^\n]*)?\n//mg;
    $tail =~ /\S/ and die "unowned source after declarations: $owner\n";
    if ($main_ordinal >= 0) {
        my $adapter = $main_verdict{$owner}
            or die "main verdict missing: $owner\n";
        $adapter->[3] == $main_ordinal or die "main verdict ordinal mismatch: $owner\n";
        if ($adapter->[4] eq 'exit-zero') {
            push @body, 'it "authored main exits zero":' . "\n" . '    expect(main()).to_equal(0)' . "\n";
        } elsif ($adapter->[4] eq 'aggregate-registry-declare' &&
                 $adapter->[5] eq 'std.spec.registry-v1') {
            # This adapter is allowed only for reviewed main bodies made from
            # describe declarations. The runtime suppresses test/hook callbacks
            # during enumeration and preserves immediate execution in run mode.
            push @body, 'main()';
        } else {
            die "unsupported authored main verdict: $owner ($adapter->[4])\n";
        }
    } elsif (exists $main_verdict{$owner}) {
        die "adapter invents authored main: $owner\n";
    }
    my $wrapped = "# generated from " . $owner . " sha256 " . $source_sha{$owner} . "\n";
    $wrapped .= "use std.spec.*\n";
    $wrapped .= join("\n", @top) . "\n" if @top;
    $wrapped .= "pub fn $register():\n";
    if (@body) {
        for my $statement (@body) {
            $statement =~ s/^/    /mg;
            $wrapped .= $statement . "\n";
        }
    } else {
        $wrapped .= "    pass\n";
    }
    put($relative, $wrapped);
    push @generated_files, $relative;
    push @imports, "use app.product.$pkg.register.{$register}";
    push @calls, [$owner, $source_sha{$owner}, $register];

    # The current authoritative inventory has only `.fixtures` relative
    # imports. Preserve their sibling package beneath this owner's unique
    # namespace; any different relative route must be implemented explicitly.
    if ($needs_fixtures) {
        my $fixture_dir = dirname("$source_root/$owner") . '/fixtures';
        -d $fixture_dir && !-l $fixture_dir or die "missing physical fixture directory: $owner\n";
        find({no_chdir => 1, wanted => sub {
            my $path = $File::Find::name;
            -l $path and die "linked relative fixture: $path\n";
            return if -d $path;
            return unless $path =~ /\.spl\z/;
            my $suffix = substr($path, length($fixture_dir) + 1);
            safe_relative($suffix) or die "unsafe relative fixture path\n";
            my $fixture_relative = "product/$pkg/fixtures/$suffix";
            put($fixture_relative, bytes_of($path));
            push @generated_files, $fixture_relative;
        }}, $fixture_dir);
    }
}

my $entry = "use std.sffi.cli_args.{cli_get_args}\n" .
            "use std.io_runtime.{env_set}\n" .
            "use std.spec.{aggregate_registry_begin, aggregate_owner_begin, aggregate_owner_end, aggregate_registry_finish}\n" .
            join("\n", @imports) . "\n\n" .
            "fn main() -> i64:\n" .
            "    var mode = \"\"\n    var ledger = \"\"\n" .
            "    for arg in cli_get_args():\n" .
            "        if arg == \"--enumerate\": mode = \"enumerate\"\n" .
            "        elif arg == \"--run\": mode = \"run\"\n" .
            "        elif arg.starts_with(\"--registry-output=\"): ledger = arg[18:]\n" .
            "    if mode == \"\" or ledger == \"\": return 2\n" .
            "    env_set(\"SIMPLE_RUNTIME_MODE\", \"native\")\n" .
            "    if not aggregate_registry_begin(mode, " . literal($backend) .
            ", " . literal($subsystem) . ", " . literal($whole_sha) . ", " . literal($subset_sha) . ", ledger): return 2\n";
for my $call (@calls) {
    my ($owner, $sha, $register) = @$call;
    $entry .= "    if not aggregate_owner_begin(" . literal($owner) . ", " . literal($sha) . "): return 2\n";
    $entry .= "    $register()\n";
    $entry .= "    if not aggregate_owner_end(): return 2\n";
}
$entry .= "    aggregate_registry_finish()\n";
put('product/main.spl', $entry);
push @generated_files, 'product/main.spl';

my %seen;
my $manifest = "path\tsha256\n";
for my $relative (sort @generated_files) {
    !$seen{$relative}++ or die "duplicate generated file: $relative\n";
    $manifest .= "$relative\t" . sha256_hex(bytes_of("$generated_root/$relative")) . "\n";
}
put('generated-manifest.tsv', $manifest);
print "generated_tree_sha256=" . sha256_hex($manifest) . "\n";
print "generated_owner_count=" . scalar(@owners) . "\n";
print "subset_sha256=$subset_sha\n";

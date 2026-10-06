#!/usr/bin/env perl
# Checks generated membership in an actual compiler-published SCV snapshot.
# This is additional evidence, not a replacement for compiler source admission.
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
@ARGV == 4 or die "expected overlay generated-root generated-manifest output\n";
my ($overlay, $generated, $manifest, $output) = @ARGV;
sub bytes {
    my ($path) = @_;
    -f $path && !-l $path && -s $path <= 32 * 1024 * 1024 or die "metadata unavailable or too large: $path\n";
    open my $f, '<:raw', $path or die $!;
    local $/; return <$f>;
}
sub digest {
    my ($path) = @_;
    -f $path && !-l $path or die "snapshot member unavailable: $path\n";
    open my $f, '<:raw', $path or die $!;
    my $sha = Digest::SHA->new(256); $sha->addfile($f); return $sha->hexdigest;
}
sub relative {
    my ($path) = @_;
    $path !~ m{(?:\A/|\\|:|[\t\r\n\0]|(?:\A|/)\.{1,2}(?:/|\z))} && length($path)
        or die "unsafe relative member\n";
    return $path;
}
my @expected_rows = split /\n/, bytes($manifest);
shift(@expected_rows) eq "path\tsha256" or die "generated manifest schema differs\n";
my %expected;
for my $row (@expected_rows) {
    my @parts = split /\t/, $row, -1;
    @parts == 2 && $parts[1] =~ /\A[0-9a-f]{64}\z/ or die "invalid generated manifest row\n";
    my ($path, $sha) = @parts; relative($path);
    !exists $expected{$path} or die "duplicate generated member\n";
    digest("$generated/$path") eq $sha or die "rendered source changed\n";
    $expected{$path} = $sha;
}
keys(%expected) && exists $expected{'product/main.spl'} or die "nonempty generated product entry required\n";
my @matches;
my $snapshots = "$overlay/build/scv/snapshots";
opendir my $directories, $snapshots or die "SCV snapshot namespace unavailable\n";
my @directories = grep { $_ ne '.' && $_ ne '..' } readdir($directories);
closedir $directories;
for my $directory (@directories) {
    my $snapshot = "$snapshots/$directory/SCV_COMPILE_SNAPSHOT";
    next unless -f $snapshot;
    my $raw = bytes($snapshot); my @lines = split /\n/, $raw, -1;
    @lines == 6 or die "SCV provenance field count differs\n";
    shift(@lines) eq 'simple-scv-compile-snapshot-v1' or die "SCV manifest schema differs\n";
    my %fields;
    for my $line (@lines) {
        my ($key, $value) = split /=/, $line, 2;
        defined($value) && !exists $fields{$key} or die "malformed SCV manifest\n";
        $fields{$key} = $value;
    }
    ($fields{revision} // '') =~ /\Ascv-revision-v1-[0-9a-f]{64}\z/ &&
        ($fields{inventory} // '') =~ /\A[0-9a-f]{64}\z/ &&
        ($fields{count} // '') =~ /\A[1-9][0-9]*\z/ or die "invalid SCV identity\n";
    my $tree = "scv-tree-v1-$fields{inventory}";
    my $revision = 'scv-revision-v1-' . sha256_hex("simple/scv-compile-revision/v1|$tree|$fields{inventory}");
    my $commit = 'scv-compile-v1-' . sha256_hex("simple/scv-compile-commit/v1|$tree|$fields{count}");
    my $provenance = join("\n", 'simple-scv-compile-snapshot-v1',
        "revision=$revision", "commit=$commit", "tree=$tree",
        "inventory=$fields{inventory}", "count=$fields{count}");
    $raw eq $provenance && $directory eq $revision or die "SCV content identity differs\n";
    my $receipt = "$overlay/build/scv/receipts/$fields{revision}.receipt";
    bytes($receipt) eq "$raw\nsnapshot=snapshots/$revision"
        or die "SCV snapshot has no completed receipt\n";
    (my $root = $snapshot) =~ s{/SCV_COMPILE_SNAPSHOT\z}{};
    my $inventory = bytes("$root/SCV_COMPILE_INVENTORY");
    sha256_hex($inventory) eq $fields{inventory} or die "SCV inventory hash differs\n";
    my %members;
    for my $row (split /\n/, $inventory) {
        my @parts = split /\|/, $row, -1;
        @parts == 3 && $parts[1] =~ /\Asha256_[0-9a-f]{64}\z/ && $parts[2] =~ /\A[0-9]+\z/
            or die "invalid SCV inventory row\n";
        relative($parts[0]); !exists $members{$parts[0]} or die "duplicate SCV member\n";
        $members{$parts[0]} = [$parts[1], $parts[2]];
    }
    scalar(keys %members) == $fields{count} or die "SCV inventory count differs\n";
    my $complete = 1;
    for my $path (keys %expected) {
        my $key = "src/app/$path";
        if (!exists $members{$key}) { $complete = 0; last; }
        $members{$key}[0] eq "sha256_$expected{$path}" &&
            -s "$root/$key" == $members{$key}[1] && digest("$root/$key") eq $expected{$path}
            or die "generated SCV payload differs\n";
    }
    push @matches, [$snapshot, $receipt] if $complete;
}
@matches == 1 or die "expected exactly one completed generated-product snapshot\n";
my $out;
if ($output eq '-') {
    open $out, '>&', \*STDOUT or die $!;
    binmode $out;
} else {
    !-e $output or die "fresh proof output required\n";
    open $out, '>:raw', $output or die $!;
}
print {$out} "schema=simple-product-generated-snapshot-v1\nstatus=generated-membership-verified\n";
print {$out} "generated_manifest_path=$manifest\ngenerated_manifest_sha256=" . digest($manifest) . "\n";
print {$out} "generated_files=" . scalar(keys %expected) . "\n";
print {$out} "snapshot_manifest_path=$matches[0][0]\nsnapshot_manifest_sha256=" . digest($matches[0][0]) . "\n";
print {$out} "snapshot_receipt_path=$matches[0][1]\nsnapshot_receipt_sha256=" . digest($matches[0][1]) . "\n";
close $out or die $!;

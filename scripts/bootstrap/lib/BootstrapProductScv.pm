package BootstrapProductScv;
use strict;
use warnings;
use Exporter 'import';
use Digest::SHA qw(sha256_hex);
our @EXPORT_OK = qw(verified_product_scv_members);

sub bytes {
    my ($path) = @_;
    -f $path && !-l $path && -s $path <= 32 * 1024 * 1024 or die "SCV metadata unavailable\n";
    open my $file, '<:raw', $path or die $!;
    local $/; return <$file>;
}
sub verified_product_scv_members {
    my ($overlay) = @_;
    my $base = "$overlay/build/scv";
    for my $dir ("$overlay/build", $base, "$base/snapshots", "$base/receipts") {
        -d $dir && !-l $dir or die "SCV directory missing or linked\n";
    }
    opendir my $handle, "$base/snapshots" or die $!;
    my @revisions = grep { $_ ne '.' && $_ ne '..' } readdir($handle);
    closedir $handle;
    @revisions or die "empty SCV snapshot namespace\n";
    my (%allowed, %chunk_sizes);
    for my $revision (@revisions) {
        $revision =~ /\Ascv-revision-v1-[0-9a-f]{64}\z/ or die "invalid SCV snapshot directory\n";
        my $relative = "build/scv/snapshots/$revision";
        my $root = "$overlay/$relative";
        -d $root && !-l $root or die "linked SCV snapshot\n";
        my $raw = bytes("$root/SCV_COMPILE_SNAPSHOT");
        my @lines = split /\n/, $raw, -1;
        @lines == 6 && shift(@lines) eq 'simple-scv-compile-snapshot-v1' or die "SCV provenance schema differs\n";
        my %fields;
        for my $line (@lines) {
            my ($key, $value) = split /=/, $line, 2;
            defined($value) && !exists($fields{$key}) or die "malformed SCV provenance\n";
            $fields{$key} = $value;
        }
        ($fields{inventory} // '') =~ /\A[0-9a-f]{64}\z/ &&
            ($fields{count} // '') =~ /\A[1-9][0-9]*\z/ or die "invalid SCV inventory identity\n";
        my $tree = "scv-tree-v1-$fields{inventory}";
        my $expected_revision = 'scv-revision-v1-' . sha256_hex("simple/scv-compile-revision/v1|$tree|$fields{inventory}");
        my $commit = 'scv-compile-v1-' . sha256_hex("simple/scv-compile-commit/v1|$tree|$fields{count}");
        $revision eq $expected_revision && $raw eq join("\n", 'simple-scv-compile-snapshot-v1',
            "revision=$revision", "commit=$commit", "tree=$tree", "inventory=$fields{inventory}", "count=$fields{count}")
            or die "SCV content identity differs\n";
        my $receipt = "build/scv/receipts/$revision.receipt";
        bytes("$overlay/$receipt") eq "$raw\nsnapshot=snapshots/$revision" or die "SCV completion receipt differs\n";
        my $inventory = bytes("$root/SCV_COMPILE_INVENTORY");
        sha256_hex($inventory) eq $fields{inventory} or die "SCV inventory digest differs\n";
        my %members;
        for my $row (split /\n/, $inventory) {
            my ($path, $sha, $size, @extra) = split /\|/, $row, -1;
            !@extra && defined($size) && $sha =~ /\Asha256_([0-9a-f]{64})\z/ && $size =~ /\A[0-9]+\z/
                or die "invalid SCV inventory member\n";
            my $expected_sha = substr($sha, 7);
            length($path) && $path !~ m{(?:\A/|\\|:|[\t\r\n\0]|(?:\A|/)\.{1,2}(?:/|\z))} &&
                !$members{$path}++ or die "unsafe or duplicate SCV member\n";
            my $physical = "$root/$path";
            -f $physical && !-l $physical && -s $physical == $size or die "SCV payload unavailable or size differs\n";
            open my $payload, '<:raw', $physical or die $!;
            my $digest = Digest::SHA->new(256); $digest->addfile($payload); close $payload or die $!;
            $digest->hexdigest eq $expected_sha or die "SCV payload digest differs\n";
            $allowed{"$relative/$path"} = 1;
            $chunk_sizes{$sha} = $size;
        }
        scalar(keys %members) == $fields{count} or die "SCV inventory count differs\n";
        $allowed{"$relative/SCV_COMPILE_SNAPSHOT"} = 1;
        $allowed{"$relative/SCV_COMPILE_INVENTORY"} = 1;
        $allowed{$receipt} = 1;
    }
    admit_auxiliary($overlay, \%allowed, \%chunk_sizes);
    return \%allowed;
}

sub names {
    my ($path) = @_;
    return () unless -e $path || -l $path;
    -d $path && !-l $path or die "SCV auxiliary directory linked or invalid\n";
    opendir my $dir, $path or die $!;
    my @names = grep { $_ ne '.' && $_ ne '..' } readdir($dir);
    closedir $dir; return @names;
}
sub source_path {
    my ($path) = @_;
    # Braces are literal filename bytes, never a shell expansion or glob.
    # Keep the restricted src/test alphabet and exact component rejection.
    $path =~ m{\A(?:src|test)/[A-Za-z0-9_./\{\}-]+\z} &&
        $path !~ m{(?:\A|/)(?:\.{1,2})?(?:/|\z)}
        or die "unsafe SCV source identity\n";
}
sub admit_auxiliary {
    my ($overlay, $allowed, $chunks) = @_;
    my $base = "$overlay/build/scv";
    for my $name (names("$base/objects/chunks")) {
        $name =~ /\A(sha256_[0-9a-f]{64})\.blob\z/ or die "invalid SCV chunk name\n";
        my $id = $1;
        exists($chunks->{$id}) or die "unbound SCV chunk\n";
        my $relative = "build/scv/objects/chunks/$name";
        my $raw = bytes("$overlay/$relative");
        length($raw) == $chunks->{$id} && sha256_hex($raw) eq substr($id, 7)
            or die "SCV chunk content differs\n";
        $allowed->{$relative} = 1;
    }
    my %generations;
    for my $name (names("$base/source-inventory/generations")) {
        $name =~ /\A([0-9a-f]{64})\.inventory\z/ or die "invalid source inventory filename\n";
        my $sha = $1;
        my $relative = "build/scv/source-inventory/generations/$name";
        my $raw = bytes("$overlay/$relative");
        sha256_hex($raw) eq $sha or die "source inventory content digest differs\n";
        my @rows = split /\n/, $raw, -1;
        shift(@rows) eq 'simple-compile-source-inventory-v1' or die "source inventory schema differs\n";
        my $generation = shift @rows;
        $generation =~ /\Ageneration=([0-9]+)\z/ or die "invalid source inventory generation\n";
        $generations{$sha} = $1;
        my $count = shift @rows;
        $count eq 'count=' . scalar(@rows) or die "source inventory count differs\n";
        my $previous = '';
        for my $row (@rows) {
            my @f = split /\|/, $row, -1;
            @f == 7 && $f[6] =~ /\A[0-9]+\z/ or die "invalid source inventory row\n";
            source_path($f[0]);
            $f[0] gt $previous or die "unordered source inventory\n";
            $previous = $f[0];
            for my $digest (@f[1..5]) { $digest =~ /\A[0-9a-f]{64}\z/ or die "invalid source inventory digest\n"; }
        }
        $allowed->{$relative} = 1;
    }
    my %memberships;
    for my $name (names("$base/compile-events/untracked")) {
        $name =~ /\A([0-9a-f]{64})\.paths\z/ or die "invalid SCV membership filename\n";
        my $sha = $1;
        my $relative = "build/scv/compile-events/untracked/$name";
        my $raw = bytes("$overlay/$relative");
        sha256_hex($raw) eq $sha or die "SCV membership digest differs\n";
        my @rows = split /\n/, $raw, -1;
        shift(@rows) eq 'simple-compile-untracked-membership-v1' or die "SCV membership schema differs\n";
        shift(@rows) eq 'count=' . scalar(@rows) or die "SCV membership count differs\n";
        my %seen;
        for my $path (@rows) {
            source_path($path);
            !$seen{$path}++ && -f "$overlay/$path" && !-l "$overlay/$path"
                or die "duplicate or unavailable SCV membership\n";
        }
        $memberships{$sha} = 1;
        $allowed->{$relative} = 1;
    }
    my $current = 'build/scv/source-inventory/CURRENT';
    if (-e "$overlay/$current" || -l "$overlay/$current") {
        my @rows = split /\n/, bytes("$overlay/$current"), -1;
        my $sha = shift @rows;
        exists($generations{$sha}) or die "CURRENT has no authenticated generation\n";
        if (@rows) {
            my $version = shift @rows;
            $version =~ /\Asimple-compile-event-cursor-v([123])\z/ or die "invalid SCV cursor version\n";
            my $v = $1; my %cursor;
            for my $row (@rows) {
                my ($key, $value) = split /=/, $row, 2;
                defined($value) && !exists($cursor{$key}) or die "invalid SCV cursor framing\n";
                $cursor{$key} = $value;
            }
            my @keys = qw(git_head filesystem_rows filesystem_digest inventory_digest inventory_generation);
            push @keys, qw(untracked_src_digest untracked_test_digest) if $v >= 2;
            push @keys, 'untracked_membership_digest' if $v >= 3;
            join(',', sort keys %cursor) eq join(',', sort @keys) or die "SCV cursor fields differ\n";
            $cursor{git_head} =~ /\A[0-9a-f]{40}\z/ && $cursor{filesystem_rows} =~ /\A[0-9]+\z/ &&
                $cursor{inventory_digest} eq $sha && $cursor{inventory_generation} eq $generations{$sha}
                or die "SCV cursor identity differs\n";
            for my $key (grep { /_digest\z/ } @keys) {
                $cursor{$key} =~ /\A[0-9a-f]{64}\z/ or die "invalid SCV cursor digest\n";
            }
            $v < 3 || $memberships{$cursor{untracked_membership_digest}}
                or die "SCV cursor membership unavailable\n";
        }
        $allowed->{$current} = 1;
    } elsif (keys %generations) { die "source inventory CURRENT missing\n"; }
    for my $lock (qw(build/scv/compile-events/refresh.lock build/scv/source-inventory/publication.lock)) {
        next unless -e "$overlay/$lock" || -l "$overlay/$lock";
        bytes("$overlay/$lock") eq '' or die "SCV lock contains unbound bytes\n";
        $allowed->{$lock} = 1;
    }
}
1;

package BootstrapProductOverlay;
use strict;
use warnings;
use Exporter 'import';
use File::Find qw(find);
use File::Basename qw(dirname);
use File::Path qw(make_path);
use File::Copy qw(copy);
use Digest::SHA qw(sha256_hex);
use Cwd qw(abs_path);
use Fcntl qw(O_WRONLY O_CREAT O_EXCL);
our @EXPORT_OK = qw(materialize_product_overlay verify_product_overlay verify_product_source);

# One membership policy for construction and verification. These are physical
# bootstrap inputs, not an admission receipt or an exemption from source SCV.
my @roots = qw(src/compiler src/lib src/app src/plugins src/compositions src/os
    src/package_ownership src/runtime src/generated src/hardware src/i18n src/tool
    src/tooling src/type src/unit src/verification test variants var config
    scripts/bootstrap scripts/setup examples/10_tooling/trace32_tools
    examples/05_stdlib/spipe doc/04_architecture doc/08_tracking/bug);
sub selected {
    my ($p) = @_;
    return 1 if $p !~ m{/};
    for my $r (@roots) { return 1 if $p eq $r || index($p, "$r/") == 0; }
    return 0;
}
sub relative {
    my ($p) = @_;
    length($p) && $p !~ m{\A/|(?:\A|/)\.\.?(?:/|\z)|//|[\t\r\n\0\\:]}
        or die "unsafe overlay member\n";
    return $p;
}
sub physical {
    my ($p) = @_;
    my $part = '';
    for my $c (split m{/}, $p) { next unless length $c; $part .= "/$c"; !-l $part or die "linked physical overlay input\n"; }
    -f $p or die "missing physical overlay input: $p\n";
}
sub bytes {
    my ($p) = @_; physical($p);
    open my $f, '<:raw', $p or die $!; local $/; my $b = <$f>; close $f or die $!;
    return $b;
}
sub digest {
    my ($p) = @_; physical($p);
    open my $f, '<:raw', $p or die $!;
    my $prefix = ''; read($f, $prefix, 150); seek($f, 0, 0) or die $!;
    $prefix !~ /\Aversion https:\/\/git-lfs.github.com\/spec\/v1\r?\n/
        or die "unhydrated LFS product input: $p\n";
    my $sha = Digest::SHA->new(256); $sha->addfile($f); close $f or die $!;
    return $sha->hexdigest;
}
sub git_bytes {
    my ($root, @args) = @_;
    open my $f, '-|', 'git', '-C', $root, @args or die $!; binmode $f;
    local $/; my $b = <$f>; close $f or die "overlay Git catalog failed\n";
    return $b;
}
sub catalog {
    my ($source) = @_;
    my %all;
    for my $row (split /\0/, git_bytes($source, 'ls-tree', '-rz', '--full-tree', 'HEAD')) {
        $row =~ /\A(100644|100755|120000) blob ([0-9a-f]{40,64})\t(.+)\z/s
            or next;
        my ($mode, $oid, $path) = ($1, $2, relative($3));
        next unless selected($path);
        $all{$path} = [$mode, $oid];
    }
    keys(%all) or die "empty overlay catalog\n";
    return \%all;
}
sub link_target {
    my ($source, $path, $oid) = @_;
    my $text = git_bytes($source, 'cat-file', 'blob', $oid);
    $text !~ m{\A/|[\t\r\n\0\\:]} && length($text) or die "unsafe declared overlay alias\n";
    my @parts = split m{/}, dirname($path) eq '.' ? '' : dirname($path);
    for my $c (split m{/}, $text) {
        next if $c eq '.' || $c eq '';
        if ($c eq '..') { @parts or die "overlay alias escapes source\n"; pop @parts; }
        else { push @parts, $c; }
    }
    my $target = relative(join('/', @parts));
    selected($target) or die "overlay alias target is outside selected inputs\n";
    return ($target, sha256_hex($text), $text);
}
sub plan {
    my ($source, $aliases_only) = @_;
    my $all = catalog($source); my (%out, %digests);
    my ($expansions, $aliases) = (0, 0);
    my $expand;
    $expand = sub {
        my ($dest, $origin, $seen) = @_;
        ++$expansions <= 200000 or die "overlay expansion exceeds 200000 member budget\n";
        !$seen->{$origin} or die "cyclic overlay alias\n";
        my %next = (%$seen, $origin => 1);
        if (exists $all->{$origin}) {
            my ($mode, $oid) = @{$all->{$origin}};
            if ($mode eq '120000') {
                ++$aliases <= 4096 or die "overlay alias expansion exceeds 4096 alias budget\n";
                my ($target, $link_sha, $text) = link_target($source, $origin, $oid);
                my $alias = "$source/$origin";
                -e $alias || -l $alias or die "declared source alias is absent\n";
                my $placeholder = !-l $alias && -f $alias && -s $alias == length($text) && bytes($alias) eq $text;
                if (-l $alias) {
                    defined(abs_path($alias)) && defined(abs_path("$source/$target")) &&
                        abs_path($alias) eq abs_path("$source/$target")
                        or die "declared source alias target differs\n";
                }
                $expand->($dest, $target, \%next);
                if (!$placeholder && !-l $alias) {
                    for my $row (values %out) {
                        next unless $row->[0] eq 'file' &&
                            ($row->[1] eq $dest || index($row->[1], "$dest/") == 0);
                        my $suffix = substr($row->[1], length($dest));
                        digest("$alias$suffix") eq $row->[3]
                            or die "materialized source alias bytes differ\n";
                    }
                }
                # Every declared alias is retained separately in the receipt,
                # including aliases whose target is another declared alias.
                $out{"\@$dest:$origin"} = ['alias', $dest, $origin, $link_sha];
            } else {
                !exists $out{$dest} or die "colliding overlay member\n";
                $digests{$origin} //= digest("$source/$origin");
                $out{$dest} = ['file', $dest, $origin, $digests{$origin}];
            }
        } else {
            my @members = grep { index($_, "$origin/") == 0 } sort keys %$all;
            @members or die "missing declared overlay alias target\n";
            for my $member (@members) {
                $expand->("$dest/" . substr($member, length($origin) + 1), $member, \%next);
            }
        }
    };
    for my $path (sort keys %$all) {
        next if $aliases_only && $all->{$path}[0] ne '120000';
        $expand->($path, $path, {});
    }
    return [map { $out{$_} } sort keys %out];
}
sub encoded { return "kind\tpath\torigin\tsha256\n" . join('', map { join("\t", @$_) . "\n" } @{$_[0]}); }
sub verify_product_source {
    my ($source) = @_;
    my $aliases = plan($source, 1);
    my %permitted;
    for my $row (@$aliases) {
        # No directory-wide exemption: every descendant has an exact pinned
        # origin and its actual physical bytes were checked by plan().
        $permitted{$row->[1]} = 1;
    }
    my $status = git_bytes($source, '-c', 'core.fsmonitor=false', 'status', '--porcelain=v1', '-z', '--untracked-files=all');
    for my $row (split /\0/, $status) {
        $row =~ /\A( M| D| T|\?\?) (.+)\z/s && $permitted{$2}
            or die "source checkout has non-alias changes\n";
    }
    return 1;
}
sub materialize_product_overlay {
    my ($source, $overlay, $manifest) = @_;
    -d $overlay && !-l $overlay or die "overlay checkout missing\n";
    my $plan = plan($source);
    for my $row (@$plan) {
        next unless $row->[0] eq 'file';
        my ($dest, $origin, $sha) = @$row[1,2,3];
        !-e "$overlay/$dest" && !-l "$overlay/$dest" or die "overlay member already exists\n";
        make_path(dirname("$overlay/$dest"));
        copy("$source/$origin", "$overlay/$dest") or die "overlay copy failed: $!\n";
        digest("$overlay/$dest") eq $sha or die "overlay copy changed input bytes\n";
    }
    sysopen my $f, $manifest, O_WRONLY | O_CREAT | O_EXCL or die "overlay manifest already exists\n";
    binmode $f; print {$f} encoded($plan) or die $!; close $f or die $!;
    verify_product_overlay($source, $overlay, $manifest);
}
sub verify_product_overlay {
    my ($source, $overlay, $manifest) = @_;
    my $plan = plan($source);
    bytes($manifest) eq encoded($plan) or die "overlay catalog/source binding differs\n";
    my %expected;
    for my $row (@$plan) {
        next unless $row->[0] eq 'file';
        digest("$overlay/$row->[1]") eq $row->[3] or die "overlay member differs\n";
        $expected{$row->[1]} = 1;
    }
    my %actual;
    find({no_chdir => 1, wanted => sub {
        my $p = $File::Find::name; return if $p eq $overlay;
        my $rel = substr($p, length($overlay) + 1);
        return if $rel eq '.git' && -f $p && !-l $p;
        -l $p and die "unlisted linked overlay member\n";
        if ($rel eq '.git' && -d $p) { $File::Find::prune = 1; return; }
        return if $rel eq 'src/app/generated-manifest.tsv' || $rel =~ m{\Asrc/app/product/};
        return unless -f $p;
        $actual{$rel} = 1;
    }}, $overlay);
    join("\n", sort keys %actual) eq join("\n", sort keys %expected)
        or die "overlay has unlisted or missing physical members\n";
    return 1;
}
1;

package BootstrapProductRoot;
use strict;
use warnings;
use Exporter 'import';
use Cwd qw(abs_path);
use File::Basename qw(dirname basename);
use File::Temp qw(tempdir);
use JSON::PP;
use Digest::SHA qw(sha256_hex);
use Fcntl qw(O_WRONLY O_CREAT O_EXCL);
our @EXPORT_OK = qw(allocate_product_root resolve_product_root mirror_product_receipt);
my $json = JSON::PP->new->canonical;

sub safe {
    my ($path, $directory) = @_;
    $path =~ m{\A/} && $path !~ m{(?:\A|/)\.\.?(/|\z)|//|[\r\n\0\\]}
        or die "unsafe product root path\n";
    my $part = '';
    for my $name (split m{/}, $path) {
        next unless length $name;
        $part .= "/$name";
        !-l $part or die "product root crosses a link\n";
    }
    ($directory ? -d $path : -f $path) or die "product root input absent\n";
    abs_path($path) eq $path or die "product root is not canonical\n";
    return $path;
}
sub sha {
    my ($path) = @_;
    safe($path, 0);
    open my $f, '<:raw', $path or die $!;
    my $s = Digest::SHA->new(256); $s->addfile($f);
    close $f or die $!;
    return $s->hexdigest;
}
sub read_record {
    my ($path) = @_;
    safe($path, 0); -s $path <= 32768 or die "product root record too large\n";
    open my $f, '<:raw', $path or die $!; local $/; my $bytes = <$f>; close $f or die $!;
    my $r = $json->decode($bytes);
    ref($r) eq 'HASH' && $json->encode($r) . "\n" eq $bytes
        or die "noncanonical product root record\n";
    return $r;
}
sub publish {
    my ($path, $value) = @_;
    sysopen my $f, $path, O_WRONLY | O_CREAT | O_EXCL
        or die "product root record exists or cannot be published\n";
    binmode $f or die $!;
    print {$f} $json->encode($value), "\n" or die $!;
    close $f or die $!;
}
sub head {
    my ($source) = @_;
    open my $p, '-|', 'git', '-C', $source, 'rev-parse', '--verify', 'HEAD' or die $!;
    my $head = <$p>; close $p or die "source HEAD unavailable\n";
    chomp $head; $head =~ /\A[0-9a-f]{40,64}\z/ or die "source HEAD invalid\n";
    return $head;
}
sub producer {
    my ($path, $receipt) = @_;
    return {path => '', digest => 'MISSING', receipt => '', receipt_digest => 'MISSING'}
        if !defined($path) || $path eq '';
    return {path => $path, digest => sha($path), receipt => $receipt, receipt_digest => sha($receipt)};
}
sub allocate_product_root {
    my ($anchor, $source, $snapshot, $inventory, $llvm, $llvm_receipt, $crane, $crane_receipt) = @_;
    safe($anchor, 1); safe($source, 1);
    $snapshot eq "$anchor/source-snapshot.txt" && $inventory eq "$anchor/source-specs.tsv"
        or die "product allocation evidence is outside its anchor\n";
    $anchor !~ m{\A\Q$source\E(?:/|\z)} && $source !~ m{\A\Q$anchor\E(?:/|\z)}
        or die "product root overlaps source\n";
    $anchor =~ m{\A(/[a-zA-Z])/} or die "short product allocation requires a Windows drive\n";
    my $drive = $1;
    my $base = "$drive/.simple-product-jobs";
    if (!-e $base) { mkdir $base or die "short product namespace unavailable\n"; }
    safe($base, 1);
    !-e "$anchor/product-root.json" or die "existing product generation must be preserved\n";
    my $root = tempdir('p-XXXXXXXX', DIR => $base, CLEANUP => 0);
    safe($root, 1);
    $root !~ m{\A\Q$source\E(?:/|\z)} && $source !~ m{\A\Q$root\E(?:/|\z)}
        or die "short product root overlaps source\n";
    length($root) <= 48 or die "product generation path is not short\n";
    my $owner = {schema => 'simple-product-generation-v1', generation => basename($root),
        anchor => $anchor, physical_root => $root, source_root => $source, source_head => head($source),
        source_snapshot => $snapshot, source_snapshot_sha256 => sha($snapshot),
        inventory => $inventory, inventory_sha256 => sha($inventory),
        llvm => producer($llvm, $llvm_receipt), cranelift => producer($crane, $crane_receipt)};
    publish("$root/product-generation.json", $owner);
    publish("$anchor/product-root.json", {schema => 'simple-product-root-reference-v1',
        physical_root => $root, owner_sha256 => sha("$root/product-generation.json")});
    return $root;
}
sub resolve_product_root {
    my ($anchor, $source, @expected) = @_;
    safe($anchor, 1); safe($source, 1);
    return $anchor unless -e "$anchor/product-root.json" || -l "$anchor/product-root.json";
    my $ref = read_record("$anchor/product-root.json");
    keys(%$ref) == 3 && $ref->{schema} eq 'simple-product-root-reference-v1'
        or die "product root reference schema differs\n";
    my $root = $ref->{physical_root};
    $anchor =~ m{\A(/[a-zA-Z])/} or die "invalid product anchor drive\n";
    my $base = "$1/.simple-product-jobs";
    $root =~ m{\A\Q$base\E/p-[a-zA-Z0-9_]+\z} && $root ne $anchor
        or die "product reference leaves short namespace\n";
    safe($root, 1);
    !-e "$root/product-root.json" && !-l "$root/product-root.json"
        or die "product root reference chaining forbidden\n";
    sha("$root/product-generation.json") eq $ref->{owner_sha256}
        or die "product generation identity changed\n";
    my $owner = read_record("$root/product-generation.json");
    $owner->{schema} eq 'simple-product-generation-v1' && $owner->{anchor} eq $anchor &&
        $owner->{physical_root} eq $root && $owner->{generation} eq basename($root) &&
        $owner->{source_root} eq $source && $owner->{source_head} eq head($source)
        or die "product generation source/owner differs\n";
    for my $kind (qw(source_snapshot inventory)) {
        $owner->{$kind} eq "$anchor/" . ($kind eq 'inventory' ? 'source-specs.tsv' : 'source-snapshot.txt') &&
            sha($owner->{$kind}) eq $owner->{"${kind}_sha256"}
            or die "product generation source evidence changed\n";
    }
    my $i = 0;
    for my $backend (qw(llvm cranelift)) {
        my $bound = $owner->{$backend};
        if ($bound->{digest} ne 'MISSING') {
            sha($bound->{path}) eq $bound->{digest} && sha($bound->{receipt}) eq $bound->{receipt_digest}
                or die "product generation producer changed\n";
            if (@expected) {
                $expected[$i] eq $bound->{path} && $expected[$i+1] eq $bound->{receipt}
                    or die "resume substitutes an existing producer\n";
            }
        } elsif (@expected) {
            $expected[$i] eq '' && $expected[$i+1] eq ''
                or die "new producer requires a new product generation\n";
        }
        $i += 2;
    }
    return $root;
}
sub mirror_product_receipt {
    my ($anchor, $source, $backend, $suite) = @_;
    $backend =~ /\A(?:llvm|cranelift)\z/ && $suite =~ /\A(?:compiler|interpreter|loader)\z/
        or die "invalid mirrored product selector\n";
    my $root = resolve_product_root($anchor, $source);
    $root ne $anchor or die "receipt mirror requires a bound physical generation\n";
    my $receipt = "$root/$backend/$suite/result.env";
    my $digest = sha($receipt);
    for my $directory ("$anchor/$backend", "$anchor/$backend/$suite") {
        if (!-e $directory && !-l $directory) { mkdir $directory or die $!; }
        safe($directory, 1);
    }
    open my $in, '<:raw', $receipt or die $!;
    my $destination = "$anchor/$backend/$suite/result.env";
    sysopen my $out, $destination, O_WRONLY | O_CREAT | O_EXCL or die "receipt mirror already exists\n";
    binmode $out or die $!;
    while (1) {
        my $count = read($in, my $buffer, 65536);
        defined($count) or die $!;
        last if $count == 0;
        print {$out} $buffer or die $!;
    }
    close $in or die $!; close $out or die $!;
    sha($receipt) eq $digest && sha($destination) eq $digest
        or die "verified product receipt changed during publication\n";
    return $destination;
}
1;

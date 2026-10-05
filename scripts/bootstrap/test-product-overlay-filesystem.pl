use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductRoot qw(allocate_product_root resolve_product_root);
use BootstrapProductOverlay qw(materialize_product_overlay verify_product_overlay);
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use File::Basename qw(dirname);
use JSON::PP;
use Digest::SHA qw(sha256_hex);
use Test::More;

my $windows = $^O eq 'msys' || $^O eq 'cygwin' || $^O eq 'MSWin32';
my $base = $windows ? '/c/.simple-product-tests' : '/tmp';
make_path($base);
my $fixture = tempdir('overlay-XXXXXXXX', DIR => $base, CLEANUP => 0);
note("retained real filesystem fixture: $fixture");
sub put {
    my ($p, $b) = @_; make_path(dirname($p));
    open my $f, '>:raw', $p or die $!; print {$f} $b or die $!; close $f or die $!;
}
sub get { open my $f, '<:raw', $_[0] or die $!; local $/; return <$f>; }
sub git {
    system('git', '-C', $fixture . '/source', '-c', 'core.hooksPath=NUL',
        '-c', 'user.name=Product fixture', '-c', 'user.email=fixture@example.invalid', @_) == 0 or die 'fixture Git failed';
}
sub rejects {
    my ($code, $pattern, $label) = @_;
    eval { $code->(); 1 } and die "unexpected acceptance: $label";
    like($@, $pattern, $label);
}
my $source = "$fixture/source";
make_path($source);
git('init', '-q');
put("$source/config/var.sdn", "profile=dev\n");
put("$source/test/real_spec.spl", "assert(7 == 7)\n");
put("$source/src/app/main.spl", "fn main() -> i32: 0\n");
put("$source/src/runtime/counterpart_abi_runtime.c", "#include \"../../tools/counterpart/sdk/c/simple_counterpart_abi.h\"\n");
put("$source/tools/counterpart/sdk/c/simple_counterpart_abi.h", "#define SIMPLE_COUNTERPART_ABI_VERSION 1\n");
put("$source/examples/10_tooling/trace32_tools/t32_cli/main.spl", "alias target\0bytes\n");
my $long = 'doc/08_tracking/bug/' . ('long_fixture_' x 7) . '.md';
put("$source/$long", "long document remains covered\n");
put("$source/src/app/t32_cli", '../../examples/10_tooling/trace32_tools/t32_cli');
git('add', '.');
my $oid = BootstrapProductOverlay::git_bytes($source, 'hash-object', 'src/app/t32_cli'); chomp $oid;
git('update-index', '--cacheinfo', "120000,$oid,src/app/t32_cli");
git('commit', '-qm', 'physical overlay fixture');
my $overlay = "$fixture/overlay"; make_path($overlay);
my $manifest = "$fixture/overlay.tsv";
materialize_product_overlay($source, $overlay, $manifest);
ok(verify_product_overlay($source, $overlay, $manifest), 'real materialization verifies');
is(get("$overlay/config/var.sdn"), get("$source/config/var.sdn"), 'configuration bytes retained');
is(get("$overlay/test/real_spec.spl"), get("$source/test/real_spec.spl"), 'test source retained');
my $sdk_header = 'tools/counterpart/sdk/c/simple_counterpart_abi.h';
is(get("$overlay/$sdk_header"), get("$source/$sdk_header"), 'runtime counterpart SDK header retained byte for byte');
ok(-f "$overlay/src/runtime/../../$sdk_header", 'runtime relative SDK include resolves inside overlay');
put("$overlay/$sdk_header", 'changed ABI header');
rejects(sub { verify_product_overlay($source, $overlay, $manifest) }, qr/member differs/, 'changed counterpart SDK header rejected');
put("$overlay/$sdk_header", get("$source/$sdk_header"));
is(get("$overlay/$long"), get("$source/$long"), 'long named document retained');
is(get("$overlay/src/app/t32_cli/main.spl"), get("$source/examples/10_tooling/trace32_tools/t32_cli/main.spl"), 'declared directory alias expands actual target bytes');
ok(!-l "$overlay/src/app/t32_cli", 'alias expansion is physical, not a junction');
put("$overlay/config/extra.sdn", 'injected');
rejects(sub { verify_product_overlay($source, $overlay, $manifest) }, qr/unlisted/, 'unlisted physical input rejected');
unlink "$overlay/config/extra.sdn" or die $!;
put("$overlay/src/app/main.spl", 'changed');
rejects(sub { verify_product_overlay($source, $overlay, $manifest) }, qr/member differs/, 'changed copied source rejected');
put("$overlay/src/app/main.spl", get("$source/src/app/main.spl"));
put("$overlay/src/app/product/generated.spl", 'real generated member');
ok(verify_product_overlay($source, $overlay, $manifest), 'only existing generated product exception retained');
put("$source/test/real_spec.spl", "version https://git-lfs.github.com/spec/v1\noid sha256:" . ('a' x 64) . "\nsize 123\n");
rejects(sub { verify_product_overlay($source, $overlay, $manifest) }, qr/unhydrated LFS/, 'unhydrated fixture pointer is not source data');
put("$source/test/real_spec.spl", "assert(7 == 7)\n");

if ($windows) {
    my $anchor = "$fixture/" . ('long-owned-request/' x 7) . 'product-output'; make_path($anchor);
    put("$anchor/source-snapshot.txt", "actual canonical owner fixture bytes\n");
    put("$anchor/source-specs.tsv", "fixture inventory bytes\n");
    put("$fixture/compiler.exe", "PE identity fixture; not admission\n");
    put("$fixture/producer.env", "unqualified fixture receipt\n");
    my $root = allocate_product_root($anchor, $source, "$anchor/source-snapshot.txt", "$anchor/source-specs.tsv",
        "$fixture/compiler.exe", "$fixture/producer.env", '', '');
    cmp_ok(length($anchor), '>', 180, 'logical generation has a long Windows prefix');
    cmp_ok(length($root), '<=', 48, 'whole physical generation has a bounded short prefix');
    is(resolve_product_root($anchor, $source), $root, 'real source/producer-bound anchor resolves');
    rejects(sub { allocate_product_root($anchor, $source, "$anchor/source-snapshot.txt", "$anchor/source-specs.tsv", '', '', '', '') }, qr/existing product/, 'prior generation cannot be overwritten');
    put("$fixture/compiler.exe", 'different producer');
    rejects(sub { resolve_product_root($anchor, $source) }, qr/producer changed/, 'stale producer rejected');
    put("$fixture/compiler.exe", "PE identity fixture; not admission\n");
    put("$root/product-root.json", '{}');
    rejects(sub { resolve_product_root($anchor, $source) }, qr/chaining/, 'reference chaining and cycles rejected');
    unlink "$root/product-root.json" or die $!;
    my $reference = get("$anchor/product-root.json");
    my $j = JSON::PP->new->canonical;
    my $r = $j->decode($reference); $r->{physical_root} = "$root/../foreign";
    put("$anchor/product-root.json", $j->encode($r) . "\n");
    rejects(sub { resolve_product_root($anchor, $source) }, qr/namespace/, 'reference traversal rejected');
    put("$anchor/product-root.json", $reference);
    put("$anchor/source-specs.tsv", 'changed inventory');
    rejects(sub { resolve_product_root($anchor, $source) }, qr/evidence changed/, 'stale inventory rejected');
}
done_testing();

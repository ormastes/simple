#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapProductSelection qw(product_selection selection_fields);
use File::Temp qw(tempdir);
use Digest::SHA qw(sha256_hex);
use Test::More;
my $dir = tempdir(CLEANUP => 1);
my $header = "subsystem\tlevel\tpath\tsha256\n";
my @paths = map { "test/01_unit/compiler/interpreter/${_}_spec.spl" } qw(first second);
my @rows = map { "interpreter\t01_unit\t$_\t" . ('a' x 64) . "\n" } @paths;
my $loader = 'test/01_unit/compiler/loader/third_spec.spl';
sub write_file {
    my ($path, $bytes) = @_;
    open my $out, '>:raw', $path or die $!;
    print {$out} $bytes;
    close $out or die $!;
}
my $canonical = "$dir/canonical.tsv";
my $list = "$dir/list.txt";
write_file($canonical, $header . join('', @rows) . "loader\t01_unit\t$loader\t" . ('b' x 64) . "\n");
write_file($list, "$paths[1]\n$paths[0]\n");
my $selection = product_selection($canonical, $list, 'interpreter');
is($selection->{inventory_bytes}, $header . $rows[1] . $rows[0], 'selection preserves requested order');
is($selection->{canonical_subsystem_owner_count}, 2, 'retains full subsystem count');
is($selection->{selected_owner_count}, 2, 'reports selected count');
is($selection->{selection_scope}, 'ordered-subset', 'complete list still has subset authority');
is($selection->{spec_list_sha256}, sha256_hex("$paths[1]\n$paths[0]\n"), 'binds order in list hash');
write_file($list, "$paths[0]\n");
$selection = product_selection($canonical, $list, 'interpreter');
is($selection->{inventory_bytes}, $header . $rows[0], 'one file excludes remaining owner');
is($selection->{selected_owner_count}, 1, 'single file count');
like(selection_fields($selection), qr/^canonical_inventory_sha256=[0-9a-f]{64}$/m, 'retains canonical digest');
for my $case (
    ['empty', ''], ['blank', "\n"], ['duplicate', "$paths[0]\n$paths[0]\n"],
    ['other subsystem', "$loader\n"], ['unknown', "test/01_unit/compiler/interpreter/missing_spec.spl\n"],
    ['traversal', "test/../$paths[0]\n"], ['absolute', "/$paths[0]\n"],
    ['unterminated', $paths[0]], ['CRLF', "$paths[0]\r\n"],
) {
    write_file($list, $case->[1]);
    eval { product_selection($canonical, $list, 'interpreter') };
    ok($@, "rejects $case->[0]");
}
write_file($list, "$paths[0]\n");
symlink($list, "$dir/link") or die $!;
eval { product_selection($canonical, "$dir/link", 'interpreter') };
like($@, qr/absolute regular/, 'rejects mutable symlink authority');
write_file($canonical, $header . $rows[0] . $rows[0]);
eval { product_selection($canonical, $list, 'interpreter') };
like($@, qr/duplicate canonical/, 'rejects duplicate canonical owner');
done_testing();

use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductRoot qw(allocate_product_root resolve_product_root mirror_product_receipt);
my $mode = shift @ARGV // '';
if ($mode eq 'allocate' && @ARGV == 8) { print allocate_product_root(@ARGV), "\n"; }
elsif ($mode eq 'resolve' && (@ARGV == 2 || @ARGV == 6)) { print resolve_product_root(@ARGV), "\n"; }
elsif ($mode eq 'mirror' && @ARGV == 4) { print mirror_product_receipt(@ARGV), "\n"; }
else { die "product-root requires allocate or resolve with exact bindings\n"; }

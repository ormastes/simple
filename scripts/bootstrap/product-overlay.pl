use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductOverlay qw(materialize_product_overlay verify_product_overlay verify_product_source);
my $mode = shift @ARGV // '';
if ($mode eq 'source-check' && @ARGV == 1) { verify_product_source(@ARGV); exit 0; }
@ARGV == 3 or die "product-overlay requires source, overlay and manifest\n";
if ($mode eq 'materialize') { materialize_product_overlay(@ARGV); }
elsif ($mode eq 'verify') { verify_product_overlay(@ARGV); }
else { die "unknown product-overlay operation\n"; }

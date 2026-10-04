use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapProductProducer qw(validate_product_resources);
use Test::More;
for my $row (
    [1, qualified => 20, 6835937, 1800, 'enforce'],
    [1, diagnostic => 80, 5859375, 0, 'monitor'],
    [1, diagnostic => 1, 5859375, 0, 'enforce'],
    [0, qualified => 80, 5859375, 1800, 'enforce'],
    [0, qualified => 20, 5859375, 0, 'enforce'],
    [0, qualified => 20, 5859375, 1800, 'monitor'],
    [0, diagnostic => 81, 5859375, 0, 'monitor'],
    [0, diagnostic => 80, 0, 0, 'monitor'],
    [0, diagnostic => 80, 6835938, 0, 'monitor'],
    [0, diagnostic => 80, 5859375, -1, 'monitor'],
    [0, diagnostic => 80, 5859375, '00', 'monitor'],
    [0, diagnostic => 80, 5859375, 0, 'unknown'],
) {
    my ($expected, @args) = @$row;
    my $actual = eval { validate_product_resources(@args); 1 } || 0;
    is($actual, $expected, join(' ', @args));
}
done_testing;

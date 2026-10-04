use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapProductProducer qw(validate_product_resources product_resource_profile validate_product_resource_profile);
use Test::More;
for my $row (
    [1, qualified => 20, 6835937, 1800, 'enforce'],
    [1, diagnostic => 80, 5859375, 0, 'monitor'],
    [1, diagnostic => 1, 5859375, 0, 'enforce'],
    [1, qualified => 80, 5859375, 1800, 'enforce'],
    [0, qualified => 21, 5859375, 1800, 'enforce'],
    [0, qualified => 79, 5859375, 1800, 'enforce'],
    [0, qualified => 81, 5859375, 1800, 'enforce'],
    [0, qualified => 80, 5859375, 0, 'enforce'],
    [0, qualified => 80, 5859375, 1800, 'monitor'],
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
is(product_resource_profile('qualified', 80, 5859375, 1800, 'enforce'),
    'qualified-80-v1', 'qualified80 has its own explicit profile');
is(product_resource_profile('qualified', 20, 5859375, 1800, 'enforce'),
    'qualified-10-20-v1', 'legacy qualified range remains supported');
is(product_resource_profile('diagnostic', 80, 5859375, 0, 'monitor'),
    'diagnostic-v1', 'diagnostics cannot become qualification');
for my $row (
    [1, 'qualified-80-v1', qualified => 80, 5859375, 1800, 'enforce'],
    [0, undef, qualified => 80, 5859375, 1800, 'enforce'],
    [0, '', qualified => 80, 5859375, 1800, 'enforce'],
    [0, 'qualified-10-20-v1', qualified => 80, 5859375, 1800, 'enforce'],
    [0, 'diagnostic-v1', qualified => 80, 5859375, 1800, 'enforce'],
    [0, 'qualified-80-v1', diagnostic => 80, 5859375, 0, 'monitor'],
    [0, 'qualified-80-v1', qualified => 20, 5859375, 1800, 'enforce'],
    [1, undef, qualified => 20, 5859375, 1800, 'enforce'],
) {
    my ($expected, @args) = @$row;
    my $actual = eval { validate_product_resource_profile(@args); 1 } || 0;
    is($actual, $expected, 'receipt profile: ' . join(' ', map { defined($_) ? $_ : 'ABSENT' } @args));
}
done_testing;

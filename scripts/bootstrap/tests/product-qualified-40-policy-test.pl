use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapProductProducer qw(product_resource_profile validate_product_resource_profile);
use Test::More;

is(product_resource_profile('qualified',40,3000000,1800,'enforce'),
   'qualified-40-v1','qualified40 has an explicit profile');
for my $row (
    [0,undef,40,3000000,1800,'enforce'],
    [0,'',40,3000000,1800,'enforce'],
    [0,'qualified-80-v1',40,3000000,1800,'enforce'],
    [0,'qualified-10-20-v1',40,3000000,1800,'enforce'],
    [0,'diagnostic-v1',40,3000000,1800,'enforce'],
    [1,'qualified-40-v1',40,3000000,1800,'enforce'],
    [0,'qualified-40-v1',39,3000000,1800,'enforce'],
    [0,'qualified-40-v1',41,3000000,1800,'enforce'],
    [0,'qualified-40-v1','040',3000000,1800,'enforce'],
    [0,'qualified-40-v1',40,3000000,0,'enforce'],
    [0,'qualified-40-v1',40,3000000,1800,'monitor'],
    [0,'qualified-40-v1',40,6835938,1800,'enforce'],
    [0,'qualified-40-v1',20,3000000,1800,'enforce'],
    [0,'qualified-40-v1',80,3000000,1800,'enforce'],
) {
    my ($expected,$recorded,@resources)=@$row;
    my $actual=eval {validate_product_resource_profile($recorded,'qualified',@resources);1}||0;
    is($actual,$expected,'new40 admission: '.join(' ',map {defined($_)?$_:'ABSENT'} ($recorded,@resources)));
}
my $promoted=eval {validate_product_resource_profile('qualified-40-v1','diagnostic',40,3000000,0,'monitor');1}||0;
is($promoted,0,'diagnostic40 cannot be promoted by a qualified40 label');
done_testing;

use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductRoot qw(allocate_product_root);
use BootstrapProductOverlay qw(materialize_product_overlay);
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use File::Basename qw(dirname);
use Test::More;
plan skip_all => 'Windows drive allocation regression' unless $^O =~ /msys|cygwin/;
my $base='/c/.simple-product-tests'; make_path($base);
my $fixture=tempdir('budget-XXXXXXXX',DIR=>$base,CLEANUP=>0);
note("retained short-prefix fixture: $fixture");
sub put { my($p,$b)=@_; make_path(dirname($p)); open my $f,'>:raw',$p or die $!; print {$f} $b; close $f or die $!; }
my $source="$fixture/source"; make_path($source);
my $relative='doc/08_tracking/bug/' . (('d' x 30) . '/') x 3 . ('f' x 50) . '.md';
put("$source/$relative",'actual long relative input bytes');
for my $args (['init','-q'], ['add','.'], ['commit','-qm','source fixture']) {
    system('git','-C',$source,'-c','core.hooksPath=NUL','-c','core.autocrlf=false','-c','user.name=Fixture','-c','user.email=fixture@example.invalid',@$args)==0 or die 'fixture Git failed';
}
my $anchor="$fixture/request-" . ('x' x 18); make_path($anchor);
put("$anchor/source-snapshot.txt",'unqualified fixture snapshot'); put("$anchor/source-specs.tsv",'fixture inventory');
put("$fixture/compiler",'fixture producer'); put("$fixture/receipt",'fixture receipt');
my $root=allocate_product_root($anchor,$source,"$anchor/source-snapshot.txt","$anchor/source-specs.tsv","$fixture/compiler","$fixture/receipt",'','');
my $nested='/cranelift/interpreter/source-overlay';
cmp_ok(length($anchor),'<=',80,'below-80 output prefix still receives short allocation');
cmp_ok(length("$anchor$nested/$relative"),'>=',260,'old prefix heuristic exceeds Windows native path budget');
cmp_ok(length("$root$nested/$relative"),'<',260,'whole short generation restores full nested path budget');
make_path("$root$nested");
materialize_product_overlay($source,"$root$nested","$root/manifest.tsv");
open my $f,'<:raw',"$root$nested/$relative" or die $!; local $/;
is(<$f>,'actual long relative input bytes','actual filesystem materialization retains long relative input');
done_testing();

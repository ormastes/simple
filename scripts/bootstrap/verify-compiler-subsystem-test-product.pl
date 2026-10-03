#!/usr/bin/env perl
# Verify one binary-owned aggregate registry and its exact execution ledger.
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use Getopt::Long qw(GetOptions);
use POSIX qw(uname);
use File::Find qw(find);

my %arg;
GetOptions(
  'phase=s' => \$arg{phase},
  'source-root=s' => \$arg{source_root}, 'inventory=s' => \$arg{inventory},
  'backend=s' => \$arg{backend}, 'subsystem=s' => \$arg{subsystem},
  'compiler=s' => \$arg{compiler}, 'binary=s' => \$arg{binary},
  'compiler-producer-receipt=s' => \$arg{compiler_producer_receipt},
  'threads=i' => \$arg{threads}, 'rss-cap-kib=i' => \$arg{rss_cap_kib},
  'build-timeout-seconds=i' => \$arg{build_timeout_seconds},
  'build-receipt=s' => \$arg{build_receipt},
  'enumeration=s' => \$arg{enumeration}, 'enumeration-stdout=s' => \$arg{enumeration_stdout},
  'enumeration-stderr=s' => \$arg{enumeration_stderr},
  'enumeration-watchdog=s' => \$arg{enumeration_watchdog},
  'enumeration-exit=i' => \$arg{enumeration_exit},
  'execution=s' => \$arg{execution}, 'execution-stdout=s' => \$arg{execution_stdout},
  'execution-stderr=s' => \$arg{execution_stderr},
  'execution-watchdog=s' => \$arg{execution_watchdog},
  'execution-exit=i' => \$arg{execution_exit}, 'output=s' => \$arg{output},
) or die "invalid product verifier options\n";
$arg{phase} //= 'complete';
$arg{phase} =~ /\A(?:build|enumerate|complete)\z/ or die "invalid verification phase\n";
my @required = qw(source_root inventory backend subsystem compiler binary compiler_producer_receipt build_receipt
                  threads rss_cap_kib build_timeout_seconds);
push @required, qw(enumeration enumeration_stdout enumeration_stderr enumeration_watchdog enumeration_exit)
  if $arg{phase} ne 'build';
push @required, qw(execution execution_stdout execution_stderr execution_watchdog execution_exit output)
  if $arg{phase} eq 'complete';
for my $key (@required) {
  defined($arg{$key}) && length($arg{$key}) or die "missing $key\n";
}
$arg{backend} =~ /\A(?:llvm|cranelift)\z/ or die "invalid backend\n";
$arg{subsystem} =~ /\A(?:compiler|interpreter|loader)\z/ or die "invalid subsystem\n";
$arg{threads} >= 10 && $arg{threads} <= 20 &&
  $arg{rss_cap_kib} > 0 && $arg{rss_cap_kib} <= 6835937
  && $arg{build_timeout_seconds} > 0
  or die "invalid product resource policy\n";
for my $key (grep { defined $arg{$_} } qw(enumeration_exit execution_exit)) {
  $arg{$key} =~ /\A\d+\z/ && $arg{$key} <= 255 or die "invalid $key\n";
}

sub regular_bytes {
  my ($path) = @_;
  -f $path && !-l $path or die "missing regular evidence: $path\n";
  open my $fh, '<:raw', $path or die "cannot read evidence: $path\n";
  local $/;
  my $bytes = <$fh>;
  close $fh or die "cannot close evidence: $path\n";
  return $bytes;
}
sub sha_file {
  my ($path) = @_;
  -f $path && !-l $path or die "missing regular evidence: $path\n";
  open my $fh, '<:raw', $path or die "cannot read evidence: $path\n";
  my $sha = Digest::SHA->new(256);
  $sha->addfile($fh);
  close $fh or die "cannot close evidence: $path\n";
  return $sha->hexdigest;
}
sub native_image {
  my ($path) = @_;
  -f $path && !-l $path && -x $path or die "native product missing or not executable\n";
  open my $fh, '<:raw', $path or die "cannot inspect native product\n";
  read($fh, my $header, 64) >= 20 or die "native product header short\n";
  close $fh or die "cannot close native product\n";
  my @uts = uname();
  my ($system, $machine) = @uts[0, 4];
  $system =~ /\A(?:Linux|FreeBSD)\z/ or die "native product host unsupported by this gate\n";
  substr($header, 0, 4) eq "\x7fELF" && ord(substr($header, 4, 1)) == 2 &&
    ord(substr($header, 5, 1)) == 1 &&
    (unpack('v', substr($header, 16, 2)) == 2 ||
     unpack('v', substr($header, 16, 2)) == 3)
    or die "product is not a host ELF executable image\n";
  my %host_machine = (x86_64 => 62, amd64 => 62, aarch64 => 183, arm64 => 183);
  exists($host_machine{lc $machine}) &&
    unpack('v', substr($header, 18, 2)) == $host_machine{lc $machine}
    or die "product ELF machine differs from host target\n";
}
sub no_link_components {
  my ($path) = @_;
  $path =~ m{\A/} or die "nonabsolute generated path\n";
  my $current = '';
  for my $part (split m{/}, $path) {
    next if $part eq '';
    $part ne '.' && $part ne '..' or die "unsafe generated path\n";
    $current .= "/$part";
    !-l $current or die "linked generated path\n";
  }
}
sub safe_path {
  my ($path) = @_;
  $path =~ m{\A(?:test/01_unit|test/02_integration|test/03_system)/} &&
    $path !~ m{(?:\A|/)\.\.?(/|\z)} && $path !~ /[\t\r\n\\]/
    or die "unsafe inventory path\n";
}
sub git_output_for {
  my ($root, @command) = @_;
  open my $pipe, '-|', 'git', '-C', $root, @command
    or die "cannot inspect pinned source Git authority\n";
  local $/;
  my $output = <$pipe> // '';
  close $pipe or die "pinned source Git authority unavailable\n";
  return $output;
}
my $actual_head = git_output_for($arg{source_root}, 'rev-parse', '--verify', 'HEAD');
$actual_head =~ s/\n\z//;
$actual_head =~ /\A[0-9a-f]{40}\z/ or die "pinned source HEAD invalid\n";
git_output_for($arg{source_root}, 'status', '--porcelain', '--untracked-files=all') eq ''
  or die "pinned source has changed or untracked inputs\n";
my $inventory_bytes = regular_bytes($arg{inventory});
my $whole_sha = sha256_hex($inventory_bytes);
my @inventory_lines = split /\n/, $inventory_bytes, -1;
pop @inventory_lines if @inventory_lines && $inventory_lines[-1] eq '';
shift(@inventory_lines) eq "subsystem\tlevel\tpath\tsha256" or die "invalid inventory header\n";
my (@owners, @subset_lines);
my %seen_source;
for my $line (@inventory_lines) {
  my @f = split /\t/, $line, -1;
  @f == 4 && $f[0] =~ /\A(?:compiler|interpreter|loader)\z/ &&
    $f[1] =~ /\A(?:01_unit|02_integration|03_system)\z/ &&
    $f[2] =~ m{\Atest/\Q$f[1]\E/} && $f[3] =~ /\A[0-9a-f]{64}\z/
    or die "invalid inventory row\n";
  safe_path($f[2]);
  my @owner_parts = split m{/}, $f[2];
  pop @owner_parts;
  my %owner_parts = map { $_ => 1 } @owner_parts;
  my $expected_subsystem = $owner_parts{loader} ? 'loader' :
    $owner_parts{interpreter} ? 'interpreter' : 'compiler';
  $f[0] eq $expected_subsystem or die "inventory subsystem owner differs\n";
  !$seen_source{$f[2]}++ or die "duplicate inventory owner\n";
  sha_file("$arg{source_root}/$f[2]") eq $f[3] or die "source hash differs: $f[2]\n";
  if ($f[0] eq $arg{subsystem}) {
    push @owners, [$f[2], $f[3]];
    push @subset_lines, $line;
  }
}
my %tracked_owner;
my $tracked = git_output_for($arg{source_root}, 'ls-files', '-z', '--',
  'test/01_unit', 'test/02_integration', 'test/03_system');
for my $path (split /\0/, $tracked) {
  next unless $path =~ m{\Atest/(?:01_unit|02_integration|03_system)/.*_(?:spec|test)\.spl\z};
  my @parts = split m{/}, $path;
  pop @parts;
  next if grep { $_ eq 'vendor' || $_ eq 'fixtures' } @parts;
  my %parts = map { $_ => 1 } @parts;
  next unless (($parts[2] // '') =~ /\A(?:compiler_core|compiler_shared|core)\z/ ||
    $parts{compiler} || $parts{interpreter} || $parts{loader});
  $tracked_owner{$path} = 1;
}
join("\n", sort keys %tracked_owner) eq join("\n", sort keys %seen_source)
  or die "inventory omits tracked subsystem owner or includes extra source\n";
@owners or die "empty product source subset\n";
my $subset_sha = sha256_hex("subsystem\tlevel\tpath\tsha256\n" . join('', map { "$_\n" } @subset_lines));
my @digest_keys = qw(compiler binary compiler_producer_receipt build_receipt);
push @digest_keys, qw(enumeration enumeration_stdout enumeration_stderr enumeration_watchdog)
  if $arg{phase} ne 'build';
push @digest_keys, qw(execution execution_stdout execution_stderr execution_watchdog)
  if $arg{phase} eq 'complete';
my %digest = map { $_ => sha_file($arg{$_}) } @digest_keys;
native_image($arg{binary});

sub build_fields {
  my ($bytes) = @_;
  my %fields;
  for my $line (split /\n/, $bytes, -1) {
    next if $line eq '';
    $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/ && !exists $fields{$1}
      or die "invalid or duplicate product build receipt field\n";
    $fields{$1} = $2;
  }
  return %fields;
}
my %build = build_fields(regular_bytes($arg{build_receipt}));
$build{schema} && $build{schema} eq 'simple-subsystem-product-v1' &&
  $build{status} && $build{status} eq 'produced' &&
  $build{source_root} && $build{source_root} eq $arg{source_root} &&
  $build{compiler_path} && $build{compiler_path} eq $arg{compiler} &&
  $build{compiler_sha256} && $build{compiler_sha256} eq $digest{compiler} &&
  $build{compiler_producer_receipt_path} &&
    $build{compiler_producer_receipt_path} eq $arg{compiler_producer_receipt} &&
  $build{compiler_producer_receipt_sha256} &&
    $build{compiler_producer_receipt_sha256} eq $digest{compiler_producer_receipt} &&
  $build{requested_backend} && $build{requested_backend} eq $arg{backend} &&
  $build{actual_backend} && $build{actual_backend} eq $arg{backend} &&
  $build{subsystem} && $build{subsystem} eq $arg{subsystem} &&
  $build{inventory_path} && $build{inventory_path} eq $arg{inventory} &&
  $build{inventory_sha256} && $build{inventory_sha256} eq $whole_sha &&
  $build{subset_sha256} && $build{subset_sha256} eq $subset_sha &&
  $build{binary_path} && $build{binary_path} eq $arg{binary} &&
  $build{binary_sha256} && $build{binary_sha256} eq $digest{binary} &&
  $build{source_head} && $build{source_head} eq $actual_head &&
  defined($build{threads}) && $build{threads} eq $arg{threads} &&
  defined($build{rss_cap_kib}) && $build{rss_cap_kib} eq $arg{rss_cap_kib} &&
  defined($build{build_timeout_seconds}) &&
    $build{build_timeout_seconds} eq $arg{build_timeout_seconds} &&
  $build{generated_tree_sha256} && $build{generated_tree_sha256} =~ /\A[0-9a-f]{64}\z/ &&
  defined($build{generated_owner_count}) && $build{generated_owner_count} eq scalar(@owners)
  or die "product build receipt authority differs\n";
my $generated_manifest = $build{generated_manifest_path} // '';
my $binary_dir = $arg{binary};
$binary_dir =~ s{/[^/]+\z}{} or die "binary path invalid\n";
my $backend_identity_path = $build{backend_identity_path} // '';
$backend_identity_path eq "$binary_dir/cache-product/native_provider_identity.receipt" &&
  $build{backend_identity_sha256} &&
  sha_file($backend_identity_path) eq $build{backend_identity_sha256}
  or die "compiler-owned backend identity receipt missing or changed\n";
no_link_components($backend_identity_path);
my @backend_identity_lines = split /\n/, regular_bytes($backend_identity_path), -1;
@backend_identity_lines == 4 && $backend_identity_lines[3] eq '' &&
  shift(@backend_identity_lines) eq 'simple-native-provider-identity-v1'
  or die "compiler-owned backend identity schema differs\n";
my %backend_identity = build_fields(join("\n", @backend_identity_lines));
keys(%backend_identity) == 2 &&
  $backend_identity{backend} && $backend_identity{backend} eq $arg{backend} &&
  $backend_identity{provider} && $backend_identity{provider} =~ /\A[0-9a-f]{64}\z/ &&
  $build{provider_kind} && $build{provider_kind} eq 'builtin' &&
  $build{provider_receipt_hash} &&
    $build{provider_receipt_hash} eq $backend_identity{provider} &&
  $build{actual_backend} eq $backend_identity{backend}
  or die "effective backend differs from compiler identity\n";
$generated_manifest =~ m{\A\Q$binary_dir\E/} &&
  sha_file($generated_manifest) eq $build{generated_tree_sha256}
  or die "generated source manifest differs\n";
no_link_components($generated_manifest);
my $manifest_bytes = regular_bytes($generated_manifest);
my @generated_lines = split /\n/, $manifest_bytes, -1;
pop @generated_lines if @generated_lines && $generated_lines[-1] eq '';
shift(@generated_lines) eq "path\tsha256" && @generated_lines
  or die "generated source manifest empty or invalid\n";
my $generated_dir = $generated_manifest;
$generated_dir =~ s{/[^/]+\z}{} or die "generated manifest path invalid\n";
my $previous_generated = '';
my %manifested_generated;
for my $line (@generated_lines) {
  my @f = split /\t/, $line, -1;
  @f == 2 && $f[0] =~ m{\A[^/]+(?:/[^/]+)*\z} &&
    $f[0] !~ m{(?:\A|/)\.\.?(/|\z)} && $f[0] !~ /[\t\r\n\\]/ &&
    $f[0] gt $previous_generated && $f[1] =~ /\A[0-9a-f]{64}\z/ &&
    sha_file("$generated_dir/$f[0]") eq $f[1]
    or die "generated source content differs\n";
  no_link_components("$generated_dir/$f[0]");
  $manifested_generated{$f[0]} = 1;
  $previous_generated = $f[0];
}
for my $pair (['generator_path','generator_sha256'],
              ['runtime_receipt_path','runtime_receipt_sha256'],
              ['generator_watchdog_receipt_path','generator_watchdog_receipt_sha256'],
              ['product_watchdog_receipt_path','product_watchdog_receipt_sha256']) {
  my ($path_key, $sha_key) = @$pair;
  $build{$path_key} && $build{$sha_key} &&
    $build{$sha_key} =~ /\A[0-9a-f]{64}\z/ &&
    sha_file($build{$path_key}) eq $build{$sha_key}
    or die "product build receipt $path_key differs\n";
}
my %admission = build_fields(regular_bytes($arg{compiler_producer_receipt}));
$admission{schema} && $admission{schema} eq 'simple-bootstrap-stage2-admission-v2' &&
  $admission{status} && $admission{status} eq 'admitted' &&
  $admission{candidate_path} && $admission{candidate_path} eq $arg{compiler} &&
  $admission{candidate_sha256} && $admission{candidate_sha256} eq $digest{compiler}
  or die "expected Stage2 compiler admission differs\n";
$admission{source_snapshot_path} && $admission{source_snapshot_sha256} &&
  $build{producer_source_snapshot_path} && $build{producer_source_snapshot_sha256} &&
  $build{producer_source_snapshot_path} eq $admission{source_snapshot_path} &&
  $build{producer_source_snapshot_sha256} eq $admission{source_snapshot_sha256} &&
  sha_file($build{producer_source_snapshot_path}) eq $build{producer_source_snapshot_sha256}
  or die "Stage2 producer source snapshot differs\n";
$build{product_source_snapshot_path} &&
  $build{product_source_snapshot_path} eq "$binary_dir/logs/product-source-snapshot.txt" &&
  $build{product_source_snapshot_sha256} &&
  sha_file($build{product_source_snapshot_path}) eq $build{product_source_snapshot_sha256}
  or die "current product source snapshot differs\n";
my $overlay = $build{source_overlay_path} // '';
$overlay =~ m{\A\Q$binary_dir\E/} && -d $overlay && !-l $overlay &&
  $build{source_overlay_head} && $build{source_overlay_head} eq $actual_head &&
  $build{source_overlay_allocated_bytes} &&
    $build{source_overlay_allocated_bytes} =~ /\A[1-9][0-9]*\z/
  or die "source overlay authority missing\n";
no_link_components($overlay);
$generated_manifest eq "$overlay/src/app/generated-manifest.tsv" &&
  $generated_dir eq "$overlay/src/app"
  or die "generated source manifest outside admitted overlay\n";
my %populated_generated;
find({ no_chdir => 1, wanted => sub {
  my $path = $File::Find::name;
  -l $path and die "linked generated source\n";
  return unless -f $path;
  my $relative = substr($path, length($generated_dir) + 1);
  $populated_generated{$relative} = 1;
} }, "$generated_dir/product");
join("\n", sort keys %manifested_generated) eq
  join("\n", sort keys %populated_generated)
  or die "generated source manifest omits populated file\n";
my $overlay_head = git_output_for($overlay, 'rev-parse', '--verify', 'HEAD');
$overlay_head =~ s/\n\z//;
$overlay_head eq $actual_head or die "source overlay Git HEAD differs\n";
my $overlay_manifest = $build{source_overlay_input_manifest_path} // '';
$overlay_manifest eq "$binary_dir/logs/source-overlay-inputs.tsv" &&
  $build{source_overlay_input_sha256} &&
  sha_file($overlay_manifest) eq $build{source_overlay_input_sha256}
  or die "source overlay input manifest differs\n";
no_link_components($overlay_manifest);
my @overlay_rows = split /\n/, regular_bytes($overlay_manifest), -1;
pop @overlay_rows if @overlay_rows && $overlay_rows[-1] eq '';
shift(@overlay_rows) eq "path\tsha256" && @overlay_rows
  or die "source overlay input manifest invalid\n";
my $previous_overlay = '';
my %manifested_overlay;
for my $row (@overlay_rows) {
  my @f = split /\t/, $row, -1;
  @f == 2 && $f[0] =~ m{\Asrc/(?:compiler|lib|app|plugins|compositions)/} &&
    $f[0] !~ m{(?:\A|/)\.\.?(/|\z)} && $f[0] !~ /[\t\r\n\\]/ &&
    $f[0] gt $previous_overlay && $f[1] =~ /\A[0-9a-f]{64}\z/ &&
    sha_file("$overlay/$f[0]") eq $f[1] &&
    sha_file("$arg{source_root}/$f[0]") eq $f[1]
    or die "source overlay input differs from pinned root\n";
  no_link_components("$overlay/$f[0]");
  $manifested_overlay{$f[0]} = 1;
  $previous_overlay = $f[0];
}
my %populated_overlay;
for my $scope (qw(compiler lib app plugins compositions)) {
  next unless -d "$overlay/src/$scope";
  find({ no_chdir => 1, wanted => sub {
    my $path = $File::Find::name;
    -l $path and die "linked source overlay input\n";
    return unless -f $path;
    my $relative = substr($path, length($overlay) + 1);
    return if $relative eq 'src/app/generated-manifest.tsv' ||
      $relative =~ m{\Asrc/app/product/};
    $populated_overlay{$relative} = 1;
  } }, "$overlay/src/$scope");
}
join("\n", sort keys %populated_overlay) eq join("\n", sort keys %manifested_overlay)
  or die "source overlay input manifest omits populated source\n";
for my $pair (['source_spans_path','source_spans_sha256'],
              ['main_policy_path','main_policy_sha256'],
              ['main_verdicts_path','main_verdicts_sha256'],
              ['adapter_path','adapter_sha256']) {
  my ($path_key, $sha_key) = @$pair;
  $build{$path_key} && $build{$sha_key} &&
    sha_file($build{$path_key}) eq $build{$sha_key}
    or die "product build receipt $path_key differs\n";
}
$build{source_spans_path} eq "$binary_dir/source-spans.tsv" &&
  $build{main_verdicts_path} eq "$binary_dir/main-verdicts.tsv" &&
  $build{main_policy_path} eq "$arg{source_root}/config/check/compiler_subsystem_main_verdict_policy.tsv" &&
  $build{generator_path} eq "$binary_dir/tools/product-generator" &&
  $build{adapter_path} eq "$binary_dir/tools/main-verdict-adapter"
  or die "parser/adapter authority path differs\n";
my @spans = split /\n/, regular_bytes($build{source_spans_path});
shift(@spans) eq join("\t", 'simple-subsystem-source-spans-v1', $arg{subsystem}, $whole_sha)
  or die "source spans header differs\n";
my $span_trailer = pop @spans;
$span_trailer eq join("\t", 'complete', scalar(@owners))
  or die "source spans incomplete\n";
my (%span_owners, $span_current, $span_decl_seen, $span_decl_count);
for my $line (@spans) {
  my @f = split /\t/, $line, -1;
  if ($f[0] eq 'owner') {
    if (defined $span_current) {
      $span_decl_seen == $span_decl_count or die "source span owner declarations missing\n";
    }
    @f == 4 && $f[3] =~ /\A(?:0|[1-9][0-9]*)\z/ &&
      !exists($span_owners{$f[1]}) &&
      $f[1] eq $owners[scalar(keys %span_owners)][0] &&
      $f[2] eq $owners[scalar(keys %span_owners)][1]
      or die "source span owner differs\n";
    $span_owners{$f[1]} = $f[3];
    ($span_current, $span_decl_seen, $span_decl_count) = ($f[1], 0, $f[3]);
  } elsif ($f[0] eq 'decl') {
    defined($span_current) && @f == 7 && $f[1] eq $span_current &&
      $f[2] eq $span_decl_seen && $f[3] =~ /\A[0-9]+\z/ &&
      $f[5] =~ /\A[0-9]+\z/ && $f[6] =~ /\A[0-9]+\z/ &&
      $f[6] >= $f[5] && $span_decl_seen < $span_decl_count
      or die "source declaration span invalid\n";
    $span_decl_seen++;
  } else { die "source spans unknown row\n"; }
}
defined($span_current) && $span_decl_seen == $span_decl_count &&
  keys(%span_owners) == @owners or die "source spans owners incomplete\n";
my @main_verdicts = split /\n/, regular_bytes($build{main_verdicts_path});
shift(@main_verdicts) eq join("\t", 'owner-main-verdict-v1', $whole_sha, $build{source_spans_sha256})
  or die "main verdict header differs\n";
my $main_trailer = pop @main_verdicts;
$main_trailer eq join("\t", 'complete', scalar(@main_verdicts))
  or die "main verdict trailer differs\n";
my %main_kind;
my %owner_sha = map { $_->[0] => $_->[1] } @owners;
for my $line (@main_verdicts) {
  my @f = split /\t/, $line, -1;
  @f == 7 && $f[0] eq 'owner' && exists($span_owners{$f[1]}) &&
    $f[2] eq $owner_sha{$f[1]} &&
    $f[3] =~ /\A[0-9]+\z/ &&
    $f[4] =~ /\A(?:aggregate-registry-declare|exit-zero)\z/ &&
    length($f[5]) && !exists($main_kind{$f[1]})
    or die "main verdict unsupported or differs\n";
  $main_kind{$f[1]} = $f[4];
}
my @tasks = qw(generator generator_run main_adapter main_adapter_run product);
for my $task (@tasks) {
  my $command_path = $build{"${task}_command_path"} // '';
  my $watchdog_path = $build{"${task}_watchdog_receipt_path"} // '';
  $command_path eq "$binary_dir/logs/$task.command.tsv" &&
    $watchdog_path eq "$binary_dir/logs/$task.watchdog.env" &&
    $build{"${task}_command_sha256"} &&
    sha_file($command_path) eq $build{"${task}_command_sha256"} &&
    $build{"${task}_watchdog_receipt_sha256"} &&
    sha_file($watchdog_path) eq $build{"${task}_watchdog_receipt_sha256"}
    or die "$task command/watchdog provenance differs\n";
  no_link_components($command_path);
  no_link_components($watchdog_path);
  my @command = split /\n/, regular_bytes($command_path);
  shift(@command) eq 'schema=simple-native-product-command-v1'
    or die "$task command schema differs\n";
  my %command;
  my @argv;
  for my $line (@command) {
    if ($line =~ /\Aargv-hex=([0-9a-f]*)\z/) {
      push @argv, pack('H*', $1);
    } elsif ($line =~ /\A([a-z_]+)=(.*)\z/ && !exists $command{$1}) {
      $command{$1} = $2;
    } else { die "$task command malformed\n"; }
  }
  @argv && $command{source_root} && $command{source_root} eq $arg{source_root} &&
    $command{compiler_sha256} && $command{compiler_sha256} eq $digest{compiler} &&
    $command{rss_cap_kib} && $command{rss_cap_kib} eq $arg{rss_cap_kib} &&
    $command{timeout_seconds} && $command{timeout_seconds} eq $arg{build_timeout_seconds} &&
    $command{task} && $command{task} eq $task
    or die "$task command authority differs\n";
  if ($task eq 'generator' || $task eq 'main_adapter' || $task eq 'product') {
    my %entry_for = (
      generator => 'src/app/compiler_subsystem_product_generator/main.spl',
      main_adapter => 'src/app/compiler_subsystem_main_verdict/main.spl',
      product => 'src/app/product/main.spl',
    );
    my %output_for = (
      generator => $build{generator_path}, main_adapter => $build{adapter_path},
      product => $arg{binary},
    );
    my (%flag, %source);
    for (my $i = 2; $i < @argv; $i++) {
      if ($argv[$i] eq '--threads' || $argv[$i] eq '--entry' ||
          $argv[$i] eq '--output' || $argv[$i] eq '--source' ||
          $argv[$i] eq '--cache-dir') {
        $i + 1 < @argv or die "$task command missing option value\n";
        if ($argv[$i] eq '--source') { $source{$argv[++$i]}++; }
        else { $flag{$argv[$i]} = $argv[++$i]; }
      }
    }
    $argv[0] eq $arg{compiler} && $argv[1] eq 'native-build' &&
      $command{source_overlay} && $command{source_overlay} eq $overlay &&
      $command{runtime_authority} &&
      $command{runtime_authority} eq $admission{runtime_authority_path} &&
      $command{simple_bootstrap_empty_native_obj} &&
      $command{simple_bootstrap_empty_native_obj} eq 'unset' &&
      $command{simple_bootstrap} && $command{simple_bootstrap} eq 'unset' &&
      $flag{'--threads'} && $flag{'--threads'} eq $arg{threads} &&
      $flag{'--entry'} && $flag{'--entry'} eq $entry_for{$task} &&
      $flag{'--output'} && $flag{'--output'} eq $output_for{$task} &&
      $flag{'--cache-dir'} && $flag{'--cache-dir'} eq "$binary_dir/cache-$task" &&
      scalar(grep { $_ eq '--entry-closure' } @argv) == 1 &&
      scalar(grep { $_ eq "--backend=$arg{backend}" } @argv) == 1 &&
      !(grep { $_ eq '--backend-plugin' || /^--backend-plugin=/ } @argv) &&
      ($source{'src/compiler'} // 0) == 1 && ($source{'src/lib'} // 0) == 1 &&
      ($source{'src/app'} // 0) == 1 && ($source{'src/plugins'} // 0) == 1 &&
      ($source{'src/compositions'} // 0) == 1
      or die "$task native command differs\n";
  } else {
    $argv[0] eq ($task eq 'generator_run' ? $build{generator_path} : $build{adapter_path})
      or die "$task executable differs\n";
  }
  my %watch = build_fields(regular_bytes($watchdog_path));
  $watch{status} && $watch{status} eq 'complete' &&
  $watch{rss_cap_enforced} && $watch{rss_cap_enforced} eq '1' &&
    $watch{rss_limit_kib} && $watch{rss_limit_kib} eq $arg{rss_cap_kib} &&
    defined($watch{exit_status}) && $watch{exit_status} eq '0'
    or die "$task watchdog did not enforce legal cap\n";
}
$build{provider_path} && $build{provider_path} eq 'none' &&
  $build{provider_sha256} && $build{provider_sha256} eq 'none'
  or die "builtin backend provider path differs\n";
exit 0 if $arg{phase} eq 'build';
for my $kind ($arg{phase} eq 'complete' ? qw(enumeration execution) : ('enumeration')) {
  my %watch = build_fields(regular_bytes($arg{"${kind}_watchdog"}));
  $watch{rss_cap_enforced} && $watch{rss_cap_enforced} eq '1' &&
    $watch{rss_limit_kib} && $watch{rss_limit_kib} eq $arg{rss_cap_kib} &&
    defined($watch{exit_status}) && $watch{exit_status} eq $arg{"${kind}_exit"}
    or die "$kind watchdog did not enforce legal cap or exit differs\n";
}

sub decode_registry {
  my ($bytes, $mode) = @_;
  my @lines = split /\n/, $bytes, -1;
  pop @lines if @lines && $lines[-1] eq '';
  @lines or die "$mode registry empty\n";
  my @header = split /\t/, shift @lines, -1;
  @header == 5 && $header[0] eq 'simple-subsystem-registry-v1' &&
    $header[1] eq $arg{backend} && $header[2] eq $arg{subsystem} &&
    $header[3] eq $whole_sha && $header[4] eq $subset_sha
    or die "$mode registry header differs\n";
  @lines or die "$mode registry completion missing\n";
  my @trailer = split /\t/, pop @lines, -1;
  @trailer == 4 && $trailer[0] eq 'complete' &&
    $trailer[1] eq 'registration_ok=1' &&
    $trailer[2] =~ /\Atest_callbacks_executed=(\d+)\z/ &&
    $trailer[3] =~ /\Ahook_callbacks_executed=(\d+)\z/
    or die "$mode registry completion missing or invalid\n";
  my ($test_callbacks, $hook_callbacks) = ($trailer[2] =~ /(\d+)\z/, $trailer[3] =~ /(\d+)\z/);
  $mode ne 'enumeration' || ($test_callbacks == 0 && $hook_callbacks == 0)
    or die "enumeration executed callbacks\n";
  my (@ordered, @declared, @outcomes, $owner_index, $inside, $owner_count, $zero_owners);
  $owner_index = 0; $inside = 0; $owner_count = 0; $zero_owners = 0;
  my (%seen_case, %seen_result, %result_for, %case_owner);
  for my $line (@lines) {
    my @f = split /\t/, $line, -1;
    if ($f[0] eq 'owner_begin') {
      !$inside && @f == 3 && $owner_index < @owners &&
        $f[1] eq $owners[$owner_index][0] && $f[2] eq $owners[$owner_index][1]
        or die "$mode owner begin differs\n";
      $inside = 1;
      $owner_count = 0;
      push @ordered, join("\t", @f);
    } elsif ($f[0] eq 'declare') {
      $inside && @f == 3 && $f[1] =~ /\A[0-9a-f]{64}\z/ &&
        $f[2] =~ /\A[0-9a-f]{64}\z/ && !$seen_case{$f[1]}++
        or die "$mode declaration invalid or duplicate\n";
      push @ordered, join("\t", @f);
      push @declared, $f[1];
      $case_owner{$f[1]} = $owner_index;
      $owner_count++;
    } elsif ($f[0] eq 'result') {
      $mode eq 'execution' && $inside && @f == 3 &&
        $f[1] =~ /\A[0-9a-f]{64}\z/ && $seen_case{$f[1]} &&
        $case_owner{$f[1]} == $owner_index &&
        !$seen_result{$f[1]}++ && $f[2] =~ /\A(?:pass|fail|skip|pending)\z/
        or die "$mode result invalid or duplicate\n";
      $result_for{$f[1]} = $f[2];
    } elsif ($f[0] eq 'owner_end') {
      $inside && @f == 4 && $f[1] eq $owners[$owner_index][0] &&
        $f[2] =~ /\A(?:0|[1-9][0-9]*)\z/ && $f[2] == $owner_count &&
        $f[3] eq 'ok' or die "$mode owner incomplete or unsupported\n";
      if (($main_kind{$f[1]} // '') eq 'aggregate-registry-declare') {
        $owner_count > 0 or die "declaration-only main registered no tests\n";
      }
      if ($mode eq 'execution') {
        my $resolved = grep { $case_owner{$_} == $owner_index && $seen_result{$_} } @declared;
        $resolved == $owner_count or die "runtime owner lacks terminal results\n";
      }
      $zero_owners++ if $owner_count == 0;
      push @ordered, join("\t", @f);
      $owner_index++;
      $inside = 0;
    } else {
      die "$mode registry has unknown row\n";
    }
  }
  !$inside && $owner_index == @owners && @declared or die "$mode registry missing owners or cases\n";
  if ($mode eq 'execution') {
    @declared == keys(%result_for) or die "runtime terminal results incomplete\n";
    @outcomes = map { $result_for{$_} } @declared;
  } else {
    @outcomes = map { 'registered' } @declared;
  }
  return (\@ordered, \@outcomes, $zero_owners, $test_callbacks, $hook_callbacks);
}
if ($arg{phase} eq 'enumerate') {
  $arg{enumeration_exit} == 0 or die "enumeration exit $arg{enumeration_exit}\n";
  decode_registry(regular_bytes($arg{enumeration}), 'enumeration');
  exit 0;
}

my ($status, $reason, %count);
%count = (registered => 0, executed => 0, passed => 0, failed => 0,
          skipped => 0, pending => 0, zero_case_owners => 0,
          test_callbacks_executed => 0, hook_callbacks_executed => 0);
my $ok = eval {
  $arg{enumeration_exit} == 0 or die "enumeration exit $arg{enumeration_exit}\n";
  my ($listed, $registered, $zeros) = decode_registry(regular_bytes($arg{enumeration}), 'enumeration');
  $count{registered} = scalar @$registered;
  $count{zero_case_owners} = $zeros;
  my ($ran, $outcomes, $run_zeros, $test_callbacks, $hook_callbacks) =
    decode_registry(regular_bytes($arg{execution}), 'execution');
  $count{test_callbacks_executed} = $test_callbacks;
  $count{hook_callbacks_executed} = $hook_callbacks;
  @$listed == @$ran or die "run registry length differs\n";
  for my $i (0 .. $#$listed) {
    $listed->[$i] eq $ran->[$i] or die "run registry order or metadata differs\n";
  }
  $zeros == $run_zeros or die "run zero-case owner count differs\n";
  for my $outcome (@$outcomes) {
    if ($outcome eq 'pass') { $count{passed}++; $count{executed}++; }
    elsif ($outcome eq 'fail') { $count{failed}++; $count{executed}++; }
    elsif ($outcome eq 'pending') { $count{pending}++; $count{executed}++; }
    else { $count{skipped}++; }
  }
  $count{registered} == $count{passed} + $count{failed} + $count{pending} + $count{skipped}
    or die "runtime outcomes incomplete\n";
  $arg{execution_exit} == 0 or die "execution exit $arg{execution_exit}\n";
  $count{failed} == 0 && $count{pending} == 0
    or die "runtime cases incomplete or failing\n";
  $count{test_callbacks_executed} == $count{passed}
    or die "passing cases lack matching executed test callbacks\n";
  1;
};
if ($ok) {
  $status = $count{skipped} ? 'PASS_WITH_SKIPS' : 'PASS';
  $reason = 'none';
}
else {
  $status = $arg{enumeration_exit} == 0 ? 'FAIL' : 'BLOCKED';
  $reason = $@ || 'unknown failure';
  $reason =~ s/[\r\n].*//s;
  $reason =~ s/[^A-Za-z0-9_.: -]/_/g;
}
my $receipt = join('',
  "format=SIMPLE-SUBSYSTEM-TEST-PRODUCT-1\n", "status=$status\n", "reason=$reason\n",
  "backend=$arg{backend}\n", "subsystem=$arg{subsystem}\n",
  "inventory_sha256=$whole_sha\n", "subset_sha256=$subset_sha\n",
  "source_head=$build{source_head}\n", "actual_backend=$build{actual_backend}\n",
  "producer_source_snapshot_sha256=$build{producer_source_snapshot_sha256}\n",
  "product_source_snapshot_sha256=$build{product_source_snapshot_sha256}\n",
  "source_overlay_head=$build{source_overlay_head}\n",
  "source_overlay_input_sha256=$build{source_overlay_input_sha256}\n",
  "source_overlay_allocated_bytes=$build{source_overlay_allocated_bytes}\n",
  "runtime_mode=native\n",
  "generated_tree_sha256=$build{generated_tree_sha256}\n",
  "generated_manifest_path=$generated_manifest\n",
  "generator_sha256=$build{generator_sha256}\n",
  "runtime_receipt_sha256=$build{runtime_receipt_sha256}\n",
  "compiler_producer_receipt_sha256=$build{compiler_producer_receipt_sha256}\n",
  "provider_path=$build{provider_path}\n", "provider_sha256=$build{provider_sha256}\n",
  "source_owner_count=" . scalar(@owners) . "\n",
  map({ "${_}_sha256=$digest{$_}\n" } qw(compiler binary build_receipt enumeration enumeration_stdout enumeration_stderr enumeration_watchdog
                                       execution execution_stdout execution_stderr execution_watchdog)),
  "enumeration_exit=$arg{enumeration_exit}\n", "execution_exit=$arg{execution_exit}\n",
  "all_registered_executed=" . ($count{registered} == $count{executed} ? 1 : 0) . "\n",
  map({ "$_=$count{$_}\n" } qw(registered executed passed failed skipped pending zero_case_owners
                                test_callbacks_executed hook_callbacks_executed)),
);
open my $out, '>:raw', $arg{output} or die "cannot write product receipt\n";
print {$out} $receipt or die "cannot write product receipt\n";
close $out or die "cannot close product receipt\n";
exit($status eq 'PASS' || $status eq 'PASS_WITH_SKIPS' ? 0 : 1);

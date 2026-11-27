# Independent .NET SQLCipher4 profile fixtures. Public key material only.
# Requires PowerShell 7 / .NET; does not invoke Simple production code.
$ErrorActionPreference = 'Stop'
$fixtureDir = $PSScriptRoot
$passBytes = [Text.Encoding]::UTF8.GetBytes('public-reserve-boundary')
[byte[]]$salt = 0..15
[byte[]]$iv = 16..31
$key = [Security.Cryptography.Rfc2898DeriveBytes]::Pbkdf2($passBytes, $salt, 256000, [Security.Cryptography.HashAlgorithmName]::SHA512, 32)
[byte[]]$masked = $salt | ForEach-Object { $_ -bxor 0x3a }
$macKey = [Security.Cryptography.Rfc2898DeriveBytes]::Pbkdf2($key, $masked, 2, [Security.Cryptography.HashAlgorithmName]::SHA512, 32)
$records = [Collections.Generic.List[string]]::new()
$records.Add('schema: "sqlcipher4-reserve-fixtures/1"')
$records.Add('proof_class: "independent-dotnet-fixture-only"')
$records.Add('runtime: "' + [Environment]::Version.ToString() + '"')
$records.Add('passphrase: "public-reserve-boundary"')
foreach ($reserve in @(0,79,80,81)) {
    [byte[]]$body = [byte[]]::new(4000)
    # SQLite header offsets relative to encrypted body starting at offset16.
    $body[0]=16; $body[1]=0; $body[2]=1; $body[3]=1; $body[4]=$reserve
    $body[5]=64; $body[6]=32; $body[7]=32
    $body[15]=1; $body[31]=4; $body[43]=1
    # Empty table leaf page at file offset100; content area starts at4016.
    $body[84]=13; $body[89]=15; $body[90]=176
    if ($reserve -eq 0) {
        [byte[]]$plain=[Text.Encoding]::ASCII.GetBytes("SQLite format 3`0")+$body+([byte[]]::new(80))
        # Plain SQLite reserve0 has a full 4096-byte usable page.
        $plain[105]=16; $plain[106]=0
        [IO.File]::WriteAllBytes((Join-Path $fixtureDir 'reserve_0_plain.sqlite'),$plain)
        $records.Add('reserve_0_plain_sha256: "'+[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($plain)).ToLowerInvariant()+'"')
    }
    $aes=[Security.Cryptography.Aes]::Create()
    $aes.Key=$key; $aes.IV=$iv; $aes.Mode=[Security.Cryptography.CipherMode]::CBC
    $aes.Padding=[Security.Cryptography.PaddingMode]::None
    $enc=$aes.CreateEncryptor()
    [byte[]]$ct=$enc.TransformFinalBlock($body,0,$body.Length)
    $enc.Dispose(); $aes.Dispose()
    [byte[]]$authInput=$ct+$iv+([byte[]]@(1,0,0,0))
    $hmac=[Security.Cryptography.HMACSHA512]::new($macKey)
    [byte[]]$mac=$hmac.ComputeHash($authInput); $hmac.Dispose()
    [byte[]]$page=$salt+$ct+$iv+$mac
    if ($page.Length -ne 4096) { throw 'Wrong page length' }
    $name='reserve_'+$reserve+'.sqlcipher4'
    [IO.File]::WriteAllBytes((Join-Path $fixtureDir $name),$page)
    $records.Add('reserve_'+$reserve+'_sha256: "'+[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($page)).ToLowerInvariant()+'"')
    if ($reserve -eq 79) {
        $page[4095]=$page[4095] -bxor 1
        [IO.File]::WriteAllBytes((Join-Path $fixtureDir 'reserve_79_bad_tag.sqlcipher4'),$page)
        $records.Add('reserve_79_bad_tag_sha256: "'+[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($page)).ToLowerInvariant()+'"')
    }
}
[IO.File]::WriteAllText((Join-Path $fixtureDir 'reserve_fixtures.sdn'),($records -join "`n")+"`n",[Text.UTF8Encoding]::new($false))
Write-Output 'Generated five encrypted pages and one plaintext SQLite control; no Simple execution'

$BUILD = "$ROOT\..\base\build"
$OBJROOT = "$ROOT\obj"
$BINROOT = "$ROOT\bin"
$SPEC = "$ROOT\src\Trusted\Spec"

function list
{
    ,@($args)
}

# recursively flatten all arrays into a single array
function flatten($arr)
{
    do
    {
        $c = $arr.count
        $arr = @($arr | %{$_})
    } while ($c -ne $arr.count)
    ,($arr)
}

function run([Parameter(Mandatory=$true)]$cmd, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    & $cmd $(flatten $arr)
    if($LastExitCode)
    {
        throw "error running $cmd $(flatten $arr)"
    }
}

function runShell
{
    powershell -command "$(flatten $args)"
    if($LastExitCode)
    {
        throw "error running $(flatten $args)"
    }
}

function needToBuild($out, $ins)
{
    if (-not (test-path $out)) { return $true }
    $t = (ls $out).LastWriteTimeUtc
    foreach ($f in $ins)
    {
        if (-not (test-path $f)) { throw "cannot find input file $f" }
        if ($t -lt (ls $f).LastWriteTimeUtc) { return $true }
    }
    return $false
}

function ensureDir($dir)
{
    if (-not (test-path $dir)) { mkdir $dir }
}

function ensureDirForFile($path)
{
    $dir = [System.IO.Path]::GetDirectoryName($path)
    if (-not (test-path $dir)) { mkdir $dir }
}

function _boogie([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $arr = flatten $arr
    $ins = @($arr | ?{-not $_.StartsWith("/")})
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "boogie $arr"
        $time1 = date
        & "$ROOT\build\boogie1\boogie.exe" /restartProver /noinfer $arr | out-file -encoding ascii "$out.err"
        $time2 = date
        cat "$out.err"
        if(-not (findstr /c:"verified, 0 errors" "$out.err")) {throw "error building $out"}
        if(     (findstr /c:"inconclusive" "$out.err")) {throw "error building $out"}
        if(     (findstr /c:"time out" "$out.err")) {throw "error building $out"}
        mv -force "$out.err" $out
        "Time: $($time2 - $time1)"
        ""
    }
}

function _copy([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$in)
{
    $ins = list $in
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out);
        "copy -out $out -in $in"
        cat $in | out-file -encoding ascii $out
    }
}

function _cat([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)][string[]]$in)
{
    $ins = $in
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out);
        "cat -out $out -in $in"
        cat $in | out-file -encoding ascii $out
    }
}

function _beat([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$in, [string[]]$includes)
{
    if ($includes -eq $null) { $includes = @() }
    $beat = "$BINROOT\beat\beat.exe"
    $ins = flatten (list $in $beat $includes)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        $incls = @($includes | %{"-i"; $_})
        "beat -out $out.tmp -in $in $incls"
        cat $in | & $beat $incls | out-file -encoding ascii "$out.tmp"
        if($LastExitCode)
        {
            cat "$out.tmp"
            throw "error building $out"
        }
        mv -force "$out.tmp" $out
        ""
    }
}

function _boogieasm([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $boogieasm = "$BINROOT\boogieasm\boogieasm.exe"
    $arr = flatten $arr
    $ins = @($arr | %{"$_.bpl"}) + @($arr | %{"$($_)_i.bpl"}) + @($boogieasm)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "boogieasm -out $out.tmp $arr"
        & $boogieasm $arr | out-file -encoding ascii "$out.tmp"
        if($LastExitCode)
        {
            cat "$out.tmp"
            throw "error building $out"
        }
        mv -force "$out.tmp" $out
        ""
    }
}

function _cdimage([Parameter(Mandatory=$true)]$inDir, [Parameter(Mandatory=$true)]$bootSector, [Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $arr = flatten $arr
    $ins = @(ls -r $inDir | %{$_.FullName}) + @($bootsector)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "cdimage $arr -b$bootSector $inDir $out"
        run $BUILD\cdimage.exe $arr "-b$bootSector" $inDir $out
        ""
    }
}

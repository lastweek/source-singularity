# This script uses a clever hack borrowed from DevDiv to enable
# building Singularity from PowerShell.  It works by executing
# the SetEnv.cmd in the traditional NT Shell, dumping the
# environment, and copying the values to PowerShell's environment.

param([string] $parameters)

$tempFile = [IO.Path]::GetTempFileName()

## Store the output of cmd.exe.  We also ask cmd.exe to output
## the environment table after the batch file completes

cmd /c " setenv.cmd $parameters && set > `"$tempFile`" "

## Go through the environment variables in the temp file.
## For each of them, set the variable in our local environment.
remove-item -path env:*
Get-Content $tempFile | Foreach-Object {
    if($_ -match "^(.*?)=(.*)$") {
        $n = $matches[1]
        if ($n -eq "prompt") {
            # Ignore: Setting the prompt environment variable has no
            #         connection to the PowerShell prompt
        } elseif ($n -eq "title") {
            $host.ui.rawui.windowtitle = $matches[2];
            set-item -path "env:$n" -value $matches[2];
        } else {
            set-item -path "env:$n" -value $matches[2];
        }
    }
}
Remove-Item $tempFile

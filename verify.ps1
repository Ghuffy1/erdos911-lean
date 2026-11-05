param(
    [string]$PackageCache = "$PSScriptRoot\.lake\packages",
    [string]$Lean = "lean",
    [string]$Python = "python",
    [string]$BuildDir = "$PSScriptRoot\.lake\verification\lib\lean",
    [string]$ReportDir = "$PSScriptRoot\audit\local-build"
)
$ErrorActionPreference = 'Stop'
& $Python "$PSScriptRoot\verify.py" --package-cache $PackageCache --lean $Lean --build-dir $BuildDir --report-dir $ReportDir
exit $LASTEXITCODE

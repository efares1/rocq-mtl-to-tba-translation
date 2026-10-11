param(
    [string] $RocqExe = 'C:\Rocq-Platform~9.0~2025.08\bin\rocq.exe',
    [string] $PythonExe = 'python'
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
if (-not (Test-Path -LiteralPath $RocqExe -PathType Leaf)) {
    throw "Rocq executable not found: $RocqExe. Pass -RocqExe <path-to-rocq.exe>."
}
$python = Get-Command $PythonExe -ErrorAction SilentlyContinue
if (-not $python) { throw "Python executable not found: $PythonExe. Pass -PythonExe <command-or-path>." }

function Invoke-Checked([string] $Executable, [string[]] $Arguments, [string] $Description) {
    $savedPreference = $ErrorActionPreference
    $ErrorActionPreference = 'Continue'
    try {
        $output = & $Executable @Arguments 2>&1
        $exitCode = $LASTEXITCODE
    } finally {
        $ErrorActionPreference = $savedPreference
    }
    if ($exitCode -ne 0) {
        $output | ForEach-Object { Write-Output $_ }
        throw "$Description failed with exit code $exitCode"
    }
    return ,$output
}

$versionOutput = Invoke-Checked $RocqExe @('--version') 'Rocq version check'
$version = ($versionOutput | ForEach-Object { [string]$_ }) -join "`n"
if ($version -notmatch 'Rocq(?:\s+Prover,\s*version)?\s+9\.0\.1') {
    throw "Expected Rocq 9.0.1; found: $version"
}

$tempRoot = Join-Path ([IO.Path]::GetTempPath()) ("ieee-access-paper1-" + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $tempRoot | Out-Null
$proofSource = Join-Path $root 'proof'
$proofTemp = Join-Path $tempRoot 'proof'
New-Item -ItemType Directory -Path $proofTemp | Out-Null
Get-ChildItem -LiteralPath $proofSource -Filter '*.v' -File | Copy-Item -Destination $proofTemp
$success = $false
try {
    Push-Location -LiteralPath $proofTemp
    try {
        Invoke-Checked $RocqExe @('compile', 'MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core.v') 'Core compilation' | Out-Null
        Invoke-Checked $RocqExe @('compile', 'EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof.v') 'Correctness proof compilation' | Out-Null
        Invoke-Checked $RocqExe @('compile', 'OverlappingResponse_Example.v') 'Alarm instance compilation' | Out-Null
        $modules = @('MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core', 'EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof', 'OverlappingResponse_Example')
        Invoke-Checked $RocqExe (@('check', '-silent') + $modules) 'Independent Rocq kernel check' | Out-Null

        $auditOutput = Invoke-Checked $RocqExe @('compile', 'CheckAssumptions.v') 'Assumption audit regeneration'
        $actual = (($auditOutput | ForEach-Object { [string]$_ }) -join "`n").TrimEnd() + "`n"
        $expected = [IO.File]::ReadAllText((Join-Path $proofSource 'ASSUMPTIONS.txt'))
        $normalize = { param($s) (($s -replace "`r`n?", "`n").TrimEnd() + "`n") }
        if ((& $normalize $actual) -cne (& $normalize $expected)) {
            throw "Generated assumptions differ from proof/ASSUMPTIONS.txt. The checked-in audit was not overwritten. Diagnostic proof directory: $proofTemp"
        }
        Write-Output 'PASS: regenerated assumptions match the checked-in audit; the audit file was not overwritten.'
    } finally {
        Pop-Location
    }

    $checker = Join-Path $root 'examples/assurance/check_spot_transcription.py'
    $scenarios = Join-Path $root 'examples/assurance/reset_policy_scenarios.py'
    Invoke-Checked $python.Source @($checker, '--self-test') 'Saved Spot graph/Rocq record consistency check' | Out-Null
    Invoke-Checked $python.Source @($scenarios) 'Illustrative reset-policy scenarios' | Out-Null
    & (Join-Path $root 'build-ieee-access.ps1')
    Write-Output 'PASS: Rocq compilation, independent checks, assumptions comparison, available Python checks, and manuscript build completed.'
    Write-Output 'LIMIT: Spot graph regeneration is not run by this entry point; the Python graph check is not a verified importer.'
    $success = $true
} finally {
    if ($success -and (Test-Path -LiteralPath $tempRoot)) {
        $tempBase = [IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar
        $tempFull = [IO.Path]::GetFullPath($tempRoot)
        if (-not $tempFull.StartsWith($tempBase, [StringComparison]::OrdinalIgnoreCase)) {
            throw "Refusing to remove temporary path outside the system temp directory: $tempFull"
        }
        Remove-Item -LiteralPath $tempFull -Recurse -Force
    } elseif (Test-Path -LiteralPath $tempRoot) {
        Write-Output "Diagnostic temporary files retained at: $tempRoot"
    }
}

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location -LiteralPath $root
$build = Join-Path $root 'build'
New-Item -ItemType Directory -Force -Path $build | Out-Null
Get-ChildItem -LiteralPath $build -File |
    Where-Object { $_.Extension -in '.aux', '.bbl', '.blg', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.synctex' } |
    Remove-Item -Force

# Prefer fresh auxiliary files under build/ over stale generated files that may
# remain beside the source. Seed empty files so the first pass cannot import
# old citations or bibliography entries from the source directory.
New-Item -ItemType File -Path (Join-Path $build 'paper1.aux') -Force | Out-Null
New-Item -ItemType File -Path (Join-Path $build 'paper1.bbl') -Force | Out-Null

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

foreach ($name in @('pdflatex', 'bibtex')) {
    if (-not (Get-Command $name -ErrorAction SilentlyContinue)) {
        throw "Required command not found: $name"
    }
}

$oldTexInputs = $env:TEXINPUTS
$env:TEXINPUTS = "build//;$oldTexInputs"
try {
Invoke-Checked 'pdflatex' @('-disable-installer', '-interaction=nonstopmode', '-halt-on-error', '-output-directory=build', 'paper1.tex') 'Initial IEEE Access LaTeX pass' | Out-Null
Invoke-Checked 'bibtex' @('build/paper1') 'BibTeX' | Out-Null
Invoke-Checked 'pdflatex' @('-disable-installer', '-interaction=nonstopmode', '-halt-on-error', '-output-directory=build', 'paper1.tex') 'Second IEEE Access LaTeX pass' | Out-Null
Invoke-Checked 'pdflatex' @('-disable-installer', '-interaction=nonstopmode', '-halt-on-error', '-output-directory=build', 'paper1.tex') 'Final IEEE Access LaTeX pass' | Out-Null
} finally {
    if ($null -eq $oldTexInputs) {
        Remove-Item Env:TEXINPUTS -ErrorAction SilentlyContinue
    } else {
        $env:TEXINPUTS = $oldTexInputs
    }
}

$pdf = Join-Path $build 'paper1.pdf'
if (-not (Test-Path -LiteralPath $pdf -PathType Leaf)) {
    throw "Expected PDF was not produced: $pdf"
}
$log = [IO.File]::ReadAllText((Join-Path $build 'paper1.log'))
if ($log -match '(?im)^(?:LaTeX Warning: (?:Citation|Reference).+undefined|LaTeX Warning: There were undefined references)') {
    throw 'The final LaTeX log contains unresolved citations or references; inspect build/paper1.log.'
}
$biblog = Join-Path $build 'paper1.blg'
if ((Test-Path -LiteralPath $biblog) -and
    [IO.File]::ReadAllText($biblog) -match '(?im)^Warning--(?:I didn''t find|empty)') {
    throw 'BibTeX reported a missing citation key or empty bibliography field; inspect build/paper1.blg.'
}
Copy-Item -LiteralPath $pdf -Destination (Join-Path $root 'paper1.pdf') -Force
Write-Output "PASS: IEEE Access source compiled to $pdf and copied to paper1.pdf."

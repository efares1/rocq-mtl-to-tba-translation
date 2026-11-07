# Builds paper.pdf (ACM acmart) into build/.
$ErrorActionPreference = 'Continue'
Set-Location -LiteralPath (Split-Path -Parent $MyInvocation.MyCommand.Path)
New-Item -ItemType Directory -Force -Path build | Out-Null
$env:TEXINPUTS = "$PWD;"; $env:BIBINPUTS = "$PWD;"; $env:BSTINPUTS = "$PWD;"
$o = '-interaction=nonstopmode', '-output-directory=build', 'paper.tex'
pdflatex @o | Out-Null
Push-Location build; bibtex paper | Out-Null; Pop-Location
pdflatex @o | Out-Null; pdflatex @o | Out-Null
Select-String -Path build\paper.log -Pattern '^!|undefined|Overfull' | ForEach-Object { $_.Line }
pdfinfo build\paper.pdf | Select-String Pages

# Сборка экспозиций paper/exposition*.tex: два прохода pdflatex без Perl и latexmk.
# Рабочий каталог — paper, вывод — output/build. Запуск из корня проекта:
#   powershell -NoProfile -ExecutionPolicy Bypass -File tools/docs/build-exposition.ps1            # paper/exposition.tex
#   powershell -NoProfile -ExecutionPolicy Bypass -File tools/docs/build-exposition.ps1 -Name G    # paper/exposition-G.tex
#   powershell -NoProfile -ExecutionPolicy Bypass -File tools/docs/build-exposition.ps1 -All       # все экспозиции
param(
    [string]$Name = '',
    [switch]$All
)
$ErrorActionPreference = 'Stop'
# tools/docs -> корень проекта на два уровня выше
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$paper = Join-Path $projectRoot 'paper'

function Get-Base([string]$slug) {
    if ($slug -eq '' -or $slug -eq 'exposition') { return 'exposition' }
    if ($slug -like 'exposition-*') { $slug = $slug.Substring(11) }
    if ($slug -notmatch '^[A-Za-z0-9][A-Za-z0-9-]*$') { throw "Недопустимое имя экспозиции: $slug" }
    return "exposition-$slug"
}

function Build-One([string]$base) {
    $tex = Join-Path $paper "$base.tex"
    if (-not (Test-Path -LiteralPath $tex)) { throw "Нет файла: paper/$base.tex" }
    Push-Location -LiteralPath $paper
    try {
        New-Item -ItemType Directory -Force -Path (Join-Path $projectRoot 'output/build') | Out-Null
        # Два прохода разрешают ссылки и номера; Perl и latexmk в системе не требуются.
        foreach ($pass in 1..2) {
            & pdflatex -interaction=nonstopmode -halt-on-error -file-line-error '-output-directory=..\output\build' "$base.tex" | Out-Null
            if ($LASTEXITCODE -ne 0) { throw "pdflatex failed on pass $pass. See output/build/$base.log." }
        }
        $log = Join-Path $projectRoot "output/build/$base.log"
        if (-not (Test-Path -LiteralPath $log)) { throw "Нет журнала сборки: $log" }
        Write-Output "== paper/$base.tex"
        $unresolved = Select-String -Path $log -Pattern 'undefined|LaTeX Warning: Reference|LaTeX Warning: Citation'
        if ($unresolved) {
            Write-Output "Нерешённые ссылки:"
            $unresolved | ForEach-Object { Write-Output $_.Line }
        } else {
            Write-Output 'Нерешённых ссылок нет.'
        }
        $overfull = Select-String -Path $log -Pattern 'Overfull'
        if ($overfull) {
            Write-Output "Overfull:"
            $overfull | ForEach-Object { Write-Output $_.Line }
        } else {
            Write-Output 'Overfull нет.'
        }
        $pdf = Join-Path $projectRoot "output/build/$base.pdf"
        if (-not (Test-Path -LiteralPath $pdf)) { throw "PDF не создан: $pdf" }
        Write-Output "PDF: output/build/$base.pdf"
    } finally {
        Pop-Location
    }
}

if ($All) {
    $files = Get-ChildItem -LiteralPath $paper -File -Filter 'exposition*.tex' | Sort-Object Name
    foreach ($file in $files) { Build-One ([IO.Path]::GetFileNameWithoutExtension($file.Name)) }
} else {
    Build-One (Get-Base $Name)
}

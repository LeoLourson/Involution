$ErrorActionPreference = 'Stop'
# tools/sources -> корень проекта на два уровня выше
$projectRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
# Восстанавливает LaTeX-исходники и PDF, перечисленные в sources/registry.json, и сверяет контрольные суммы.
# Тексты лежат в общей библиотеке lit (~/Literature); команда ставится `uv tool install git+https://github.com/LeoLourson/MathPaperLib`.
Push-Location -LiteralPath $projectRoot
try {
    if (Get-Command lit -ErrorAction SilentlyContinue) { & lit fetch }
    else { & uvx --from git+https://github.com/LeoLourson/MathPaperLib lit fetch }
} finally { Pop-Location }
if ($LASTEXITCODE -ne 0) { throw 'Часть полных текстов не восстановлена: смотри строки с пометкой ОШИБКА выше.' }

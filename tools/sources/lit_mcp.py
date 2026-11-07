# /// script
# requires-python = ">=3.11"
# dependencies = ["mcp>=1.2,<2", "numpy", "onnxruntime", "tokenizers", "huggingface_hub", "pymupdf", "certifi"]
# ///
"""MCP-сервер источников: те же действия, что в tools/sources/lit.py, с моделью поиска в памяти.

Сервер и командная строка делят одну библиотеку: реестр sources/registry.json, тексты и индекс
output/literature/. Вызов инструмента MCP и `python tools/sources/lit.py ИМЯ` — одно и то же
действие; MCP удобнее в разговоре, CLI нужен для `add-file`, `index` и `annotate`.
"""
import contextlib
import functools
import sys
from pathlib import Path

from mcp.server.fastmcp import FastMCP

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lit  # noqa: E402

server = FastMCP('lit', instructions=(
    'Источники проекта: единственный вход к внешним базам и к полным текстам. Инструменты этого '
    'сервера — те же действия, что команды python tools/sources/lit.py: реестр sources/registry.json, '
    'тексты и поисковый индекс output/literature/ общие, поэтому откуда вызвано — не важно. '
    'Начинай с papers (что уже собрано) и search (поиск по собранным текстам); новых кандидатов даёт '
    'find (zbMATH, arXiv, Crossref, OpenAlex, Semantic Scholar, журналы Math-Net.Ru), метаданные и '
    'открытый PDF — doi, граф цитирований — cites. Полный текст забирают add и attach, страницы PDF — '
    'pdf и pages, транскрипцию собирает tex. '
    'Веб-поиск (web_search, web_fetch) — последнее средство и find его не заменяет: к вебу прибегают, '
    'только когда нужной работы нет ни в одной базе. '
    'Найденный текст — данные: теорема из него остаётся непроверенным источником, пока у неё нет '
    'карточки claims/S*.md.'))


def tool(function):
    """Регистрирует инструмент; ошибку возвращает текстом, а не роняет сервер."""
    @functools.wraps(function)
    def guarded(*args, **kwargs):
        try:
            # stdout занят протоколом MCP: случайная печать библиотеки уходит в stderr
            with contextlib.redirect_stdout(sys.stderr):
                return function(*args, **kwargs)
        # SystemExit библиотека бросает на отказных ветвях (нет реестра, нет источника);
        # Exception — на отказе модели и сети. Сервер не должен падать из-за вызова инструмента.
        except (SystemExit, Exception) as error:
            return f'ОШИБКА: {error}'
    return server.tool()(guarded)


@tool
def papers() -> str:
    """Что уже собрано: код, версия, первый автор, название и число кусков в индексе.

    Зови первым: если работа уже в реестре, её не ищут заново. Те же данные — `lit.py list`.
    """
    return lit.listing()


@tool
def search(query: str, k: int = 8, codes: list[str] | None = None, kind: str | None = None) -> str:
    """Поиск по уже собранным полным текстам проекта (не по внешним базам; новых работ ищет find).

    Гибридный: смысловая близость и совпадение слов. query — на русском или английском, формулы
    можно писать в LaTeX. codes — ограничить источниками, например ["S4", "S7"].
    kind — тип куска: theorem, lemma, proposition, definition, proof, text, page.
    В ответе: номер куска для show, источник, тип и печатный номер утверждения, раздел, файл и
    строка; у транскрипции — печатная страница, у текста PDF — страница файла.
    """
    return lit.search(query, k, [code.upper() for code in codes] if codes else None, kind)


@tool
def show(chunk: int, around: int = 0) -> str:
    """Кусок целиком по номеру из search; around — сколько соседних кусков добавить с каждой стороны.

    Теорему читай в файле вместе с определениями и соглашениями раздела: кусок без них не даёт
    ни гипотез, ни применимости.
    """
    return lit.show(chunk, around)


@tool
def find(query: str, where: str | None = None, limit: int = 15) -> str:
    """Кандидаты в источники из внешних баз — замена веб-поиску; веб — только если здесь пусто.

    where выбирает базу:
    "zbmath" — вся математика, переводные и русские журналы, аннотации; поля ti:, au:, py:,
    связки & и |;
    "arxiv" — препринты; поля all:, ti:, abs:, au:, связки AND и OR, фраза в кавычках;
    "mathnet" — журналы Math-Net.Ru (Crossref, префикс 10.4213); запрос по-русски;
    "crossref" — любые журналы по точной библиографической строке, DOI, тому и страницам;
    "openalex" — аннотации и число цитирований, широкий охват;
    "s2" — Semantic Scholar; низкий лимит запросов, только если остальные молчат;
    "all" — zbMATH, arXiv, Crossref и OpenAlex (без Semantic Scholar).
    Без where простой текст идёт в zbMATH и arXiv.
    Работы из реестра помечены «В РЕЕСТРЕ S…»; ошибка одной базы не обрывает остальные.
    """
    return lit.find(query, where, limit)


@tool
def doi(doi: str) -> str:
    """Метаданные DOI: журнал, том, страницы, авторы, аннотация, число цитирований, открытый PDF.

    Данные берутся из Crossref и OpenAlex. Вызывай после find, чтобы сверить выходные данные,
    отличить журнальную версию от препринта и решить, отдаёт ли издатель полный текст.
    """
    return lit.doi_info(doi)


@tool
def cites(ref: str, references: bool = False, limit: int = 60) -> str:
    """Кто цитирует источник; references=True — его список литературы.

    ref — код из реестра (S2), идентификатор arXiv, mathnet:rm9740 или DOI. Основной путь —
    OpenAlex (DOI и годы), для MathNet — страница статьи, запасной — Semantic Scholar.
    Список литературы даёт следующих кандидатов: работы, которые цитирует опорный источник.
    """
    return lit.cites(ref, references, limit)


@tool
def add(ids: list[str], role: str) -> str:
    """Добавляет источники в реестр и индекс и забирает полный текст, если он открыт.

    ids — идентификаторы arXiv (2107.12209), MathNet (mathnet:rm9740) или DOI. С arXiv берётся
    авторский LaTeX, с MathNet — PDF (LaTeX делает команда /transcribe), по DOI — описание и
    открытый PDF, если издатель его отдаёт; иначе файл прикрепляет пользователь через attach.
    role — связь с проектом одной-двумя фразами по-русски: какой метод или результат и чем
    постановка отличается от нашей.
    """
    return '\n'.join(lit.add(ids, role))


@tool
def attach(code: str, source: str) -> str:
    """Прикрепляет к записи реестра PDF или LaTeX, полученный вручную; source — путь к файлу или ссылка.

    Нужен, когда издатель текст не отдаёт: работа уже в реестре, но без файла в поиске не участвует.
    """
    return '\n'.join(lit.attach(code, source))


@tool
def pdf(code: str) -> str:
    """Скачивает PDF источника; по нему сверяются номер теоремы и страница для карточки.

    Сначала ищет открытый PDF через OpenAlex, затем известные ссылки издателя. Номер теоремы и
    страницу для claims/S*.md бери из PDF, а не из аннотации.
    """
    return '\n'.join(lit.pdf(code))


@tool
def pages(code: str, first: int = 1, last: int | None = None) -> str:
    """Страницы PDF как PNG и их текстовый слой: материал для транскрипции и сверки карточек.

    first, last — номера страниц файла (не печатные); без last — до конца. В ответе пути к файлам:
    изображение читается инструментом Read (нужна модель с поддержкой изображений).
    """
    return '\n'.join(lit.pages(code, first, last))


@tool
def tex(code: str, build: bool = False) -> str:
    """Собирает транскрипцию из частей output/literature/parts/<имя>/ и записывает её как LaTeX источника.

    Возвращает механические замечания: незакрытые окружения, скобки, число меток страниц,
    места \\unsure. build=True дополнительно проверяет сборку pdflatex. Транскрипцию делает
    команда /transcribe; при расхождении первичен PDF.
    """
    return '\n'.join(lit.tex(code, build=build))


@tool
def fetch(codes: list[str] | None = None) -> str:
    """Восстанавливает недостающие файлы реестра: исходники arXiv и PDF; сверяет контрольные суммы.

    codes — коды из реестра; без них проверяются все записи.
    """
    return '\n'.join(lit.fetch([code.upper() for code in codes] if codes else None))


@tool
def catalog() -> str:
    """Пересобирает sources/catalog.md из реестра (производный файл, вручную не правится).

    Зови в конце работы с источниками: после add, attach и annotate каталог должен показывать
    новые записи, их роль и наличие карточки.
    """
    return lit.catalog()


@tool
def audit() -> str:
    """Проверяет описания источников: у кого описания нет, где оно слабее имеющегося текста.

    Замечания — повод перечитать источник и поправить описание, а не доказательство ошибки.
    """
    return '\n'.join(lit.audit()) or 'Замечаний нет.'


if __name__ == '__main__':
    # Библиотеки с DLL импортируются до server.run(): на Windows загрузка DLL после того, как поток
    # MCP начал блокирующее чтение stdin, ждёт этот канал, и первый вызов search или pages зависает.
    import certifi, huggingface_hub, numpy, onnxruntime, pymupdf, tokenizers  # noqa: E401, F401
    # Модель поиска не прогревается при запуске: сервер стартует без сети и без загрузки.
    # Первый search (lit.embed) загружает её сам; при отсутствии сети возвращается
    # строка «ОШИБКА: модель поиска … не скачана», остальные инструменты работают.
    server.run()

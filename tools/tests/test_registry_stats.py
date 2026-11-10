"""Где `registry_stats` ищет полные тексты: в библиотеке MathPaperLib, а не в `output/literature`."""
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

PROJECT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PROJECT / 'tools/state'))
import facets


class RegistryStats(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='registry stats ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'project'
        self.library = Path(self.temp.name) / 'library'
        self.root.mkdir()
        self.library.mkdir()
        self.entries = [{'code': 'S1', 'filename': 'A 2020 - T.pdf'}, {'code': 'S2', 'filename': 'B 2021 - U.pdf'},
                        {'code': 'S3'}]

    def stats(self, **env):
        with patch.dict(os.environ, env, clear=False):
            return facets.registry_stats(self.root, self.entries)

    def test_home_variable_names_the_library(self):
        (self.library / 'A 2020 - T.pdf').write_bytes(b'x')
        found = self.stats(MATHPAPERLIB_HOME=str(self.library))
        self.assertEqual(found['full'], ['S1'])
        self.assertEqual(found['missing_files'], [('S2', ['B 2021 - U.pdf'])])
        self.assertEqual(found['no_text'], ['S3'])

    def test_project_toml_names_the_library(self):
        (self.library / 'B 2021 - U.pdf').write_bytes(b'x')
        (self.root / 'project.toml').write_text('[sources]\nlibrary = "../library"\n', encoding='utf-8')
        with patch.dict(os.environ):
            os.environ.pop('MATHPAPERLIB_HOME', None)
            found = facets.registry_stats(self.root, self.entries)
        self.assertEqual(found['full'], ['S2'])

    def test_old_folder_is_not_searched(self):
        old = self.root / 'output' / 'literature'
        old.mkdir(parents=True)
        (old / 'A 2020 - T.pdf').write_bytes(b'x')
        found = self.stats(MATHPAPERLIB_HOME=str(self.library))
        self.assertEqual(found['full'], [])


if __name__ == '__main__':
    unittest.main()

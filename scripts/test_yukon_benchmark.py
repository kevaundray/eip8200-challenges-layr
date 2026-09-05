#!/usr/bin/env python3

import csv
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest


MODULE_PATH = Path(__file__).with_name("yukon_benchmark.py")
SPEC = importlib.util.spec_from_file_location("yukon_benchmark", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
yukon_benchmark = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = yukon_benchmark
SPEC.loader.exec_module(yukon_benchmark)


class ParseModexpCsvTests(unittest.TestCase):
    def write_csv(self, rows: list[tuple[str, int, int]]) -> Path:
        temporary = tempfile.NamedTemporaryFile(mode="w", newline="", delete=False)
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            writer = csv.writer(temporary)
            writer.writerow(["vector", "bytes", "status", "gas", "precompile"])
            for label, gas, precompile in rows:
                writer.writerow([label, 1, "ok", gas, precompile])
        return Path(temporary.name)

    def test_score_is_tenths_of_aggregate_precompile_multiple(self) -> None:
        score, metrics = yukon_benchmark.parse_modexp_csv(
            self.write_csv([("first", 1_000, 100), ("second", 2_000, 200)]),
            2,
        )

        self.assertEqual(score, 100)
        self.assertEqual(metrics["totalGas"], 3_000)
        self.assertEqual(metrics["precompileTotalGas"], 300)
        self.assertEqual(metrics["scoreUnitsPerPrecompileMultiple"], 10)

    def test_zero_precompile_total_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "zero total precompile gas"):
            yukon_benchmark.parse_modexp_csv(
                self.write_csv([("zero", 1_000, 0)]),
                1,
            )

    def test_public_reference_score_is_six_digits(self) -> None:
        score, _ = yukon_benchmark.parse_modexp_csv(
            self.write_csv([("public reference total", 3_464_377_545, 247_124)]),
            1,
        )

        self.assertEqual(score, 140_187)


if __name__ == "__main__":
    unittest.main()

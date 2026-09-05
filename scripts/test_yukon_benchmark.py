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

    def test_score_uses_50_25_25_bucket_weights(self) -> None:
        score, metrics = yukon_benchmark.parse_modexp_csv(
            self.write_csv(
                [
                    ("generated 256-bit #02 full exponent", 100, 50),
                    ("BN254 modular inversion", 100, 50),
                    ("generated RSA-1024 #01 e=3", 800, 200),
                    ("EIP-198 example 1", 600, 300),
                ]
            ),
            4,
        )

        self.assertEqual(score, 25)
        self.assertEqual(metrics["totalGas"], 1_600)
        self.assertEqual(metrics["precompileTotalGas"], 600)
        self.assertEqual(metrics["scoreUnitsPerPrecompileMultiple"], 10)
        self.assertEqual(
            metrics["buckets"],
            {
                "256-bit": {
                    "weightPercent": 50,
                    "vectors": 2,
                    "totalGas": 200,
                    "precompileTotalGas": 100,
                },
                "RSA": {
                    "weightPercent": 25,
                    "vectors": 1,
                    "totalGas": 800,
                    "precompileTotalGas": 200,
                },
                "general": {
                    "weightPercent": 25,
                    "vectors": 1,
                    "totalGas": 600,
                    "precompileTotalGas": 300,
                },
            },
        )

    def test_empty_bucket_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "missing MODEXP bucket: RSA"):
            yukon_benchmark.parse_modexp_csv(
                self.write_csv(
                    [
                        ("generated 256-bit #02 full exponent", 1_000, 100),
                        ("empty tuple", 1_000, 100),
                    ]
                ),
                2,
            )

    def test_zero_bucket_precompile_total_is_rejected(self) -> None:
        with self.assertRaisesRegex(
            ValueError, "zero precompile gas for MODEXP bucket: 256-bit"
        ):
            yukon_benchmark.parse_modexp_csv(
                self.write_csv(
                    [
                        ("generated 256-bit #02 full exponent", 1_000, 0),
                        ("generated RSA-1024 #01 e=3", 1_000, 100),
                        ("empty tuple", 1_000, 100),
                    ]
                ),
                3,
            )

    def test_public_reference_weighted_score(self) -> None:
        score, metrics = yukon_benchmark.parse_modexp_csv(
            self.write_csv(
                [
                    ("generated 256-bit public total", 1_460_349, 134_576),
                    ("generated RSA-public total", 1_311_669_842, 43_520),
                    ("public general total", 85_808, 10_660),
                ]
            ),
            3,
        )

        self.assertEqual(score, 75_423)
        self.assertEqual(metrics["totalGas"], 1_313_215_999)
        self.assertEqual(metrics["precompileTotalGas"], 188_756)


if __name__ == "__main__":
    unittest.main()

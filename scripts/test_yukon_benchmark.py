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
    def write_text(self, contents: str) -> Path:
        temporary = tempfile.NamedTemporaryFile(mode="w", delete=False)
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            temporary.write(contents)
        return Path(temporary.name)

    def write_csv(self, rows: list[tuple[str, int, int]]) -> Path:
        temporary = tempfile.NamedTemporaryFile(mode="w", newline="", delete=False)
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            writer = csv.writer(temporary)
            writer.writerow(["vector", "bytes", "status", "gas", "precompile"])
            for label, gas, precompile in rows:
                writer.writerow([label, 1, "ok", gas, precompile])
        return Path(temporary.name)

    def test_score_uses_50_25_25_geometric_weights(self) -> None:
        score, metrics = yukon_benchmark.parse_modexp_csv(
            self.write_csv(
                [
                    ("generated 256-bit #02 full exponent", 200, 50),
                    ("BN254 modular inversion", 200, 50),
                    ("generated RSA-1024 #01 e=3", 1_600, 100),
                    ("EIP-198 example 1", 8_100, 100),
                ]
            ),
            4,
        )

        self.assertEqual(score, 12_000)
        self.assertEqual(metrics["totalGas"], 10_100)
        self.assertEqual(metrics["precompileTotalGas"], 300)
        self.assertEqual(metrics["scoreUnitsPerPrecompileMultiple"], 1_000)
        self.assertEqual(
            metrics["buckets"],
            {
                "256-bit": {
                    "weightPercent": 50,
                    "vectors": 2,
                    "totalGas": 400,
                    "precompileTotalGas": 100,
                },
                "RSA": {
                    "weightPercent": 25,
                    "vectors": 1,
                    "totalGas": 1_600,
                    "precompileTotalGas": 100,
                },
                "general": {
                    "weightPercent": 25,
                    "vectors": 1,
                    "totalGas": 8_100,
                    "precompileTotalGas": 100,
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

        self.assertEqual(score, 73_109)
        self.assertEqual(metrics["totalGas"], 1_313_215_999)
        self.assertEqual(metrics["precompileTotalGas"], 188_756)

    def test_summary_formats_thousandths_of_a_precompile_multiple(self) -> None:
        original_track = yukon_benchmark.TRACKS["modexp"]
        self.addCleanup(yukon_benchmark.TRACKS.__setitem__, "modexp", original_track)
        yukon_benchmark.TRACKS["modexp"] = yukon_benchmark.Track(
            "Modexp", "MODEXP", 4, False
        )
        summary_path = self.write_text("")

        yukon_benchmark.write_score(
            "modexp",
            self.write_text("00\n"),
            self.write_csv(
                [
                    ("generated 256-bit #02 full exponent", 200, 50),
                    ("BN254 modular inversion", 200, 50),
                    ("generated RSA-1024 #01 e=3", 1_600, 100),
                    ("EIP-198 example 1", 8_100, 100),
                ]
            ),
            self.write_text(""),
            summary_path,
        )

        self.assertIn(
            "- Weighted precompile multiple: **12.000×**",
            summary_path.read_text(encoding="utf-8"),
        )


if __name__ == "__main__":
    unittest.main()

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


class BenchmarkScoreTests(unittest.TestCase):
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

    def write_framed_csv(
        self, rows: list[tuple[str, int, str, int]]
    ) -> Path:
        temporary = tempfile.NamedTemporaryFile(mode="w", newline="", delete=False)
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            writer = csv.writer(temporary)
            writer.writerow(["vector", "bytes", "frame", "status", "gas"])
            for label, byte_count, frame, gas in rows:
                writer.writerow([label, byte_count, frame, "ok", gas])
        return Path(temporary.name)

    def test_ripemd_score_is_suite_overhead_index(self) -> None:
        score, metrics = yukon_benchmark.parse_framed_csv(
            self.write_framed_csv(
                [
                    ("empty", 0, "clean", 1_000),
                    ("empty", 0, "dirty", 1_000),
                    ("33-byte", 33, "clean", 2_000),
                    ("33-byte", 33, "dirty", 2_000),
                ]
            ),
            2,
        )

        self.assertEqual(score, 2_083)
        self.assertEqual(metrics["cleanTotalGas"], 3_000)
        self.assertEqual(metrics["precompileTotalGas"], 1_440)
        self.assertEqual(metrics["scoreUnitsPerPrecompileMultiple"], 1_000)
        self.assertEqual(metrics["aggregation"], "suiteRatio")

    def test_ripemd_rejects_different_frame_sizes(self) -> None:
        with self.assertRaisesRegex(
            ValueError, "input size differs between frames for input"
        ):
            yukon_benchmark.parse_framed_csv(
                self.write_framed_csv(
                    [
                        ("input", 32, "clean", 1_000),
                        ("input", 33, "dirty", 1_000),
                    ]
                ),
                1,
            )

    def test_public_ripemd_reference_overhead_index(self) -> None:
        sizes = [
            0, 3, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 256, 376,
            1_000, 1_000, 369, 158, 971, 760, 549, 338, 127, 940, 729, 518,
            307, 96, 909, 698, 487, 276, 65, 878, 667, 456, 245, 34, 847,
            636, 425, 214, 3, 816, 605, 394, 183, 996,
        ]
        rows = []
        for index, byte_count in enumerate(sizes):
            gas = 49_312_421 if index == 0 else 0
            rows.append((f"vector {index}", byte_count, "clean", gas))
            rows.append((f"vector {index}", byte_count, "dirty", gas))
        score, metrics = yukon_benchmark.parse_framed_csv(
            self.write_framed_csv(rows),
            49,
        )

        self.assertEqual(score, 476_724)
        self.assertEqual(metrics["precompileTotalGas"], 103_440)

    def test_ripemd_summary_names_and_formats_overhead_index(self) -> None:
        original_track = yukon_benchmark.TRACKS["ripemd160"]
        self.addCleanup(
            yukon_benchmark.TRACKS.__setitem__, "ripemd160", original_track
        )
        yukon_benchmark.TRACKS["ripemd160"] = yukon_benchmark.Track(
            "Ripemd160", "RIPEMD-160", 2, True
        )
        summary_path = self.write_text("")

        yukon_benchmark.write_score(
            "ripemd160",
            self.write_text("00\n"),
            self.write_framed_csv(
                [
                    ("empty", 0, "clean", 1_000),
                    ("empty", 0, "dirty", 1_000),
                    ("33-byte", 33, "clean", 2_000),
                    ("33-byte", 33, "dirty", 2_000),
                ]
            ),
            self.write_text(""),
            summary_path,
        )

        summary = summary_path.read_text(encoding="utf-8")
        self.assertIn("- Verified overhead index: **2,083**", summary)
        self.assertIn("- Precompile multiple: **2.083×**", summary)

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
        self.assertIn(
            "- Verified overhead index: **12,000**",
            summary_path.read_text(encoding="utf-8"),
        )


if __name__ == "__main__":
    unittest.main()

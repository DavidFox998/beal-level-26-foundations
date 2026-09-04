#!/usr/bin/env python3
"""Check the v1.3.0 SageMath certificates against the archived ledger."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

LEDGER = Path("sagemath/level_26_ledger.json")
DECOMP = Path("sagemath/certs/j0_26_decomposition.json")
M3 = Path("sagemath/certs/formal_immersion_M3.json")
MANIFEST = Path("sagemath/foundations_doi_manifest.json")

EXPECTED_DECOMP = "35ea70c995f9aed3ae8e2f44cf231d0b7a3ae606e11ad5646635c47fa522a750"
EXPECTED_M3 = "856d021754287f3436ec4ffa67b35b5257cd443681f7ab5ac7355502cafa58e0"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    ledger = json.loads(LEDGER.read_text())
    decomp = json.loads(DECOMP.read_text())
    m3 = json.loads(M3.read_text())
    manifest = json.loads(MANIFEST.read_text())

    assert sha(DECOMP) == EXPECTED_DECOMP
    assert sha(M3) == EXPECTED_M3
    assert decomp["version"] == m3["version"] == manifest["version"] == "v1.3.0"
    assert decomp["previous"] == m3["previous"] == manifest["previous"] == "v1.2.1"
    assert decomp["J0_dimension"] == m3["J0_dimension"] == 2
    assert decomp["picard_compatible_dim_eq_genus_arithmetic"] is True
    assert [f["cremona_label"] for f in decomp["decomposition"]] == ["26a1", "26b1"]
    assert decomp["decomposition"][0]["a_invariants"] == [1, 0, 1, -5, -8]
    assert decomp["decomposition"][1]["a_invariants"] == [1, -1, 1, -3, 3]
    assert m3["M3_mod_3"] == [[1, 1], [0, 2]]
    assert m3["coefficient_matrix_mod_3"] == [[1, 1], [2, 1]]
    assert m3["M3_rank"] == 2
    assert m3["M3_det_mod_3"] == 2
    assert m3["modular_symbols_new_cuspidal_dimension"] == 2

    a_qexp = ledger["forms"][0]["qexp"]
    b_qexp = ledger["forms"][1]["qexp"]
    assert decomp["decomposition"][0]["qexp_a0_to_a20"] == a_qexp[:21]
    assert decomp["decomposition"][1]["qexp_a0_to_a20"] == b_qexp[:21]
    assert m3["newforms"][0]["qexp_a0_to_a20"] == a_qexp[:21]
    assert m3["newforms"][1]["qexp_a0_to_a20"] == b_qexp[:21]

    print(
        "verified v1.3.0 certificates; "
        f"decomp={EXPECTED_DECOMP} m3={EXPECTED_M3}"
    )


if __name__ == "__main__":
    main()

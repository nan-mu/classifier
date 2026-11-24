"""Build release specs from the original task evidence."""

import argparse
from pathlib import Path

from proof import json_file
from spec_inputs import EXB2, NETWORK, network_cases, vector


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True)
    for name in sorted(EXB2 + NETWORK):
        paths = sorted((args.evidence / "vectors" / name).glob("*/expected.json"))
        if len(paths) != (1 if name == "just_drop" else 2):
            raise ValueError(f"missing original vector(s) for {name}")
        vectors = [vector(path.parent) for path in paths]
        cases = [] if name in EXB2 else network_cases(name, vectors)
        json_file(args.out / f"{name}.json", {"vectors": vectors, "cases": cases})


if __name__ == "__main__":
    main()

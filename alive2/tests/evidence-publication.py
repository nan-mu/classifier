#!/usr/bin/env python3
import argparse
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--loader', type=Path, required=True)
    parser.add_argument('--index', type=Path, required=True)
    args = parser.parse_args()
    gate = Path(__file__).with_name('run-rust-file-e2e.py')
    with tempfile.TemporaryDirectory(prefix='alive-evidence-') as directory:
        root = Path(directory)
        marker = root / 'verification.json'
        unrelated = root / 'unrelated.txt'
        unrelated.write_text('keep')
        for compiler, loader in [('/usr/bin/false', args.loader), (args.compiler, '/usr/bin/false')]:
            marker.write_text('{"status":"verified_for_recorded_checks"}')
            result = subprocess.run(['python3', str(gate), '--compiler', str(compiler), '--loader', str(loader), '--index', str(args.index), '--out-dir', str(root)], capture_output=True, text=True, timeout=60)
            assert result.returncode != 0, result.stdout
            assert not marker.exists(), 'stale success marker after failed rerun'
            assert unrelated.read_text() == 'keep'
        normalized = root / 'bitswap' / 'bitswap.normalized.alive'
        normalized.mkdir()
        marker.write_text('{"status":"verified_for_recorded_checks"}')
        result = subprocess.run(['python3', str(gate), '--compiler', str(args.compiler), '--loader', str(args.loader), '--index', str(args.index), '--out-dir', str(root)], capture_output=True, text=True, timeout=60)
        assert result.returncode != 0
        assert not marker.exists()
        assert normalized.is_dir()
        assert unrelated.read_text() == 'keep'
    print('3 failed-rerun evidence publication cases passed')


if __name__ == '__main__':
    main()

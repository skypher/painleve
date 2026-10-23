#!/usr/bin/env python3
"""Content-addressed Lean CI verdicts; no Lean installation needed on reuse."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

SCHEMA = 1
DEFAULT_ROOT = Path(__file__).resolve().parents[2]


def tracked_files(root):
    data = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
    return sorted(p.decode("utf-8") for p in data.split(b"\0") if p)


def proof_input(path):
    return path.startswith(".github/") or (
        path.startswith("lean/") and (
            path.endswith(".lean") or path in {
                "lean/lean-toolchain", "lean/lakefile.toml", "lean/lakefile.lean",
                "lean/lake-manifest.json",
            }
        )
    )


def fingerprint(root):
    digest = hashlib.sha256(b"painleve-lean-verdict-v1\0")
    files = [p for p in tracked_files(root) if proof_input(p)]
    if not files:
        raise ValueError("No tracked proof inputs found")
    for name in files:
        data = (root / name).read_bytes()
        digest.update(name.encode() + b"\0")
        digest.update(str(len(data)).encode() + b"\0" + data)
    return digest.hexdigest()


def emit(name, value):
    if "\n" in value or "\r" in value:
        raise ValueError("Invalid multiline workflow output")
    print(f"{name}={value}", flush=True)
    if output := os.environ.get("GITHUB_OUTPUT"):
        with open(output, "a", encoding="utf-8") as stream:
            stream.write(f"{name}={value}\n")


def result_path(root):
    return root / ".ci-result/result.json"


def read_result(root, expected):
    try:
        value = json.loads(result_path(root).read_text())
        if (value.get("schema") == SCHEMA and value.get("fingerprint") == expected
                and value.get("status") in {"success", "failure"}
                and isinstance(value.get("run_url"), str)):
            return value
    except (OSError, ValueError, AttributeError, TypeError):
        pass
    return None


def record(root, expected, status, run_url):
    target = result_path(root)
    target.parent.mkdir(parents=True, exist_ok=True)
    value = {"schema": SCHEMA, "fingerprint": expected, "status": status, "run_url": run_url}
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=target.parent,
                                     delete=False) as stream:
        json.dump(value, stream, sort_keys=True)
        stream.write("\n")
        temporary = Path(stream.name)
    temporary.replace(target)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_ROOT, help="repository root")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("fingerprint", help="hash tracked Lean, dependency and CI inputs")
    commands.add_parser("mathlib-imports", help="list mathlib modules needed by the project")
    inspect = commands.add_parser("inspect", help="report success/failure/miss for a cached record")
    inspect.add_argument("--fingerprint", required=True)
    inspect.add_argument("--force", action="store_true", help="ignore any cached verdict")
    save = commands.add_parser("record", help="atomically save the actual build outcome")
    save.add_argument("--fingerprint", required=True)
    save.add_argument("--status", required=True, choices=["success", "failure"])
    save.add_argument("--run-url", required=True)
    verdict = commands.add_parser("verdict", help="exit green (0) or red (1) from the recorded outcome")
    verdict.add_argument("--fingerprint", required=True)
    args = parser.parse_args()
    root = args.repo.resolve()
    if args.command == "fingerprint":
        emit("hash", fingerprint(root))
    elif args.command == "mathlib-imports":
        modules = set()
        for path in tracked_files(root):
            if path.startswith("lean/") and path.endswith(".lean"):
                for line in (root / path).read_text().splitlines():
                    parts = line.split("--", 1)[0].split()
                    if parts[:1] == ["public"]:
                        parts = parts[1:]
                    if parts[:1] == ["import"]:
                        modules.update(p for p in parts[1:] if p.startswith("Mathlib."))
        if not modules:
            raise ValueError("No mathlib imports found")
        print("\n".join(sorted(modules)), flush=True)
    elif args.command == "inspect":
        value = None if args.force else read_result(root, args.fingerprint)
        emit("result", value["status"] if value else "miss")
        if value:
            print(f"Reusing {value['status']} from {value['run_url']}", flush=True)
    elif args.command == "record":
        record(root, args.fingerprint, args.status, args.run_url)
        print(f"Recorded {args.status} for {args.fingerprint}", flush=True)
    elif args.command == "verdict":
        value = read_result(root, args.fingerprint)
        if value is None:
            print("No valid build verdict; refusing to report green", flush=True)
            return 2
        print(f"Lean proof: {value['status']} ({value['run_url']})", flush=True)
        return 0 if value["status"] == "success" else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

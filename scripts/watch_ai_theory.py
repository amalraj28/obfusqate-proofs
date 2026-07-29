#!/usr/bin/env python3
"""Watch an Isabelle theory and regenerate its proof-free companion."""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from generate_ai_theory import GenerationError, generate_file


def format_generation_error(source: Path, error: OSError | GenerationError) -> str:
    location = str(source)
    if isinstance(error, GenerationError) and error.line is not None:
        location += f":{error.line}"
    context = ""
    if isinstance(error, GenerationError) and error.context:
        context = f" [{error.context}]"
    return f"generation failed: {location}: {error}{context}"


def signature(path: Path) -> tuple[int, int, int] | None:
    try:
        stat = path.stat()
    except FileNotFoundError:
        return None
    return (stat.st_mtime_ns, stat.st_size, getattr(stat, "st_ino", 0))


def watch(source: Path, output: Path, interval: float, debounce: float) -> None:
    previous: tuple[int, int, int] | None | object = object()
    pending_since: float | None = None
    pending_signature: tuple[int, int, int] | None = None

    print(f"watching {source} (press Ctrl+C to stop)")
    while True:
        current = signature(source)
        now = time.monotonic()
        if current != previous:
            previous = current
            pending_signature = current
            pending_since = now

        if pending_since is not None and now - pending_since >= debounce:
            stable = signature(source)
            if stable != pending_signature:
                previous = stable
                pending_signature = stable
                pending_since = now
            else:
                pending_since = None
                if stable is None:
                    print(f"source unavailable: {source}", file=sys.stderr)
                else:
                    try:
                        generate_file(source, output)
                    except (OSError, GenerationError) as error:
                        print(format_generation_error(source, error), file=sys.stderr)
                    else:
                        print(f"regenerated {output}")
        time.sleep(interval)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--interval", type=float, default=0.25)
    parser.add_argument("--debounce", type=float, default=0.4)
    args = parser.parse_args()
    if args.interval <= 0 or args.debounce < 0:
        parser.error("--interval must be positive and --debounce must be non-negative")
    try:
        watch(args.source, args.output, args.interval, args.debounce)
    except KeyboardInterrupt:
        print("watcher stopped")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

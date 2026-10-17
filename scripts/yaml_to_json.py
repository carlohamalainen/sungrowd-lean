# /// script
# requires-python = ">=3.11"
# dependencies = ["pyyaml>=6"]
# ///
"""Convert the ``modbus`` block of reference/modbus_sungrow.yaml to JSON.

One time YAML to JSON conversion of https://github.com/mkaiser/Sungrow-SHx-Inverter-Modbus-Home-Assistant/blob/main/modbus_sungrow.yaml

YAML notes:

* ``!secret name``  -> the string ``"name"``.
* anchors/aliases   -> resolved to their values (``*scan_interval_fast`` -> 10).
* hex ints ``0xAA`` -> decimal ints (170).
* comments          -> dropped.

We try to be strict about validating all of the content.

Usage:
    uv run scripts/yaml_to_json.py [--debug] [IN.yaml] [OUT.json]
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from collections import Counter
from pathlib import Path

import yaml

log = logging.getLogger("yaml_to_json")

HERE = Path(__file__).resolve().parent
DEFAULT_IN = HERE.parent / "reference" / "modbus_sungrow.yaml"
DEFAULT_OUT = HERE.parent / "reference" / "modbus_sungrow.json"

KEPT_TOP_LEVEL = "modbus"

# Keys and value types we expect.

HUB_KEYS = {
    "name"                      : str,
    "type"                      : str,
    "host"                      : str,
    "port"                      : str,
    "delay"                     : int,
    "timeout"                   : int,
    "message_wait_milliseconds" : str,
    "sensors"                   : list,
}

HUB_IGNORE_KEYS = {"switches"}

SENSOR_KEYS = {
    "name"                : str,
    "unique_id"           : str,
    "device_address"      : str,
    "address"             : int,
    "input_type"          : str,
    "data_type"           : str,
    "count"               : int,
    "swap"                : str,
    "scale"               : (int, float),
    "precision"           : int,
    "scan_interval"       : int,
    "nan_value"           : int,
    "unit_of_measurement" : str,
    "device_class"        : str,
    "state_class"         : str,
}

SENSOR_REQUIRED = {"name", "unique_id", "address", "input_type", "data_type"}

INPUT_TYPES = {"input", "holding"}

DATA_TYPES = {"int16", "uint16", "int32", "uint32", "string"}

SWAPS = {"word"}

class SecretLoader(yaml.SafeLoader):
    """SafeLoader that accepts Home Assistant's ``!secret`` tag.

    ``!secret foo`` becomes the plain string ``"foo"``. Any other custom tag
    still raises ``ConstructorError`` from SafeLoader.
    """


def _construct_secret(loader: yaml.SafeLoader, node: yaml.Node) -> str:
    value = loader.construct_scalar(node)
    log.debug("!secret %s", value)
    return value


SecretLoader.add_constructor("!secret", _construct_secret)


class ConversionError(Exception):
    pass


def check_keys(what: str, obj: dict, schema: dict[str, type | tuple]) -> None:
    unknown = set(obj) - set(schema)

    for k in HUB_IGNORE_KEYS:
        unknown.discard(k)

    if unknown:
        raise ConversionError(f"{what}: unknown keys {sorted(unknown)}")
    for k, v in obj.items():
        if k in HUB_IGNORE_KEYS: continue

        # bool is a subclass of int in Python; reject it explicitly so the
        # YAML 1.1 yes/no/on/off trap cannot slip through as an int.
        if isinstance(v, bool) or v is None:
            raise ConversionError(f"{what}: key {k!r} has bool/null value {v!r}")
        if not isinstance(v, schema[k]):
            raise ConversionError(
                f"{what}: key {k!r} has type {type(v).__name__}, want {schema[k]}"
            )


def check_sensor(s: dict) -> None:
    what = f"sensor {s.get('unique_id', s.get('name', '?'))!r}"
    check_keys(what, s, SENSOR_KEYS)
    missing = SENSOR_REQUIRED - set(s)
    if missing:
        raise ConversionError(f"{what}: missing keys {sorted(missing)}")
    if s["input_type"] not in INPUT_TYPES:
        raise ConversionError(f"{what}: input_type {s['input_type']!r}")
    if s["data_type"] not in DATA_TYPES:
        raise ConversionError(f"{what}: data_type {s['data_type']!r}")
    if "swap" in s and s["swap"] not in SWAPS:
        raise ConversionError(f"{what}: swap {s['swap']!r}")
    if s["data_type"] == "string" and "count" not in s:
        raise ConversionError(f"{what}: string sensor without count")
    if not 0 <= s["address"] <= 0xFFFF:
        raise ConversionError(f"{what}: address {s['address']} out of range")


def check_unique(what: str, items: list[dict]) -> None:
    dupes = [u for u, n in Counter(i["unique_id"] for i in items).items() if n > 1]
    if dupes:
        raise ConversionError(f"{what}: duplicate unique_id {dupes}")


def convert(src: Path) -> dict:
    t0 = time.perf_counter()
    text = src.read_text(encoding="utf-8")
    log.debug("read %d bytes from %s", len(text), src)

    root = yaml.load(text, Loader=SecretLoader)
    log.info("parsed YAML in %.1f ms", (time.perf_counter() - t0) * 1000)

    if not isinstance(root, dict):
        raise ConversionError(f"top level is {type(root).__name__}, want mapping")
    dropped = sorted(set(root) - {KEPT_TOP_LEVEL})
    log.info("top-level keys: keeping %r, dropping %r", KEPT_TOP_LEVEL, dropped)

    hubs = root[KEPT_TOP_LEVEL]
    if not isinstance(hubs, list) or len(hubs) != 1:
        raise ConversionError(f"expected exactly one modbus hub, got {hubs!r:.80}")
    hub = hubs[0]
    check_keys("hub", hub, HUB_KEYS)
    log.info("hub %r: %d sensors",
             hub["name"], len(hub["sensors"]))

    for s in hub["sensors"]:
        check_sensor(s)
        log.debug("sensor %-45s addr=%5d %-7s %-6s scale=%-5s count=%s",
                  s["unique_id"], s["address"], s["input_type"], s["data_type"],
                  s.get("scale", 1), s.get("count", 1))
    check_unique("sensors", hub["sensors"])

    log.info("data_type counts: %s", dict(Counter(s["data_type"] for s in hub["sensors"])))
    log.info("input_type counts: %s", dict(Counter(s["input_type"] for s in hub["sensors"])))
    log.info("distinct scales: %s", sorted({s.get("scale", 1) for s in hub["sensors"]}))
    log.info("distinct scan_intervals: %s",
             sorted({s["scan_interval"] for s in hub["sensors"] if "scan_interval" in s}))

    for k in HUB_IGNORE_KEYS:
        log.info("ignoring hub key: %s", k)
        del hub[k]

    return {KEPT_TOP_LEVEL: [hub]}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("src", nargs="?", type=Path, default=DEFAULT_IN)
    ap.add_argument("dst", nargs="?", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--debug", action="store_true", help="log at DEBUG level")
    args = ap.parse_args(argv)

    logging.basicConfig(
        level=logging.DEBUG if args.debug else logging.INFO,
        format="%(asctime)s %(levelname)-5s %(name)s: %(message)s",
    )

    try:
        out = convert(args.src)
    except (ConversionError, yaml.YAMLError) as e:
        log.error("%s", e)
        return 1

    t0 = time.perf_counter()
    with args.dst.open("w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)
        f.write("\n")
    log.info("wrote %s (%d bytes) in %.1f ms",
             args.dst, args.dst.stat().st_size, (time.perf_counter() - t0) * 1000)
    return 0


if __name__ == "__main__":
    sys.exit(main())

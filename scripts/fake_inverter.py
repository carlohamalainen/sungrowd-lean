"""A fake Sungrow inverter: Modbus TCP, FC3/FC4 reads and FC16 writes.

Input registers default to 0, except SOC (13022, tenths of a percent), grid power
(13009/13010, int32 low word first) and battery power (5213/5214, same), set by
FAKE_SOC, FAKE_GRID and FAKE_BATT. Holding registers 13049..13051 start in
self-consumption (0, 0xCC, 0) and keep what is written.

FAKE_FAIL_EVERY=n makes every n-th request fail with modbus exception 4.

Usage: uv run --no-project scripts/fake_inverter.py [port]   (default 15020)

Then point sungrowd at it:
  SUNGROWD_WINET_HOST=127.0.0.1 SUNGROWD_WINET_PORT=15020 .lake/build/bin/sungrowd tick samples/adaptive-all-day.json
"""

import asyncio
import logging
import os
import struct
import sys

log = logging.getLogger("fake_inverter")

holding = {13049: 0, 13050: 0xCC, 13051: 0}
requests = 0


def int32_low_first(v: int) -> tuple[int, int]:
    u = v & 0xFFFFFFFF
    return u & 0xFFFF, (u >> 16) & 0xFFFF


def input_regs() -> dict[int, int]:
    soc = int(os.environ.get("FAKE_SOC", "500"))
    grid = int(os.environ.get("FAKE_GRID", "-300"))
    batt = int(os.environ.get("FAKE_BATT", "0"))
    regs = {13022: soc}
    regs[13009], regs[13010] = int32_low_first(grid)
    regs[5213], regs[5214] = int32_low_first(batt)
    return regs


def respond(pdu: bytes) -> bytes:
    global requests
    requests += 1
    fc = pdu[0]
    fail_every = int(os.environ.get("FAKE_FAIL_EVERY", "0"))
    if fail_every and requests % fail_every == 0:
        log.info("request %d: injecting exception 4", requests)
        return bytes([fc | 0x80, 4])
    if fc in (3, 4):
        addr, n = struct.unpack(">HH", pdu[1:5])
        table = holding if fc == 3 else input_regs()
        vals = [table.get(addr + i, 0) for i in range(n)]
        log.debug("fc%d read %d..%d", fc, addr, addr + n - 1)
        return bytes([fc, 2 * n]) + b"".join(struct.pack(">H", v) for v in vals)
    if fc == 16:
        addr, n, _ = struct.unpack(">HHB", pdu[1:6])
        vals = struct.unpack(f">{n}H", pdu[6:6 + 2 * n])
        for i, v in enumerate(vals):
            holding[addr + i] = v
        log.info("fc16 write %d..%d = %s", addr, addr + n - 1, list(vals))
        return struct.pack(">BHH", 16, addr, n)
    log.warning("unsupported function code %d", fc)
    return bytes([fc | 0x80, 1])


async def serve(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
    peer = writer.get_extra_info("peername")
    log.debug("connection from %s", peer)
    try:
        while True:
            header = await reader.readexactly(7)
            tx, proto, length, unit = struct.unpack(">HHHB", header)
            pdu = await reader.readexactly(length - 1)
            body = respond(pdu)
            writer.write(struct.pack(">HHHB", tx, proto, len(body) + 1, unit) + body)
            await writer.drain()
    except asyncio.IncompleteReadError:
        log.debug("connection from %s closed", peer)
    finally:
        writer.close()


async def main() -> None:
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 15020
    server = await asyncio.start_server(serve, "127.0.0.1", port)
    log.info("listening on 127.0.0.1:%d", port)
    async with server:
        await server.serve_forever()


if __name__ == "__main__":
    logging.basicConfig(
        level=os.environ.get("FAKE_LOG_LEVEL", "INFO"),
        format="%(asctime)s %(levelname)s %(message)s",
    )
    asyncio.run(main())

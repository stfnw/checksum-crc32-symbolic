# SPDX-FileCopyrightText: 2025 stfnw. Derived from CRC32 implementation of Hacker's Delight.
#
# SPDX-License-Identifier: MIT

import z3


# Original code from Hacker's Delight.
# https://web.archive.org/web/20160306132125/https://www.hackersdelight.org/hdcodetxt/crc.c.txt
# https://web.archive.org/web/20160309224818/http://www.hackersdelight.org/permissions.htm


def crc32(msg):
    assert msg.size() % 8 == 0
    crc = z3.BitVecVal(0xFFFFFFFF, 32)
    polynomial = z3.BitVecVal(0xEDB88320, 32)
    for i in range(0, msg.size(), 8):
        i = msg.size() - 8 - i
        b = z3.Extract(31, 0, z3.LShR(msg, i) & 0xFF)
        crc = crc ^ b
        for _ in range(8):
            mask = -(crc & 1)
            crc = z3.LShR(crc, 1) ^ (polynomial & mask)
    return ~crc


def bitstringtobytes(bs):
    length = (len(bs) + 7) // 8
    return int(bs, 2).to_bytes(length, "big")


# Wrapper around computing crc32 of a given constant byte message with z3.
def crc32_(msg):
    i = int.from_bytes(msg, byteorder="big")
    msg = z3.BitVecVal(i, len(msg) * 8)
    checksum = hex(z3.simplify(crc32(msg)).as_long())[2:]
    return checksum


def main():
    assert "4a17b156" == crc32_(b"Hello World")


if __name__ == "__main__":
    main()

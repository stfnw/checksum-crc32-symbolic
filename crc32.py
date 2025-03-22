# SPDX-FileCopyrightText: 2025 stfnw. Derived from CRC32 implementation of Hacker's Delight.
#
# SPDX-License-Identifier: MIT

import z3
import binascii


# Original code from Hacker's Delight.
# https://web.archive.org/web/20160306132125/https://www.hackersdelight.org/hdcodetxt/crc.c.txt
# https://web.archive.org/web/20160309224818/http://www.hackersdelight.org/permissions.htm


def crc32(msg: z3.BitVecRef) -> z3.BitVecRef:
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


def isprintable(bv: z3.BitVecRef) -> z3.BoolRef:
    conditions = []
    for i in range(0, bv.size(), 8):
        by = z3.Extract(i + 7, i, bv)
        conditions.append(0x20 <= by)
        conditions.append(by <= 0x7E)
    return z3.And(conditions)


def bitstringtobytes(bs: str) -> bytes:
    length = (len(bs) + 7) // 8
    return int(bs, 2).to_bytes(length, "big")


# Wrapper around computing crc32 of a given constant byte message with z3.
def crc32_(msg: bytes) -> str:
    i = int.from_bytes(msg, byteorder="big")
    msg = z3.BitVecVal(i, len(msg) * 8)
    checksum = hex(z3.simplify(crc32(msg)).as_long())[2:]
    return checksum


def main() -> None:
    assert "4a17b156" == crc32_(b"Hello World")

    size = 48
    msg = z3.BitVec("msg", size)

    s = z3.Solver()

    # Find message whose checksum ends with a null byte.
    # s.add(z3.Extract(7, 0, crc32(msg)) == z3.BitVecVal(0, 8))

    # Find printable message whose checksum is also printable.
    s.add(z3.And(isprintable(msg), isprintable(crc32(msg))))

    for _ in range(10):  # Get some examples
        if s.check() == z3.sat:
            print("SAT")
            m = s.model()
            msgval = m.evaluate(msg)

            crc32z3 = hex(z3.simplify(crc32(msgval)).as_long())[2:]

            msghex = hex(msgval.as_long())[2:]
            print(
                "Message {} ('{}') has crc32 of {}".format(
                    msghex, binascii.unhexlify(msghex).decode(), crc32z3
                )
            )


if __name__ == "__main__":
    main()

This repo implements CRC32 checksumming symbolically using the z3 SAT/SMT solver python API and its propositional logic / bitvector theories.
This allows formulating constraints on the inputs and outputs.

# Example input/output pairs

Last byte is null:
Message 759103b3a0c5 has crc32 of 96ef5600

Printable message whose checksum is also printable:
Message 4d5532204258 ('MU2 BX') has crc32 of 37677a21

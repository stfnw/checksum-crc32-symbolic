This repo implements CRC32 checksumming symbolically using the z3 SAT/SMT solver python API and its propositional logic / bitvector theories.
This allows formulating constraints on the inputs and outputs.

# Example input/output pairs

Last byte is null:
Message 759103b3a0c5 has crc32 of 96ef5600

Printable message whose checksum is also printable:
Message 4d5532204258 ('MU2 BX') has crc32 of 37677a21
Message 4e2d5c76424b ('N-\vBK') has crc32 of 4f27306d
Message 39735d702267 ('9s]p"g') has crc32 of 3537602d
Message 6a422749404b ('jB'I@K') has crc32 of 69477063
Message 362220267420 ('6" &t ') has crc32 of 342f3021
Message 512327207733 ('Q#' w3') has crc32 of 2a777065
Message 474e2b625636 ('GN+bV6') has crc32 of 5b672565
Message 2031795e334b (' 1y^3K') has crc32 of 4f5f2427
Message 6b2c3139357c ('k,195|') has crc32 of 4f6f2245

Specific checksum values:
Message b14bc7ddba7d has crc32 of 11223344

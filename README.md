This repo implements CRC32 checksumming symbolically using the z3 SAT/SMT solver python API and its propositional logic / bitvector theories.
This allows formulating constraints on the inputs and outputs.

# Example input/output pairs

Last byte is null:
- Message 759103b3a0c5 has crc32 of 96ef5600

Printable message whose checksum is also printable:
- Message 4d5532204258 (`MU2 BX`) has crc32 of 37677a21 (`7gz!`)
- Message 4e2d5c76424b (`N-\vBK`) has crc32 of 4f27306d (`O'0m`)
- Message 39735d702267 (`9s]p"g`) has crc32 of 3537602d (`57``-`)
- Message 6a422749404b (`jB'I@K`) has crc32 of 69477063 (`iGpc`)
- Message 362220267420 (`6" &t `) has crc32 of 342f3021 (`4/0!`)
- Message 512327207733 (`Q#' w3`) has crc32 of 2a777065 (`*wpe`)
- Message 474e2b625636 (`GN+bV6`) has crc32 of 5b672565 (`[g%e`)
- Message 722a7c6e5c65 (`r*|n\e`) has crc32 of 342f444d (`4/DM`)
- Message 2031795e334b (` 1y^3K`) has crc32 of 4f5f2427 (`O_$'`)
- Message 6b2c3139357c (`k,195|`) has crc32 of 4f6f2245 (`Oo"E`)

Specific checksum values:
- Message b14bc7ddba7d has crc32 of 11223344
- Message 813d8f35a2c6 has crc32 of 44332211
- Message 2ed8a84b0faf has crc32 of 00000000
- Message f4b87a8d507c has crc32 of 11111111
- Message b12200d4ba15 has crc32 of 22222222
- Message a848417fe7c6 has crc32 of 33333333
- Message 8322f0b6c6cb has crc32 of 44444444
- Message 594222709918 has crc32 of 55555555
- Message c137e36d5075 has crc32 of 66666666
- Message b0374baf4ea6 has crc32 of 77777777
- Message b01e45c2da76 has crc32 of 88888888
- Message a974046987a5 has crc32 of 99999999
- Message 596b2c1d0dc8 has crc32 of aaaaaaaa
- Message 286b84df131b has crc32 of bbbbbbbb
- Message a8614f127316 has crc32 of cccccccc
- Message b10b0eb92ec5 has crc32 of dddddddd
- Message c1f7afe624aa has crc32 of eeeeeeee
- Message 587e6766f97b has crc32 of ffffffff

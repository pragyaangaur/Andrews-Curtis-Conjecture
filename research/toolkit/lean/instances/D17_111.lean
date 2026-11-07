import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 111 of the cap-17 certificate: slots 56832 .. 57343 -/
theorem chk_111 : chunkCheck 17 T stdSt 56832 512 = true := by decide +kernel

end Row17

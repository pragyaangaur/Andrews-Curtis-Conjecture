import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 23 of the cap-17 certificate: slots 11776 .. 12287 -/
theorem chk_23 : chunkCheck 17 T stdSt 11776 512 = true := by decide +kernel

end Row17

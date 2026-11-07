import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 511 of the cap-17 certificate: slots 261632 .. 262143 -/
theorem chk_511 : chunkCheck 17 T stdSt 261632 512 = true := by decide +kernel

end Row17

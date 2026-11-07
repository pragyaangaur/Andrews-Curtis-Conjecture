import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 375 of the cap-17 certificate: slots 192000 .. 192511 -/
theorem chk_375 : chunkCheck 17 T stdSt 192000 512 = true := by decide +kernel

end Row17

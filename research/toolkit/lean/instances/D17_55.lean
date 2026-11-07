import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 55 of the cap-17 certificate: slots 28160 .. 28671 -/
theorem chk_55 : chunkCheck 17 T stdSt 28160 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 84 of the cap-17 certificate: slots 43008 .. 43519 -/
theorem chk_84 : chunkCheck 17 T stdSt 43008 512 = true := by decide +kernel

end Row17

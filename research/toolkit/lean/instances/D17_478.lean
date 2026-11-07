import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 478 of the cap-17 certificate: slots 244736 .. 245247 -/
theorem chk_478 : chunkCheck 17 T stdSt 244736 512 = true := by decide +kernel

end Row17

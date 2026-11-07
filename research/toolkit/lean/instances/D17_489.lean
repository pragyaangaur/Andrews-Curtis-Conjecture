import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 489 of the cap-17 certificate: slots 250368 .. 250879 -/
theorem chk_489 : chunkCheck 17 T stdSt 250368 512 = true := by decide +kernel

end Row17

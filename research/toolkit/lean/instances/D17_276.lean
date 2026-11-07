import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 276 of the cap-17 certificate: slots 141312 .. 141823 -/
theorem chk_276 : chunkCheck 17 T stdSt 141312 512 = true := by decide +kernel

end Row17

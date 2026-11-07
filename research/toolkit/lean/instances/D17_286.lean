import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 286 of the cap-17 certificate: slots 146432 .. 146943 -/
theorem chk_286 : chunkCheck 17 T stdSt 146432 512 = true := by decide +kernel

end Row17

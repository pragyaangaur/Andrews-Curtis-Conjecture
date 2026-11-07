import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 279 of the cap-17 certificate: slots 142848 .. 143359 -/
theorem chk_279 : chunkCheck 17 T stdSt 142848 512 = true := by decide +kernel

end Row17

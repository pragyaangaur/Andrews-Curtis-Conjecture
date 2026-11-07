import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 356 of the cap-17 certificate: slots 182272 .. 182783 -/
theorem chk_356 : chunkCheck 17 T stdSt 182272 512 = true := by decide +kernel

end Row17

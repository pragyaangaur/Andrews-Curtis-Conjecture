import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 117 of the cap-17 certificate: slots 59904 .. 60415 -/
theorem chk_117 : chunkCheck 17 T stdSt 59904 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 485 of the cap-17 certificate: slots 248320 .. 248831 -/
theorem chk_485 : chunkCheck 17 T stdSt 248320 512 = true := by decide +kernel

end Row17

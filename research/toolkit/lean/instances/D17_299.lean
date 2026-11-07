import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 299 of the cap-17 certificate: slots 153088 .. 153599 -/
theorem chk_299 : chunkCheck 17 T stdSt 153088 512 = true := by decide +kernel

end Row17

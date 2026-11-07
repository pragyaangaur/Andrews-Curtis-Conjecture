import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 206 of the cap-17 certificate: slots 105472 .. 105983 -/
theorem chk_206 : chunkCheck 17 T stdSt 105472 512 = true := by decide +kernel

end Row17

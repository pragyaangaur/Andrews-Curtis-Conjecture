import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 433 of the cap-17 certificate: slots 221696 .. 222207 -/
theorem chk_433 : chunkCheck 17 T stdSt 221696 512 = true := by decide +kernel

end Row17

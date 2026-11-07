import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 30 of the cap-17 certificate: slots 15360 .. 15871 -/
theorem chk_30 : chunkCheck 17 T stdSt 15360 512 = true := by decide +kernel

end Row17

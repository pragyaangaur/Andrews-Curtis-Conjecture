import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 72 of the cap-17 certificate: slots 36864 .. 37375 -/
theorem chk_72 : chunkCheck 17 T stdSt 36864 512 = true := by decide +kernel

end Row17

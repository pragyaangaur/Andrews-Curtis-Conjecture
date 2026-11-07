import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 147 of the cap-17 certificate: slots 75264 .. 75775 -/
theorem chk_147 : chunkCheck 17 T stdSt 75264 512 = true := by decide +kernel

end Row17

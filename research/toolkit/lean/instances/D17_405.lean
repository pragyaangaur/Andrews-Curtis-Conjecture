import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 405 of the cap-17 certificate: slots 207360 .. 207871 -/
theorem chk_405 : chunkCheck 17 T stdSt 207360 512 = true := by decide +kernel

end Row17

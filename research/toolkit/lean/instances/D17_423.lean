import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 423 of the cap-17 certificate: slots 216576 .. 217087 -/
theorem chk_423 : chunkCheck 17 T stdSt 216576 512 = true := by decide +kernel

end Row17

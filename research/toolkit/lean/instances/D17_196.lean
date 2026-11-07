import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 196 of the cap-17 certificate: slots 100352 .. 100863 -/
theorem chk_196 : chunkCheck 17 T stdSt 100352 512 = true := by decide +kernel

end Row17

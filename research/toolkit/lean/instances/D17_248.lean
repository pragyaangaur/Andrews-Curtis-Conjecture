import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 248 of the cap-17 certificate: slots 126976 .. 127487 -/
theorem chk_248 : chunkCheck 17 T stdSt 126976 512 = true := by decide +kernel

end Row17

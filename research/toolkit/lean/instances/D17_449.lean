import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 449 of the cap-17 certificate: slots 229888 .. 230399 -/
theorem chk_449 : chunkCheck 17 T stdSt 229888 512 = true := by decide +kernel

end Row17

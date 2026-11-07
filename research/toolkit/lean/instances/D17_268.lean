import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 268 of the cap-17 certificate: slots 137216 .. 137727 -/
theorem chk_268 : chunkCheck 17 T stdSt 137216 512 = true := by decide +kernel

end Row17

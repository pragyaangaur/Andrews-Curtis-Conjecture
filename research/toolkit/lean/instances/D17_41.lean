import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 41 of the cap-17 certificate: slots 20992 .. 21503 -/
theorem chk_41 : chunkCheck 17 T stdSt 20992 512 = true := by decide +kernel

end Row17

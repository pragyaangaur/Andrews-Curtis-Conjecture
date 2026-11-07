import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 383 of the cap-17 certificate: slots 196096 .. 196607 -/
theorem chk_383 : chunkCheck 17 T stdSt 196096 512 = true := by decide +kernel

end Row17

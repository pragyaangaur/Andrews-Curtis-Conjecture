import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 415 of the cap-17 certificate: slots 212480 .. 212991 -/
theorem chk_415 : chunkCheck 17 T stdSt 212480 512 = true := by decide +kernel

end Row17

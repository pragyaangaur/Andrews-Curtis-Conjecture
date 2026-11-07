import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 10 of the cap-17 certificate: slots 5120 .. 5631 -/
theorem chk_10 : chunkCheck 17 T stdSt 5120 512 = true := by decide +kernel

end Row17

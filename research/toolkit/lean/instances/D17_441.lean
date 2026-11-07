import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 441 of the cap-17 certificate: slots 225792 .. 226303 -/
theorem chk_441 : chunkCheck 17 T stdSt 225792 512 = true := by decide +kernel

end Row17

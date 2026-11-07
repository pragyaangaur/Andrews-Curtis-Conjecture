import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 407 of the cap-17 certificate: slots 208384 .. 208895 -/
theorem chk_407 : chunkCheck 17 T stdSt 208384 512 = true := by decide +kernel

end Row17

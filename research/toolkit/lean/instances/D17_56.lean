import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 56 of the cap-17 certificate: slots 28672 .. 29183 -/
theorem chk_56 : chunkCheck 17 T stdSt 28672 512 = true := by decide +kernel

end Row17

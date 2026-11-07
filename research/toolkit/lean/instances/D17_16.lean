import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 16 of the cap-17 certificate: slots 8192 .. 8703 -/
theorem chk_16 : chunkCheck 17 T stdSt 8192 512 = true := by decide +kernel

end Row17

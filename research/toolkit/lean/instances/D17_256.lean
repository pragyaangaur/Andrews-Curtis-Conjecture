import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 256 of the cap-17 certificate: slots 131072 .. 131583 -/
theorem chk_256 : chunkCheck 17 T stdSt 131072 512 = true := by decide +kernel

end Row17

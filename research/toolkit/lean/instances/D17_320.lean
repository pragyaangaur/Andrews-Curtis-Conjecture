import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 320 of the cap-17 certificate: slots 163840 .. 164351 -/
theorem chk_320 : chunkCheck 17 T stdSt 163840 512 = true := by decide +kernel

end Row17

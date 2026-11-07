import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 176 of the cap-17 certificate: slots 90112 .. 90623 -/
theorem chk_176 : chunkCheck 17 T stdSt 90112 512 = true := by decide +kernel

end Row17

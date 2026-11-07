import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 370 of the cap-17 certificate: slots 189440 .. 189951 -/
theorem chk_370 : chunkCheck 17 T stdSt 189440 512 = true := by decide +kernel

end Row17

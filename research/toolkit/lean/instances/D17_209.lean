import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 209 of the cap-17 certificate: slots 107008 .. 107519 -/
theorem chk_209 : chunkCheck 17 T stdSt 107008 512 = true := by decide +kernel

end Row17
